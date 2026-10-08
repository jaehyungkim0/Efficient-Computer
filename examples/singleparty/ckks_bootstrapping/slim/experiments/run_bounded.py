#!/usr/bin/env python3
"""Run one experiment with an exclusive lock, RSS limit and disk-only output."""
import argparse
import fcntl
import json
import os
from pathlib import Path
import signal
import subprocess
import time


def process_group_members(pgid):
    rows = subprocess.check_output(["/bin/ps", "-axo", "pid=,pgid=,uid=,stat=,rss="], text=True)
    return [(int(pid), int(uid), state, int(rss) * 1024)
            for pid, group, uid, state, rss in (row.split() for row in rows.splitlines())
            if int(group) == pgid]


def process_group_rss(pgid):
    return sum(row[3] for row in process_group_members(pgid))


def live_group_members(pgid):
    return [row for row in process_group_members(pgid) if not row[2].startswith("Z")]


def kill_process_group(pgid):
    # On macOS, killpg can return EPERM for an already-exited group. Check
    # live members first, and never signal an unrelated or foreign process.
    members = live_group_members(pgid)
    if not members:
        return []
    if any(uid != os.getuid() for _, uid, _, _ in members):
        return ["process group contains a process owned by another user"]
    try:
        os.killpg(pgid, signal.SIGKILL)
        return []
    except ProcessLookupError:
        return []
    except PermissionError:
        errors = []
        for pid, uid, _, _ in live_group_members(pgid):
            try:
                if uid == os.getuid() and os.getpgid(pid) == pgid:
                    os.kill(pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            except PermissionError as exc:
                errors.append(f"cannot terminate process {pid}: {exc}")
        return errors


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rss-mib", type=int, required=True)
    parser.add_argument("--seconds", type=int, default=7200)
    parser.add_argument("--lock-wait-seconds", type=int, default=7200)
    parser.add_argument("--lock", default="/tmp/perfect-correct-heavy-job.lock")
    parser.add_argument("--log", required=True)
    parser.add_argument("--report", required=True)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command or not 64 <= args.rss_mib <= 24576:
        parser.error("provide a command and an RSS budget from 64 through 24576 MiB")
    if args.seconds <= 0 or args.lock_wait_seconds <= 0:
        parser.error("job and lock-wait timeouts must be positive")
    interrupted_signal = None

    def interrupt(signum, frame):
        nonlocal interrupted_signal
        interrupted_signal = signum
        raise KeyboardInterrupt

    signal.signal(signal.SIGINT, interrupt)
    signal.signal(signal.SIGTERM, interrupt)
    process_group_rss(-1)  # Check monitoring permission before starting a job.
    log_path, report_path = Path(args.log), Path(args.report)
    log_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.parent.mkdir(parents=True, exist_ok=True)
    # Never overwrite the evidence from an earlier execution.
    if log_path.exists() or report_path.exists():
        parser.error("log or report already exists; choose a new run name")
    with open(args.lock, "a") as lock:
        def lock_timeout(signum, frame):
            raise TimeoutError("exclusive job lock unavailable before timeout")

        previous_alarm = signal.signal(signal.SIGALRM, lock_timeout)
        signal.alarm(args.lock_wait_seconds)
        try:
            # Sleeping in the kernel lock queue avoids repeated batch polling.
            fcntl.flock(lock, fcntl.LOCK_EX)
        except TimeoutError as exc:
            raise SystemExit(str(exc))
        except KeyboardInterrupt:
            raise SystemExit("cancelled while waiting; no job was started")
        finally:
            signal.alarm(0)
            signal.signal(signal.SIGALRM, previous_alarm)
        env = dict(os.environ, GOMAXPROCS="1", OMP_NUM_THREADS="1",
                   OPENBLAS_NUM_THREADS="1", MKL_NUM_THREADS="1",
                   VECLIB_MAXIMUM_THREADS="1", NUMEXPR_NUM_THREADS="1", PYTHONUNBUFFERED="1",
                   GOMEMLIMIT=str(args.rss_mib * 1024 * 1024 * 2 // 3))
        start, peak, reason, child = time.monotonic(), 0, None, None
        code, cleanup_errors = 1, []

        def report(status=None):
            result = dict(status=status or ("passed" if code == 0 and not reason else "stopped" if reason else "failed"),
                          exit_code=code, reason=reason, cleanup_errors=cleanup_errors,
                          peak_rss_mib=round(peak / 1024**2, 2), rss_budget_mib=args.rss_mib,
                          seconds=round(time.monotonic() - start, 2), command=command,
                          log=str(log_path), gomaxprocs=1)
            temporary = report_path.with_suffix(report_path.suffix + ".tmp")
            temporary.write_text(json.dumps(result, indent=2) + "\n")
            temporary.replace(report_path)
            return result

        try:
            with log_path.open("x") as log:
                child = subprocess.Popen(command, stdout=log, stderr=subprocess.STDOUT,
                                         start_new_session=True, env=env)
                while child.poll() is None:
                    rss = process_group_rss(child.pid)
                    peak = max(peak, rss)
                    if rss > args.rss_mib * 1024 * 1024:
                        reason = "memory_budget"
                    elif time.monotonic() - start > args.seconds:
                        reason = "time_budget"
                    if reason:
                        report("stopping")
                        break
                    time.sleep(0.25)
                if reason is None:
                    code = child.wait()
        except KeyboardInterrupt:
            reason = "interrupted"
            code = 128 + (interrupted_signal or signal.SIGINT)
        except Exception as exc:
            reason = "runner_error"
            cleanup_errors.append(f"{type(exc).__name__}: {exc}")
        finally:
            if child is not None:
                # The command can have descendants even if its leader exited.
                signal.signal(signal.SIGINT, signal.SIG_IGN)
                signal.signal(signal.SIGTERM, signal.SIG_IGN)
                while True:
                    try:
                        errors = kill_process_group(child.pid)
                        if not live_group_members(child.pid):
                            break
                    except Exception as exc:
                        errors = [f"cleanup monitor: {type(exc).__name__}: {exc}"]
                    for error in errors:
                        if error not in cleanup_errors:
                            cleanup_errors.append(error)
                            print(error, flush=True)
                    # Do not release the exclusive lock while a child might
                    # still be alive. Persist diagnostics even on failure.
                    report("cleanup_pending")
                    time.sleep(0.25 if not errors else 2)
                child_code = child.wait()
                if reason not in ("interrupted", "runner_error"):
                    code = child_code
        result = report()
        # Give other two-second polling waiters a turn between batch jobs.
        fcntl.flock(lock, fcntl.LOCK_UN)
        time.sleep(3)
        print(json.dumps(result), flush=True)
        raise SystemExit(0 if result["status"] == "passed" else 1)


if __name__ == "__main__":
    main()
