"""Small subprocess tests for the experiment runner, without FHE workloads."""
import json
import importlib.util
import os
from pathlib import Path
import runpy
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location("bounded_runner", Path(__file__).with_name("run_bounded.py"))
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


class BoundedRunnerTest(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="bounded-runner-test-")
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)

    def command(self, code, seconds=10):
        return [sys.executable, str(Path(__file__).with_name("run_bounded.py")),
                "--rss-mib", "64", "--seconds", str(seconds),
                "--lock", str(self.root / "lock"),
                "--log", str(self.root / "job.log"),
                "--report", str(self.root / "report.json"),
                "--", sys.executable, "-c", code]

    def report(self):
        return json.loads((self.root / "report.json").read_text())

    def test_success_and_thread_environment(self):
        result = subprocess.run(self.command(
            "import os; print(os.environ['GOMAXPROCS'], os.environ['OMP_NUM_THREADS'])"),
            capture_output=True, text=True, timeout=15)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.report()["status"], "passed")
        self.assertEqual((self.root / "job.log").read_text().strip(), "1 1")

    def test_time_limit(self):
        result = subprocess.run(self.command("import time; time.sleep(60)", seconds=1),
                                capture_output=True, text=True, timeout=15)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(self.report()["reason"], "time_budget")

    def test_memory_limit_saves_report(self):
        result = subprocess.run(self.command(
            "import time; data=bytearray(80*1024*1024); time.sleep(60)"),
            capture_output=True, text=True, timeout=15)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(self.report()["reason"], "memory_budget")
        self.assertGreater(self.report()["peak_rss_mib"], 64)

    def test_no_signal_for_empty_or_zombie_group(self):
        for members in ([], [(123, os.getuid(), "Z", 0)]):
            with patch.object(runner, "process_group_members", return_value=members), patch.object(os, "killpg") as kill:
                self.assertEqual(runner.kill_process_group(123), [])
                kill.assert_not_called()

    def test_group_permission_error_falls_back_to_verified_members(self):
        with patch.object(runner, "process_group_members", return_value=[(123, os.getuid(), "S", 0)]), \
                patch.object(os, "killpg", side_effect=PermissionError()), \
                patch.object(os, "getpgid", return_value=123), patch.object(os, "kill") as kill:
            self.assertEqual(runner.kill_process_group(123), [])
            kill.assert_called_once_with(123, signal.SIGKILL)

    def test_no_signal_for_reused_pid_or_foreign_member(self):
        with patch.object(runner, "process_group_members", return_value=[(123, os.getuid(), "S", 0)]), \
                patch.object(os, "killpg", side_effect=PermissionError()), \
                patch.object(os, "getpgid", return_value=999), patch.object(os, "kill") as kill:
            self.assertEqual(runner.kill_process_group(123), [])
            kill.assert_not_called()
        with patch.object(runner, "process_group_members", return_value=[(123, os.getuid()+1, "S", 0)]), \
                patch.object(os, "killpg") as kill:
            self.assertTrue(runner.kill_process_group(123))
            kill.assert_not_called()

    def test_descendant_cleanup_after_leader_exits(self):
        result = subprocess.run(self.command(
            "import subprocess,sys; p=subprocess.Popen([sys.executable,'-c','import time;time.sleep(60)']);print(p.pid,flush=True)"),
            capture_output=True, text=True, timeout=15)
        self.assertEqual(result.returncode, 0, result.stderr)
        pid = int((self.root / "job.log").read_text().strip())
        state = subprocess.run(["/bin/ps", "-p", str(pid), "-o", "stat="],
                               capture_output=True, text=True).stdout.strip()
        self.assertTrue(not state or state.startswith("Z"), state)

    def test_termination_records_interruption_and_kills_child(self):
        proc = subprocess.Popen(self.command(
            "import os, time; print(os.getpid(), flush=True); time.sleep(60)"),
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        try:
            deadline = time.monotonic() + 10
            log = self.root / "job.log"
            while not log.exists() or not log.read_text().strip():
                if proc.poll() is not None or time.monotonic() >= deadline:
                    self.fail("runner did not start its child")
                time.sleep(0.02)
            child_pid = int(log.read_text().strip())
            proc.send_signal(signal.SIGTERM)
            proc.communicate(timeout=10)
            self.assertEqual(self.report()["reason"], "interrupted")
            self.assertEqual(self.report()["status"], "stopped")
            with self.assertRaises(ProcessLookupError):
                os.kill(child_pid, 0)
        finally:
            if proc.poll() is None:
                proc.send_signal(signal.SIGTERM)
                proc.communicate(timeout=10)

    def check_batch_interruption(self, script, arguments):
        previous_signal = signal.getsignal(signal.SIGTERM)
        previous_directory = os.getcwd()
        self.addCleanup(signal.signal, signal.SIGTERM, previous_signal)
        self.addCleanup(os.chdir, previous_directory)
        with patch.object(sys, "argv", [str(script), *arguments]), patch("subprocess.Popen") as start:
            child = start.return_value
            child.wait.side_effect = [KeyboardInterrupt(), 0]
            with self.assertRaisesRegex(SystemExit, "interrupted; later"):
                runpy.run_path(str(script), run_name="__main__")
            start.assert_called_once()
            child.terminate.assert_called_once()
            self.assertEqual(child.wait.call_count, 2)

    def test_experiment_batch_forwards_interruption(self):
        script = Path(__file__).with_name("run_matrix.py").resolve()
        self.check_batch_interruption(script, ["--suite", "full", "--output", str(self.root / "batch"),
                                               "--go", "go", "--only", "bfv-conversion-65537"])

    def test_selected_case_order(self):
        script = Path(__file__).with_name("run_matrix.py").resolve()
        self.addCleanup(signal.signal, signal.SIGTERM, signal.getsignal(signal.SIGTERM))
        self.addCleanup(os.chdir, os.getcwd())
        arguments = [str(script), "--suite", "full", "--output", str(self.root / "batch"),
                     "--go", "go", "--only", "gbfv-comparison-ell256", "gbfv-conversion-ell16"]
        with patch.object(sys, "argv", arguments), patch("subprocess.Popen") as start:
            start.return_value.wait.return_value = 0
            runpy.run_path(str(script), run_name="__main__")
            commands = [call.args[0] for call in start.call_args_list]
        self.assertEqual(len(commands), 2)
        self.assertIn("gbfv-compare", commands[0])
        self.assertIn("256", commands[0])
        self.assertIn("conversion", commands[1])
        self.assertIn("16", commands[1])

    def test_audit_batch_forwards_interruption(self):
        script = Path(__file__).resolve().parents[1] / "security" / "run_audit.py"
        self.check_batch_interruption(script, ["--output", str(self.root / "audit"),
                                               "--sage-python", "python", "--name", "bfv-goldilocks",
                                               "--kind", "main", "--attacks", "usvp"])


if __name__ == "__main__":
    unittest.main()
