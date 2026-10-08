"""Audit exact parameters in fresh, resource-bounded, serialized Sage processes."""
import argparse
import json
from pathlib import Path
import signal
import subprocess
import sys


def interrupt(signum, frame):
    raise KeyboardInterrupt


signal.signal(signal.SIGTERM, interrupt)
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--output", type=Path, required=True)
parser.add_argument("--resume", type=Path)
parser.add_argument("--sage-python", required=True)
parser.add_argument("--seconds", type=int, default=1200)
parser.add_argument("--name")
parser.add_argument("--kind", choices=["main", "ephemeral", "input-ephemeral", "packing", "return-packing"])
parser.add_argument("--attacks", nargs="+", choices=["usvp", "bdd", "bdd_hybrid", "bdd_mitm_hybrid", "dual", "dual_hybrid", "mitm", "bkw", "arora-gb"])
args = parser.parse_args()
root = Path(__file__).resolve().parent
runner = root.parent / "experiments/run_bounded.py"
args.output.mkdir(parents=True, exist_ok=True)
entries = json.loads((root / "parameters.json").read_text())
attacks = ("usvp", "bdd", "bdd_hybrid", "bdd_mitm_hybrid", "dual", "dual_hybrid", "mitm", "bkw", "arora-gb")
if args.attacks:
    attacks = args.attacks
cases = [(e["name"], "main", a) for e in entries for a in attacks]
cases += [(name, kind, a) for name, kind in
          [("bfv-goldilocks", "ephemeral"), ("bfv-goldilocks", "input-ephemeral"), ("gbfv-16", "packing"), ("gbfv-16", "return-packing")]
          for a in attacks]
cases = [c for c in cases if (not args.name or c[0] == args.name) and (not args.kind or c[1] == args.kind)]
if not cases:
    parser.error("no parameter profiles match the requested name/kind")
summary = json.loads(args.resume.read_text()) if args.resume else []
for name, kind, attack in cases:
    if any(r["name"] == name and r["kind"] == kind and r["attack"] == attack
           and r.get("status") == "finite_estimate" for r in summary):
        continue
    label = f"{name}-{kind}-{attack}"
    path = args.output / (label + ".log")
    resource = args.output / (label + ".resources.json")
    command = [sys.executable, str(runner), "--rss-mib", "2048", "--seconds", str(args.seconds),
               "--log", str(path), "--report", str(resource), "--", args.sage_python,
               str(root / "estimate.py"), "--parameters", str(root / "parameters.json"),
               "--name", name, "--kind", kind, "--attack", attack]
    child = subprocess.Popen(command, stdout=subprocess.DEVNULL)
    try:
        code = child.wait()
    except KeyboardInterrupt:
        child.terminate()
        child.wait()
        raise SystemExit("interrupted; later attacks were not started")
    record = {"name": name, "kind": kind, "attack": attack, "model": "MATZOV",
              "exit_code": code, "status": "incomplete"}
    if resource.exists():
        report = json.loads(resource.read_text())
        record.update(peak_rss_mib=report["peak_rss_mib"], resource_status=report["status"], reason=report["reason"])
    if path.exists():
        for line in path.read_text().splitlines():
            if line.startswith("RESULT "):
                record.update(json.loads(line[7:]))
    summary.append(record)
    (args.output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(record), flush=True)
