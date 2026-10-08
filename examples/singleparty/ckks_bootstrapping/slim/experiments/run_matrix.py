"""Run the paper's experiment matrix serially, preserving logs and source hashes."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys


def interrupt(signum, frame):
    raise KeyboardInterrupt


signal.signal(signal.SIGTERM, interrupt)
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--suite", choices=["short", "full"], required=True)
parser.add_argument("--output", type=Path, required=True)
parser.add_argument("--only", nargs="*")
parser.add_argument("--go", default=shutil.which("go"))
args = parser.parse_args()
if not args.go:
    parser.error("Go executable not found; specify --go")
here = Path(__file__).resolve().parent
root = here.parents[4]
slim = here.parent.relative_to(root)
bfv, gold, gbfv = [str(slim / f) for f in ("conv-btd-sign-65537.go", "conv-btd-goldilocks.go", "conv-gbfv-to-cpl25.go")]
cases = []
if args.suite == "full":
    for p, program in [("65537", bfv), ("goldilocks", gold)]:
        for operation, label in [("conversion", "conversion"), ("bfv-compare", "comparison"), ("bfv-sign", "sign")]:
            cases.append((f"bfv-{label}-{p}", program, ["-operation", operation]))
else:
    cases += [("bfv-all-65537", bfv, ["-operation", "all"]), ("bfv-all-goldilocks", gold, ["-operation", "all"])]
cases.append(("bfv-sign-8179", bfv, ["-prime", "8179", "-operation", "bfv-sign"]))
for ell in (16, 64, 256, 1024):
    operations = [("conversion", "conversion"), ("gbfv-compare", "comparison")] if args.suite == "full" else [("gbfv-compare", "comparison")]
    for operation, label in operations:
        cases.append((f"gbfv-{label}-ell{ell}", gbfv, ["-gbfv-ell", str(ell), "-operation", operation]))
for density in ("1/8", "1/4", "1/2"):
    cases.append(("gbfv-sparse-ell1024-" + density.replace("/", "-"), gbfv,
                  ["-gbfv-ell", "1024", "-operation", "conversion", "-gbfv-density", density]))
if args.only:
    unknown = set(args.only) - {c[0] for c in cases}
    if unknown:
        parser.error(f"unknown cases: {sorted(unknown)}")
    by_name = {case[0]: case for case in cases}
    cases = [by_name[name] for name in dict.fromkeys(args.only)]
args.output.mkdir(parents=True, exist_ok=True)
source_paths = [root / p for p in (bfv, gold, gbfv)]
source_paths += sorted((here.parent / "returnpath").glob("*.go"))
source_paths += sorted((here.parent / "carrier").glob("*.go"))
source_paths += [root / "circuits/ckks/bootstrapping/keys.go"]
sources = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in source_paths}
manifest = args.output / "manifest.json"
if manifest.exists() and json.loads(manifest.read_text())["source_sha256"] != sources:
    parser.error("source files changed; use a new output directory")
manifest.write_text(json.dumps({"suite": args.suite, "gomaxprocs": 1, "source_sha256": sources}, indent=2) + "\n")
os.chdir(root)
for name, program, flags in cases:
    log, report = args.output / (name + ".log"), args.output / (name + ".resources.json")
    if report.exists() and json.loads(report.read_text())["status"] == "passed":
        continue
    command = [sys.executable, str(here / "run_bounded.py"), "--rss-mib", "3072" if args.suite == "short" else "24576",
               "--seconds", "900" if args.suite == "short" else "7200", "--log", str(log), "--report", str(report),
               "--", args.go, "run", program, *(["-short"] if args.suite == "short" else []), *flags]
    print("Starting " + name, flush=True)
    child = subprocess.Popen(command)
    try:
        code = child.wait()
    except KeyboardInterrupt:
        child.terminate()
        child.wait()
        raise SystemExit("interrupted; later cases were not started")
    if code:
        raise SystemExit(f"{name} failed; later cases were not started")
