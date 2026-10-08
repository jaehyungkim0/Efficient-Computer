"""One bounded audit job per process; run with SageMath and pinned estimator."""
import argparse
import json
import math
import os
import sys
import time

sys.path.insert(0, os.environ.get("ESTIMATOR_PATH", "/estimator"))
from sage.all import ZZ, RR, oo
from estimator import LWE, ND
from estimator.reduction import RC

parser = argparse.ArgumentParser()
parser.add_argument("--parameters", default="/audit/parameters.json")
parser.add_argument("--name", required=True)
parser.add_argument("--kind", choices=["main", "ephemeral", "input-ephemeral", "packing", "return-packing"], required=True)
parser.add_argument("--attack", choices=["rough", "usvp", "bdd", "bdd_hybrid", "bdd_mitm_hybrid", "dual", "dual_hybrid", "mitm", "bkw", "arora-gb"], required=True)
parser.add_argument("--model", choices=["MATZOV", "ADPS16"], default="MATZOV")
args = parser.parse_args()
with open(args.parameters) as f:
    entry = next(e for e in json.load(f) if e["name"] == args.name)
primes = entry["Q"] + entry["P"]
n, h = entry["n"], entry["secret_weight"]
if args.kind == "ephemeral":
    primes, h = [entry["Q"][0], entry["P"][0]], 32
elif args.kind == "input-ephemeral":
    primes, h = entry["Q"][:2] + entry["P"][:1], 32
elif args.kind == "packing":
    primes, n, h = [entry["Q"][0], entry["P"][0]], 4096, 0
elif args.kind == "return-packing":
    primes, n, h = entry["Q"][:2] + entry["P"][:1], 8192, 0
q = ZZ(math.prod(primes))
class FixedWeightTernary(ND.SparseBinomial):
    """SparseBinomial(eta=1), keeping RR arithmetic after estimator resizing."""
    def __init__(self, hw, n):
        super().__init__(1, hw, n=n)
        self.stddev = (RR(hw) / n).sqrt() if n else RR(0)

    def resize(self, new_n):
        return FixedWeightTernary(self.hw, new_n)

    def split_balanced(self, new_n, new_hw=None):
        left, right = super().split_balanced(new_n, new_hw)
        return FixedWeightTernary(left.hw, left.n), FixedWeightTernary(right.hw, right.n)

# eta=1 conditioned on nonzero gives independent fair signs at fixed weight,
# exactly matching Lattigo's Hamming-weight ternary secret sampler. Only the
# arithmetic type differs: RR avoids floating overflow at >1024-bit moduli.
secret = FixedWeightTernary(h, n) if h else ND.Uniform(-1, 1)
error = ND.DiscreteGaussian(RR(entry["sigma"]))
params = LWE.Parameters(n=n, q=q, Xs=secret, Xe=error, m=oo)
print(json.dumps({"name":args.name, "kind":args.kind, "attack":args.attack,
    "model":"ADPS16" if args.attack == "rough" else args.model,
    "n":n, "log2_q":float(RR(q).log2()), "h":h,
    "sigma":entry["sigma"], "samples":"infinity"}), flush=True)
start = time.monotonic()
if args.attack == "rough":
    result = LWE.estimate.rough(params, jobs=1, catch_exceptions=False)
else:
    functions = {"usvp":LWE.primal_usvp, "bdd":LWE.primal_bdd,
        "bdd_hybrid":LWE.primal_hybrid, "bdd_mitm_hybrid":LWE.primal_hybrid,
        "dual":LWE.dual, "dual_hybrid":LWE.dual_hybrid, "mitm":LWE.mitm,
        "bkw":LWE.coded_bkw, "arora-gb":LWE.guess_composition(LWE.arora_gb)}
    kwargs = {} if args.attack in ("bkw", "arora-gb", "mitm") else {"red_cost_model":getattr(RC,args.model)}
    if args.attack in ("bdd_hybrid", "bdd_mitm_hybrid"):
        kwargs.update(mitm=args.attack == "bdd_mitm_hybrid", babai=args.attack == "bdd_mitm_hybrid")
    result = {args.attack:functions[args.attack](params, **kwargs)}
for attack, cost in result.items():
    bits = float(RR(cost["rop"]).log2())
    print("RESULT " + json.dumps({"attack":attack,
        "log2_rop":bits if math.isfinite(bits) else None,
        "status":"finite_estimate" if math.isfinite(bits) else "nonfinite_not_a_security_certificate",
        "cost":repr(cost),
        "seconds":time.monotonic()-start}), flush=True)
