"""Exact lower bounds on two pinned estimator models, not optimized attacks."""
import argparse
import hashlib
import json
import math
from pathlib import Path
import sys


MODEL_SOURCES = {
    "lwe_bkw.py": "6caf4a9a1301a173a3c28863c39535d13c4927d7e870f37d68ad4b09e894a9f2",
    "gb.py": "d785ee73ad40a470422d1ddc21d76e9f32b8ab1d85d88ae2539590b32bbd7edc",
    "lwe_guess.py": "33020dcf5a4783a6d90f489a44314ed2bc3b594862262c99f19bf7c2493ee8fb",
}


def verify_sources(estimator):
    for name, expected in MODEL_SOURCES.items():
        actual = hashlib.sha256((Path(estimator) / "estimator" / name).read_bytes()).hexdigest()
        if actual != expected:
            raise ValueError("cost model differs from the analyzed version: " + name)


def max_completions(remaining, weight=None):
    if remaining < 0 or (weight is not None and weight < 0):
        raise ValueError("negative dimension or weight")
    if weight is None:
        return 3**remaining
    # A fixed prefix leaves an exact residual weight j <= weight, not an
    # arbitrary ternary suffix. Maximizing over j covers every prefix.
    return max(math.comb(remaining, j) * 2**j for j in range(min(weight, remaining) + 1))


def arora_bound(n, weight=None):
    if n < 1024 or (weight is not None and not 0 <= weight <= n):
        raise ValueError("bound requires n >= 1024 and a valid secret weight")
    support = 3**n if weight is None else math.comb(n, weight) * 2**weight
    hilbert = math.comb(1033, 9)**2
    guessing = support // (2 * max_completions(1023, weight))
    return min(hilbert, guessing), hilbert, guessing


def bkw_bound(q):
    if not isinstance(q, int) or q < 2:
        raise ValueError("invalid modulus")
    return q*q


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--estimator", type=Path, required=True)
    parser.add_argument("--parameters", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        parser.error("output already exists; preserve the previous record")
    verify_sources(args.estimator)
    sys.path.insert(0, str(args.estimator))
    from sage.all import RR, ZZ, oo
    from estimator import LWE, ND
    from estimator.gb import gb_cost

    entries = json.loads(args.parameters.read_text())
    cases = [(e, "main", e["n"], e["secret_weight"], e["Q"] + e["P"]) for e in entries]
    gold = next(e for e in entries if e["name"] == "bfv-goldilocks")
    packed = next(e for e in entries if e["name"] == "gbfv-16")
    cases += [
        (gold, "ephemeral", gold["n"], 32, gold["Q"][:1] + gold["P"][:1]),
        (gold, "input-ephemeral", gold["n"], 32, gold["Q"][:2] + gold["P"][:1]),
        (packed, "packing", 4096, None, packed["Q"][:1] + packed["P"][:1]),
        (packed, "return-packing", 8192, None, packed["Q"][:2] + packed["P"][:1]),
    ]
    # Execute the unchanged upstream Hilbert routine at the earliest possible
    # crossing; the argument in MODEL_BOUNDS.md covers the other dimensions.
    probe = gb_cost(1024, [(9, 1025**9), (3, 1024)], prec=10)
    if probe["dreg"] != 9 or probe["rop"] != math.comb(1033, 9)**2:
        raise ValueError("upstream Hilbert cost does not match the bound")
    records = []
    for e, kind, n, weight, primes in cases:
        q = math.prod(primes)
        secret = ND.Uniform(-1, 1) if weight is None else ND.SparseBinomial(1, weight, n=n)
        params = LWE.Parameters(n=n, q=ZZ(q), Xs=secret,
                                Xe=ND.DiscreteGaussian(RR(e["sigma"])), m=oo).normalize()
        if params.n != n or params.q != q or tuple(params.Xs.bounds) != (-1, 1) or params.Xs > params.Xe:
            raise ValueError("unexpected normalization or secret range")
        if not params.Xe.is_Gaussian_like or math.ceil(float(params.Xe.stddev)) < 4:
            raise ValueError("Gaussian equation degree may be below nine")
        if params.Xe.is_bounded and params.Xe.bounds[1] - params.Xe.bounds[0] + 1 < 9:
            raise ValueError("bounded-error equation degree may be below nine")
        lower, hilbert, guessing = arora_bound(n, weight)
        for attack, bound in (("bkw", bkw_bound(q)), ("arora-gb", lower)):
            if bound < 2**128:
                raise ValueError(f"target not established: {e['name']} {kind} {attack}")
            record = dict(name=e["name"], kind=kind, attack=attack, n=n,
                          secret_weight=weight, status="model_lower_bound",
                          target_bits=128, lower_bound_operations=str(bound),
                          lower_bound_bits=float(RR(bound).log2()),
                          optimized_attack_bits=None)
            if attack == "arora-gb":
                record.update(hilbert_bound=str(hilbert), guessing_bound=str(guessing))
            records.append(record)
    result = dict(estimator_commit="53da5982597709ba0fdf94ea37a84d822310fd84",
                  scope="Lower bounds on pinned classical cost models, not numerical optimizer results.",
                  parameter_sha256=hashlib.sha256(args.parameters.read_bytes()).hexdigest(),
                  model_sources=MODEL_SOURCES,
                  upstream_hilbert_probe={str(k): str(v) for k, v in probe.items()},
                  records=records)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(dict(status="passed", records=len(records), target_bits=128,
                          minimum_bound_bits=min(r["lower_bound_bits"] for r in records))))


if __name__ == "__main__":
    main()
