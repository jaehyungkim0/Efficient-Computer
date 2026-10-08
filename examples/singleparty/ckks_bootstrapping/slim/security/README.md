# Security Audit

The audit uses the upstream lattice-estimator commit
`53da5982597709ba0fdf94ea37a84d822310fd84`, retrieved on 2026-10-07,
and SageMath 10.9 for the native runs (10.10 for the initial container runs).
The estimator source is not modified. The full-size parameter sets meet the
128-bit target under the adopted classical MATZOV model and the model checks
described below. Modulus-budget guards alone are not security estimates.

`results-20261007.json` preserves 52 finite estimates together with failed
and nonfinite calls. Every main-key profile has completed uSVP, BDD,
BDD-hybrid, BDD-MITM-hybrid, and dual-hybrid estimates. The lowest completed
estimate is **134.21 bits**, for Goldilocks main-key BDD-MITM-hybrid.
The minimum completed estimates for the largest forward and return
ring-packing profiles are 143.36 and 204.11 bits, respectively. For the
one-prime and two-prime sparse-key profiles, they are 176.41 and 163.79 bits.
These largest-modulus profiles cover the smaller active moduli in each key
family; the main-key parameter sets are evaluated separately.

Numerical optimizer failures are not counted as successful estimates.
For Coded BKW and Arora-GB, separate checks of the pinned cost formulas
establish lower bounds above 128 bits for all ten audited profiles; see
[`MODEL_BOUNDS.md`](MODEL_BOUNDS.md) and `model-bounds-20261007.json`.
Those records are explicitly labeled `model_lower_bound`, not numerical
optimizer results. The limitations of these checks are stated below.

## Scope and Inputs

`export.go` mirrors the full-size parameter literals in the three experimental
drivers and invokes this checkout's CKKS parameter generator. `parameters.json`
records the exact primes and the SHA-256 of each source driver. Regenerate it
from the repository root with:

```sh
go run ./examples/singleparty/ckks_bootstrapping/slim/security > examples/singleparty/ckks_bootstrapping/slim/security/parameters.json
```

The audit distinguishes the following key systems:

- Main computation: ring degree 65536, fixed-weight ternary secret of weight
  192, and the product of all Q and P primes.
- Sparse bootstrapping encapsulation: ring degree 65536, fixed-weight ternary
  secret of weight 32, and Q[0]*P[0]. The reverse switching key is encrypted
  under the main secret, not under the sparse secret at the full modulus.
- Forward ring packing: ring degree 4096 at Q[0]*P[0], with the default
  independent uniform ternary secret. Intermediate switching rings have
  degrees 8192, 16384 and 32768 at this same active key modulus. The full-ring
  endpoint uses the main secret. When an output key is embedded in a larger
  ring, the relevant secret dimension is the smaller ring's dimension.
- Return ring packing: ring degree 8192 at Q[0]*Q[1]*P[0], with a uniform
  ternary secret. Two Q primes retain the q0-scaled comparison bit before
  the final GBFV modulus switch. The largest key modulus is 140 bits.
- Goldilocks input encapsulation uses a weight-32 secret at
  Q[0]*Q[1]*P[0], or 158 bits. It is audited separately from the one-prime
  bootstrapping encapsulation before being used in full-size experiments.

The error sampler has standard deviation 3.2 and implementation cutoff 19.2.
The estimator uses its discrete-Gaussian model and unlimited samples. These
are conventional generic-LWE estimates for the RLWE key systems, not a proof
against every possible structured-ring attack. Debug `-short` configurations
are not included in the security claim.

The fixed-weight sampler has independent random signs; it is represented by
`ND.SparseBinomial(eta=1, hw=H)`, not by a fixed equal count of positive and
negative coefficients. The input adapter retains this distribution while
using Sage RR arithmetic during resizing to avoid overflow when multiplying
its standard deviation by moduli larger than 1024 bits.

The input-lifting helper uses the same low-modulus sparse-secret encapsulation
pattern as the bootstrapper; see
[Bossuat et al., ACNS 2022](https://eprint.iacr.org/2022/024). Goldilocks retains
its two-prime input modulus during this switch rather than discarding the
precision needed for its 64-bit message.

## Cost Models and Resources

The audit distinguishes the estimator's default classical MATZOV cost model
from its `rough` ADPS16/Core-SVP model. Results from these models are not
interchangeable. In particular, the initial Goldilocks Core-SVP estimate was
about 111.5 bits, whereas the default-model uSVP estimate is about 144.8 bits.
The paper identifies MATZOV as the adopted model; the 128-bit statement does
not apply to the Core-SVP convention. The explicit ADPS16 rerun is recorded in
`model-comparison-20261008.json`, separately from the MATZOV portfolio, so that
the choice of cost model is explicit.

`run_audit.py` runs one attack in one fresh subprocess at a time, with a
1200-second timeout and a 2048 MiB process-group RSS cutoff. The runner fixes
numerical-library thread counts to one. Raw logs are small scalar estimates
and are retained in the local experiment logs. Timeouts, errors
and nonfinite results do not count as successful security checks. The initial
container runs used one CPU, 2 GiB RAM, no swap and no network, with this image:

```text
sagemath/sagemath@sha256:310dfe23fc786f3a5a06a7b0387c60201ec79b32c0db941b7624505ee5edb565
```

For native retries, an RSS watchdog and a shared exclusive job lock prevent
overlap among cooperating jobs. A computation does not start while that
lock is occupied; the lock does not control unrelated system workloads.
The native retry budget is 2048 MiB RSS and 1200 seconds;
the watchdog stops the child process group if either limit is exceeded.

The upstream plain-dual implementation does not accept `SparseBinomial`
secrets. The failed call is recorded as incomplete, with its unsupported-input
exception preserved in the raw log, rather than as a successful estimate;
the MATZOV dual-hybrid and primal-hybrid implementations accept this sampler.
The algebraic-attack check uses `guess_composition(arora_gb)`, matching the
upstream default estimator interface.

The supplemental Coded-BKW call on the 1550-bit main modulus encounters a
Sage/Maxima floating-point overflow. This is recorded as an incomplete
optimizer result. In the upstream Coded-BKW formula, the table parameter is
at least 2 and the nonnegative cost term C4 includes `q^b`; thus this specific
routine's unmodified-modulus cost is already at least `q^2`, well above the
128-bit target. This coarse formula bound is not a successful numerical run
and does not cover a different attack with an additional modulus-switching
strategy. The two-prime sparse input profile's numerical BKW call completes
at approximately 331.14 bits.

## Evaluation-Key Correction

The audit found that the dense-to-sparse bootstrapping evaluation key was
allocated at full Q and P, although the sparse output secret was available
only at Q[0] and P[0]. The extra Q limbs therefore used a zero output secret;
a small reproduction recovered all 1024 input-secret coefficients from the
public evaluation key alone. Modulus-budget checks cannot detect this bug.

The key is now generated explicitly at `LevelQ=0, LevelP=0`, restoring the
low-modulus encapsulation construction without changing circuit parameters.
`TestEncapsulationKeyModuli` checks both switching-key moduli and a
dense-to-sparse-to-dense switching round trip. The previously generated
evaluation keys must not be reused. All experiment runs must regenerate keys,
and old measurements do not validate this corrected construction.
