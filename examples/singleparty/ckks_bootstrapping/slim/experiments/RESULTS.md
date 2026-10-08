# Recorded Experiments

The [recorded runs](results-20261008/summary.json) contain the 18 full-size
paper cases, one iteration each, measured on an Apple M4 Max with 128 GB RAM,
macOS 15.7.9, and Go 1.24.2. Computation was single-threaded, with one heavy
job at a time, a 16 GiB Go soft memory limit, and a 24 GiB process-group RSS
cutoff. Evaluation keys remained in memory.

Each group includes the original source-hash manifest, unchanged raw program
logs, and resource reports. Only absolute executable and local log paths in
the resource reports have been replaced by portable paths. The summary
records homomorphic-operation time, not the runner's setup-inclusive wall
time. Key generation, setup, and final decryption checks are excluded from
the paper's operation timings.

## Full-Density Results

Times below are rounded to three significant figures. BFV bootstrap counts
are total calls. GBFV counts are per packed output; full density has eight
outputs. Logical-operation times and counts include the return conversion.

| BFV modulus | Operation | Time (s) | Bootstrappings |
| --- | --- | ---: | ---: |
| 65537 | Conversion | 232 | 32 |
| 65537 | Comparison | 555 | 77 |
| 65537 | Sign | 254 | 35 |
| Goldilocks | Conversion | 745 | 92 |
| Goldilocks | Comparison | 1980 | 221 |
| Goldilocks | Sign | 762 | 95 |
| 8179 | Sign | 452 | 62 |

| GBFV exponent | Conversion (s) | Comparison (s) | Conversion bootstrappings/output | Comparison bootstrappings/output |
| ---: | ---: | ---: | ---: | ---: |
| 16 | 573 | 1430 | 7 | 16 |
| 64 | 760 | 1780 | 8 | 18 |
| 256 | 878 | 2030 | 8 | 18 |
| 1024 | 1070 | 2400 | 10 | 22 |

At exponent 1024, partial-output conversions took 134 s, 268 s, and 538 s
for densities 1/8, 1/4, and 1/2, respectively. These use one, two, and four
output ciphertexts and 10 bootstrappings per output. Relative to full density,
the measured latency reductions were 8.02x, 4.00x, and 2.00x.

The raw logs retain timing breakdowns and unrounded values. Exact conversion,
logical-operation, and final coefficient-decryption checks are separate from
the reported approximation errors. Passing a sampled run does not establish
a failure probability; each input combines random messages and explicit
boundary cases.

## Provenance Notes

- `bfv-small` contains the 65537 and 8179 measurements. They precede the
  single-input mean-noise reporting correction: add one to the logged
  `Mean digit noise in Log 2` for conversion/sign in this group. This does
  not change exact checks, maximum noise, timings, or the comparison report.
- `bfv-goldilocks` contains all three Goldilocks measurements with the
  corrected reporter and two-prime input encapsulation.
- `gbfv-ell64` contains the exponent-64 measurements. The subsequent
  leveled symbol cleaner applies only to carry chains of at least six
  rounds and is not executed in this setting; its measured arithmetic is
  unchanged.
- `gbfv-final` contains the other full-density GBFV cases and all three
  partial-output conversions, with the leveled carry-symbol cleaner.

All recorded runs use regenerated keys after the low-modulus encapsulation
key correction. The separate [security audit](../security/README.md)
documents the adopted cost model, pinned estimator revision, and incomplete
optimizer calls. The [runner documentation](README.md) records the remaining
inherited generic-bootstrapping test limitation.
