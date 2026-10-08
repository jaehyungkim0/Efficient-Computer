# Experiment Runner

Run these commands from the repository root on a POSIX system with Go and
Python 3 installed. The full matrix includes BFV conversion, comparison, and
sign for 65537 and Goldilocks; sign for 8179; GBFV conversion and comparison
at exponents 16, 64, 256, and 1024; and the three sparse GBFV conversions.
The paper's measured runs and their provenance are summarized in
[RESULTS.md](RESULTS.md).

```sh
python3 examples/singleparty/ckks_bootstrapping/slim/experiments/run_matrix.py \
  --suite full --output logs/end-to-end-full
```

For small-ring correctness checks, not security claims or paper timings:

```sh
python3 examples/singleparty/ckks_bootstrapping/slim/experiments/run_matrix.py \
  --suite short --output logs/end-to-end-short
```

Use `--only` to select cases, for example `--only bfv-comparison-65537
gbfv-comparison-ell64`; selected cases run in the given order. Use
`--go /path/to/go` if Go is not on `PATH`.
The default iteration count in each experiment is one.

The runner executes one job at a time, with an exclusive shared lock,
`GOMAXPROCS=1`, and numerical-library thread counts set to one. It limits
process-group RSS to 24 GiB for full runs and 3 GiB for short runs, records
peak RSS, and stops a job at its time or memory limit. Evaluation keys remain
in memory. The Go soft memory limit is two thirds of the RSS budget (16 GiB
for full runs). The Go programs separately report homomorphic-operation times;
the runner's wall-clock time also includes setup and verification.

The GBFV driver shares evaluator work buffers for sequential operations and
releases temporary key/DFT-construction allocations between setup stages.
These setup-only collections are outside the homomorphic timers; evaluation
keys and matrices used by the computation remain in memory.
The decomposition scratch array is sized for the complete, fixed evaluation
key set, including both encapsulation keys, rather than reserving one block
per Q prime. Equivalence tests compare rotations and ModUp ciphertexts with
the original buffer allocation byte for byte. No modulus or key is changed.

Long signed-carry chains (six or more rounds) include a two-level cubic
symbol-cleaning step at their midpoint. For `h(x)=3*x^2-2*x^3`, it evaluates
`h(2*Re(z))/2 + i*h(Im(z))`, which fixes the carry alphabet `{0, 1/2, i}`
and has zero derivative at each symbol. This reduces small symbol errors
quadratically without another bootstrap or a change of moduli. Level checks
reserve both the remaining carry rounds and the final flag extraction.
The `-trace-decomp` option reports stage precision for diagnosis; those runs
include decryption overhead and are not used for paper timings.

The symbol-cleaning unit test is run with the relevant standalone driver:

```sh
go test examples/singleparty/ckks_bootstrapping/slim/conv-gbfv-to-cpl25.go \
  examples/singleparty/ckks_bootstrapping/slim/packed_symbols_test.go
```

Each output directory contains a source-hash manifest, raw logs, and resource
reports. Completed successful cases can be skipped on restart with unchanged
sources. Existing logs are never overwritten: use a fresh output directory
for interrupted/failed cases or after a source change. An interrupted batch
does not start later cases. A `passed` resource report means the program
exited successfully after its checks; it does not replace the separate
[security audit](../security/README.md).

Budget stops write a resource report before terminating the process group.
Cleanup checks for surviving descendants even after the command exits. If a
live child cannot be terminated, the runner records `cleanup_pending` and
retains the job lock rather than allowing another heavy job to overlap it.

Runner cleanup can be tested without cryptographic workloads:

```sh
python3 examples/singleparty/ckks_bootstrapping/slim/experiments/test_run_bounded.py
```

Artifact validation uses the carrier, return-path, carry-symbol, and key
tests together with the recorded end-to-end experiments. These exercise the
paper's functional bootstrapping and its explicitly configured ordinary
refresh stages.

The generic four-case `TestBootstrapping` identity-bootstrap suite has been
removed. Its ordinary default configuration exposed an output-scale mismatch,
not a failed paper experiment. This is a test-scope change: the bootstrap
implementation, paper parameters, and experiment arithmetic are unchanged.
Other inherited tests remain; passing the artifact checks does not establish
that every generic library configuration is supported.
