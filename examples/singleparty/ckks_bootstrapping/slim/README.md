# Slim Discrete-CKKS Proof-of-Concept Examples

This directory contains research proof-of-concept programs built on Lattigo's
CKKS bootstrapping examples. The files are intended to validate the conversion
and logical-operation interfaces used in the paper: BFV-to-discrete-CKKS
conversion, modular reduction in the radix integer-computer representation,
GBFV-to-packed-radix conversion, comparison, and sign/top-bit-style experiments.

These examples are not a stable application API. Several programs expose
operation-level helper functions that can be reused inside other examples, but
the parameter sets, tracing flags, and command-line programs are mainly for
experiments. The `-short` flag uses smaller insecure parameters and is only for
fast precision/debug checks.

All example binaries in this directory accept `-num-iter N` to repeat the
measured homomorphic operation block and print `Average homomorphic operation
time` at the end. The timing excludes one-time setup such as parameter
construction, key generation, plaintext encoding setup, and bootstrapping-key
generation.

The combined conversion examples also support operation-specific timing. Use
`-operation conversion`, `-operation kim25-compare`, `-operation bfv-compare`,
`-operation kim25-sign`, or `-operation bfv-sign` for the
BFV-to-discrete-CKKS drivers, and `-operation conversion`,
`-operation cpl25-compare`, or
`-operation gbfv-compare` for the GBFV-to-packed-radix driver. In the internal
compare/sign modes, the required conversion is still computed as preparation,
but it is excluded from the measured operation time.

## Provenance and Scope

This artifact directory contains files derived from the earlier
Efficient-Computer implementation together with additional implementation work
prepared for this artifact. Efficient-Computer is the public repository
`https://github.com/jaehyungkim0/Efficient-Computer` and is itself based on the
public CRT-FHE repository
`https://github.com/jaehyungkim0/CRT-FHE`, which is built on Lattigo.

Inherited baseline examples and helper code:

- The baseline slim arithmetic examples and many standard utilities, including
  CRT/FFT/DFT-style helper routines, are inherited from the
  Efficient-Computer/CRT-FHE lineage and predate the new conversion
  work. Comments in several files already record that some of these standard
  helper routines were written with help from ChatGPT in the earlier
  implementation.
- `left-shift.go`, `right-shift.go`, `prime25519.go`, `mult-256.go`, and
  `mult-ext-256.go` should be read primarily as inherited Efficient-Computer
  experiments in this directory.

Implemented or refactored in this artifact:

- `add.go`, `sub.go`, `compare.go`, and `mult.go` were refactored into more
  reusable operation-level APIs in this artifact, while retaining the
  inherited example structure and helper utilities.
- `redc-16.go`, `redc-65537.go`, `redc-goldilocks.go`, `conv-btd-16.go`,
  `conv-btd-sign-65537.go`, `conv-btd-goldilocks.go`, and
  `conv-gbfv-to-cpl25.go` are the new artifact-level REDC, ConvBtD, and
  GBFV-to-packed-radix proof-of-concept experiments.
- This README and the root README pointer were added in this artifact to
  document the implementation split and artifact-level AI disclosure.

## File Map

Inherited and refactored basic integer-computer operations:

- `add.go` implements radix-slot addition.
- `sub.go` implements radix-slot subtraction.
- `mult.go` implements radix-slot multiplication.
- `compare.go` implements reusable multi-precision comparison helpers and a
  comparison example.
- `left-shift.go` and `right-shift.go` implement radix shifts.
- `prime25519.go`, `mult-256.go`, and `mult-ext-256.go` are larger-modulus and
  256-bit multiplication experiments.

Modular-reduction experiments:

- `redc-16.go` implements the Montgomery-style `IntCom.REDC_p` experiment for a
  small 16-bit prime modulus, useful for debugging against ordinary integer
  Montgomery reduction.
- `redc-65537.go` specializes reduction to the Fermat prime `2^16+1`, where the
  relation `2^16 = -1 mod p` gives a cheaper fold.
- `redc-goldilocks.go` implements a special reduction experiment for the
  Goldilocks prime `2^64 - 2^32 + 1`.

Conversion experiments:

- `conv-btd-16.go` implements a small-prime `ConvBtD`-style conversion from a
  combined discrete-CKKS value to digit/radix form, followed by reduction.
- `conv-btd-sign-65537.go` implements `ConvBtD`, comparison, and a
  top-bit/sign-style evaluation for `p=65537`.
- `conv-btd-goldilocks.go` implements the Goldilocks `ConvBtD` experiment from
  a coefficient-encoded CKKS/BFV-style carrier, followed by comparison and
  top-bit/sign-style evaluation.
- `conv-gbfv-to-cpl25.go` implements the current `ConvGtD` proof of concept:
  two GBFV-style coefficient carriers are converted into the packed
  discrete-CKKS radix encoding and compared in that representation.

## Scope Relative to the Paper

The programs in this directory are proof-of-concept experiments rather than a
complete library implementation of every interface in the paper.

- The BFV-side files implement the forward BFV-to-discrete-CKKS conversion
  interface used in the experiments, including the public `pK` offset,
  iterative digit decomposition, modular reduction, comparison, and
  sign/top-bit-style evaluation. They use CKKS coefficient ciphertexts as the
  experimental carrier for the BFV-compatible coefficient representation.
- The GBFV-side file implements the forward `ConvGtD` conversion and packed
  comparison experiment. It does not implement the reverse `ConvDtG` conversion
  as a standalone experiment.
- The `-gbfv-density` option measures the sparse-packing latency effect for the
  GBFV conversion experiment by producing only the required number of packed
  radix ciphertexts. It is separate from the sparse BFV and sparse CKKS
  protocols discussed later in the paper.
- The code checks the algebraic output by decrypting and rounding the active
  support after each experiment. A successful run reports exact active-support
  digits or comparison bits and zero integer/comparison error.

## Current GBFV-to-Packed-Radix Flow

The file `conv-gbfv-to-cpl25.go` is the main GBFV conversion experiment. It
follows the paper's `ConvGtD` algorithm at the plaintext-layout level, while
using CKKS coefficient ciphertexts as the carrier in this proof of concept.

At a high level, the implementation does the following:

1. Encodes the input as a level-0 GBFV-style coefficient plaintext for the
   restricted modulus family `p = b^D + 1`.
2. Modraises the carrier and multiplies by the GBFV plaintext polynomial. The
   code uses the sign convention `b - X^h` for its MSB-oriented coefficient
   layout; this is the implementation-side convention for exposing the bounded
   signed radix coefficients used by the conversion.
3. Adjusts the scale by public constant multiplication/rescaling so that the
   exposed coefficients enter the packed radix interface at the intended scale.
4. Extracts and ring-packs the coefficients into the packed radix layout using
   Lattigo's `rlwe` repacking interface with ring switching. The default secure
   path uses `logN=16` for homomorphic computation and a checked smaller-ring
   key path for ring packing.
5. Performs one ordinary CKKS refresh after ring packing.
6. Adds the public redundant offset `A*p*` digitwise, where
   `p*=(b+1,b-1,...,b-1,0,...,0)` represents `p=b^D+1`; this is a public
   digitwise offset, not a carry-normalization step.
7. Applies the packed lazy-radix reduction path to produce canonical packed
   radix ciphertexts modulo `p` using backend length `L=2D`.
8. Repeats the conversion for a second operand and evaluates packed comparison
   bits `lhs >= rhs` using the lazy-carry sign/nonnegative-mask path.

The default settings use `b=16`, `D=64`, and therefore
`p=16^64+1=2^256+1`. The same setting can also be selected as
`-gbfv-ell 256`; more generally, `-gbfv-ell ell` chooses
`D=ell/log2(b)`, while `-gbfv-digits D` directly chooses the digit count.

For the full-size experiment settings used in the paper, the default security
checks require `logN=16` and `logQP <= 1550` for the main homomorphic
parameters. The ring-packing key path is checked separately; by default it uses
ring switching down to `logN=12` only when the active key modulus is within the
documented smaller-ring security guard. The `-short` flag deliberately disables
these production-size parameters and is only for quick precision/debug checks.

For `b=16`, the current full-density conversion schedules use the following
bootstrapping counts per packed output:

- `-gbfv-ell 16`: `7` total, consisting of one ring-pack refresh and six
  reduction bootstrappings.
- `-gbfv-ell 64`: `8` total, consisting of one ring-pack refresh and seven
  reduction bootstrappings.
- `-gbfv-ell 256`: `8` total, consisting of one ring-pack refresh and seven
  reduction bootstrappings.
- `-gbfv-ell 1024`: `10` total, consisting of one ring-pack refresh and nine
  reduction bootstrappings.

The public `A*p*` offset uses zero bootstrappings. The extra reduction
bootstrappings for larger `D` come from symbol cleaning during long carry
propagation and from the final carry canonicalization needed at the
`b^D = -1 mod p` boundary.

Useful commands:

```bash
cd examples/singleparty/ckks_bootstrapping/slim
go run conv-gbfv-to-cpl25.go -gbfv-ell 16 -operation conversion
go run conv-gbfv-to-cpl25.go -gbfv-ell 64 -operation conversion
go run conv-gbfv-to-cpl25.go -gbfv-ell 256 -operation conversion
go run conv-gbfv-to-cpl25.go -gbfv-ell 1024 -operation conversion
go run conv-gbfv-to-cpl25.go -gbfv-ell 1024 -gbfv-density 1/8 -operation conversion
go run conv-gbfv-to-cpl25.go -gbfv-ell 64 -operation gbfv-compare
go run conv-gbfv-to-cpl25.go -short -gbfv-ell 64 -operation conversion
go run conv-gbfv-to-cpl25.go -short -gbfv-density 1/8 -trace-levels
go run conv-btd-sign-65537.go -short -prime 8191 -operation conversion
go run conv-btd-sign-65537.go -short -prime 8191 -operation kim25-sign
go run conv-btd-sign-65537.go -short -prime 8179 -operation conversion
go run conv-btd-sign-65537.go -short -prime 8179 -operation kim25-sign
```

## References Used by the Examples

- The implementation follows the interfaces described in the paper. For the
  BFV path, this means the coefficient carrier is modulus-raised, shifted by a
  public multiple of the plaintext modulus, decomposed into radix digits, and
  reduced by the Montgomery-style reduction routine.
- For the GBFV path, this means the level-0 GBFV-style coefficient carrier is
  modulus-raised, multiplied by the plaintext polynomial, extracted and
  ring-packed, shifted by the public redundant `A*p*` digit vector, and reduced
  to the canonical packed radix representation.
- The black-box integer-computer operations and packed radix layout follow the
  cited discrete-CKKS integer-computer backend. Ring packing uses Lattigo's
  `rlwe` repacking interface in the HERMES-style extraction/repacking workflow.

## AI Assistance Statement

This implementation artifact was prepared with assistance from OpenAI ChatGPT
and OpenAI Codex. The assistance for this artifact included refactoring
operation-level APIs, drafting and editing new REDC/ConvBtD/ConvGtD
proof-of-concept code, renaming helper
functions for clearer correspondence with the algorithms, debugging numerical
and level-management issues, suggesting and checking example parameter changes,
and drafting this README.

Some standard helper utilities in the inherited Efficient-Computer codebase,
including CRT/FFT/DFT-style routines, predate this artifact. The disclosure
above does not claim that those inherited helpers were newly generated for this
implementation; where older source files already acknowledge ChatGPT assistance
for such utilities, that acknowledgement is preserved as provenance of the
earlier code.

The scientific claims, algorithmic choices, parameter decisions, and final
artifact content remain the responsibility of the authors. AI-generated or
AI-edited material was reviewed, modified, and tested by the authors before
being included in this artifact. No AI tool is an author of this work.
