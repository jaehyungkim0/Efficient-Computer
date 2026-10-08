# Bounded Checks of Non-Lattice Cost Models

These checks establish a 128-bit threshold for two particular classical cost
models in lattice-estimator commit `53da5982597709ba0fdf94ea37a84d822310fd84`.
They do not report optimized attack costs or substitute for the numerical
lattice-attack runs. Source hashes are checked before applying the bounds.
The upstream estimator is not modified.

The analyzed upstream sources are
[Coded BKW](https://github.com/malb/lattice-estimator/blob/53da5982597709ba0fdf94ea37a84d822310fd84/estimator/lwe_bkw.py),
[the Hilbert-series cost](https://github.com/malb/lattice-estimator/blob/53da5982597709ba0fdf94ea37a84d822310fd84/estimator/gb.py), and
[the guessing wrapper](https://github.com/malb/lattice-estimator/blob/53da5982597709ba0fdf94ea37a84d822310fd84/estimator/lwe_guess.py).

## Coded BKW

In `lwe_bkw.py`, the default search uses table parameter `b >= 2` and
`ell = b-1`. The nonnegative cost term C4 contains `q^(ell+1)`. The other
terms are nonnegative, and the final success-probability divisor is at most
one. Therefore every finite cost in this search is at least `q^2`.
This bound addresses the pinned routine at its input modulus; it does not
analyze an additional modulus-switching strategy outside that routine.

## Arora-GB With Guessing

For the secret laws used here, each secret coefficient belongs to
`{-1,0,1}`. The estimator's secret equations have degree 3. With error
standard deviation 3.2, its Gaussian equation search starts at
`t=ceil(3.2)=4`, hence degree `2t+1 >= 9`. Any bounded-error branch also has
degree at least 9; the script checks this condition after normalization.

At residual dimension `r >= 1024`, the Hilbert series before degree 9 has
the same coefficients as `(1+z+z^2)^r`, all positive. Error equations of
degree at least 9 cannot change these coefficients. Thus a finite first
negative coefficient has degree `dreg >= 9`. With the default linear-algebra
exponent 2, `gb_cost` is at least `binomial(1033,9)^2 > 2^143`.
The script executes the unchanged upstream `gb_cost` at the most optimistic
degree-9 crossing with precision 10 and checks this exact cost.

For `r < 1024`, account for the guesses rather than the Hilbert cost. Let
`S` be the uniform support size of the original secret. Each guessed prefix
has at most `M` possible completions. Testing `s` prefixes therefore succeeds
with probability at most `s*M/S`. By the union bound, repetition to reach
success probability 0.99 requires at least `S/(2*M)` total prefix trials;
each trial has cost at least one. This also lower-bounds the pinned
guessing wrapper's exhaustive guesses and success amplification.

For uniform ternary secrets, `S=3^n` and `M <= 3^1023`. For independent-sign
fixed-weight secrets of weight `H`, `S=binomial(n,H)*2^H`. A fixed prefix
leaves an exact residual weight `j <= H`, so a sharper valid bound is
`M <= max_{0 <= j <= min(H,1023)} binomial(1023,j)*2^j`. The script uses this
maximum, which is essential for the weight-32 keys; the looser unrestricted
ternary suffix bound would not establish the target for them.

Taking the smaller of the Hilbert and guessing bounds covers all residual
dimensions. The checks reject any parameter profile for which this bound
does not reach `2^128`. Small exhaustive tests independently verify the
fixed-weight prefix counts and the first Hilbert-series crossing.

The JSON records use `model_lower_bound`, with no optimized attack-bit
value. Failed or interrupted numerical calls remain separately recorded.
