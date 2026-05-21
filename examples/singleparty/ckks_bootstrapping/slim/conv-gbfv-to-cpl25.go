// Proof-of-concept for the paper's ConvGtD algorithm: conversion from the
// restricted GBFV plaintext layout to the packed discrete-CKKS radix layout.
//
// The target radix layout and carry/reduction machinery follows:
// Gyeongwon Cha, Dongjin Park, and Joon-Woo Lee,
// "Improved Radix-based Approximate Homomorphic Encryption for Large Integers
// via Lightweight Bootstrapped Digit Carry", ePrint 2025/1740 (CPL25).
//
// This file also uses the ring-packing interface from Lattigo's rlwe package.
// The default path performs extraction/repacking with ring switching, using
// secure checked parameters for both the main homomorphic ring and the smaller
// rings used by the packing keys. This follows the HERMES-style ring-packing
// viewpoint without implementing the MLWE midpoint optimization:
// Youngjin Bae et al., "HERMES: Efficient ring packing using MLWE ciphertexts
// and application to transciphering", CRYPTO 2023.
//
// The source plaintext ring is restricted to the GBFV form Z_{b^D+1}, where
// D=N/k is the number of base-b digits per GBFV slot. The ciphertext object is
// represented by a CKKS coefficient ciphertext in this proof-of-concept, but the
// plaintext layout follows the public GBFV-to-CKKS-2 implementation:
// coefficient j*k+i physically stores
// q0*(b^{D-j-1} m_i mod (b^D+1))/(b^D+1), with CKKS metadata scale q0.
// The conversion ModRaises this level-0 GBFV carrier,
// multiplies by t(X)=b-X^k, adjusts the scale back to the CKKS default scale,
// extracts/ring-packs the resulting low-norm signed coefficients, adds the
// public redundant radix digits A*p* without any carry normalization, and then
// reduces the resulting bounded nonnegative lazy radix input modulo p=b^D+1 to
// obtain canonical CPL25 packed radix ciphertexts.

// Use the flag -short to run the examples fast but with insecure parameters.
package main

import (
	"crypto/rand"
	"errors"
	"flag"
	"fmt"
	"math"
	"math/big"
	"math/cmplx"
	"strconv"
	"strings"
	"time"

	"github.com/tuneinsight/lattigo/v6/circuits/ckks/bootstrapping"
	"github.com/tuneinsight/lattigo/v6/circuits/ckks/dft"
	"github.com/tuneinsight/lattigo/v6/circuits/ckks/mod1"
	"github.com/tuneinsight/lattigo/v6/circuits/ckks/polynomial"
	"github.com/tuneinsight/lattigo/v6/core/rlwe"
	"github.com/tuneinsight/lattigo/v6/ring"
	"github.com/tuneinsight/lattigo/v6/schemes/ckks"
	"github.com/tuneinsight/lattigo/v6/utils"
	"github.com/tuneinsight/lattigo/v6/utils/bignum"
)

var flagShort = flag.Bool("short", false, "run the example with a smaller and insecure ring degree.")
var flagBaseBits = flag.Int("base-bits", 4, "log2 of the radix base b; default 4 gives b=16.")
var flagGBFVEll = flag.Int("gbfv-ell", 0, "optional exponent ell for p=2^ell+1; if set, D=ell/base-bits overrides -gbfv-digits.")
var flagGBFVDigits = flag.Int("gbfv-digits", 64, "GBFV digit capacity D=N/k; plaintext modulus is b^D+1, so the default is 2^256+1.")
var flagGBFVDensity = flag.String("gbfv-density", "1", "fraction of the fully packed GBFV slots to populate: 1/8, 1/4, 1/2, or 1.")
var flagOffsetMultiplier = flag.Int("offset-multiplier", 0, "public multiplier A for the redundant A*p* offset before CPL25-side reduction; non-positive uses ceil(beta*K/(beta-1)) with K=beta.")
var flagLegacyRepresentativeShift = flag.Int("representative-shift", 0, "deprecated alias for -offset-multiplier.")
var flagNumIter = flag.Int("num-iter", 1, "number of randomized homomorphic-operation iterations to run.")
var flagOperation = flag.String("operation", "all", "homomorphic operation to time: all, conversion, cpl25-compare, or gbfv-compare.")
var flagGBFVPackMode = flag.String("gbfv-pack-mode", "ring", "coefficient packing mode: ring uses ring-switching ExtractNaive+Repack.")
var flagGBFVRingPackMinLogN = flag.Int("gbfv-ring-pack-min-logN", 0, "minimum ring LogN used by ring-switching ring packing; 0 uses the modulus-aware default.")
var flagAllowInsecureRingSwitch = flag.Bool("allow-insecure-ring-switch", false, "allow ring-packing ring switching below the modulus/security guard; intended only for debugging.")
var flagTraceLevels = flag.Bool("trace-levels", false, "print ciphertext levels through REDC stages.")
var flagTraceDecomp = flag.Bool("trace-decomp", false, "decrypt and trace ConvGtD intermediates.")

var traceParams ckks.Parameters
var traceDecryptor *rlwe.Decryptor
var traceEncoder *ckks.Encoder

const lowModulusRingPackMinLogN = 12
const lowModulusRingPackMaxLogQP = 108.0
const defaultRingPackMinLogN = 15

func isPrime(n uint64) bool {
	if int(n) <= 1 {
		return false
	}
	if int(n) == 2 || int(n) == 3 {
		return true
	}
	if int(n)%2 == 0 || int(n)%3 == 0 {
		return false
	}
	sqrtN := int(math.Sqrt(float64(n)))
	for i := 5; i <= sqrtN; i += 6 {
		if int(n)%i == 0 || int(n)%(i+2) == 0 {
			return false
		}
	}
	return true
}

func firstKPrimes(k uint64) []uint64 {
	if k <= 0 {
		return []uint64{}
	}

	primes := []uint64{}
	num := uint64(2)

	for len(primes) < int(k) {
		if isPrime(num) {
			primes = append(primes, num)
		}
		num++
	}

	return primes
}

func Moduli(n uint64, k uint64) []uint64 {
	list := firstKPrimes(k)
	result := []uint64{}
	for i := 0; i < int(k); i++ {
		tmp := list[i]
		for tmp*list[i] <= n {
			tmp *= list[i]
		}
		result = append(result, tmp)
	}
	return result
}

func FFT(a []complex128, invert bool) {
	n := len(a)
	if n == 1 {
		return
	}
	y0 := make([]complex128, n/2)
	y1 := make([]complex128, n/2)
	for i := 0; i < n/2; i++ {
		y0[i] = a[i*2]
		y1[i] = a[i*2+1]
	}

	FFT(y0, invert)
	FFT(y1, invert)

	angle := 2 * math.Pi / float64(n)
	if invert {
		angle = -angle
	}
	wn := cmplx.Exp(complex(0, angle))
	w := complex(1, 0)

	for i := 0; i < n/2; i++ {
		a[i] = y0[i] + w*y1[i]
		a[i+n/2] = y0[i] - w*y1[i]
		if invert {
			a[i] /= 2
			a[i+n/2] /= 2
		}
		w *= wn
	}
}

func DFT(a []complex128, invert bool) []complex128 {
	n := len(a)
	out := make([]complex128, n)
	sign := 1.0
	if invert {
		sign = -1.0
	}
	for k := 0; k < n; k++ {
		sum := complex(0, 0)
		for j := 0; j < n; j++ {
			angle := 2 * math.Pi * float64(j*k) / float64(n) * sign
			sum += a[j] * cmplx.Exp(complex(0, angle))
		}
		if invert {
			sum /= complex(float64(n), 0)
		}
		out[k] = sum
	}
	return out
}

func isPowerOfTwo(n int) bool {
	return (n > 0) && (n&(n-1)) == 0
}

func nextPowerOfTwo(n int) int {
	if n <= 1 {
		return 1
	}

	pow := 1
	for pow < n {
		pow <<= 1
	}
	return pow
}

func packedLayoutDigits(rawLimbs int) int {
	digits := nextPowerOfTwo(rawLimbs)
	if digits < 8 {
		return 8
	}
	if digits < 64 && digits > 8 {
		return 64
	}
	return digits
}

func interpolate(values []complex128) []complex128 {
	n := len(values)
	if isPowerOfTwo(n) {
		coeffs := make([]complex128, n)
		copy(coeffs, values)
		FFT(coeffs, true)
		return coeffs
	}
	return DFT(values, true)
}

func HermiteInterpolation(n int, deg int) []complex128 {
	z := cmplx.Exp(2 * math.Pi * 1i / complex(float64(n), 0))

	A := make([][]complex128, 2*n)
	b := make([]complex128, 2*n)

	for i := 0; i < n; i++ {
		zi := cmplx.Pow(z, complex(float64(i), 0))

		A[i] = make([]complex128, 2*n)
		for j := 0; j < 2*n; j++ {
			A[i][j] = cmplx.Pow(zi, complex(float64(j), 0))
		}
		b[i] = complex(float64(i), 0)

		A[n+i] = make([]complex128, 2*n)
		for j := 1; j < 2*n; j++ {
			A[n+i][j] = complex(float64(j), 0) * cmplx.Pow(zi, complex(float64(j-1), 0))
		}
		b[n+i] = 0
	}

	list := solveLinearSystem(A, b)
	coeffs := make([]complex128, deg+1)
	for i := 0; i < 2*n; i++ {
		coeffs[i] = list[i]
	}
	for i := 2 * n; i <= deg; i++ {
		coeffs[i] = complex(0, 0)
	}
	return coeffs
}

func intPowBig(base uint64, exp int) *big.Int {
	result := big.NewInt(1)
	if exp <= 0 {
		return result
	}
	b := new(big.Int).SetUint64(base)
	return result.Exp(b, big.NewInt(int64(exp)), nil)
}

func solveLinearSystem(A [][]complex128, b []complex128) []complex128 {
	n := len(b)
	for i := 0; i < n; i++ {
		maxRow := i
		for k := i + 1; k < n; k++ {
			if cmplx.Abs(A[k][i]) > cmplx.Abs(A[maxRow][i]) {
				maxRow = k
			}
		}
		A[i], A[maxRow] = A[maxRow], A[i]
		b[i], b[maxRow] = b[maxRow], b[i]

		pivot := A[i][i]
		for j := i; j < n; j++ {
			A[i][j] /= pivot
		}
		b[i] /= pivot

		for k := i + 1; k < n; k++ {
			factor := A[k][i]
			for j := i; j < n; j++ {
				A[k][j] -= factor * A[i][j]
			}
			b[k] -= factor * b[i]
		}
	}

	x := make([]complex128, n)
	for i := n - 1; i >= 0; i-- {
		x[i] = b[i]
		for j := i + 1; j < n; j++ {
			x[i] -= A[i][j] * x[j]
		}
	}

	return x
}

func traceSlotsCiphertext(tag string, ct *rlwe.Ciphertext, count int) {
	if !*flagTraceDecomp || traceDecryptor == nil || traceEncoder == nil {
		return
	}
	values := decodeCiphertext(traceParams, ct, traceDecryptor, traceEncoder)
	if count > len(values) {
		count = len(values)
	}
	fmt.Printf("[trace] %s | level=%d log2(scale)=%.2f slots=", tag, ct.Level(), ct.Scale.Log2())
	for i := 0; i < count; i++ {
		if i != 0 {
			fmt.Printf(", ")
		}
		fmt.Printf("%0.4f", real(values[i]))
	}
	fmt.Println()
}

func traceCoeffsCiphertext(tag string, ct *rlwe.Ciphertext, count int) {
	if !*flagTraceDecomp || traceDecryptor == nil || traceEncoder == nil {
		return
	}
	values := make([]float64, traceParams.N())
	if err := traceEncoder.Decode(traceDecryptor.DecryptNew(ct), values); err != nil {
		panic(err)
	}
	if count > len(values) {
		count = len(values)
	}
	fmt.Printf("[trace] %s | level=%d log2(scale)=%.2f coeffs=", tag, ct.Level(), ct.Scale.Log2())
	for i := 0; i < count; i++ {
		if i != 0 {
			fmt.Printf(", ")
		}
		fmt.Printf("%0.8f", values[i])
	}
	fmt.Println()
}

type REDCComputer struct {
	params    ckks.Parameters
	eval      *bootstrapping.Evaluator
	polyEval  *polynomial.Evaluator
	slotCount int
	limbBits  int
	limbCount int
	mods      uint64
	degEval   int
	mapping   map[int][]int
}

func NewREDCComputer(params ckks.Parameters, eval *bootstrapping.Evaluator, evk *bootstrapping.EvaluationKeys, slotCount, limbBits, totalBits int) (*REDCComputer, error) {
	if slotCount <= 0 || slotCount > params.MaxSlots() {
		return nil, errors.New("slotCount must be in [1, params.MaxSlots()]")
	}
	if limbBits <= 0 {
		return nil, errors.New("limbBits must be positive")
	}
	if totalBits <= 0 || totalBits%limbBits != 0 {
		return nil, errors.New("totalBits must be a positive multiple of limbBits")
	}
	if limbBits >= 63 {
		return nil, errors.New("limbBits must be smaller than 63")
	}

	limbCount := totalBits / limbBits
	mods := uint64(1 << limbBits)
	degEval := 2*int(mods) - 1

	pos := make([]int, slotCount)
	for i := range pos {
		pos[i] = i
	}

	return &REDCComputer{
		params:    params,
		eval:      eval,
		polyEval:  polynomial.NewEvaluator(params, ckks.NewEvaluator(params, evk)),
		slotCount: slotCount,
		limbBits:  limbBits,
		limbCount: limbCount,
		mods:      mods,
		degEval:   degEval,
		mapping:   map[int][]int{0: pos},
	}, nil
}

func (c *REDCComputer) decomposeBig(values []*big.Int, limbs int) [][]complex128 {
	digits := make([][]complex128, limbs)
	mask := big.NewInt(int64(c.mods - 1))
	for i := range digits {
		digits[i] = make([]complex128, len(values))
	}

	for slot, value := range values {
		num := new(big.Int).Set(value)
		for limb := 0; limb < limbs; limb++ {
			digits[limb][slot] = complex(float64(new(big.Int).And(num, mask).Uint64()), 0)
			num.Rsh(num, uint(c.limbBits))
		}
	}

	return digits
}

func (c *REDCComputer) decomposeConst(value *big.Int, limbs int, slots int) [][]complex128 {
	values := make([]*big.Int, slots)
	for i := range values {
		values[i] = new(big.Int).Set(value)
	}
	return c.decomposeBig(values, limbs)
}

func (c *REDCComputer) encryptDigits(encoder *ckks.Encoder, encryptor *rlwe.Encryptor, digits [][]complex128, level int) ([]*rlwe.Ciphertext, error) {
	ciphertexts := make([]*rlwe.Ciphertext, len(digits))
	for i := range digits {
		pt := ckks.NewPlaintext(c.params, level)
		pt.LogDimensions.Cols = int(math.Log2(float64(len(digits[i]))))
		if err := encoder.Encode(digits[i], pt); err != nil {
			return nil, err
		}
		ct, err := encryptor.EncryptNew(pt)
		if err != nil {
			return nil, err
		}
		ciphertexts[i] = ct
	}
	return ciphertexts, nil
}

func (c *REDCComputer) bootstrap(ct *rlwe.Ciphertext) (*rlwe.Ciphertext, float64, int, error) {
	var err error
	bootCount := 1

	if ct, err = c.eval.SlotsToCoeffs(ct, nil); err != nil {
		return nil, 0, bootCount, err
	}
	if ct, _, err = c.eval.ScaleDown(ct); err != nil {
		return nil, 0, bootCount, err
	}

	zeroScale := ct.Scale.Float64()
	targetScale := float64(c.params.RingQ().ModulusAtLevel[0].Uint64())

	if ct, err = c.eval.ModUp(ct); err != nil {
		return nil, 0, bootCount, err
	}

	real, imag, err := c.eval.CoeffsToSlots(ct)
	if err != nil {
		return nil, 0, bootCount, err
	}
	if imag != nil {
		if err = c.eval.Evaluator.Conjugate(real, imag); err != nil {
			return nil, 0, bootCount, err
		}
		if err = c.eval.Evaluator.Add(real, imag, real); err != nil {
			return nil, 0, bootCount, err
		}
	}
	if imag, err = c.eval.EvalModAndScale(real, 2*math.Pi); err != nil {
		return nil, 0, bootCount, err
	}
	if real, err = c.eval.EvalElseAndScale(real, 2*math.Pi); err != nil {
		return nil, 0, bootCount, err
	}
	if err = c.eval.Evaluator.Mul(imag, 1i, imag); err != nil {
		return nil, 0, bootCount, err
	}
	if err = c.eval.Evaluator.Add(real, imag, ct); err != nil {
		return nil, 0, bootCount, err
	}

	polys, err := polynomial.NewPolynomialVector([]bignum.Polynomial{
		bignum.NewPolynomial(0, HermiteInterpolation(int(c.mods), c.degEval), nil),
	}, c.mapping)
	if err != nil {
		return nil, 0, bootCount, err
	}

	if ct, err = c.polyEval.Evaluate(ct, polys, c.params.DefaultScale()); err != nil {
		return nil, 0, bootCount, err
	}

	return ct, targetScale / zeroScale, bootCount, nil
}

func (c *REDCComputer) multiplyLow(lhs, rhs []*rlwe.Ciphertext) ([]*rlwe.Ciphertext, error) {
	out := make([]*rlwe.Ciphertext, c.limbCount+1)
	for i := 0; i < c.limbCount; i++ {
		for j := 0; j <= i; j++ {
			ctmp, err := c.eval.MulRelinNew(lhs[j], rhs[i-j])
			if err != nil {
				return nil, err
			}
			if j == 0 {
				out[i] = ctmp.CopyNew()
			} else {
				if out[i], err = c.eval.AddNew(out[i], ctmp); err != nil {
					return nil, err
				}
			}
		}
		if err := c.eval.Rescale(out[i], out[i]); err != nil {
			return nil, err
		}
	}
	zero, err := c.eval.SubNew(lhs[0], lhs[0])
	if err != nil {
		return nil, err
	}
	out[c.limbCount] = zero

	reduced, _, err := c.reduceProductDigits(out)
	if err != nil {
		return nil, err
	}

	return reduced[:c.limbCount], nil
}

func (c *REDCComputer) multiplyExt(lhs, rhs []*rlwe.Ciphertext, zero *rlwe.Ciphertext) ([]*rlwe.Ciphertext, error) {
	out := make([]*rlwe.Ciphertext, 2*c.limbCount+1)
	for i := 0; i < 2*c.limbCount-1; i++ {
		lowBound := 0
		if i >= c.limbCount {
			lowBound = i - c.limbCount + 1
		}
		for j := lowBound; j <= (i - lowBound); j++ {
			ctmp, err := c.eval.MulRelinNew(lhs[j], rhs[i-j])
			if err != nil {
				return nil, err
			}
			if j == lowBound {
				out[i] = ctmp.CopyNew()
			} else {
				if out[i], err = c.eval.AddNew(out[i], ctmp); err != nil {
					return nil, err
				}
			}
		}
		if err := c.eval.Rescale(out[i], out[i]); err != nil {
			return nil, err
		}
	}
	out[2*c.limbCount-1] = zero.CopyNew()
	out[2*c.limbCount] = zero.CopyNew()
	return out, nil
}

func (c *REDCComputer) reduceProductDigits(digits []*rlwe.Ciphertext) ([]*rlwe.Ciphertext, int, error) {
	out := make([]*rlwe.Ciphertext, len(digits))
	copy(out, digits)

	_, scaleDiff, bootCount, err := c.bootstrap(out[0].CopyNew())
	if err != nil {
		return nil, 0, err
	}

	var carry1 *rlwe.Ciphertext
	var carry2 *rlwe.Ciphertext
	for i := range out {
		current := out[i].CopyNew()
		if i != 0 {
			if err := c.eval.Evaluator.Add(current, carry1, current); err != nil {
				return nil, 0, err
			}
		}

		remainder := current.CopyNew()
		if err := c.eval.Mul(current, scaleDiff/float64(c.mods), current); err != nil {
			return nil, 0, err
		}
		if err := c.eval.Rescale(current, current); err != nil {
			return nil, 0, err
		}

		current, ratio, used, err := c.bootstrap(current)
		if err != nil {
			return nil, 0, err
		}
		bootCount += used
		if ratio != 0 {
			scaleDiff = ratio
		}
		out[i] = current.CopyNew()

		if i != len(out)-1 {
			if err := c.eval.Evaluator.Sub(remainder, current, remainder); err != nil {
				return nil, 0, err
			}

			carry2 = remainder.CopyNew()
			if err := c.eval.Evaluator.Mul(remainder, scaleDiff/float64(c.mods*c.mods), remainder); err != nil {
				return nil, 0, err
			}
			if err := c.eval.Rescale(remainder, remainder); err != nil {
				return nil, 0, err
			}

			remainder, ratio, used, err = c.bootstrap(remainder)
			if err != nil {
				return nil, 0, err
			}
			bootCount += used
			if ratio != 0 {
				scaleDiff = ratio
			}
			carry1 = remainder.CopyNew()

			tmp := remainder.CopyNew()
			if err := c.eval.Evaluator.Mul(remainder, c.mods, tmp); err != nil {
				return nil, 0, err
			}
			if err := c.eval.Evaluator.Sub(carry2, tmp, carry2); err != nil {
				return nil, 0, err
			}
			if err := c.eval.Evaluator.Mul(carry2, scaleDiff/float64(c.mods*c.mods*c.mods), carry2); err != nil {
				return nil, 0, err
			}
			if err := c.eval.Rescale(carry2, carry2); err != nil {
				return nil, 0, err
			}

			carry2, ratio, used, err = c.bootstrap(carry2)
			if err != nil {
				return nil, 0, err
			}
			bootCount += used
			if ratio != 0 {
				scaleDiff = ratio
			}

			if err := c.eval.Evaluator.Mul(carry2, c.mods, carry2); err != nil {
				return nil, 0, err
			}
			if i != 0 {
				if err := c.eval.Evaluator.Add(carry1, carry2, carry1); err != nil {
					return nil, 0, err
				}
			}
		}
	}

	return out, bootCount, nil
}

func (c *REDCComputer) reduceSmallDigits(digits []*rlwe.Ciphertext) ([]*rlwe.Ciphertext, int, error) {
	out := make([]*rlwe.Ciphertext, len(digits))
	copy(out, digits)

	_, scaleDiff, bootCount, err := c.bootstrap(out[0].CopyNew())
	if err != nil {
		return nil, 0, err
	}

	var carry *rlwe.Ciphertext
	for i := range out {
		current := out[i].CopyNew()
		if i != 0 {
			if err := c.eval.Evaluator.Add(current, carry, current); err != nil {
				return nil, 0, err
			}
		}

		remainder := current.CopyNew()
		if err := c.eval.Mul(current, scaleDiff/float64(c.mods), current); err != nil {
			return nil, 0, err
		}
		if err := c.eval.Rescale(current, current); err != nil {
			return nil, 0, err
		}

		current, ratio, used, err := c.bootstrap(current)
		if err != nil {
			return nil, 0, err
		}
		bootCount += used
		if ratio != 0 {
			scaleDiff = ratio
		}
		out[i] = current.CopyNew()

		if err := c.eval.Evaluator.Sub(remainder, current, remainder); err != nil {
			return nil, 0, err
		}
		if err := c.eval.Evaluator.Mul(remainder, scaleDiff/float64(c.mods*c.mods), remainder); err != nil {
			return nil, 0, err
		}
		if err := c.eval.Rescale(remainder, remainder); err != nil {
			return nil, 0, err
		}

		remainder, ratio, used, err = c.bootstrap(remainder)
		if err != nil {
			return nil, 0, err
		}
		bootCount += used
		if ratio != 0 {
			scaleDiff = ratio
		}
		carry = remainder
	}

	return out, bootCount, nil
}

func (c *REDCComputer) subtractDigits(lhs, rhs []*rlwe.Ciphertext) ([]*rlwe.Ciphertext, int, error) {
	if len(lhs) != len(rhs) {
		return nil, 0, fmt.Errorf("mismatched limb counts: lhs=%d rhs=%d", len(lhs), len(rhs))
	}

	out := make([]*rlwe.Ciphertext, len(lhs))
	for i := 0; i < len(lhs); i++ {
		ct, err := c.eval.SubNew(lhs[i], rhs[i])
		if err != nil {
			return nil, 0, err
		}
		out[i] = ct
	}

	_, scaleDiff, bootCount, err := c.bootstrap(out[0].CopyNew())
	if err != nil {
		return nil, 0, err
	}

	var borrow *rlwe.Ciphertext
	for i := range out {
		current := out[i].CopyNew()
		if i != 0 {
			if err := c.eval.Evaluator.Add(current, borrow, current); err != nil {
				return nil, 0, err
			}
		}

		remainder := current.CopyNew()
		if err := c.eval.Mul(current, scaleDiff/float64(c.mods), current); err != nil {
			return nil, 0, err
		}
		if err := c.eval.Rescale(current, current); err != nil {
			return nil, 0, err
		}

		current, ratio, used, err := c.bootstrap(current)
		if err != nil {
			return nil, 0, err
		}
		bootCount += used
		if ratio != 0 {
			scaleDiff = ratio
		}
		out[i] = current.CopyNew()

		if err := c.eval.Evaluator.Sub(remainder, current, remainder); err != nil {
			return nil, 0, err
		}
		if err := c.eval.Evaluator.Mul(remainder, scaleDiff/float64(c.mods*c.mods), remainder); err != nil {
			return nil, 0, err
		}
		if err := c.eval.Rescale(remainder, remainder); err != nil {
			return nil, 0, err
		}
		remainder, err = c.eval.AddNew(remainder, 0.5)
		if err != nil {
			return nil, 0, err
		}

		remainder, ratio, used, err = c.bootstrap(remainder)
		if err != nil {
			return nil, 0, err
		}
		bootCount += used
		if ratio != 0 {
			scaleDiff = ratio
		}

		borrow, err = c.eval.SubNew(remainder, float64(c.mods/2))
		if err != nil {
			return nil, 0, err
		}
	}

	return out, bootCount, nil
}

func (c *REDCComputer) compareGE(lhs, rhs []*rlwe.Ciphertext) (*rlwe.Ciphertext, int, error) {
	if len(lhs) != len(rhs) {
		return nil, 0, fmt.Errorf("mismatched limb counts: lhs=%d rhs=%d", len(lhs), len(rhs))
	}

	diff := make([]*rlwe.Ciphertext, len(lhs))
	for i := 0; i < len(lhs); i++ {
		ct, err := c.eval.SubNew(lhs[i], rhs[i])
		if err != nil {
			return nil, 0, err
		}
		diff[i] = ct
	}

	_, scaleDiff, bootCount, err := c.bootstrap(diff[0].CopyNew())
	if err != nil {
		return nil, 0, err
	}

	var borrow *rlwe.Ciphertext
	var result *rlwe.Ciphertext
	for i := range diff {
		current := diff[i].CopyNew()
		if i != 0 {
			if err := c.eval.Evaluator.Add(current, borrow, current); err != nil {
				return nil, 0, err
			}
		}

		remainder := current.CopyNew()
		if err := c.eval.Mul(current, scaleDiff/float64(c.mods), current); err != nil {
			return nil, 0, err
		}
		if err := c.eval.Rescale(current, current); err != nil {
			return nil, 0, err
		}

		current, ratio, used, err := c.bootstrap(current)
		if err != nil {
			return nil, 0, err
		}
		bootCount += used
		if ratio != 0 {
			scaleDiff = ratio
		}

		if err := c.eval.Evaluator.Sub(remainder, current, remainder); err != nil {
			return nil, 0, err
		}
		if err := c.eval.Evaluator.Mul(remainder, scaleDiff/float64(c.mods*c.mods), remainder); err != nil {
			return nil, 0, err
		}
		if err := c.eval.Rescale(remainder, remainder); err != nil {
			return nil, 0, err
		}
		remainder, err = c.eval.AddNew(remainder, 0.5)
		if err != nil {
			return nil, 0, err
		}

		remainder, ratio, used, err = c.bootstrap(remainder)
		if err != nil {
			return nil, 0, err
		}
		bootCount += used
		if ratio != 0 {
			scaleDiff = ratio
		}

		borrow, err = c.eval.SubNew(remainder, float64(c.mods/2))
		if err != nil {
			return nil, 0, err
		}
		if i == len(diff)-1 {
			result, err = c.eval.AddNew(borrow, 1.0)
			if err != nil {
				return nil, 0, err
			}
		}
	}

	return result, bootCount, nil
}

func (c *REDCComputer) selectDigits(base, alt []*rlwe.Ciphertext, flag *rlwe.Ciphertext) ([]*rlwe.Ciphertext, error) {
	out := make([]*rlwe.Ciphertext, len(base))
	for i := range base {
		delta, err := c.eval.SubNew(alt[i], base[i])
		if err != nil {
			return nil, err
		}
		delta, err = c.eval.MulRelinNew(delta, flag)
		if err != nil {
			return nil, err
		}
		if err := c.eval.Rescale(delta, delta); err != nil {
			return nil, err
		}
		if out[i], err = c.eval.AddNew(base[i], delta); err != nil {
			return nil, err
		}
	}
	return out, nil
}

func (c *REDCComputer) REDCP(t, modulus, modulusInv []*rlwe.Ciphertext, zero *rlwe.Ciphertext) ([]*rlwe.Ciphertext, []*rlwe.Ciphertext, []*rlwe.Ciphertext, *rlwe.Ciphertext, int, error) {
	if *flagTraceLevels {
		fmt.Printf("level trace: input t min=%d modulus min=%d modulusInv min=%d\n", minLevel(t), minLevel(modulus), minLevel(modulusInv))
	}
	q, err := c.multiplyLow(t[:c.limbCount], modulusInv)
	if err != nil {
		return nil, nil, nil, nil, 0, err
	}
	if *flagTraceLevels {
		fmt.Printf("level trace: after q=min %d\n", minLevel(q))
	}

	qp, err := c.multiplyExt(q, modulus, zero)
	if err != nil {
		return nil, nil, nil, nil, 0, err
	}
	if *flagTraceLevels {
		fmt.Printf("level trace: after qp=min %d\n", minLevel(qp))
	}

	sum := make([]*rlwe.Ciphertext, len(qp))
	for i := range sum {
		if i < len(t) {
			if sum[i], err = c.eval.AddNew(qp[i], t[i]); err != nil {
				return nil, nil, nil, nil, 0, err
			}
			continue
		}
		sum[i] = qp[i].CopyNew()
	}
	if *flagTraceLevels {
		fmt.Printf("level trace: after sum=min %d\n", minLevel(sum))
	}

	normalized, bootNorm, err := c.reduceProductDigits(sum)
	if err != nil {
		return nil, nil, nil, nil, 0, err
	}
	if *flagTraceLevels {
		fmt.Printf("level trace: after normalize=min %d\n", minLevel(normalized))
	}

	u := make([]*rlwe.Ciphertext, len(normalized)-c.limbCount)
	for i := range u {
		u[i] = normalized[i+c.limbCount].CopyNew()
	}
	if *flagTraceLevels {
		fmt.Printf("level trace: extracted u=min %d\n", minLevel(u))
	}

	modulusPadded := make([]*rlwe.Ciphertext, len(u))
	for i := range modulusPadded {
		if i < len(modulus) {
			modulusPadded[i] = modulus[i].CopyNew()
			continue
		}
		modulusPadded[i] = zero.CopyNew()
	}

	diff, bootSub, err := c.subtractDigits(u, modulusPadded)
	if err != nil {
		return nil, nil, nil, nil, 0, err
	}
	if *flagTraceLevels {
		fmt.Printf("level trace: after subtract=min %d\n", minLevel(diff))
	}

	flag, bootCmp, err := c.compareGE(u, modulusPadded)
	if err != nil {
		return nil, nil, nil, nil, 0, err
	}
	if *flagTraceLevels {
		fmt.Printf("level trace: compare flag level=%d\n", flag.Level())
	}

	out, err := c.selectDigits(u, diff, flag)
	if err != nil {
		return nil, nil, nil, nil, 0, err
	}
	out, bootOut, err := c.reduceSmallDigits(out)
	if err != nil {
		return nil, nil, nil, nil, 0, err
	}
	if *flagTraceLevels {
		fmt.Printf("level trace: final out=min %d\n", minLevel(out))
	}

	return out, q, u, flag, bootNorm + bootSub + bootCmp + bootOut, nil
}

func (c *REDCComputer) halfIntBoot(ct *rlwe.Ciphertext) (ctOut *rlwe.Ciphertext, bootCount int, err error) {
	if ct, err = c.eval.ModUp(ct); err != nil {
		return nil, 1, err
	}

	realPart, imagPart, err := c.eval.CoeffsToSlots(ct)
	if err != nil {
		return nil, 1, err
	}

	if imagPart, err = c.eval.EvalModAndScale(realPart, 2*math.Pi); err != nil {
		return nil, 1, err
	}
	if realPart, err = c.eval.EvalElseAndScale(realPart, 2*math.Pi); err != nil {
		return nil, 1, err
	}
	if err = c.eval.Evaluator.Mul(imagPart, 1i, imagPart); err != nil {
		return nil, 1, err
	}
	if err = c.eval.Evaluator.Add(realPart, imagPart, ct); err != nil {
		return nil, 1, err
	}
	ct.IsBatched = true

	polys, err := polynomial.NewPolynomialVector([]bignum.Polynomial{
		bignum.NewPolynomial(0, HermiteInterpolation(int(c.mods), c.degEval), nil),
	}, c.mapping)
	if err != nil {
		return nil, 1, err
	}

	if ctOut, err = c.polyEval.Evaluate(ct, polys, c.params.DefaultScale()); err != nil {
		return nil, 1, err
	}
	ctOut.IsBatched = true

	return ctOut, 1, nil
}

func (c *REDCComputer) intBootDigits(ct *rlwe.Ciphertext, limbs int) ([]*rlwe.Ciphertext, int, error) {
	current := ct.CopyNew()
	out := make([]*rlwe.Ciphertext, limbs)
	bootCount := 0

	traceCoeffsCiphertext("current/init", current, 8)

	for i := 0; i < limbs; i++ {
		shifted := current.CopyNew()
		pow := limbs - 1 - i
		if pow > 0 {
			if err := c.eval.Evaluator.Mul(shifted, intPowBig(c.mods, pow), shifted); err != nil {
				return nil, 0, err
			}
		}
		traceCoeffsCiphertext(fmt.Sprintf("iter=%d shifted", i), shifted, 8)

		digit, used, err := c.halfIntBoot(shifted)
		if err != nil {
			return nil, 0, err
		}
		bootCount += used
		traceSlotsCiphertext(fmt.Sprintf("iter=%d digit", i), digit, 8)

		out[i] = digit

		if i != limbs-1 {
			digitForStC := digit.CopyNew()
			if err := c.eval.Mul(digitForStC, 1.0/float64(intPowBig(c.mods, limbs).Uint64()), digitForStC); err != nil {
				return nil, 0, err
			}
			if err := c.eval.Rescale(digitForStC, digitForStC); err != nil {
				return nil, 0, err
			}
			if digitForStC.Level() > c.eval.SlotsToCoeffsParameters.LevelQ {
				digitForStC.Resize(digitForStC.Degree(), c.eval.SlotsToCoeffsParameters.LevelQ)
			}
			back, err := c.eval.SlotsToCoeffs(digitForStC, nil)
			if err != nil {
				return nil, 0, err
			}
			back.IsBatched = false
			if i > 0 {
				if err := c.eval.Evaluator.Mul(back, intPowBig(c.mods, i), back); err != nil {
					return nil, 0, err
				}
			}
			traceCoeffsCiphertext(fmt.Sprintf("iter=%d back", i), back, 8)
			if err := c.eval.Evaluator.Sub(current, back, current); err != nil {
				return nil, 0, err
			}
			traceCoeffsCiphertext(fmt.Sprintf("iter=%d current-after-sub", i), current, 8)
		}
	}

	return out, bootCount, nil
}

// legacyConvBtDReference is kept from the standalone BFV-to-Discrete-CKKS example
// as a reference implementation of Algorithm 3/REDC composition. The ConvGtD
// experiment in main does not call this helper.
func (c *REDCComputer) legacyConvBtDReference(ctCombined *rlwe.Ciphertext, modulus, modulusInv []*rlwe.Ciphertext, zero *rlwe.Ciphertext) (out, decomposed, q, u []*rlwe.Ciphertext, flag *rlwe.Ciphertext, bootCount int, err error) {
	decomposed, bootDecomp, err := c.intBootDigits(ctCombined, c.limbCount)
	if err != nil {
		return nil, nil, nil, nil, nil, 0, err
	}

	padded := make([]*rlwe.Ciphertext, 2*c.limbCount)
	for i := 0; i < len(padded); i++ {
		if i < len(decomposed) {
			padded[i] = decomposed[i].CopyNew()
		} else {
			padded[i] = zero.CopyNew()
		}
	}

	out, q, u, flag, bootREDC, err := c.REDCP(padded, modulus, modulusInv, zero)
	if err != nil {
		return nil, nil, nil, nil, nil, 0, err
	}

	return out, decomposed, q, u, flag, bootDecomp + bootREDC, nil
}

func (c *REDCComputer) reduceByRepeatedSub(digits, modulus []*rlwe.Ciphertext, rounds int) (out []*rlwe.Ciphertext, bootCount int, err error) {
	out = make([]*rlwe.Ciphertext, len(digits))
	for i := range digits {
		out[i] = digits[i].CopyNew()
	}

	for step := 0; step < rounds; step++ {
		flag, bootCmp, err := c.compareGE(out, modulus)
		if err != nil {
			return nil, bootCount, err
		}
		sub, bootSub, err := c.subtractDigits(out, modulus)
		if err != nil {
			return nil, bootCount, err
		}
		out, err = c.selectDigits(out, sub, flag)
		if err != nil {
			return nil, bootCount, err
		}
		bootCount += bootCmp + bootSub

		if step != rounds-1 {
			for i := range out {
				refreshed, _, bootRefresh, err := c.bootstrap(out[i])
				if err != nil {
					return nil, bootCount, err
				}
				out[i] = refreshed
				bootCount += bootRefresh
			}
		}
	}

	return out, bootCount, nil
}

func smallLogSlots(slots int) int {
	logSlots := 0
	for (1 << (logSlots + 1)) <= slots {
		logSlots++
	}
	return logSlots
}

func parseDensityFraction(literal string) (num, den int, err error) {
	compact := strings.TrimSpace(literal)
	compact = strings.ReplaceAll(compact, " ", "")
	if compact == "" {
		return 0, 0, errors.New("empty GBFV density")
	}

	parts := strings.Split(compact, "/")
	if len(parts) > 2 {
		return 0, 0, fmt.Errorf("invalid GBFV density %q", literal)
	}

	num, err = strconv.Atoi(parts[0])
	if err != nil {
		return 0, 0, fmt.Errorf("invalid GBFV density numerator %q", parts[0])
	}
	if len(parts) == 1 {
		den = 1
	} else {
		den, err = strconv.Atoi(parts[1])
		if err != nil {
			return 0, 0, fmt.Errorf("invalid GBFV density denominator %q", parts[1])
		}
	}

	if num <= 0 || den <= 0 || num > den {
		return 0, 0, fmt.Errorf("GBFV density must be in (0, 1], got %q", literal)
	}
	if den%num == 0 {
		switch den / num {
		case 1, 2, 4, 8:
			return num, den, nil
		}
	}
	return 0, 0, fmt.Errorf("unsupported GBFV density %q: use 1/8, 1/4, 1/2, or 1", literal)
}

func sampleGBFVMessages(gbfv GBFVPlaintextLayout, slots int) ([]*big.Int, error) {
	if slots <= 0 || slots > gbfv.slots {
		return nil, fmt.Errorf("active GBFV slot count must be in [1, %d], got %d", gbfv.slots, slots)
	}

	messages := make([]*big.Int, slots)
	for i := range messages {
		value, err := rand.Int(rand.Reader, gbfv.plaintextModulus)
		if err != nil {
			return nil, err
		}
		messages[i] = value
	}

	return messages, nil
}

type GBFVPlaintextLayout struct {
	base                  int64
	slots                 int
	ringDegree            int
	digitCount            int
	q                     uint64
	baseInt               *big.Int
	plaintextModulus      *big.Int
	plaintextModulusFloat *big.Float
	floatPrecision        uint
}

func newGBFVPlaintextLayout(params ckks.Parameters, base int64, slots int) (GBFVPlaintextLayout, error) {
	if base <= 1 {
		return GBFVPlaintextLayout{}, fmt.Errorf("GBFV base must be at least 2, got %d", base)
	}
	if slots <= 0 || params.N()%slots != 0 {
		return GBFVPlaintextLayout{}, fmt.Errorf("GBFV slots k=%d must divide ring degree N=%d", slots, params.N())
	}

	prec := uint(2048)
	baseInt := big.NewInt(base)
	digitCount := params.N() / slots
	plaintextModulus := new(big.Int).Exp(baseInt, big.NewInt(int64(digitCount)), nil)
	plaintextModulus.Add(plaintextModulus, big.NewInt(1))

	plaintextModulusFloat := new(big.Float).SetPrec(prec)
	plaintextModulusFloat.SetInt(plaintextModulus)

	return GBFVPlaintextLayout{
		base:                  base,
		slots:                 slots,
		ringDegree:            params.N(),
		digitCount:            digitCount,
		q:                     params.RingQ().ModulusAtLevel[0].Uint64(),
		baseInt:               baseInt,
		plaintextModulus:      plaintextModulus,
		plaintextModulusFloat: plaintextModulusFloat,
		floatPrecision:        prec,
	}, nil
}

func gbfvCoefficientValues(params ckks.Parameters, gbfv GBFVPlaintextLayout, values []*big.Int) ([]float64, error) {
	if len(values) != gbfv.slots {
		return nil, fmt.Errorf("GBFV layout expects %d message coefficients, got %d", gbfv.slots, len(values))
	}

	coeffs := make([]float64, params.N())
	for i := range coeffs {
		slot := i % gbfv.slots
		digit := i / gbfv.slots

		exponent := big.NewInt(int64(gbfv.digitCount - digit - 1))
		coefficient := new(big.Int).Exp(gbfv.baseInt, exponent, nil)
		coefficient.Mul(coefficient, values[slot])
		coefficient.Mod(coefficient, gbfv.plaintextModulus)

		scaled := new(big.Float).SetPrec(gbfv.floatPrecision)
		scaled.SetInt(coefficient)
		scaled.Quo(scaled, gbfv.plaintextModulusFloat)

		coeffs[i], _ = scaled.Float64()
		coeffs[i] *= float64(gbfv.q)
	}

	return coeffs, nil
}

func tPolynomial(size int, gbfv GBFVPlaintextLayout) []float64 {
	values := make([]float64, size)
	values[0] = float64(gbfv.base)
	values[gbfv.slots] = -1.0
	return values
}

func encodeCoefficientPolynomial(params ckks.Parameters, values []float64, pt *rlwe.Plaintext) error {
	if len(values) > params.N() {
		return fmt.Errorf("cannot encode coefficient polynomial: maximum number of values is %d but got %d", params.N(), len(values))
	}

	ringQ := params.RingQ().AtLevel(pt.Level())
	ckks.Float64ToFixedPointCRT(ringQ, values, 1.0, pt.Value.Coeffs)
	ringQ.NTT(pt.Value, pt.Value)
	return nil
}

func encryptGBFVInputCiphertext(params ckks.Parameters, encryptor *rlwe.Encryptor, values []float64, level int, gbfv GBFVPlaintextLayout) (*rlwe.Ciphertext, error) {
	pt := ckks.NewPlaintext(params, level)
	pt.IsBatched = false
	pt.LogDimensions = params.LogMaxDimensions()
	if err := encodeCoefficientPolynomial(params, values, pt); err != nil {
		return nil, err
	}
	pt.Scale = rlwe.NewScale(float64(gbfv.q))
	return encryptor.EncryptNew(pt)
}

func multiplyByTPolynomial(params ckks.Parameters, eval *ckks.Evaluator, ct *rlwe.Ciphertext, gbfv GBFVPlaintextLayout) (*rlwe.Ciphertext, error) {
	ptT := ckks.NewPlaintext(params, ct.Level())
	ptT.IsBatched = false
	ptT.LogDimensions = params.LogMaxDimensions()
	ptT.Scale = rlwe.NewScale(1)
	if err := encodeCoefficientPolynomial(params, tPolynomial(params.N(), gbfv), ptT); err != nil {
		return nil, err
	}

	out, err := eval.MulNew(ct, ptT)
	if err != nil {
		return nil, err
	}
	out.IsBatched = false
	out.LogDimensions = params.LogMaxDimensions()
	return out, nil
}

func modRaiseCentered(params ckks.Parameters, ct *rlwe.Ciphertext, targetLevel int) (*rlwe.Ciphertext, error) {
	if ct.Level() != 0 {
		return nil, fmt.Errorf("centered ModRaise expects level-0 input, got level %d", ct.Level())
	}
	if targetLevel <= 0 || targetLevel > params.MaxLevel() {
		return nil, fmt.Errorf("invalid centered ModRaise target level %d", targetLevel)
	}

	out := ct.CopyNew()
	ringQ0 := params.RingQ().AtLevel(0)
	for i := range out.Value {
		ringQ0.INTT(out.Value[i], out.Value[i])
	}

	out.Resize(out.Degree(), targetLevel)
	ringQ := params.RingQ().AtLevel(targetLevel)
	q0 := ringQ.SubRings[0].Modulus
	halfQ0 := q0 >> 1
	N := ringQ.N()

	for poly := range out.Value {
		coeffs0 := out.Value[poly].Coeffs[0]
		for level := 1; level <= targetLevel; level++ {
			qi := ringQ.SubRings[level].Modulus
			coeffs := out.Value[poly].Coeffs[level]
			for j := 0; j < N; j++ {
				coeff := coeffs0[j]
				if coeff >= halfQ0 {
					magnitude := (q0 - coeff) % qi
					if magnitude == 0 {
						coeffs[j] = 0
					} else {
						coeffs[j] = qi - magnitude
					}
				} else {
					coeffs[j] = coeff % qi
				}
			}
		}
	}

	for i := range out.Value {
		ringQ.NTT(out.Value[i], out.Value[i])
	}
	return out, nil
}

func gbfvTProductDigits(values []*big.Int, gbfv GBFVPlaintextLayout, limbs int) ([][]complex128, error) {
	out := make([][]complex128, limbs)
	for i := range out {
		out[i] = make([]complex128, len(values))
	}

	modCoeffs := make([]*big.Int, gbfv.digitCount)
	for slot, value := range values {
		for digit := 0; digit < gbfv.digitCount; digit++ {
			exponent := big.NewInt(int64(gbfv.digitCount - digit - 1))
			coefficient := new(big.Int).Exp(gbfv.baseInt, exponent, nil)
			coefficient.Mul(coefficient, value)
			coefficient.Mod(coefficient, gbfv.plaintextModulus)
			modCoeffs[digit] = coefficient
		}

		for digit := 0; digit < gbfv.digitCount; digit++ {
			numerator := new(big.Int).Mul(big.NewInt(gbfv.base), modCoeffs[digit])
			if digit == 0 {
				numerator.Add(numerator, modCoeffs[gbfv.digitCount-1])
			} else {
				numerator.Sub(numerator, modCoeffs[digit-1])
			}

			quotient, remainder := new(big.Int).QuoRem(numerator, gbfv.plaintextModulus, new(big.Int))
			if remainder.Sign() != 0 {
				return nil, fmt.Errorf("non-integral GBFV t-product digit at slot=%d digit=%d remainder=%s", slot, digit, remainder.String())
			}
			if digit < limbs {
				out[digit][slot] = complex(float64(quotient.Int64()), 0)
			} else if quotient.Sign() != 0 {
				return nil, fmt.Errorf("nonzero GBFV t-product digit outside CPL25 window at slot=%d digit=%d value=%s", slot, digit, quotient.String())
			}
		}
	}

	return out, nil
}

func centeredModularRepresentative(value, modulus *big.Int) *big.Int {
	out := new(big.Int).Set(value)
	half := new(big.Int).Rsh(new(big.Int).Set(modulus), 1)
	if out.Cmp(half) >= 0 {
		out.Sub(out, modulus)
	}
	return out
}

func gbfvCenteredTProductDigits(values []*big.Int, gbfv GBFVPlaintextLayout, limbs int) ([][]complex128, error) {
	out := make([][]complex128, limbs)
	for i := range out {
		out[i] = make([]complex128, len(values))
	}

	centeredCoeffs := make([]*big.Int, gbfv.digitCount)
	for slot, value := range values {
		for digit := 0; digit < gbfv.digitCount; digit++ {
			exponent := big.NewInt(int64(gbfv.digitCount - digit - 1))
			coefficient := new(big.Int).Exp(gbfv.baseInt, exponent, nil)
			coefficient.Mul(coefficient, value)
			coefficient.Mod(coefficient, gbfv.plaintextModulus)
			centeredCoeffs[digit] = centeredModularRepresentative(coefficient, gbfv.plaintextModulus)
		}

		for digit := 0; digit < gbfv.digitCount; digit++ {
			numerator := new(big.Int).Mul(big.NewInt(gbfv.base), centeredCoeffs[digit])
			if digit == 0 {
				numerator.Add(numerator, centeredCoeffs[gbfv.digitCount-1])
			} else {
				numerator.Sub(numerator, centeredCoeffs[digit-1])
			}

			quotient, remainder := new(big.Int).QuoRem(numerator, gbfv.plaintextModulus, new(big.Int))
			if remainder.Sign() != 0 {
				return nil, fmt.Errorf("non-integral centered GBFV t-product digit at slot=%d digit=%d remainder=%s", slot, digit, remainder.String())
			}
			if digit < limbs {
				out[digit][slot] = complex(float64(quotient.Int64()), 0)
			} else if quotient.Sign() != 0 {
				return nil, fmt.Errorf("nonzero centered GBFV t-product digit outside CPL25 window at slot=%d digit=%d value=%s", slot, digit, quotient.String())
			}
		}
	}

	return out, nil
}

func minInt(a, b int) int {
	if a < b {
		return a
	}
	return b
}

func ringPackingKeyLogQ(params ckks.Parameters, levelQ int) float64 {
	logQ := 0.0
	for i := 0; i <= levelQ; i++ {
		logQ += math.Log2(float64(params.Q()[i]))
	}
	return logQ
}

func ringPackingKeyLogQP(params ckks.Parameters, levelQ, levelP int) float64 {
	logQP := ringPackingKeyLogQ(params, levelQ)
	if levelP >= 0 {
		for i := 0; i <= levelP; i++ {
			logQP += math.Log2(float64(params.P()[i]))
		}
	}
	return logQP
}

func resolveRingPackMinLogN(params ckks.Parameters, requested, keyLevelQ, keyLevelP int, allowInsecure bool) (int, error) {
	maxLogN := params.LogN()
	keyLogQP := ringPackingKeyLogQP(params, keyLevelQ, keyLevelP)
	minLogN := requested
	if minLogN == 0 {
		if keyLogQP <= lowModulusRingPackMaxLogQP {
			minLogN = minInt(maxLogN, lowModulusRingPackMinLogN)
		} else {
			minLogN = minInt(maxLogN, defaultRingPackMinLogN)
		}
	}
	if minLogN < 1 || minLogN > maxLogN {
		return 0, fmt.Errorf("ring-pack minLogN=%d outside [1, %d]", minLogN, maxLogN)
	}
	if minLogN < maxLogN && minLogN < defaultRingPackMinLogN && keyLogQP > lowModulusRingPackMaxLogQP && !allowInsecure {
		return 0, fmt.Errorf("ring-pack minLogN=%d with key logQP %.2f exceeds low-modulus bound %.2f; use -allow-insecure-ring-switch only for debugging",
			minLogN, keyLogQP, lowModulusRingPackMaxLogQP)
	}
	return minLogN, nil
}

func checkSecurityAssumptions(params ckks.Parameters, short bool, ringPackMinLogN int, ringPackKeyLogQP float64, allowInsecure bool) error {
	if short {
		fmt.Println("Security note: -short uses intentionally insecure toy parameters for quick precision checks.")
		return nil
	}
	if params.LogN() != 16 || params.LogQP() > 1550 {
		if !allowInsecure {
			return fmt.Errorf("main CKKS parameters need review: logN=%d logQP=%.2f; expected logN=16 with logQP<=1550",
				params.LogN(), params.LogQP())
		}
		fmt.Printf("Security warning: main CKKS parameters bypassed by debug flag: logN=%d logQP=%.2f\n", params.LogN(), params.LogQP())
	} else {
		fmt.Printf("Security check: main homomorphic parameters use logN=%d and logQP=%.2f <= 1550.\n", params.LogN(), params.LogQP())
	}
	if ringPackMinLogN == lowModulusRingPackMinLogN && ringPackKeyLogQP <= lowModulusRingPackMaxLogQP {
		fmt.Printf("Security check: ring packing uses logN=%d with key logQP=%.2f <= %.0f.\n",
			ringPackMinLogN, ringPackKeyLogQP, lowModulusRingPackMaxLogQP)
		return nil
	}
	if ringPackMinLogN >= defaultRingPackMinLogN {
		fmt.Printf("Security check: ring packing uses conservative minLogN=%d with key logQP=%.2f.\n", ringPackMinLogN, ringPackKeyLogQP)
		return nil
	}
	if allowInsecure {
		fmt.Printf("Security warning: ring packing minLogN=%d key logQP=%.2f bypassed by debug flag.\n", ringPackMinLogN, ringPackKeyLogQP)
		return nil
	}
	return fmt.Errorf("ring-packing parameters need review: minLogN=%d key logQP=%.2f", ringPackMinLogN, ringPackKeyLogQP)
}

func newRingPackingEvaluator(params ckks.Parameters, sk *rlwe.SecretKey, minLogN, keyLevelQ, keyLevelP int) (*rlwe.RingPackingEvaluator, error) {
	evkParams := rlwe.EvaluationKeyParameters{
		LevelQ: utils.Pointy(keyLevelQ),
		LevelP: utils.Pointy(keyLevelP),
	}
	rpk := &rlwe.RingPackingEvaluationKey{}

	if minLogN < params.LogN() {
		ski, err := rpk.GenRingSwitchingKeys(&params, sk, minLogN, evkParams)
		if err != nil {
			return nil, err
		}
		rpk.GenRepackEvaluationKeys(rpk.Parameters[minLogN], ski[minLogN], evkParams)
		rpk.GenRepackEvaluationKeys(rpk.Parameters[params.LogN()], ski[params.LogN()], evkParams)
	} else {
		rpk.Parameters = map[int]rlwe.ParameterProvider{params.LogN(): &params}
		rpk.GenRepackEvaluationKeys(&params, sk, evkParams)
	}

	return rlwe.NewRingPackingEvaluator(rpk), nil
}

func extractAndRingPackDigits(
	params ckks.Parameters,
	coeffCiphertext *rlwe.Ciphertext,
	limbCount, batch int,
	coefficientIndex func(limb, slot int) int,
	packer *rlwe.RingPackingEvaluator,
	dftEval *dft.Evaluator,
	ctsMatrix dft.Matrix,
) ([]*rlwe.Ciphertext, error) {
	out := make([]*rlwe.Ciphertext, limbCount)
	logSlots := params.LogMaxSlots()

	for limb := 0; limb < limbCount; limb++ {
		idx := make(map[int]bool, batch)
		for slot := 0; slot < batch; slot++ {
			coeffIdx := coefficientIndex(limb, slot)
			if coeffIdx < 0 || coeffIdx >= params.N() {
				return nil, fmt.Errorf("coefficient index %d for limb=%d slot=%d exceeds ring degree %d", coeffIdx, limb, slot, params.N())
			}
			idx[coeffIdx] = true
		}

		extracted, err := packer.ExtractNaive(coeffCiphertext, idx)
		if err != nil {
			return nil, err
		}

		permuted := make(map[int]*rlwe.Ciphertext, batch)
		for slot := 0; slot < batch; slot++ {
			permuted[int(utils.BitReverse64(uint64(slot), logSlots))] = extracted[coefficientIndex(limb, slot)]
		}

		repacked, err := packer.Repack(permuted)
		if err != nil {
			return nil, err
		}

		repacked.IsBatched = false
		repacked.LogDimensions = params.LogMaxDimensions()
		repacked.Scale = params.DefaultScale()

		real, imag, err := dftEval.CoeffsToSlotsNew(repacked, ctsMatrix)
		if err != nil {
			return nil, err
		}
		if imag != nil {
			// For the dense packing path used below, the input is purely real and the
			// imaginary component is expected to stay near zero. We keep the real part,
			// which carries the payload used by the radix computer.
		}
		real.IsBatched = true
		real.LogDimensions.Cols = ctsMatrix.LogSlots
		out[limb] = real
	}

	return out, nil
}

func extractAndRingPackPackedCoefficients(
	params ckks.Parameters,
	coeffCiphertext *rlwe.Ciphertext,
	limbCount, batch int,
	coefficientIndex func(limb, slot int) int,
	radix PackedRadixParams,
	packer *rlwe.RingPackingEvaluator,
) (*rlwe.Ciphertext, error) {
	idx := make(map[int]bool, limbCount*batch)
	for limb := 0; limb < limbCount; limb++ {
		for slot := 0; slot < batch; slot++ {
			coeffIdx := coefficientIndex(limb, slot)
			if coeffIdx < 0 || coeffIdx >= params.N() {
				return nil, fmt.Errorf("coefficient index %d for limb=%d slot=%d exceeds ring degree %d", coeffIdx, limb, slot, params.N())
			}
			idx[coeffIdx] = true
		}
	}

	extracted, err := packer.ExtractNaive(coeffCiphertext, idx)
	if err != nil {
		return nil, err
	}

	logSlots := params.LogMaxSlots()
	permuted := make(map[int]*rlwe.Ciphertext, limbCount*batch)
	for limb := 0; limb < limbCount; limb++ {
		for slot := 0; slot < batch; slot++ {
			targetSlot := limb*radix.batchStride + slot
			permuted[int(utils.BitReverse64(uint64(targetSlot), logSlots))] = extracted[coefficientIndex(limb, slot)]
		}
	}

	repacked, err := packer.Repack(permuted)
	if err != nil {
		return nil, err
	}

	repacked.IsBatched = false
	repacked.LogDimensions = params.LogMaxDimensions()
	repacked.Scale = params.DefaultScale()
	return repacked, nil
}

type PackedRadixParams struct {
	base        int
	digits      int
	sliceLength int
	logDigits   int
	batchStride int
}

func newPackedRadixParams(params ckks.Parameters, base, digits int) (PackedRadixParams, error) {
	if digits <= 0 || !isPowerOfTwo(digits) {
		return PackedRadixParams{}, fmt.Errorf("packed radix expects a power-of-two digit count, got %d", digits)
	}

	sliceLength := 2 * digits
	if params.MaxSlots()%sliceLength != 0 {
		return PackedRadixParams{}, fmt.Errorf("slice length %d must divide MaxSlots=%d", sliceLength, params.MaxSlots())
	}

	return PackedRadixParams{
		base:        base,
		digits:      digits,
		sliceLength: sliceLength,
		logDigits:   int(math.Log2(float64(digits))),
		batchStride: params.MaxSlots() / sliceLength,
	}, nil
}

type PackedRadixContext struct {
	params            *ckks.Parameters
	encoder           *ckks.Encoder
	eval              *ckks.Evaluator
	btp               *bootstrapping.Evaluator
	refreshBtp        *bootstrapping.Evaluator
	refreshCorrection float64
}

func minIntToSymbolInputLevel(cc PackedRadixContext) int {
	// IntToSymbol applies SlotsToCoeffs and then spends one level for the
	// scalar multiply/rescale before ModUp. Running it at exactly the
	// SlotsToCoeffs start level is therefore an invalid circuit input.
	return cc.btp.SlotsToCoeffsParameters.LevelQ + 1
}

func targetIntToSymbolInputLevel(cc PackedRadixContext) int {
	return cc.btp.SlotsToCoeffsParameters.LevelQ + 4
}

func twistedVec(vec []complex128, n int, N int) []complex128 {
	batch := N / n
	twisted := make([]complex128, N)
	for i := 0; i < n; i++ {
		for j := 0; j < batch; j++ {
			twisted[i*batch+j] = vec[j*n+i]
		}
	}
	return twisted
}

func invTwistedVec(vec []complex128, n int, N int) []complex128 {
	batch := N / n
	untwisted := make([]complex128, N)
	for i := 0; i < n; i++ {
		for j := 0; j < batch; j++ {
			untwisted[j*n+i] = vec[i*batch+j]
		}
	}
	return untwisted
}

func hermiteInterpolationExp2NegateSymbol(n int, deg int, base int) []complex128 {
	z := cmplx.Exp(2 * math.Pi * 1i / complex(float64(n), 0))

	A := make([][]complex128, 2*n)
	b := make([]complex128, 2*n)

	for i := 0; i < n; i++ {
		zi := cmplx.Pow(z, complex(float64(i), 0))

		A[i] = make([]complex128, 2*n)
		for j := 0; j < 2*n; j++ {
			A[i][j] = cmplx.Pow(zi, complex(float64(j), 0))
		}

		if i >= base {
			b[i] = complex(0, 1)
		} else if i == 0 {
			b[i] = complex(0.5, 0)
		} else {
			b[i] = 0
		}

		A[n+i] = make([]complex128, 2*n)
		for j := 1; j < 2*n; j++ {
			A[n+i][j] = complex(float64(j), 0) * cmplx.Pow(zi, complex(float64(j-1), 0))
		}
		b[n+i] = 0
	}

	list := solveLinearSystem(A, b)
	coeffs := make([]complex128, deg+1)
	for i := 0; i < 2*n; i++ {
		coeffs[i] = list[i]
	}
	for i := 2 * n; i <= deg; i++ {
		coeffs[i] = 0
	}
	return coeffs
}

func hermiteInterpolationExp2Symbol(n int, deg int, base int) []complex128 {
	z := cmplx.Exp(2 * math.Pi * 1i / complex(float64(n), 0))

	A := make([][]complex128, 2*n)
	b := make([]complex128, 2*n)

	for i := 0; i < n; i++ {
		zi := cmplx.Pow(z, complex(float64(i), 0))

		A[i] = make([]complex128, 2*n)
		for j := 0; j < 2*n; j++ {
			A[i][j] = cmplx.Pow(zi, complex(float64(j), 0))
		}

		if i >= base {
			b[i] = complex(0, 1)
		} else if i == base-1 {
			b[i] = complex(0.5, 0)
		} else {
			b[i] = 0
		}

		A[n+i] = make([]complex128, 2*n)
		for j := 1; j < 2*n; j++ {
			A[n+i][j] = complex(float64(j), 0) * cmplx.Pow(zi, complex(float64(j-1), 0))
		}
		b[n+i] = 0
	}

	list := solveLinearSystem(A, b)
	coeffs := make([]complex128, deg+1)
	for i := 0; i < 2*n; i++ {
		coeffs[i] = list[i]
	}
	for i := 2 * n; i <= deg; i++ {
		coeffs[i] = 0
	}
	return coeffs
}

func hermiteInterpolationSymbol2Symbol() []complex128 {
	z := cmplx.Exp(2 * math.Pi * 1i / complex(float64(32), 0))

	A := make([][]complex128, 4)
	b := make([]complex128, 4)

	for i := 0; i < 2; i++ {
		zi := cmplx.Pow(z, complex(float64(i), 0))

		A[i] = make([]complex128, 4)
		for j := 0; j < 4; j++ {
			A[i][j] = cmplx.Pow(zi, complex(float64(j), 0))
		}
		if i == 0 {
			b[i] = 0
		} else {
			b[i] = complex(0.5, 0)
		}

		A[2+i] = make([]complex128, 4)
		for j := 1; j < 4; j++ {
			A[2+i][j] = complex(float64(j), 0) * cmplx.Pow(zi, complex(float64(j-1), 0))
		}
		b[2+i] = 0
	}

	list := solveLinearSystem(A, b)
	coeffs := make([]complex128, 4)
	for i := 0; i < 4; i++ {
		coeffs[i] = list[i]
	}
	return coeffs
}

func hermiteInterpolationSymbol2SymbolImag() []complex128 {
	z := cmplx.Exp(2 * math.Pi * 1i / complex(float64(16), 0))

	A := make([][]complex128, 4)
	b := make([]complex128, 4)

	for i := 0; i < 2; i++ {
		zi := cmplx.Pow(z, complex(float64(i), 0))

		A[i] = make([]complex128, 4)
		for j := 0; j < 4; j++ {
			A[i][j] = cmplx.Pow(zi, complex(float64(j), 0))
		}
		if i == 0 {
			b[i] = 0
		} else {
			b[i] = complex(0, 1)
		}

		A[2+i] = make([]complex128, 4)
		for j := 1; j < 4; j++ {
			A[2+i][j] = complex(float64(j), 0) * cmplx.Pow(zi, complex(float64(j-1), 0))
		}
		b[2+i] = 0
	}

	list := solveLinearSystem(A, b)
	coeffs := make([]complex128, 4)
	for i := 0; i < 4; i++ {
		coeffs[i] = list[i]
	}
	return coeffs
}

func packRingPackedDigits(eval *ckks.Evaluator, digits []*rlwe.Ciphertext, radix PackedRadixParams) (*rlwe.Ciphertext, error) {
	if len(digits) == 0 {
		return nil, errors.New("cannot pack an empty digit list")
	}
	if len(digits) > radix.digits {
		return nil, fmt.Errorf("too many digits for packed radix: got %d want <= %d", len(digits), radix.digits)
	}

	acc := digits[0].CopyNew()
	for limb := 1; limb < len(digits); limb++ {
		shifted := digits[limb].CopyNew()
		if err := eval.Rotate(shifted, -limb*radix.batchStride, shifted); err != nil {
			return nil, err
		}
		if err := eval.Add(acc, shifted, acc); err != nil {
			return nil, err
		}
	}

	return acc, nil
}

func multiplyByScalarAndRescale(eval *ckks.Evaluator, ct *rlwe.Ciphertext, constant float64) error {
	if err := eval.Mul(ct, constant, ct); err != nil {
		return err
	}
	return eval.Rescale(ct, ct)
}

func multiplyByScalarAndSetScale(eval *ckks.Evaluator, ct *rlwe.Ciphertext, constant float64, scale rlwe.Scale) error {
	ratio := scale.Div(ct.Scale).Value
	ratio.Mul(&ratio, new(big.Float).SetFloat64(constant))
	if err := eval.Mul(ct, &ratio, ct); err != nil {
		return err
	}
	if err := eval.RescaleTo(ct, scale, ct); err != nil {
		return err
	}
	ct.Scale = scale
	return nil
}

func halfBootstrapRingPackedCoefficients(
	btp *bootstrapping.Evaluator,
	eval *ckks.Evaluator,
	ct *rlwe.Ciphertext,
	targetLevel int,
	maxMessage float64,
	logMessageRatio int,
	restoreCorrection float64,
) (*rlwe.Ciphertext, int, error) {
	work := ct.CopyNew()
	if *flagTraceLevels {
		fmt.Printf("packed levels: half-bootstrap coeff input=%d\n", work.Level())
	}
	if work.Level() > 1 {
		eval.DropLevel(work, work.Level()-1)
		if *flagTraceLevels {
			fmt.Printf("packed levels: dropped half-bootstrap input to level=%d\n", work.Level())
		}
	}
	if work.Level() != 0 && work.Level() != 1 {
		return nil, 0, fmt.Errorf("half-bootstrap expects ring-packed coefficient input at level 0 or 1, got level %d", work.Level())
	}

	if maxMessage <= 0 {
		return nil, 0, fmt.Errorf("invalid half-bootstrap max message bound %f", maxMessage)
	}
	if restoreCorrection <= 0 {
		return nil, 0, fmt.Errorf("invalid half-bootstrap restore correction %f", restoreCorrection)
	}

	messageRatio := math.Exp2(float64(logMessageRatio))
	valueAdjustment := float64(btp.BootstrappingParameters.Q()[0]) / (work.Scale.Float64() * maxMessage * messageRatio)
	if valueAdjustment <= 0 {
		return nil, 0, fmt.Errorf("invalid half-bootstrap value adjustment %f", valueAdjustment)
	}

	if work.Level() == 1 && math.Abs(valueAdjustment-1) > 1e-12 {
		if err := multiplyByScalarAndRescale(eval, work, valueAdjustment); err != nil {
			return nil, 0, err
		}
		if *flagTraceLevels {
			fmt.Printf("packed levels: after message-ratio adjustment=%d factor=%.8g\n", work.Level(), valueAdjustment)
		}
	} else if work.Level() == 0 && *flagTraceLevels {
		fmt.Printf("packed levels: message-ratio adjustment already applied before ring packing factor=%.8g\n", valueAdjustment)
	}
	if work.Level() != 0 {
		return nil, 0, fmt.Errorf("message-ratio adjustment should finish at level 0, got level %d", work.Level())
	}

	var err error
	if work, err = btp.ModUp(work); err != nil {
		return nil, 1, err
	}
	if *flagTraceLevels {
		fmt.Printf("packed levels: after half-bootstrap ModRaise=%d\n", work.Level())
	}

	realPart, _, err := btp.CoeffsToSlots(work)
	if err != nil {
		return nil, 1, err
	}
	if *flagTraceLevels {
		fmt.Printf("packed levels: after half-bootstrap CtS=%d mod1LevelQ=%d\n", realPart.Level(), btp.Mod1Parameters.LevelQ)
	}

	refreshed, err := btp.EvalMod(realPart)
	if err != nil {
		return nil, 1, err
	}
	if *flagTraceLevels {
		fmt.Printf("packed levels: after half-bootstrap EvalMod=%d\n", refreshed.Level())
	}

	inverseAdjustment := restoreCorrection / valueAdjustment
	if math.Abs(inverseAdjustment-1) > 1e-12 {
		if math.Abs(inverseAdjustment-math.Round(inverseAdjustment)) < 1e-12 {
			if err := eval.Mul(refreshed, int64(math.Round(inverseAdjustment)), refreshed); err != nil {
				return nil, 1, err
			}
		} else {
			if err := multiplyByScalarAndRescale(eval, refreshed, inverseAdjustment); err != nil {
				return nil, 1, err
			}
		}
		if *flagTraceLevels {
			fmt.Printf("packed levels: after restoring message scale=%d factor=%.8g\n", refreshed.Level(), inverseAdjustment)
		}
	}

	if refreshed.Level() < targetLevel {
		return nil, 1, fmt.Errorf("half-bootstrap output level %d is below REDC input level %d", refreshed.Level(), targetLevel)
	}
	if refreshed.Level() > targetLevel {
		eval.DropLevel(refreshed, refreshed.Level()-targetLevel)
	}
	refreshed.IsBatched = true
	return refreshed, 1, nil
}

func encryptPackedConstantDigits(
	params ckks.Parameters,
	encoder *ckks.Encoder,
	encryptor *rlwe.Encryptor,
	value *big.Int,
	level int,
	computer *REDCComputer,
	radix PackedRadixParams,
) (*rlwe.Ciphertext, error) {
	digits := computer.decomposeConst(value, radix.digits, 1)
	untwisted := make([]complex128, params.MaxSlots())
	for batch := 0; batch < radix.batchStride; batch++ {
		for limb := 0; limb < radix.digits; limb++ {
			untwisted[batch*radix.sliceLength+limb] = digits[limb][0]
		}
	}

	pt := ckks.NewPlaintext(params, level)
	if err := encoder.Encode(twistedVec(untwisted, radix.sliceLength, params.MaxSlots()), pt); err != nil {
		return nil, err
	}
	return encryptor.EncryptNew(pt)
}

func decodePackedDigits(params ckks.Parameters, ct *rlwe.Ciphertext, decryptor *rlwe.Decryptor, encoder *ckks.Encoder, radix PackedRadixParams, activeDigits int) [][]complex128 {
	values := decodeCiphertext(params, ct, decryptor, encoder)
	untwisted := invTwistedVec(values, radix.sliceLength, len(values))
	digits := make([][]complex128, activeDigits)
	for limb := 0; limb < activeDigits; limb++ {
		digits[limb] = make([]complex128, radix.batchStride)
		for batch := 0; batch < radix.batchStride; batch++ {
			digits[limb][batch] = untwisted[batch*radix.sliceLength+limb]
		}
	}
	return digits
}

func tracePackedDigits(tag string, ct *rlwe.Ciphertext, radix PackedRadixParams, activeDigits, count int) {
	if !*flagTraceDecomp || traceDecryptor == nil || traceEncoder == nil {
		return
	}
	if count > activeDigits {
		count = activeDigits
	}
	digits := decodePackedDigits(traceParams, ct, traceDecryptor, traceEncoder, radix, activeDigits)
	fmt.Printf("[trace] %s | level=%d log2(scale)=%.2f digits=", tag, ct.Level(), ct.Scale.Log2())
	for limb := 0; limb < count; limb++ {
		fmt.Printf(" %.6f", real(digits[limb][0]))
	}
	fmt.Println()
}

func countPackedGarbage(params ckks.Parameters, ct *rlwe.Ciphertext, decryptor *rlwe.Decryptor, encoder *ckks.Encoder, radix PackedRadixParams, activeBatch, activeDigits int) int {
	values := decodeCiphertext(params, ct, decryptor, encoder)
	untwisted := invTwistedVec(values, radix.sliceLength, len(values))
	count := 0
	for batch := 0; batch < radix.batchStride; batch++ {
		for idx := 0; idx < radix.sliceLength; idx++ {
			isActive := batch < activeBatch && idx < activeDigits
			if isActive {
				continue
			}
			if math.Round(real(untwisted[batch*radix.sliceLength+idx])) != 0 {
				count++
			}
		}
	}
	return count
}

func addPackedDigitConstant(params ckks.Parameters, eval *ckks.Evaluator, ct *rlwe.Ciphertext, radix PackedRadixParams, limbs []int, value float64) error {
	if value == 0 {
		return nil
	}
	values := make([]complex128, params.MaxSlots())
	for batch := 0; batch < radix.batchStride; batch++ {
		for _, limb := range limbs {
			if limb < 0 || limb >= radix.digits {
				return fmt.Errorf("packed digit constant limb %d outside [0, %d)", limb, radix.digits)
			}
			values[batch*radix.sliceLength+limb] += complex(value, 0)
		}
	}
	return eval.Add(ct, twistedVec(values, radix.sliceLength, params.MaxSlots()), ct)
}

func addPublicRedundantPStarOffset(params ckks.Parameters, eval *ckks.Evaluator, ct *rlwe.Ciphertext, radix PackedRadixParams, sourceLimbs int, offsetMultiplier int) error {
	if sourceLimbs <= 0 || 2*sourceLimbs > radix.digits {
		return fmt.Errorf("source limbs %d incompatible with packed digit count %d", sourceLimbs, radix.digits)
	}
	if offsetMultiplier <= 0 {
		return fmt.Errorf("redundant p* offset multiplier must be positive, got %d", offsetMultiplier)
	}

	// This is the public lazy offset from ConvGtD. For p=beta^D+1, the
	// redundant radix vector p*=(beta+1,beta-1,...,beta-1,0,...,0) has value p.
	// Adding A*p* makes the low digits nonnegative without carrying; REDC then
	// consumes the resulting bounded non-canonical radix vector.
	if err := addPackedDigitConstant(params, eval, ct, radix, []int{0}, float64(offsetMultiplier*(radix.base+1))); err != nil {
		return err
	}
	if sourceLimbs == 1 {
		return nil
	}
	limbs := make([]int, sourceLimbs-1)
	for limb := 1; limb < sourceLimbs; limb++ {
		limbs[limb-1] = limb
	}
	return addPackedDigitConstant(params, eval, ct, radix, limbs, float64(offsetMultiplier*(radix.base-1)))
}

func maskPackedDigitRange(params ckks.Parameters, eval *ckks.Evaluator, ct *rlwe.Ciphertext, radix PackedRadixParams, start, end int) (*rlwe.Ciphertext, error) {
	if start < 0 || end < start || end > radix.digits {
		return nil, fmt.Errorf("invalid packed digit mask range [%d, %d) for %d digits", start, end, radix.digits)
	}
	values := make([]complex128, params.MaxSlots())
	for batch := 0; batch < radix.batchStride; batch++ {
		for limb := start; limb < end; limb++ {
			values[batch*radix.sliceLength+limb] = 1
		}
	}
	out := ct.CopyNew()
	if err := eval.MulRelin(out, twistedVec(values, radix.sliceLength, params.MaxSlots()), out); err != nil {
		return nil, err
	}
	if err := eval.Rescale(out, out); err != nil {
		return nil, err
	}
	out.Scale = params.DefaultScale()
	return out, nil
}

func reducePackedFermatModulus(
	params ckks.Parameters,
	encoder *ckks.Encoder,
	encryptor *rlwe.Encryptor,
	computer *REDCComputer,
	ct *rlwe.Ciphertext,
	modulus *big.Int,
	sourceLimbs int,
	radix PackedRadixParams,
	cc PackedRadixContext,
) (*rlwe.Ciphertext, int, error) {
	if sourceLimbs <= 0 || 2*sourceLimbs > radix.digits {
		return nil, 0, fmt.Errorf("source limbs %d incompatible with packed digit count %d", sourceLimbs, radix.digits)
	}

	bootCount := 0
	work := ct.CopyNew()

	var used int
	var err error
	// First REDC step for p=beta^D+1: carry the non-canonical 2D-limb input
	// enough to expose the quotient in the upper D limbs. This is part of the
	// modular reduction, not part of the public A*p* digit addition.
	logSourceLimbs := int(math.Log2(float64(sourceLimbs)))
	work, used, err = applyLCtoCPackedWithLazyPassesAndCarryLog(computer, work, radix, cc, 2, logSourceLimbs, 3)
	if err != nil {
		return nil, bootCount + used, err
	}
	bootCount += used
	if *flagTraceLevels {
		fmt.Printf("packed levels: after REDC quotient carry=%d\n", work.Level())
	}
	tracePackedDigits("after REDC quotient carry", work, radix, 2*sourceLimbs, 8)

	low, err := maskPackedDigitRange(params, cc.eval, work, radix, 0, sourceLimbs)
	if err != nil {
		return nil, bootCount, err
	}
	high, err := maskPackedDigitRange(params, cc.eval, work, radix, sourceLimbs, 2*sourceLimbs)
	if err != nil {
		return nil, bootCount, err
	}
	if err := cc.eval.Rotate(high, sourceLimbs*radix.batchStride, high); err != nil {
		return nil, bootCount, err
	}

	folded, err := cc.eval.SubNew(low, high)
	if err != nil {
		return nil, bootCount, err
	}
	folded.Scale = params.DefaultScale()
	if *flagTraceLevels {
		fmt.Printf("packed levels: after beta^D=-1 fold=%d\n", folded.Level())
	}
	tracePackedDigits("after beta^D=-1 fold", folded, radix, 2*sourceLimbs, 8)

	_ = encoder
	_ = encryptor
	_ = modulus
	out, used, err := reduceSignedFermatFoldWithLCtoCNeg(params, folded, sourceLimbs, radix, cc)
	if err != nil {
		return nil, bootCount + used, err
	}
	bootCount += used
	if *flagTraceLevels {
		fmt.Printf("packed levels: after signed fold canonicalization=%d\n", out.Level())
	}

	return out, bootCount, nil
}

func intToSymbolNegate(base int, sliceLength int, ciphertext *rlwe.Ciphertext, cc PackedRadixContext) (*rlwe.Ciphertext, int, error) {
	params := cc.params
	eval := cc.eval
	btp := cc.btp

	var err error

	minLevel := minIntToSymbolInputLevel(cc)
	if ciphertext.Level() < minLevel {
		return nil, 0, fmt.Errorf("IntToSymbolNegate input level %d is below required level %d", ciphertext.Level(), minLevel)
	}

	targetLevel := targetIntToSymbolInputLevel(cc)
	if ciphertext.Level() > targetLevel {
		eval.DropLevel(ciphertext, ciphertext.Level()-targetLevel)
	}
	if *flagTraceLevels {
		fmt.Printf("packed levels: IntToSymbol input=%d target=%d\n", ciphertext.Level(), targetLevel)
	}
	if ciphertext, err = btp.SlotsToCoeffs(ciphertext, nil); err != nil {
		return nil, 1, err
	}
	if *flagTraceLevels {
		fmt.Printf("packed levels: IntToSymbol after StC=%d\n", ciphertext.Level())
	}

	scaleFactor := float64(base) / float64(2*base-1) * params.DefaultScale().Float64() / ciphertext.Scale.Float64()
	if err := eval.Mul(ciphertext, scaleFactor, ciphertext); err != nil {
		return nil, 1, err
	}
	if *flagTraceLevels {
		fmt.Printf("packed levels: IntToSymbol after mul=%d\n", ciphertext.Level())
	}
	if err := eval.Rescale(ciphertext, ciphertext); err != nil {
		return nil, 1, err
	}
	if ciphertext, err = btp.ModUp(ciphertext); err != nil {
		return nil, 1, err
	}

	realPart, imagPart, err := btp.CoeffsToSlots(ciphertext)
	if err != nil {
		return nil, 1, err
	}
	if *flagTraceLevels {
		fmt.Printf("packed levels: IntToSymbol after CtS real=%d imag=%d mod1LevelQ=%d\n", realPart.Level(), imagPart.Level(), btp.Mod1Parameters.LevelQ)
	}
	eval.Conjugate(realPart, imagPart)
	eval.Add(realPart, imagPart, realPart)

	if imagPart, err = btp.EvalModAndScale(realPart, 2*math.Pi/complex(float64(base), 0)); err != nil {
		return nil, 1, err
	}
	if realPart, err = btp.EvalElseAndScale(realPart, 2*math.Pi/complex(float64(base), 0)); err != nil {
		return nil, 1, err
	}
	if err = btp.Evaluator.Mul(imagPart, 1i, imagPart); err != nil {
		return nil, 1, err
	}
	if err = btp.Evaluator.Add(realPart, imagPart, ciphertext); err != nil {
		return nil, 1, err
	}

	polyEval := polynomial.NewEvaluator(*params, eval)
	poly := polynomial.NewPolynomial(bignum.NewPolynomial(0, hermiteInterpolationExp2NegateSymbol(2*base-1, 4*base-3, base), nil))

	ctOut, err := polyEval.Evaluate(ciphertext, poly, params.DefaultScale())
	if err != nil {
		return nil, 1, err
	}
	return ctOut, 1, nil
}

func intToSymbol(base int, sliceLength int, ciphertext *rlwe.Ciphertext, cc PackedRadixContext) (*rlwe.Ciphertext, int, error) {
	params := cc.params
	eval := cc.eval
	btp := cc.btp

	var err error

	minLevel := minIntToSymbolInputLevel(cc)
	if ciphertext.Level() < minLevel {
		return nil, 0, fmt.Errorf("IntToSymbol input level %d is below required level %d", ciphertext.Level(), minLevel)
	}

	targetLevel := targetIntToSymbolInputLevel(cc)
	if ciphertext.Level() > targetLevel {
		eval.DropLevel(ciphertext, ciphertext.Level()-targetLevel)
	}
	if ciphertext, err = btp.SlotsToCoeffs(ciphertext, nil); err != nil {
		return nil, 1, err
	}

	scaleFactor := float64(base) / float64(2*base-1) * params.DefaultScale().Float64() / ciphertext.Scale.Float64()
	if err := eval.Mul(ciphertext, scaleFactor, ciphertext); err != nil {
		return nil, 1, err
	}
	if err := eval.Rescale(ciphertext, ciphertext); err != nil {
		return nil, 1, err
	}
	if ciphertext, err = btp.ModUp(ciphertext); err != nil {
		return nil, 1, err
	}

	realPart, imagPart, err := btp.CoeffsToSlots(ciphertext)
	if err != nil {
		return nil, 1, err
	}
	eval.Conjugate(realPart, imagPart)
	eval.Add(realPart, imagPart, realPart)

	if imagPart, err = btp.EvalModAndScale(realPart, 2*math.Pi/complex(float64(base), 0)); err != nil {
		return nil, 1, err
	}
	if realPart, err = btp.EvalElseAndScale(realPart, 2*math.Pi/complex(float64(base), 0)); err != nil {
		return nil, 1, err
	}
	if err = btp.Evaluator.Mul(imagPart, 1i, imagPart); err != nil {
		return nil, 1, err
	}
	if err = btp.Evaluator.Add(realPart, imagPart, ciphertext); err != nil {
		return nil, 1, err
	}

	polyEval := polynomial.NewEvaluator(*params, eval)
	poly := polynomial.NewPolynomial(bignum.NewPolynomial(0, hermiteInterpolationExp2Symbol(2*base-1, 4*base-3, base), nil))

	ctOut, err := polyEval.Evaluate(ciphertext, poly, params.DefaultScale())
	if err != nil {
		return nil, 1, err
	}
	return ctOut, 1, nil
}

func cleaningSymbol(base int, sliceLength int, ctSymbol *rlwe.Ciphertext, cc PackedRadixContext) (*rlwe.Ciphertext, int, error) {
	params := cc.params
	eval := cc.eval
	btp := cc.btp

	var err error

	targetLevel := btp.SlotsToCoeffsParameters.LevelQ + 4
	if ctSymbol.Level() > targetLevel {
		eval.DropLevel(ctSymbol, ctSymbol.Level()-targetLevel)
	}
	if ctSymbol, err = btp.SlotsToCoeffs(ctSymbol, nil); err != nil {
		return nil, 1, err
	}
	if err = eval.SetScale(ctSymbol, rlwe.NewScale(float64(params.Q()[0])/float64(base))); err != nil {
		return nil, 1, err
	}
	if ctSymbol, err = btp.ModUp(ctSymbol); err != nil {
		return nil, 1, err
	}

	realPart, imagPart, err := btp.CoeffsToSlots(ctSymbol)
	if err != nil {
		return nil, 1, err
	}
	eval.Mul(realPart, 2.0, realPart)
	eval.Mul(imagPart, 2.0, imagPart)

	imagMod, err := btp.EvalModAndScale(imagPart, 2*math.Pi/complex(float64(base), 0))
	if err != nil {
		return nil, 1, err
	}
	imagElse, err := btp.EvalElseAndScale(imagPart, 2*math.Pi/complex(float64(base), 0))
	if err != nil {
		return nil, 1, err
	}
	realMod, err := btp.EvalModAndScale(realPart, 2*math.Pi/complex(float64(base), 0))
	if err != nil {
		return nil, 1, err
	}
	realElse, err := btp.EvalElseAndScale(realPart, 2*math.Pi/complex(float64(base), 0))
	if err != nil {
		return nil, 1, err
	}

	if err = btp.Evaluator.Mul(imagMod, 1i, imagMod); err != nil {
		return nil, 1, err
	}
	if err = btp.Evaluator.Add(imagElse, imagMod, imagElse); err != nil {
		return nil, 1, err
	}
	if err = btp.Evaluator.Mul(realMod, 1i, realMod); err != nil {
		return nil, 1, err
	}
	if err = btp.Evaluator.Add(realElse, realMod, realElse); err != nil {
		return nil, 1, err
	}

	polyEval := polynomial.NewEvaluator(*params, eval)
	polyReal := polynomial.NewPolynomial(bignum.NewPolynomial(0, hermiteInterpolationSymbol2Symbol(), nil))
	polyImag := polynomial.NewPolynomial(bignum.NewPolynomial(0, hermiteInterpolationSymbol2SymbolImag(), nil))

	if realElse, err = polyEval.Evaluate(realElse, polyReal, params.DefaultScale()); err != nil {
		return nil, 1, err
	}
	if imagElse, err = polyEval.Evaluate(imagElse, polyImag, params.DefaultScale()); err != nil {
		return nil, 1, err
	}
	if err = btp.Evaluator.Add(realElse, imagElse, ctSymbol); err != nil {
		return nil, 1, err
	}

	return ctSymbol, 1, nil
}

func applyLCtoCNegCarryPacked(base int, logSliceHalf int, sliceLength int, ctSymbol *rlwe.Ciphertext, ctCarry *rlwe.Ciphertext, cc PackedRadixContext) (*rlwe.Ciphertext, int, error) {
	params := cc.params
	eval := cc.eval
	bootCount := 0

	for i := 0; i < logSliceHalf; i++ {
		ctRot, err := eval.RotateNew(ctSymbol, -1*(1<<i)*(params.MaxSlots())/sliceLength)
		if err != nil {
			return nil, bootCount, err
		}

		temp := ctSymbol.CopyNew()
		eval.Conjugate(temp, temp)
		eval.Add(temp, ctSymbol, temp)

		temp2, err := eval.SubNew(ctRot, ctSymbol)
		if err != nil {
			return nil, bootCount, err
		}
		if err = eval.MulRelin(temp, temp2, temp); err != nil {
			return nil, bootCount, err
		}
		if err = eval.Rescale(temp, temp); err != nil {
			return nil, bootCount, err
		}
		eval.Add(temp, ctSymbol, ctSymbol)

		remainingCarryRounds := logSliceHalf - i - 1
		if ctSymbol.Level() < remainingCarryRounds+1 {
			ctSymbol, _, err = cleaningSymbol(base, sliceLength, ctSymbol, cc)
			if err != nil {
				return nil, bootCount, err
			}
			bootCount++
		}
	}

	if ctSymbol.Level() < 1 {
		var err error
		ctSymbol, _, err = cleaningSymbol(base, sliceLength, ctSymbol, cc)
		if err != nil {
			return nil, bootCount, err
		}
		bootCount++
	}

	temp := ctSymbol.CopyNew()
	eval.Conjugate(temp, temp)
	eval.Sub(temp, ctSymbol, temp)

	values := make([]complex128, params.MaxSlots())
	scaleFactor := params.DefaultScale().Float64() * 0.5 / ctSymbol.Scale.Float64()
	for i := 0; i < params.MaxSlots(); i++ {
		values[i] = complex(0, scaleFactor)
	}

	pt := ckks.NewPlaintext(*params, params.MaxLevel())
	pt.Scale = rlwe.NewScale(params.Q()[temp.Level()])
	if err := cc.encoder.Encode(values, pt); err != nil {
		return nil, bootCount, err
	}
	if err := eval.MulRelin(temp, pt, ctSymbol); err != nil {
		return nil, bootCount, err
	}
	if err := eval.Rescale(ctSymbol, ctSymbol); err != nil {
		return nil, bootCount, err
	}
	ctSymbol.Scale = params.DefaultScale()

	temp = ctSymbol.CopyNew()
	if err := eval.MulRelin(ctSymbol, base, temp); err != nil {
		return nil, bootCount, err
	}
	if err := eval.Add(ctCarry, temp, ctCarry); err != nil {
		return nil, bootCount, err
	}
	if err := eval.Rotate(ctSymbol, -1*params.MaxSlots()/sliceLength, ctSymbol); err != nil {
		return nil, bootCount, err
	}
	if err := eval.Sub(ctCarry, ctSymbol, ctCarry); err != nil {
		return nil, bootCount, err
	}

	return ctCarry, bootCount, nil
}

func applyLCtoCCarryPackedWithForcedClean(base int, logSliceHalf int, sliceLength int, ctSymbol *rlwe.Ciphertext, ctCarry *rlwe.Ciphertext, cc PackedRadixContext, forcedCleanInterval int) (*rlwe.Ciphertext, int, error) {
	params := cc.params
	eval := cc.eval
	bootCount := 0

	for i := 0; i < logSliceHalf; i++ {
		ctRot, err := eval.RotateNew(ctSymbol, -1*(1<<i)*(params.MaxSlots())/sliceLength)
		if err != nil {
			return nil, bootCount, err
		}

		temp := ctSymbol.CopyNew()
		eval.Conjugate(temp, temp)
		eval.Add(temp, ctSymbol, temp)

		temp2, err := eval.SubNew(ctRot, ctSymbol)
		if err != nil {
			return nil, bootCount, err
		}
		if err = eval.MulRelin(temp, temp2, temp); err != nil {
			return nil, bootCount, err
		}
		if err = eval.Rescale(temp, temp); err != nil {
			return nil, bootCount, err
		}
		eval.Add(temp, ctSymbol, ctSymbol)

		if forcedCleanInterval > 0 && (i+1)%forcedCleanInterval == 0 && i+1 < logSliceHalf {
			ctSymbol, _, err = cleaningSymbol(base, sliceLength, ctSymbol, cc)
			if err != nil {
				return nil, bootCount, err
			}
			bootCount++
		} else if ctSymbol.Level() <= 5 {
			ctSymbol, _, err = cleaningSymbol(base, sliceLength, ctSymbol, cc)
			if err != nil {
				return nil, bootCount, err
			}
			bootCount++
		}
	}

	if ctSymbol.Level() < 6 {
		var err error
		ctSymbol, _, err = cleaningSymbol(base, sliceLength, ctSymbol, cc)
		if err != nil {
			return nil, bootCount, err
		}
		bootCount++
	}

	temp := ctSymbol.CopyNew()
	eval.Conjugate(temp, temp)
	eval.Sub(temp, ctSymbol, temp)

	values := make([]complex128, params.MaxSlots())
	scaleFactor := params.DefaultScale().Float64() * 0.5 / ctSymbol.Scale.Float64()
	for i := 0; i < params.MaxSlots(); i++ {
		values[i] = complex(0, scaleFactor)
	}

	pt := ckks.NewPlaintext(*params, params.MaxLevel())
	pt.Scale = rlwe.NewScale(params.Q()[temp.Level()])
	if err := cc.encoder.Encode(values, pt); err != nil {
		return nil, bootCount, err
	}
	if err := eval.MulRelin(temp, pt, ctSymbol); err != nil {
		return nil, bootCount, err
	}
	if err := eval.Rescale(ctSymbol, ctSymbol); err != nil {
		return nil, bootCount, err
	}
	ctSymbol.Scale = params.DefaultScale()

	temp = ctSymbol.CopyNew()
	if err := eval.MulRelin(ctSymbol, base, temp); err != nil {
		return nil, bootCount, err
	}
	if err := eval.Sub(ctCarry, temp, ctCarry); err != nil {
		return nil, bootCount, err
	}
	if err := eval.Rotate(ctSymbol, -1*params.MaxSlots()/sliceLength, ctSymbol); err != nil {
		return nil, bootCount, err
	}
	if err := eval.Add(ctCarry, ctSymbol, ctCarry); err != nil {
		return nil, bootCount, err
	}

	return ctCarry, bootCount, nil
}

func applyLCtoCCarryPacked(base int, logSliceHalf int, sliceLength int, ctSymbol *rlwe.Ciphertext, ctCarry *rlwe.Ciphertext, cc PackedRadixContext) (*rlwe.Ciphertext, int, error) {
	return applyLCtoCCarryPackedWithForcedClean(base, logSliceHalf, sliceLength, ctSymbol, ctCarry, cc, 0)
}

func applyLCtoCNegPacked(diff *rlwe.Ciphertext, carryDigits, fillDigits int, radix PackedRadixParams, cc PackedRadixContext) (*rlwe.Ciphertext, *rlwe.Ciphertext, *rlwe.Ciphertext, int, error) {
	if carryDigits <= 0 || carryDigits > radix.digits {
		return nil, nil, nil, 0, fmt.Errorf("carry digit count %d outside [1, %d]", carryDigits, radix.digits)
	}
	if fillDigits <= 0 || fillDigits > radix.digits {
		return nil, nil, nil, 0, fmt.Errorf("fill digit count %d outside [1, %d]", fillDigits, radix.digits)
	}
	if !isPowerOfTwo(carryDigits) || !isPowerOfTwo(fillDigits) {
		return nil, nil, nil, 0, fmt.Errorf("carry and fill digit counts must be powers of two, got %d and %d", carryDigits, fillDigits)
	}
	base := radix.base
	sliceLength := radix.sliceLength
	logCarryDigits := int(math.Log2(float64(carryDigits)))
	logFillDigits := int(math.Log2(float64(fillDigits)))
	maxSlots := cc.params.MaxSlots()
	batch := maxSlots / sliceLength

	work := diff.CopyNew()
	if *flagTraceLevels {
		fmt.Printf("packed levels: sign input=%d\n", work.Level())
	}

	ctSymbol := work.CopyNew()
	ctCarry := work.CopyNew()

	ctSymbol, bootCount, err := intToSymbolNegate(base, sliceLength, ctSymbol, cc)
	if err != nil {
		return nil, nil, nil, bootCount, err
	}
	if *flagTraceLevels {
		fmt.Printf("packed levels: after sign IntToSymbolNegate=%d\n", ctSymbol.Level())
	}

	ctCarry, bootCarry, err := applyLCtoCNegCarryPacked(base, logCarryDigits, sliceLength, ctSymbol, ctCarry, cc)
	if err != nil {
		return nil, nil, nil, bootCount + bootCarry, err
	}
	bootCount += bootCarry
	if *flagTraceLevels {
		fmt.Printf("packed levels: after sign LazyCarryToCarryNegate=%d\n", ctCarry.Level())
	}

	masking := make([]complex128, maxSlots)
	for i := 0; i < batch; i++ {
		masking[i*sliceLength+carryDigits] = 1
	}
	twistedMask := twistedVec(masking, sliceLength, maxSlots)
	sign := ctCarry.CopyNew()
	if err := cc.eval.MulRelin(sign, twistedMask, sign); err != nil {
		return nil, nil, nil, bootCount, err
	}
	if err := cc.eval.Rescale(sign, sign); err != nil {
		return nil, nil, nil, bootCount, err
	}
	if err := cc.eval.Rotate(sign, carryDigits*batch, sign); err != nil {
		return nil, nil, nil, bootCount, err
	}
	if *flagTraceLevels {
		fmt.Printf("packed levels: after sign flag isolate=%d\n", sign.Level())
	}

	one := sign.CopyNew()
	for i := 0; i < logFillDigits; i++ {
		temp, err := cc.eval.RotateNew(one, -1*(1<<i)*batch)
		if err != nil {
			return nil, nil, nil, bootCount, err
		}
		if err := cc.eval.Add(one, temp, one); err != nil {
			return nil, nil, nil, bootCount, err
		}
	}

	return ctCarry, sign, one, bootCount, nil
}

func nonNegativeMaskFromLCtoCNegWithCarryDigits(diff *rlwe.Ciphertext, carryDigits, fillDigits int, radix PackedRadixParams, cc PackedRadixContext) (*rlwe.Ciphertext, int, error) {
	_, _, one, bootCount, err := applyLCtoCNegPacked(diff, carryDigits, fillDigits, radix, cc)
	return one, bootCount, err
}

func nonNegativeMaskFromLCtoCNeg(diff *rlwe.Ciphertext, radix PackedRadixParams, cc PackedRadixContext) (*rlwe.Ciphertext, int, error) {
	return nonNegativeMaskFromLCtoCNegWithCarryDigits(diff, radix.digits, radix.digits, radix, cc)
}

func refreshForIntToSymbol(ct *rlwe.Ciphertext, requiredLevel int, force bool, label string, cc PackedRadixContext) (*rlwe.Ciphertext, int, error) {
	if !force && ct.Level() >= requiredLevel {
		return ct, 0, nil
	}
	if cc.refreshBtp == nil {
		return nil, 0, fmt.Errorf("%s level %d is below required IntToSymbol input level %d and no refresh evaluator was provided", label, ct.Level(), requiredLevel)
	}
	scaleRelaxation := 1.0
	if ct.Level() == 0 && cc.refreshCorrection > 1 {
		ct.Scale = ct.Scale.Div(rlwe.NewScale(cc.refreshCorrection))
		scaleRelaxation = cc.refreshCorrection
	}
	if *flagTraceLevels {
		fmt.Printf("packed levels: refreshing %s from level=%d to required=%d\n", label, ct.Level(), requiredLevel)
	}
	refreshed, err := cc.refreshBtp.Bootstrap(ct)
	if err != nil {
		return nil, 1, err
	}
	if refreshed.Level() < requiredLevel {
		return nil, 1, fmt.Errorf("refreshed %s level %d is below required IntToSymbol input level %d", label, refreshed.Level(), requiredLevel)
	}
	effectiveCorrection := cc.refreshCorrection / scaleRelaxation
	if math.Abs(effectiveCorrection-1) > 1e-12 {
		if math.Abs(effectiveCorrection-math.Round(effectiveCorrection)) < 1e-12 {
			if err := cc.eval.Mul(refreshed, int64(math.Round(effectiveCorrection)), refreshed); err != nil {
				return nil, 1, err
			}
		} else {
			if err := multiplyByScalarAndRescale(cc.eval, refreshed, effectiveCorrection); err != nil {
				return nil, 1, err
			}
		}
	}
	if *flagTraceLevels {
		fmt.Printf("packed levels: refreshed %s=%d\n", label, refreshed.Level())
	}
	return refreshed, 1, nil
}

func reduceSignedFermatFoldWithLCtoCNeg(params ckks.Parameters, folded *rlwe.Ciphertext, sourceLimbs int, radix PackedRadixParams, cc PackedRadixContext) (*rlwe.Ciphertext, int, error) {
	signInput := folded.CopyNew()
	if err := addPackedDigitConstant(params, cc.eval, signInput, radix, []int{sourceLimbs}, 1); err != nil {
		return nil, 0, err
	}

	requiredLevel := minIntToSymbolInputLevel(cc)
	bootCount := 0
	var used int
	var err error
	signInput, used, err = refreshForIntToSymbol(signInput, requiredLevel, false, "signed Fermat sign input", cc)
	if err != nil {
		return nil, bootCount + used, err
	}
	bootCount += used

	carried, nonNegativeAtZero, _, used, err := applyLCtoCNegPacked(signInput, sourceLimbs, radix.digits, radix, cc)
	if err != nil {
		return nil, bootCount + used, err
	}
	bootCount += used
	tracePackedDigits("after signed Fermat LCtoCneg carry", carried, radix, 2*sourceLimbs, 8)
	tracePackedDigits("after signed Fermat nonnegative mask", nonNegativeAtZero, radix, 2*sourceLimbs, 8)

	// LCtoCneg returns folded mod B^D. If folded was negative, adding one to
	// limb 0 completes folded + (B^D + 1). The sign digit itself is cleared by
	// subtracting the extracted sign rotated back to limb D.
	negative := nonNegativeAtZero.CopyNew()
	if err := cc.eval.Mul(negative, -1, negative); err != nil {
		return nil, bootCount, err
	}
	if err := addPackedDigitConstant(params, cc.eval, negative, radix, []int{0}, 1); err != nil {
		return nil, bootCount, err
	}
	negative.Scale = params.DefaultScale()

	signAtD := nonNegativeAtZero.CopyNew()
	if err := cc.eval.Rotate(signAtD, -sourceLimbs*radix.batchStride, signAtD); err != nil {
		return nil, bootCount, err
	}

	adjusted := carried.CopyNew()
	if adjusted.Level() > signAtD.Level() {
		cc.eval.DropLevel(adjusted, adjusted.Level()-signAtD.Level())
	}
	if signAtD.Level() > adjusted.Level() {
		cc.eval.DropLevel(signAtD, signAtD.Level()-adjusted.Level())
	}
	if err := cc.eval.Sub(adjusted, signAtD, adjusted); err != nil {
		return nil, bootCount, err
	}
	if negative.Level() > adjusted.Level() {
		cc.eval.DropLevel(negative, negative.Level()-adjusted.Level())
	}
	if adjusted.Level() > negative.Level() {
		cc.eval.DropLevel(adjusted, adjusted.Level()-negative.Level())
	}
	if err := cc.eval.Add(adjusted, negative, adjusted); err != nil {
		return nil, bootCount, err
	}
	adjusted.Scale = params.DefaultScale()
	tracePackedDigits("after signed Fermat case adjustment", adjusted, radix, 2*sourceLimbs, 8)

	// The sign-dependent +1 can leave the special residue beta^D as a lazy
	// low-limb overflow, e.g. [beta, beta-1, ..., beta-1]. Propagate carries
	// only through the source-limb window so ConvGtD returns the clean CPL25
	// radix state rather than an equivalent lazy representative.
	//
	// This final carry is implemented by IntToSymbol followed by LCtoC. It is
	// both level- and precision-sensitive: the beta^D boundary is exactly where
	// a one-unit carry error changes the canonical representative. Refreshing
	// here makes the canonicalization robust on full packed ciphertexts.
	adjusted, used, err = refreshForIntToSymbol(adjusted, requiredLevel, true, "final Fermat carry input", cc)
	if err != nil {
		return nil, bootCount + used, err
	}
	bootCount += used
	tracePackedDigits("after final Fermat carry refresh", adjusted, radix, 2*sourceLimbs, 8)

	carrySymbol, bootSymbol, err := intToSymbol(radix.base, radix.sliceLength, adjusted.CopyNew(), cc)
	if err != nil {
		return nil, bootCount + bootSymbol, err
	}
	tracePackedDigits("final Fermat carry symbol", carrySymbol, radix, 2*sourceLimbs, 8)
	logSourceLimbs := int(math.Log2(float64(sourceLimbs)))
	adjusted, bootCarry, err := applyLCtoCCarryPacked(radix.base, logSourceLimbs, radix.sliceLength, carrySymbol, adjusted.CopyNew(), cc)
	if err != nil {
		return nil, bootCount + bootSymbol + bootCarry, err
	}
	bootCount += bootSymbol + bootCarry

	return adjusted, bootCount, nil
}

func conditionalSubPacked(computer *REDCComputer, lhs, rhs *rlwe.Ciphertext, radix PackedRadixParams, cc PackedRadixContext) (*rlwe.Ciphertext, int, error) {
	_ = computer
	diff, err := cc.eval.SubNew(lhs, rhs)
	if err != nil {
		return nil, 0, err
	}
	if *flagTraceLevels {
		fmt.Printf("packed levels: after sub=%d\n", diff.Level())
	}

	maxSlots := cc.params.MaxSlots()
	sliceLength := radix.sliceLength
	batch := maxSlots / sliceLength
	masking := make([]complex128, maxSlots)
	for i := 0; i < batch; i++ {
		masking[i*sliceLength+sliceLength/2] = 1
	}
	if err := cc.eval.Add(diff, twistedVec(masking, sliceLength, maxSlots), diff); err != nil {
		return nil, 0, err
	}

	diffCanonical, _, one, bootCount, err := applyLCtoCNegPacked(diff, radix.digits, radix.digits, radix, cc)
	if err != nil {
		return nil, bootCount, err
	}
	diffCanonical, bootClean, err := applyLCtoCPackedWithLazyPasses(computer, diffCanonical, radix, cc, 1)
	if err != nil {
		return nil, bootCount + bootClean, err
	}
	bootCount += bootClean
	if *flagTraceLevels {
		fmt.Printf("packed levels: after cleaned LCtoCneg diff=%d\n", diffCanonical.Level())
	}

	if err := cc.eval.MulRelin(diffCanonical, one, diffCanonical); err != nil {
		return nil, bootCount, err
	}
	if err := cc.eval.Rescale(diffCanonical, diffCanonical); err != nil {
		return nil, bootCount, err
	}
	if *flagTraceLevels {
		fmt.Printf("packed levels: after diff select=%d\n", diffCanonical.Level())
	}

	if err := cc.eval.Sub(one, 1, one); err != nil {
		return nil, bootCount, err
	}
	if err := cc.eval.Mul(one, -1, one); err != nil {
		return nil, bootCount, err
	}

	temp := lhs.CopyNew()
	if err := cc.eval.MulRelin(temp, one, temp); err != nil {
		return nil, bootCount, err
	}
	if err := cc.eval.Rescale(temp, temp); err != nil {
		return nil, bootCount, err
	}
	if *flagTraceLevels {
		fmt.Printf("packed levels: after base select=%d\n", temp.Level())
	}

	out, err := cc.eval.AddNew(diffCanonical, temp)
	return out, bootCount, err
}

func comparePackedGE(lhs, rhs *rlwe.Ciphertext, carryDigits int, radix PackedRadixParams, cc PackedRadixContext, refreshBtp *bootstrapping.Evaluator, refreshCorrection float64) (*rlwe.Ciphertext, int, error) {
	if carryDigits <= 0 || carryDigits > radix.digits || !isPowerOfTwo(carryDigits) {
		return nil, 0, fmt.Errorf("invalid packed comparison carry digit count %d for radix digits %d", carryDigits, radix.digits)
	}
	diff, err := cc.eval.SubNew(lhs, rhs)
	if err != nil {
		return nil, 0, err
	}
	if *flagTraceLevels {
		fmt.Printf("packed levels: comparison diff=%d\n", diff.Level())
	}
	tracePackedDigits("comparison diff before optional refresh", diff, radix, radix.digits, 8)

	bootCount := 0
	minLevel := cc.btp.SlotsToCoeffsParameters.LevelQ
	if diff.Level() < minLevel {
		if refreshBtp == nil {
			return nil, bootCount, fmt.Errorf("comparison diff level %d is below SlotsToCoeffs start level %d and no refresh evaluator was provided", diff.Level(), minLevel)
		}
		scaleRelaxation := 1.0
		if diff.Level() == 0 && refreshCorrection > 1 {
			// Level-0 bootstrapping has a stricter q/scale precondition because it
			// cannot spend an input prime for scale matching. Lowering only the
			// metadata scale lets the bootstrap accept the ciphertext; the inverse
			// factor is folded into the post-refresh correction below.
			diff.Scale = diff.Scale.Div(rlwe.NewScale(refreshCorrection))
			scaleRelaxation = refreshCorrection
		}
		if *flagTraceLevels {
			fmt.Printf("packed levels: refreshing comparison diff from level=%d to at least=%d\n", diff.Level(), minLevel)
		}
		diff, err = refreshBtp.Bootstrap(diff)
		bootCount++
		if err != nil {
			return nil, bootCount, err
		}
		if diff.Level() < minLevel {
			return nil, bootCount, fmt.Errorf("refreshed comparison diff level %d is below SlotsToCoeffs start level %d", diff.Level(), minLevel)
		}
		effectiveCorrection := refreshCorrection / scaleRelaxation
		if math.Abs(effectiveCorrection-1) > 1e-12 {
			if math.Abs(effectiveCorrection-math.Round(effectiveCorrection)) < 1e-12 {
				if err := cc.eval.Mul(diff, int64(math.Round(effectiveCorrection)), diff); err != nil {
					return nil, bootCount, err
				}
			} else {
				if err := multiplyByScalarAndRescale(cc.eval, diff, effectiveCorrection); err != nil {
					return nil, bootCount, err
				}
			}
		}
		if *flagTraceLevels {
			fmt.Printf("packed levels: refreshed comparison diff=%d\n", diff.Level())
		}
		tracePackedDigits("comparison diff after refresh", diff, radix, radix.digits, 8)
	}

	maxSlots := cc.params.MaxSlots()
	sliceLength := radix.sliceLength
	batch := maxSlots / sliceLength
	padding := make([]complex128, maxSlots)
	for i := 0; i < batch; i++ {
		padding[i*sliceLength+carryDigits] = 1
	}
	if err := cc.eval.Add(diff, twistedVec(padding, sliceLength, maxSlots), diff); err != nil {
		return nil, 0, err
	}

	// nonNegativeMaskFromLCtoCNeg returns a packed 0/1 mask. Limb zero carries
	// the comparison bit for each packed message, and the value is replicated
	// across the active radix positions for convenient use in select circuits.
	mask, used, err := nonNegativeMaskFromLCtoCNegWithCarryDigits(diff, carryDigits, radix.digits, radix, cc)
	return mask, bootCount + used, err
}

func reducePackedByRepeatedSub(ct, modulus *rlwe.Ciphertext, rounds int, radix PackedRadixParams, cc PackedRadixContext) (*rlwe.Ciphertext, int, error) {
	out := ct.CopyNew()
	bootCount := 0
	for i := 0; i < rounds; i++ {
		next, used, err := conditionalSubPacked(nil, out, modulus, radix, cc)
		if err != nil {
			return nil, bootCount + used, err
		}
		out = next
		bootCount += used
	}
	return out, bootCount, nil
}

func applyLCPacked(computer *REDCComputer, ct *rlwe.Ciphertext, radix PackedRadixParams, cc PackedRadixContext) (*rlwe.Ciphertext, int, error) {
	_ = computer
	params := cc.params
	eval := cc.eval
	btp := cc.btp
	bootCount := 1

	temp := ct.CopyNew()
	work := ct.CopyNew()

	if work.Level() > btp.SlotsToCoeffsParameters.LevelQ {
		eval.DropLevel(work, work.Level()-btp.SlotsToCoeffsParameters.LevelQ)
	}

	var err error
	if work, err = btp.SlotsToCoeffs(work, nil); err != nil {
		return nil, bootCount, err
	}
	if err = eval.SetScale(work, rlwe.NewScale(float64(params.Q()[0])/float64(radix.base))); err != nil {
		return nil, bootCount, err
	}
	if work, err = btp.ModUp(work); err != nil {
		return nil, bootCount, err
	}

	realPart, imagPart, err := btp.CoeffsToSlots(work)
	if err != nil {
		return nil, bootCount, err
	}
	eval.Conjugate(realPart, imagPart)
	eval.Add(realPart, imagPart, realPart)

	if imagPart, err = btp.EvalModAndScale(realPart, 2*math.Pi/complex(float64(radix.base), 0)); err != nil {
		return nil, bootCount, err
	}
	if realPart, err = btp.EvalElseAndScale(realPart, 2*math.Pi/complex(float64(radix.base), 0)); err != nil {
		return nil, bootCount, err
	}
	if err = btp.Evaluator.Mul(imagPart, 1i, imagPart); err != nil {
		return nil, bootCount, err
	}
	if err = btp.Evaluator.Add(realPart, imagPart, work); err != nil {
		return nil, bootCount, err
	}

	polyEval := polynomial.NewEvaluator(*params, eval)
	poly := polynomial.NewPolynomial(bignum.NewPolynomial(0, HermiteInterpolation(radix.base, 2*radix.base-1), nil))

	ctMod, err := polyEval.Evaluate(work, poly, temp.Scale)
	if err != nil {
		return nil, bootCount, err
	}

	ctQ, err := eval.SubNew(temp, ctMod)
	if err != nil {
		return nil, bootCount, err
	}
	if err := eval.Rotate(ctQ, -radix.batchStride, ctQ); err != nil {
		return nil, bootCount, err
	}

	mask := make([]complex128, params.MaxSlots())
	scaleFactor := 1.0 / float64(radix.base) * params.DefaultScale().Float64() / ctQ.Scale.Float64()
	for batch := 0; batch < radix.batchStride; batch++ {
		for j := 1; j < radix.sliceLength/2; j++ {
			mask[batch*radix.sliceLength+j] = complex(scaleFactor, 0)
		}
	}

	pt := ckks.NewPlaintext(*params, params.MaxLevel())
	pt.Scale = rlwe.NewScale(params.Q()[ctQ.Level()])
	if err := cc.encoder.Encode(twistedVec(mask, radix.sliceLength, params.MaxSlots()), pt); err != nil {
		return nil, bootCount, err
	}
	if err := eval.MulRelin(ctQ, pt, ctQ); err != nil {
		return nil, bootCount, err
	}
	if err := eval.Rescale(ctQ, ctQ); err != nil {
		return nil, bootCount, err
	}
	ctQ.Scale = params.DefaultScale()

	eval.SetScale(ctMod, params.DefaultScale())
	out, err := eval.AddNew(ctMod, ctQ)
	return out, bootCount, err
}

func applyLCtoCPackedWithLazyPassesAndCarryLog(computer *REDCComputer, ct *rlwe.Ciphertext, radix PackedRadixParams, cc PackedRadixContext, maxLazyCarryPasses, carryLog, forcedCarryCleanAfter int) (*rlwe.Ciphertext, int, error) {
	if *flagTraceLevels {
		fmt.Printf("packed levels: LCtoC input=%d\n", ct.Level())
	}
	carried := ct.CopyNew()
	bootTotal := 0

	// The number of lazy-carry passes is part of the selected circuit. Do not
	// silently reduce it based on the available level: doing so evaluates a
	// different normalization circuit and can hide precision bugs.
	requiredLevel := targetIntToSymbolInputLevel(cc) + maxLazyCarryPasses
	if carried.Level() < requiredLevel {
		var used int
		var err error
		carried, used, err = refreshForIntToSymbol(carried, requiredLevel, false, fmt.Sprintf("LCtoC input before %d lazy carry passes", maxLazyCarryPasses), cc)
		bootTotal += used
		if err != nil {
			return nil, bootTotal, err
		}
	}
	for i := 0; i < maxLazyCarryPasses; i++ {
		var bootLC int
		var err error
		carried, bootLC, err = applyLCPacked(computer, carried, radix, cc)
		if err != nil {
			return nil, bootTotal + bootLC, err
		}
		bootTotal += bootLC
		if *flagTraceLevels {
			fmt.Printf("packed levels: after LC%d=%d\n", i+1, carried.Level())
		}
		tracePackedDigits(fmt.Sprintf("after LC%d", i+1), carried, radix, radix.digits, 8)
	}
	ctSymbol, bootSymbol, err := intToSymbol(radix.base, radix.sliceLength, carried.CopyNew(), cc)
	if err != nil {
		return nil, bootTotal + bootSymbol, err
	}
	if *flagTraceLevels {
		fmt.Printf("packed levels: after LCtoC IntToSymbol=%d\n", ctSymbol.Level())
	}
	tracePackedDigits("after LCtoC IntToSymbol", ctSymbol, radix, radix.digits, 8)

	out, bootCarry, err := applyLCtoCCarryPackedWithForcedClean(radix.base, carryLog, radix.sliceLength, ctSymbol, carried.CopyNew(), cc, forcedCarryCleanAfter)
	if err != nil {
		return nil, bootTotal + bootSymbol + bootCarry, err
	}
	tracePackedDigits("after LCtoC carry propagation", out, radix, radix.digits, 8)

	return out, bootTotal + bootSymbol + bootCarry, nil
}

func applyLCtoCPackedWithLazyPasses(computer *REDCComputer, ct *rlwe.Ciphertext, radix PackedRadixParams, cc PackedRadixContext, maxLazyCarryPasses int) (*rlwe.Ciphertext, int, error) {
	return applyLCtoCPackedWithLazyPassesAndCarryLog(computer, ct, radix, cc, maxLazyCarryPasses, radix.logDigits, 0)
}

func applyLCtoCPacked(computer *REDCComputer, ct *rlwe.Ciphertext, radix PackedRadixParams, cc PackedRadixContext) (*rlwe.Ciphertext, int, error) {
	return applyLCtoCPackedWithLazyPasses(computer, ct, radix, cc, 4)
}

func exactSlotMetrics(decodedLimbs [][]complex128, wantDigits [][]complex128, wantValues []*big.Int, limbBits int) (exact int, maxAbsErr *big.Int, maxNoise, meanNoise float64) {
	exact, _, maxNoise, meanNoise = exactDigitMetrics(decodedLimbs, wantDigits)
	_, maxAbsErr = canonicalIntegerMetrics(decodedLimbs, wantValues, limbBits)
	return
}

func canonicalIntegerMetrics(decodedLimbs [][]complex128, want []*big.Int, limbBits int) (exact int, maxAbsErr *big.Int) {
	exact = 0
	maxAbsErr = new(big.Int)
	tmp := new(big.Int)

	for slot := range want {
		got, ok := reconstructCanonicalSlotValue(decodedLimbs, slot, limbBits)
		if ok && got.Cmp(want[slot]) == 0 {
			exact++
			continue
		}
		if ok {
			tmp.Sub(got, want[slot])
			tmp.Abs(tmp)
		} else {
			tmp.SetInt64(1)
		}
		if tmp.Cmp(maxAbsErr) > 0 {
			maxAbsErr.Set(tmp)
		}
	}

	return exact, maxAbsErr
}

func exactDigitMetrics(decodedLimbs, wantDigits [][]complex128) (exact int, maxRoundedErr int64, maxNoise, meanNoise float64) {
	maxNoise, meanNoise = digitNoiseMetrics(decodedLimbs, wantDigits)
	if len(wantDigits) == 0 {
		return 0, 0, maxNoise, meanNoise
	}

	slots := len(wantDigits[0])
	for slot := 0; slot < slots; slot++ {
		slotExact := true
		for limb := range wantDigits {
			got := int64(math.Round(real(decodedLimbs[limb][slot])))
			want := int64(math.Round(real(wantDigits[limb][slot])))
			diff := got - want
			if diff < 0 {
				diff = -diff
			}
			if diff != 0 {
				slotExact = false
			}
			if diff > maxRoundedErr {
				maxRoundedErr = diff
			}
		}
		if slotExact {
			exact++
		}
	}

	return exact, maxRoundedErr, maxNoise, meanNoise
}

func trimDecodedLimbs(decodedLimbs [][]complex128, slots int) [][]complex128 {
	out := make([][]complex128, len(decodedLimbs))
	for i := range decodedLimbs {
		out[i] = decodedLimbs[i][:slots]
	}
	return out
}

func countNonZeroOutsideSupport(decodedLimbs [][]complex128, activeSlots int) int {
	count := 0
	for _, limb := range decodedLimbs {
		for i := activeSlots; i < len(limb); i++ {
			if math.Round(real(limb[i])) != 0 {
				count++
			}
		}
	}
	return count
}

func decodeCiphertext(params ckks.Parameters, ciphertext *rlwe.Ciphertext, decryptor *rlwe.Decryptor, encoder *ckks.Encoder) []complex128 {
	slots := ciphertext.Slots()
	if !ciphertext.IsBatched {
		slots *= 2
	}

	values := make([]complex128, slots)
	if err := encoder.Decode(decryptor.DecryptNew(ciphertext), values); err != nil {
		panic(err)
	}

	return values
}

func reconstructSlotValue(decodedLimbs [][]complex128, slot int, limbBits int) *big.Int {
	acc := new(big.Int)
	baseShift := uint(limbBits)
	for limb := len(decodedLimbs) - 1; limb >= 0; limb-- {
		acc.Lsh(acc, baseShift)
		digit := int64(math.Round(real(decodedLimbs[limb][slot])))
		acc.Add(acc, big.NewInt(digit))
	}
	return acc
}

func reconstructCanonicalSlotValue(decodedLimbs [][]complex128, slot int, limbBits int) (*big.Int, bool) {
	acc := new(big.Int)
	baseShift := uint(limbBits)
	base := int64(1 << limbBits)
	for limb := len(decodedLimbs) - 1; limb >= 0; limb-- {
		acc.Lsh(acc, baseShift)
		digit := int64(math.Round(real(decodedLimbs[limb][slot])))
		if digit < 0 || digit >= base {
			return acc, false
		}
		acc.Add(acc, big.NewInt(digit))
	}
	return acc, true
}

func integerMetrics(decodedLimbs [][]complex128, want []*big.Int, limbBits int) (exact int, maxAbsErr *big.Int) {
	exact = 0
	maxAbsErr = new(big.Int)
	tmp := new(big.Int)

	for slot := range want {
		got := reconstructSlotValue(decodedLimbs, slot, limbBits)
		if got.Cmp(want[slot]) == 0 {
			exact++
			continue
		}

		tmp.Sub(got, want[slot])
		tmp.Abs(tmp)
		if tmp.Cmp(maxAbsErr) > 0 {
			maxAbsErr.Set(tmp)
		}
	}

	return exact, maxAbsErr
}

func compareGEBits(lhs, rhs []*big.Int) []*big.Int {
	if len(lhs) != len(rhs) {
		panic(fmt.Sprintf("mismatched comparison lengths: lhs=%d rhs=%d", len(lhs), len(rhs)))
	}
	out := make([]*big.Int, len(lhs))
	for i := range lhs {
		if lhs[i].Cmp(rhs[i]) >= 0 {
			out[i] = big.NewInt(1)
		} else {
			out[i] = big.NewInt(0)
		}
	}
	return out
}

func digitNoiseMetrics(decodedLimbs, wantDigits [][]complex128) (maxErr, meanErr float64) {
	count := 0
	for limb := range wantDigits {
		for slot := range wantDigits[limb] {
			err := math.Abs(real(decodedLimbs[limb][slot]) - real(wantDigits[limb][slot]))
			meanErr += err
			if err > maxErr {
				maxErr = err
			}
			count++
		}
	}
	if count > 0 {
		meanErr /= float64(count)
	}
	return
}

func minLevel(cts []*rlwe.Ciphertext) int {
	if len(cts) == 0 {
		return -1
	}
	minLvl := cts[0].Level()
	for _, ct := range cts[1:] {
		if ct.Level() < minLvl {
			minLvl = ct.Level()
		}
	}
	return minLvl
}

func repeatInt(value, count int) []int {
	out := make([]int, count)
	for i := range out {
		out[i] = value
	}
	return out
}

func main() {
	flag.Parse()
	if *flagBaseBits <= 0 || *flagBaseBits >= 31 {
		panic("base-bits must be in [1, 30]")
	}
	if *flagGBFVDigits <= 0 {
		panic("gbfv-digits must be positive")
	}
	limbBits := *flagBaseBits
	sourceLimbs := *flagGBFVDigits
	if *flagGBFVEll > 0 {
		if *flagGBFVEll%limbBits != 0 {
			panic(fmt.Sprintf("gbfv-ell=%d must be divisible by base-bits=%d", *flagGBFVEll, limbBits))
		}
		sourceLimbs = *flagGBFVEll / limbBits
	}
	if sourceLimbs <= 0 {
		panic("GBFV digit capacity D must be positive")
	}
	if !isPowerOfTwo(sourceLimbs) {
		panic(fmt.Sprintf("GBFV digit capacity D=%d must be a power of two for the packed CPL25 layout", sourceLimbs))
	}
	base := 1 << limbBits

	densityNum, densityDen, err := parseDensityFraction(*flagGBFVDensity)
	if err != nil {
		panic(err)
	}
	packMode := strings.ToLower(*flagGBFVPackMode)
	switch packMode {
	case "direct", "coeffs-to-slots", "c2s":
		panic("direct coefficient packing is disabled: CoeffsToSlots exposes coefficients in bit-reversed order and the level-preserving slot masks needed to untwist it are not numerically reliable; use -gbfv-pack-mode ring")
	case "ring", "legacy", "extract-repack":
		packMode = "ring"
	default:
		panic(fmt.Sprintf("unsupported gbfv-pack-mode %q: use ring", *flagGBFVPackMode))
	}

	LogN := 16
	if *flagShort {
		LogN -= 4
	}

	packedDigitLog := int(math.Log2(float64(2 * sourceLimbs)))
	circuitPrimeCount := packedDigitLog + 3
	const logQPBudget = 1548
	const minDefaultScale = 38
	maxCircuitPrimeCountAtMinScale := (logQPBudget-68)/minDefaultScale - 27
	if circuitPrimeCount > maxCircuitPrimeCountAtMinScale {
		circuitPrimeCount = maxCircuitPrimeCountAtMinScale
	}
	if sourceLimbs >= 256 && circuitPrimeCount > packedDigitLog {
		circuitPrimeCount = packedDigitLog
	}
	LogDefaultScale := (logQPBudget - 68) / (27 + circuitPrimeCount)
	if LogDefaultScale < minDefaultScale {
		panic(fmt.Sprintf("selected D=%d needs %d circuit primes, leaving only %d-bit scale under logQP budget", sourceLimbs, circuitPrimeCount, LogDefaultScale))
	}
	largePrimeBits := LogDefaultScale + 4
	q0 := []int{largePrimeBits, LogDefaultScale}
	qiSlotsToCoeffs := repeatInt(LogDefaultScale, 3)
	qiCircuitSlots := repeatInt(LogDefaultScale, circuitPrimeCount)
	qiLookUpTable := repeatInt(LogDefaultScale, 6)
	qiEvalMod := repeatInt(largePrimeBits, 8)
	qiCoeffsToSlots := repeatInt(largePrimeBits, 3)
	logP := repeatInt(largePrimeBits, 5)
	coeffsLevels := []int{1, 1, 1}
	slotsLevels := []int{1, 1, 1}

	LogQ := append(q0, qiSlotsToCoeffs...)
	LogQ = append(LogQ, qiCircuitSlots...)
	Lv := len(LogQ)
	redcInputLevel := Lv - 1
	ringPackInputLevel := 0
	ringPackKeyLevelQ := ringPackInputLevel
	ringPackKeyLevelP := 0
	gbfvInputLevel := 0
	modRaiseTargetLevel := ringPackInputLevel + 1
	LogQ = append(LogQ, qiLookUpTable...)
	LogQ = append(LogQ, qiEvalMod...)
	LogQ = append(LogQ, qiCoeffsToSlots...)

	params, err := ckks.NewParametersFromLiteral(ckks.ParametersLiteral{
		LogN:            LogN,
		LogQ:            LogQ,
		LogP:            logP,
		LogDefaultScale: LogDefaultScale,
		Xs:              ring.Ternary{H: 192},
	})
	if err != nil {
		panic(err)
	}
	ringPackMinLogN, err := resolveRingPackMinLogN(params, *flagGBFVRingPackMinLogN, ringPackKeyLevelQ, ringPackKeyLevelP, *flagAllowInsecureRingSwitch)
	if err != nil {
		panic(err)
	}
	ringPackKeyLogQP := ringPackingKeyLogQP(params, ringPackKeyLevelQ, ringPackKeyLevelP)
	ringPackKeyLogQ := ringPackingKeyLogQ(params, ringPackKeyLevelQ)
	if err := checkSecurityAssumptions(params, *flagShort, ringPackMinLogN, ringPackKeyLogQP, *flagAllowInsecureRingSwitch); err != nil {
		panic(err)
	}

	coeffsToSlots := dft.MatrixLiteral{
		Type:         dft.HomomorphicEncode,
		Format:       dft.RepackImagAsReal,
		LogSlots:     params.LogMaxSlots(),
		LevelQ:       params.MaxLevelQ(),
		LevelP:       params.MaxLevelP(),
		LogBSGSRatio: 1,
		Scaling:      new(big.Float).SetFloat64(0.5),
		Levels:       coeffsLevels,
	}

	mod1Params := mod1.ParametersLiteral{
		LevelQ:          params.MaxLevel() - coeffsToSlots.Depth(true),
		LogScale:        largePrimeBits,
		Mod1Type:        mod1.CosDiscrete,
		Mod1Degree:      31,
		DoubleAngle:     3,
		K:               16,
		LogMessageRatio: 4,
		Mod1InvDegree:   0,
	}

	slotsToCoeffs := dft.MatrixLiteral{
		Type:         dft.HomomorphicDecode,
		LogSlots:     params.LogMaxSlots(),
		LogBSGSRatio: 1,
		LevelP:       params.MaxLevelP(),
		Levels:       slotsLevels,
	}
	slotsToCoeffs.LevelQ = len(slotsToCoeffs.Levels) + 1
	refreshOutputLevel := redcInputLevel + 1
	refreshSlotsToCoeffs := slotsToCoeffs
	refreshSlotsToCoeffs.LevelQ = refreshOutputLevel

	refreshLogMessageRatio := 6
	ordinaryRefreshMod1Params := mod1Params
	ordinaryRefreshMod1Params.Mod1Type = mod1.SinContinuous
	ordinaryRefreshMod1Params.Mod1Degree = 127
	ordinaryRefreshMod1Params.DoubleAngle = 0
	ordinaryRefreshMod1Params.LogMessageRatio = refreshLogMessageRatio
	ordinaryRefreshMod1Params.Mod1InvDegree = 7
	ordinaryRefreshMod1Params.LevelQ = refreshOutputLevel + ordinaryRefreshMod1Params.Depth()

	refreshCoeffsToSlots := coeffsToSlots
	refreshCoeffsToSlots.LevelQ = ordinaryRefreshMod1Params.LevelQ + len(refreshCoeffsToSlots.Levels)
	refreshCoeffsToSlots.Scaling = nil

	btpParams := bootstrapping.Parameters{
		ResidualParameters:      params,
		BootstrappingParameters: params,
		SlotsToCoeffsParameters: slotsToCoeffs,
		Mod1ParametersLiteral:   mod1Params,
		CoeffsToSlotsParameters: coeffsToSlots,
		EphemeralSecretWeight:   32,
		CircuitOrder:            bootstrapping.DecodeThenModUp,
	}
	refreshBtpParams := btpParams
	refreshBtpParams.SlotsToCoeffsParameters = refreshSlotsToCoeffs
	refreshBtpParams.CoeffsToSlotsParameters = refreshCoeffsToSlots
	refreshBtpParams.Mod1ParametersLiteral = ordinaryRefreshMod1Params
	refreshBtpParams.CircuitOrder = bootstrapping.ModUpThenEncode

	fmt.Printf("Bootstrapping parameters: logN=%d, logSlots=%d, H(%d; %d), sigma=%f, logQP=%f, levels=%d, scale=2^%d\n",
		btpParams.BootstrappingParameters.LogN(),
		btpParams.BootstrappingParameters.LogMaxSlots(),
		btpParams.BootstrappingParameters.XsHammingWeight(),
		btpParams.EphemeralSecretWeight,
		btpParams.BootstrappingParameters.Xe(),
		btpParams.BootstrappingParameters.LogQP(),
		btpParams.BootstrappingParameters.QCount(),
		btpParams.BootstrappingParameters.LogDefaultScale())
	if ringPackMinLogN < params.LogN() {
		fmt.Printf("Ring packing parameters: ring-switching enabled, maxLogN=%d, minLogN=%d, keyLevelQ=%d, keyLevelP=%d, activeKeyLogQ=%.2f, keyLogQP=%.2f\n",
			params.LogN(), ringPackMinLogN, ringPackKeyLevelQ, ringPackKeyLevelP, ringPackKeyLogQ, ringPackKeyLogQP)
	} else {
		fmt.Printf("Ring packing parameters: ring-switching disabled, maxLogN=minLogN=%d, keyLevelQ=%d, keyLevelP=%d, activeKeyLogQ=%.2f, keyLogQP=%.2f\n",
			params.LogN(), ringPackKeyLevelQ, ringPackKeyLevelP, ringPackKeyLogQ, ringPackKeyLogQP)
	}

	kgen := rlwe.NewKeyGenerator(params)
	sk, pk := kgen.GenKeyPairNew()

	encoder := ckks.NewEncoder(params)
	decryptor := rlwe.NewDecryptor(params, sk)
	encryptor := rlwe.NewEncryptor(params, pk)
	traceParams = params
	traceDecryptor = decryptor
	traceEncoder = encoder

	fmt.Println()
	fmt.Println("Generating bootstrapping evaluation keys...")
	evk, _, err := btpParams.GenEvaluationKeys(sk)
	if err != nil {
		panic(err)
	}
	fmt.Println("Done")
	fmt.Println("Generating ring-pack refresh bootstrapping evaluation keys...")
	refreshEvk, _, err := refreshBtpParams.GenEvaluationKeys(sk)
	if err != nil {
		panic(err)
	}
	fmt.Println("Done")

	eval, err := bootstrapping.NewEvaluator(btpParams, evk)
	if err != nil {
		panic(err)
	}
	refreshEval, err := bootstrapping.NewEvaluator(refreshBtpParams, refreshEvk)
	if err != nil {
		panic(err)
	}

	offsetMultiplier := *flagOffsetMultiplier
	if offsetMultiplier <= 0 && *flagLegacyRepresentativeShift > 0 {
		offsetMultiplier = *flagLegacyRepresentativeShift
	}
	if offsetMultiplier <= 0 {
		exposedDigitBoundK := base
		offsetMultiplier = (base*exposedDigitBoundK + (base - 2)) / (base - 1)
	}
	if params.N()%sourceLimbs != 0 {
		panic(fmt.Sprintf("GBFV digit capacity D=%d must divide ring degree N=%d", sourceLimbs, params.N()))
	}
	fullMessages := params.N() / sourceLimbs
	gbfv, err := newGBFVPlaintextLayout(params, int64(base), fullMessages)
	if err != nil {
		panic(err)
	}
	if gbfv.digitCount != sourceLimbs {
		panic(fmt.Sprintf("GBFV layout mismatch: D=%d but N/k=%d", sourceLimbs, gbfv.digitCount))
	}

	cpl25Limbs := 2 * sourceLimbs
	if 2*cpl25Limbs > params.MaxSlots() {
		panic(fmt.Sprintf("GBFV D=%d needs CPL25 container with %d radix digits, but MaxSlots=%d only supports %d packed digits",
			sourceLimbs, cpl25Limbs, params.MaxSlots(), params.MaxSlots()/2))
	}

	computer, err := NewREDCComputer(params, eval, evk, params.MaxSlots(), limbBits, cpl25Limbs*limbBits)
	if err != nil {
		panic(err)
	}
	packedRadix, err := newPackedRadixParams(params, int(computer.mods), computer.limbCount)
	if err != nil {
		panic(err)
	}
	if sourceLimbs <= 0 || sourceLimbs > computer.limbCount {
		panic(fmt.Sprintf("invalid source limb count %d for CPL25 digit length %d", sourceLimbs, computer.limbCount))
	}
	batch := packedRadix.batchStride
	fullOutputCount := fullMessages / batch
	if fullOutputCount <= 0 || fullOutputCount*batch != fullMessages {
		panic(fmt.Sprintf("CPL25 tuple layout mismatch: fullMessages=%d, batch=%d", fullMessages, batch))
	}
	outputCount := (fullOutputCount*densityNum + densityDen - 1) / densityDen
	if outputCount <= 0 {
		outputCount = 1
	}
	totalMessages := outputCount * batch
	if totalMessages > fullMessages {
		panic(fmt.Sprintf("sparse GBFV layout requested %d messages but full layout only supports %d", totalMessages, fullMessages))
	}
	extraRotations := make([]int, 0, packedRadix.digits+packedRadix.logDigits+1)
	for limb := 1; limb < packedRadix.digits; limb++ {
		extraRotations = append(extraRotations, -limb*packedRadix.batchStride)
	}
	for i := 0; i < packedRadix.logDigits; i++ {
		extraRotations = append(extraRotations, -(1<<i)*packedRadix.batchStride)
	}
	extraRotations = append(extraRotations, sourceLimbs*packedRadix.batchStride)
	extraRotations = append(extraRotations, params.MaxSlots()/2)

	extraGalEls := make([]uint64, len(extraRotations))
	for i, rot := range extraRotations {
		extraGalEls[i] = params.GaloisElementForRotation(rot)
	}
	rlk, err := evk.GetRelinearizationKey()
	if err != nil {
		panic(err)
	}
	packedKeySet := rlwe.NewMemEvaluationKeySet(rlk)
	for _, galEl := range evk.GetGaloisKeysList() {
		gk, err := evk.GetGaloisKey(galEl)
		if err != nil {
			panic(err)
		}
		packedKeySet.GaloisKeys[galEl] = gk
	}
	for _, gk := range kgen.GenGaloisKeysNew(extraGalEls, sk) {
		packedKeySet.GaloisKeys[gk.GaloisElement] = gk
	}
	packedEvaluator := ckks.NewEvaluator(params, packedKeySet)
	refreshCorrection := math.Exp2(float64(refreshLogMessageRatio - mod1Params.LogMessageRatio))
	packedContext := PackedRadixContext{
		params:            &params,
		encoder:           encoder,
		eval:              packedEvaluator,
		btp:               eval,
		refreshBtp:        refreshEval,
		refreshCorrection: refreshCorrection,
	}

	ringPacker, err := newRingPackingEvaluator(params, sk, ringPackMinLogN, ringPackKeyLevelQ, ringPackKeyLevelP)
	if err != nil {
		panic(err)
	}

	fmt.Printf("Running GBFV-to-CPL25 ConvGtD with beta=%d, D=N/k=%d, k=%d, q_GBFV=beta^D+1=%s, q0=%d, density=%d/%d\n",
		computer.mods, gbfv.digitCount, gbfv.slots, gbfv.plaintextModulus.String(), gbfv.q, densityNum, densityDen)
	fmt.Printf("CPL25 container digits=%d (%d source digits + %d zero headroom), outputs=%d/%d, batch/output=%d\n",
		computer.limbCount, sourceLimbs, computer.limbCount-sourceLimbs, outputCount, fullOutputCount, batch)
	fmt.Printf("GBFV input is q0-scaled coefficient plaintext at level %d, ModRaised to level %d, multiplied by t(X), scale-adjusted, packed with mode=%s, offset by A*p* with A=%d, and reduced modulo p\n",
		gbfvInputLevel, modRaiseTargetLevel, packMode, offsetMultiplier)
	restoreCorrection := 1.0

	conversionMessageBound := float64(computer.mods * computer.mods)

	convertMessages := func(label string, messages []*big.Int) (packed []*rlwe.Ciphertext, refreshCounts, redcCounts []int, elapsed time.Duration, err error) {
		gbfvMessages := make([]*big.Int, gbfv.slots)
		for i := range gbfvMessages {
			gbfvMessages[i] = new(big.Int)
		}
		for i, message := range messages {
			gbfvMessages[i].Set(message)
		}

		gbfvValues, err := gbfvCoefficientValues(params, gbfv, gbfvMessages)
		if err != nil {
			return nil, nil, nil, 0, err
		}
		ctGBFV, err := encryptGBFVInputCiphertext(params, encryptor, gbfvValues, gbfvInputLevel, gbfv)
		if err != nil {
			return nil, nil, nil, 0, err
		}
		traceCoeffsCiphertext(label+" GBFV input coefficients", ctGBFV, 8)
		ctRaised, err := modRaiseCentered(params, ctGBFV, modRaiseTargetLevel)
		if err != nil {
			return nil, nil, nil, 0, err
		}
		traceCoeffsCiphertext(label+" ModRaised GBFV input coefficients", ctRaised, 8)
		ctPrime, err := multiplyByTPolynomial(params, packedEvaluator, ctRaised, gbfv)
		if err != nil {
			return nil, nil, nil, 0, err
		}
		traceCoeffsCiphertext(label+" post-t(X)*ct coefficients", ctPrime, 8)
		messageRatio := math.Exp2(float64(refreshLogMessageRatio))
		preRingPackAdjustment := float64(params.Q()[0]) / (params.DefaultScale().Float64() * conversionMessageBound * messageRatio)
		if err := multiplyByScalarAndSetScale(packedEvaluator, ctPrime, preRingPackAdjustment, params.DefaultScale()); err != nil {
			return nil, nil, nil, 0, err
		}
		if ctPrime.Level() != ringPackInputLevel {
			return nil, nil, nil, 0, fmt.Errorf("scale-adjusted %s t(X) output level %d does not match expected ring-pack level %d", label, ctPrime.Level(), ringPackInputLevel)
		}
		if *flagTraceLevels {
			fmt.Printf("packed levels: pre-ring-pack message-ratio adjustment=%d factor=%.8g\n", ctPrime.Level(), preRingPackAdjustment)
		}
		traceCoeffsCiphertext(label+" scale-adjusted t(X)*ct coefficients", ctPrime, 8)

		start := time.Now()
		packed = make([]*rlwe.Ciphertext, outputCount)
		refreshCounts = make([]int, outputCount)
		redcCounts = make([]int, outputCount)
		var ringPackTime, refreshTime, offsetTime, redcTime time.Duration

		for out := 0; out < outputCount; out++ {
			baseSlot := out * batch
			coefficientIndex := func(limb, slot int) int {
				return limb*gbfv.slots + baseSlot + slot
			}
			var bootRefresh int
			stepStart := time.Now()
			packedCoeffs, err := extractAndRingPackPackedCoefficients(params, ctPrime, sourceLimbs, batch, coefficientIndex, packedRadix, ringPacker)
			ringPackTime += time.Since(stepStart)
			if err != nil {
				return nil, nil, nil, 0, err
			}
			stepStart = time.Now()
			packed[out], bootRefresh, err = halfBootstrapRingPackedCoefficients(
				refreshEval,
				packedEvaluator,
				packedCoeffs,
				redcInputLevel,
				conversionMessageBound,
				refreshLogMessageRatio,
				restoreCorrection,
			)
			refreshTime += time.Since(stepStart)
			if err != nil {
				return nil, nil, nil, 0, err
			}
			if packed[out].Level() < redcInputLevel {
				return nil, nil, nil, 0, fmt.Errorf("ring-pack half-bootstrap output level %d is below REDC input level %d", packed[out].Level(), redcInputLevel)
			}
			if packed[out].Level() > redcInputLevel {
				packedEvaluator.DropLevel(packed[out], packed[out].Level()-redcInputLevel)
			}
			if out == 0 {
				tracePackedDigits(label+" after ring-pack half-bootstrap", packed[out], packedRadix, computer.limbCount, 8)
			}

			stepStart = time.Now()
			if err := addPublicRedundantPStarOffset(params, packedEvaluator, packed[out], packedRadix, sourceLimbs, offsetMultiplier); err != nil {
				return nil, nil, nil, 0, err
			}
			offsetTime += time.Since(stepStart)
			if *flagTraceLevels {
				fmt.Printf("packed levels: %s after public A*p* digit offset=%d\n", label, packed[out].Level())
			}
			if out == 0 {
				tracePackedDigits(label+" after public A*p* digit offset", packed[out], packedRadix, computer.limbCount, 8)
			}

			var bootReduce int
			stepStart = time.Now()
			packed[out], bootReduce, err = reducePackedFermatModulus(
				params,
				encoder,
				encryptor,
				computer,
				packed[out],
				gbfv.plaintextModulus,
				sourceLimbs,
				packedRadix,
				packedContext,
			)
			redcTime += time.Since(stepStart)
			if err != nil {
				return nil, nil, nil, 0, err
			}
			if out == 0 {
				tracePackedDigits(label+" after A*p*-offset modular reduction", packed[out], packedRadix, computer.limbCount, 8)
			}
			refreshCounts[out] = bootRefresh
			redcCounts[out] = bootReduce
		}
		elapsed = time.Since(start)
		fmt.Printf("%s ConvGtD timing breakdown: ring-pack/extract=%s, refresh=%s, public offset=%s, REDC=%s, measured total=%s\n",
			label, ringPackTime, refreshTime, offsetTime, redcTime, elapsed)
		return packed, refreshCounts, redcCounts, elapsed, nil
	}

	numIter := *flagNumIter
	if numIter <= 0 {
		panic(fmt.Sprintf("num-iter must be positive, got %d", numIter))
	}
	operation := strings.ToLower(*flagOperation)
	switch operation {
	case "compare", "comparison", "internal-compare", "packed-compare", "cpl25-comparison":
		operation = "cpl25-compare"
	case "gbfv-comparison", "end-to-end-compare", "end-to-end-comparison":
		operation = "gbfv-compare"
	}
	switch operation {
	case "all", "conversion", "cpl25-compare", "gbfv-compare":
	default:
		panic(fmt.Sprintf("unsupported operation %q: use all, conversion, cpl25-compare, or gbfv-compare", *flagOperation))
	}
	fmt.Println("Selected operation:", operation)
	totalOperationTime := time.Duration(0)

	for iter := 0; iter < numIter; iter++ {
		if numIter > 1 {
			fmt.Printf("Iteration %d/%d\n", iter+1, numIter)
		}

		leftMessages, err := sampleGBFVMessages(gbfv, totalMessages)
		if err != nil {
			panic(err)
		}
		var rightMessages []*big.Int
		if operation == "all" || operation == "cpl25-compare" || operation == "gbfv-compare" {
			rightMessages, err = sampleGBFVMessages(gbfv, totalMessages)
			if err != nil {
				panic(err)
			}
		}

		var start time.Time
		if operation == "all" || operation == "conversion" || operation == "gbfv-compare" {
			start = time.Now()
		}
		leftPacked, leftRefreshCounts, leftREDCCounts, leftTime, err := convertMessages("lhs", leftMessages)
		if err != nil {
			panic(err)
		}
		if operation == "conversion" {
			totalOperationTime += leftTime
			fmt.Printf("ConvGtD conversion time: %s\n", leftTime)
		}

		var rightPacked []*rlwe.Ciphertext
		var rightRefreshCounts, rightREDCCounts []int
		rightTime := time.Duration(0)
		if operation == "all" || operation == "cpl25-compare" || operation == "gbfv-compare" {
			rightPacked, rightRefreshCounts, rightREDCCounts, rightTime, err = convertMessages("rhs", rightMessages)
			if err != nil {
				panic(err)
			}
		}

		var comparePacked []*rlwe.Ciphertext
		compareCounts := make([]int, outputCount)
		compareTime := time.Duration(0)
		if operation == "cpl25-compare" {
			start = time.Now()
		}
		if operation == "all" || operation == "cpl25-compare" || operation == "gbfv-compare" {
			comparePacked = make([]*rlwe.Ciphertext, outputCount)
			compareStart := time.Now()
			for out := 0; out < outputCount; out++ {
				comparePacked[out], compareCounts[out], err = comparePackedGE(leftPacked[out], rightPacked[out], sourceLimbs, packedRadix, packedContext, refreshEval, refreshCorrection)
				if err != nil {
					panic(err)
				}
			}
			compareTime = time.Since(compareStart)
			if operation == "cpl25-compare" {
				elapsed := time.Since(start)
				totalOperationTime += elapsed
				fmt.Printf("CPL25 compare time: %s\n", elapsed)
			}
		}
		if operation == "all" || operation == "gbfv-compare" {
			elapsed := time.Since(start)
			totalOperationTime += elapsed
			fmt.Printf("End-to-end GBFV comparison time: %s (lhs ConvGtD=%s, rhs ConvGtD=%s, CPL25 compare=%s)\n", elapsed, leftTime, rightTime, compareTime)
		}

		totalLeftBootCount := 0
		totalRightBootCount := 0
		totalCompareBootCount := 0
		maxRefreshCount := 0
		maxREDCCount := 0
		maxCompareCount := 0
		for _, count := range leftRefreshCounts {
			if count > maxRefreshCount {
				maxRefreshCount = count
			}
		}
		if rightRefreshCounts != nil {
			for _, count := range rightRefreshCounts {
				if count > maxRefreshCount {
					maxRefreshCount = count
				}
			}
		}
		for _, count := range leftREDCCounts {
			if count > maxREDCCount {
				maxREDCCount = count
			}
		}
		if rightREDCCounts != nil {
			for _, count := range rightREDCCounts {
				if count > maxREDCCount {
					maxREDCCount = count
				}
			}
		}
		for i := 0; i < outputCount; i++ {
			left := leftRefreshCounts[i] + leftREDCCounts[i]
			totalLeftBootCount += left
			if rightRefreshCounts != nil {
				right := rightRefreshCounts[i] + rightREDCCounts[i]
				totalRightBootCount += right
			}
			if comparePacked != nil {
				totalCompareBootCount += compareCounts[i]
				if compareCounts[i] > maxCompareCount {
					maxCompareCount = compareCounts[i]
				}
			}
		}
		if operation == "conversion" {
			fmt.Printf("Number of bootstrappings per packed output: ConvGtD=%d\n", maxRefreshCount+maxREDCCount)
			fmt.Printf("Total sequential evaluator calls: ConvGtD=%d\n", totalLeftBootCount)
		} else if operation == "cpl25-compare" {
			fmt.Printf("Number of bootstrappings per packed output: CPL25 compare=%d\n", maxCompareCount)
			fmt.Printf("Total sequential evaluator calls: CPL25 compare=%d\n", totalCompareBootCount)
		} else {
			fmt.Printf("Number of bootstrappings per packed output: lhs ConvGtD=%d, rhs ConvGtD=%d, CPL25 compare=%d, total=%d\n",
				maxRefreshCount+maxREDCCount, maxRefreshCount+maxREDCCount, maxCompareCount, 2*(maxRefreshCount+maxREDCCount)+maxCompareCount)
			fmt.Printf("Total sequential evaluator calls: lhs ConvGtD=%d, rhs ConvGtD=%d, CPL25 compare=%d, total=%d\n",
				totalLeftBootCount, totalRightBootCount, totalCompareBootCount, totalLeftBootCount+totalRightBootCount+totalCompareBootCount)
		}
		if operation != "cpl25-compare" {
			fmt.Printf("ConvGtD bootstrapping breakdown per packed output: ring-pack refresh=%d, public A*p* digit offset=0, REDC=%d\n", maxRefreshCount, maxREDCCount)
		}
		fmt.Printf("Packed CPL25 slice_length=%d, batch_stride=%d, tuple_outputs=%d\n", packedRadix.sliceLength, packedRadix.batchStride, outputCount)

		exactLeftCanonical := 0
		exactRightCanonical := 0
		exactComparison := 0
		maxCanonicalErr := new(big.Int)
		maxCompareErr := new(big.Int)
		maxCanonicalNoise := 0.0
		weightedCanonicalNoise := 0.0
		maxCompareNoise := 0.0
		weightedCompareNoise := 0.0
		garbageOutsideConverted := 0
		metricWeight := float64(2 * totalMessages * computer.limbCount)

		var firstLeftDecoded [][]complex128
		var firstRightDecoded [][]complex128
		var firstCompareDecoded [][]complex128
		var firstLeftWantDigits [][]complex128
		var firstRightWantDigits [][]complex128
		var firstCompareWant []*big.Int

		for out := 0; out < outputCount; out++ {
			startSlot := out * batch
			leftWantValues := leftMessages[startSlot : startSlot+batch]
			leftWantDigits := computer.decomposeBig(leftWantValues, computer.limbCount)
			leftDecoded := decodePackedDigits(params, leftPacked[out], decryptor, encoder, packedRadix, computer.limbCount)

			groupLeftExact, groupLeftMaxErr, groupLeftMaxNoise, groupLeftMeanNoise := exactSlotMetrics(leftDecoded, leftWantDigits, leftWantValues, limbBits)

			exactLeftCanonical += groupLeftExact
			if groupLeftMaxErr.Cmp(maxCanonicalErr) > 0 {
				maxCanonicalErr.Set(groupLeftMaxErr)
			}
			if groupLeftMaxNoise > maxCanonicalNoise {
				maxCanonicalNoise = groupLeftMaxNoise
			}
			weightedCanonicalNoise += groupLeftMeanNoise * float64(batch*computer.limbCount)
			garbageOutsideConverted += countPackedGarbage(params, leftPacked[out], decryptor, encoder, packedRadix, batch, computer.limbCount)

			if out == 0 {
				firstLeftDecoded = leftDecoded
				firstLeftWantDigits = leftWantDigits
			}

			if rightPacked != nil {
				rightWantValues := rightMessages[startSlot : startSlot+batch]
				rightWantDigits := computer.decomposeBig(rightWantValues, computer.limbCount)
				rightDecoded := decodePackedDigits(params, rightPacked[out], decryptor, encoder, packedRadix, computer.limbCount)
				groupRightExact, groupRightMaxErr, groupRightMaxNoise, groupRightMeanNoise := exactSlotMetrics(rightDecoded, rightWantDigits, rightWantValues, limbBits)
				exactRightCanonical += groupRightExact
				if groupRightMaxErr.Cmp(maxCanonicalErr) > 0 {
					maxCanonicalErr.Set(groupRightMaxErr)
				}
				if groupRightMaxNoise > maxCanonicalNoise {
					maxCanonicalNoise = groupRightMaxNoise
				}
				weightedCanonicalNoise += groupRightMeanNoise * float64(batch*computer.limbCount)
				garbageOutsideConverted += countPackedGarbage(params, rightPacked[out], decryptor, encoder, packedRadix, batch, computer.limbCount)
				if out == 0 {
					firstRightDecoded = rightDecoded
					firstRightWantDigits = rightWantDigits
				}
			}

			if comparePacked != nil {
				rightWantValues := rightMessages[startSlot : startSlot+batch]
				compareWantValues := compareGEBits(leftWantValues, rightWantValues)
				compareWantDigits := computer.decomposeBig(compareWantValues, 1)
				compareDecoded := decodePackedDigits(params, comparePacked[out], decryptor, encoder, packedRadix, 1)
				groupCompareExact, groupCompareMaxErr := integerMetrics(compareDecoded, compareWantValues, 1)
				groupCompareMaxNoise, groupCompareMeanNoise := digitNoiseMetrics(compareDecoded, compareWantDigits)
				exactComparison += groupCompareExact
				if groupCompareMaxErr.Cmp(maxCompareErr) > 0 {
					maxCompareErr.Set(groupCompareMaxErr)
				}
				if groupCompareMaxNoise > maxCompareNoise {
					maxCompareNoise = groupCompareMaxNoise
				}
				weightedCompareNoise += groupCompareMeanNoise * float64(batch)
				if out == 0 {
					firstCompareDecoded = compareDecoded
					firstCompareWant = compareWantValues
				}
			}
		}
		if rightPacked == nil {
			metricWeight = float64(totalMessages * computer.limbCount)
		}
		meanCanonicalNoise := weightedCanonicalNoise / metricWeight
		meanCompareNoise := weightedCompareNoise / float64(totalMessages)

		if *flagShort {
			for limb := 0; limb < minInt(computer.limbCount, 4); limb++ {
				fmt.Printf("sample lhs CPL25 limb %d: got=%0.4f want=%0.4f\n", limb, real(firstLeftDecoded[limb][0]), real(firstLeftWantDigits[limb][0]))
				if firstRightDecoded != nil {
					fmt.Printf("sample rhs CPL25 limb %d: got=%0.4f want=%0.4f\n", limb, real(firstRightDecoded[limb][0]), real(firstRightWantDigits[limb][0]))
				}
			}
			if firstCompareDecoded != nil {
				fmt.Printf("sample comparison lhs>=rhs: got=%0.4f want=%s (lhs=%s rhs=%s)\n",
					real(firstCompareDecoded[0][0]), firstCompareWant[0].String(), leftMessages[0].String(), rightMessages[0].String())
			}
			for out := 0; out < outputCount; out++ {
				startSlot := out * batch
				leftDecoded := decodePackedDigits(params, leftPacked[out], decryptor, encoder, packedRadix, computer.limbCount)
				leftWantDigits := computer.decomposeBig(leftMessages[startSlot:startSlot+batch], computer.limbCount)
				var rightDecoded [][]complex128
				var rightWantDigits [][]complex128
				if rightPacked != nil {
					rightDecoded = decodePackedDigits(params, rightPacked[out], decryptor, encoder, packedRadix, computer.limbCount)
					rightWantDigits = computer.decomposeBig(rightMessages[startSlot:startSlot+batch], computer.limbCount)
				}
				var compareDecoded [][]complex128
				var compareWant []*big.Int
				if comparePacked != nil {
					compareDecoded = decodePackedDigits(params, comparePacked[out], decryptor, encoder, packedRadix, 1)
					compareWant = compareGEBits(leftMessages[startSlot:startSlot+batch], rightMessages[startSlot:startSlot+batch])
				}
				for slot := 0; slot < batch; slot++ {
					for limb := 0; limb < computer.limbCount; limb++ {
						got := int64(math.Round(real(leftDecoded[limb][slot])))
						want := int64(math.Round(real(leftWantDigits[limb][slot])))
						if got != want {
							fmt.Printf("lhs mismatch output %d slot %d limb %d got=%d want=%d\n", out, slot, limb, got, want)
							break
						}
						if rightDecoded != nil {
							got = int64(math.Round(real(rightDecoded[limb][slot])))
							want = int64(math.Round(real(rightWantDigits[limb][slot])))
							if got != want {
								fmt.Printf("rhs mismatch output %d slot %d limb %d got=%d want=%d\n", out, slot, limb, got, want)
								break
							}
						}
					}
					if compareDecoded != nil {
						gotCompare := int64(math.Round(real(compareDecoded[0][slot])))
						wantCompare := compareWant[slot].Int64()
						if gotCompare != wantCompare {
							fmt.Printf("comparison mismatch output %d slot %d got=%d want=%d\n", out, slot, gotCompare, wantCompare)
						}
					}
				}
			}
		}

		fmt.Printf("Exact lhs canonical CPL25 digits after A*p*-offset modular reduction: %d/%d\n", exactLeftCanonical, totalMessages)
		if rightPacked != nil {
			fmt.Printf("Exact rhs canonical CPL25 digits after A*p*-offset modular reduction: %d/%d\n", exactRightCanonical, totalMessages)
		}
		if comparePacked != nil {
			fmt.Printf("Exact packed GBFV comparison bits lhs>=rhs: %d/%d, max comparison error=%s\n", exactComparison, totalMessages, maxCompareErr.String())
		}
		fmt.Printf("Max conversion integer error=%s\n", maxCanonicalErr.String())
		fmt.Printf("Nonzero rounded conversion digits outside active CPL25 support: %d\n", garbageOutsideConverted)
		if maxCanonicalNoise > 0 {
			fmt.Println("Max canonical digit noise in Log 2:", math.Log2(maxCanonicalNoise))
			fmt.Println("Mean canonical digit noise in Log 2:", math.Log2(meanCanonicalNoise))
		}
		if maxCompareNoise > 0 {
			fmt.Println("Max comparison-bit noise in Log 2:", math.Log2(maxCompareNoise))
			fmt.Println("Mean comparison-bit noise in Log 2:", math.Log2(meanCompareNoise))
		}
		if exactLeftCanonical != totalMessages || (rightPacked != nil && exactRightCanonical != totalMessages) {
			panic("GBFV-to-CPL25 conversion check failed")
		}
		if comparePacked != nil && exactComparison != totalMessages {
			panic("GBFV comparison check failed")
		}
	}

	averageOperationTime := totalOperationTime / time.Duration(numIter)
	switch operation {
	case "conversion":
		fmt.Println("Total measured conversion time", totalOperationTime)
		fmt.Println("Average conversion time", averageOperationTime)
	case "cpl25-compare":
		fmt.Println("Total measured CPL25 compare time", totalOperationTime)
		fmt.Println("Average CPL25 compare time", averageOperationTime)
	case "gbfv-compare":
		fmt.Println("Total measured GBFV comparison time", totalOperationTime)
		fmt.Println("Average GBFV comparison time", averageOperationTime)
	default:
		fmt.Println("Total measured homomorphic operation time", totalOperationTime)
		fmt.Println("Average homomorphic operation time", averageOperationTime)
	}
}

func printDebug(params ckks.Parameters, ciphertext *rlwe.Ciphertext, valuesWant []complex128, decryptor *rlwe.Decryptor, encoder *ckks.Encoder) (valuesTest []complex128) {
	slots := ciphertext.Slots()
	if !ciphertext.IsBatched {
		slots *= 2
	}

	valuesTest = make([]complex128, slots)
	if err := encoder.Decode(decryptor.DecryptNew(ciphertext), valuesTest); err != nil {
		panic(err)
	}

	return valuesTest
}
