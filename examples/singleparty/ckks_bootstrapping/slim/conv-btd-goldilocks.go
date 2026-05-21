// Acknowledgement: Some standard helper functions (e.g. FFT/DFT interpolation) are written with the help of ChatGPT.

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
var flagNumIter = flag.Int("num-iter", 1, "number of randomized homomorphic-operation iterations to run.")
var flagOperation = flag.String("operation", "all", "homomorphic operation to time: all, conversion, kim25-compare, bfv-compare, kim25-sign, or bfv-sign.")
var flagOffsetMultiplier = flag.Int("offset-multiplier", 0, "diagnostic override for the public multiplier K in the pK offset before Goldilocks reduction; non-positive uses the paper-derived bound.")
var flagTraceLevels = flag.Bool("trace-levels", false, "print ciphertext levels through the reduction stages.")
var flagTraceDecomp = flag.Bool("trace-decomp", false, "decrypt and trace ConvBtD intermediates.")

var traceParams ckks.Parameters
var traceDecryptor *rlwe.Decryptor
var traceEncoder *ckks.Encoder

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
	out := big.NewInt(1)
	b := new(big.Int).SetUint64(base)
	for i := 0; i < exp; i++ {
		out.Mul(out, b)
	}
	return out
}

func roundScaledBigFloat(value *big.Float, scale *big.Int) *big.Int {
	scaled := new(big.Float).SetPrec(256).Mul(
		new(big.Float).SetPrec(256).Set(value),
		new(big.Float).SetPrec(256).SetInt(scale),
	)
	if scaled.Sign() >= 0 {
		scaled.Add(scaled, new(big.Float).SetFloat64(0.5))
	} else {
		scaled.Sub(scaled, new(big.Float).SetFloat64(0.5))
	}
	out := new(big.Int)
	scaled.Int(out)
	return out
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

func traceCoeffsCiphertext(tag string, ct *rlwe.Ciphertext, count int) {
	if !*flagTraceDecomp || traceDecryptor == nil || traceEncoder == nil {
		return
	}
	values := make([]*big.Float, traceParams.N())
	for i := range values {
		values[i] = new(big.Float).SetPrec(160)
	}
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
		v, _ := values[i].Float64()
		fmt.Printf("%0.8f", v)
	}
	fmt.Println()
}

func traceSlotsCiphertext(tag string, ct *rlwe.Ciphertext, count int) {
	if !*flagTraceDecomp || traceDecryptor == nil || traceEncoder == nil {
		return
	}
	slots := ct.Slots()
	if !ct.IsBatched {
		slots *= 2
	}
	values := make([]complex128, slots)
	if err := traceEncoder.Decode(traceDecryptor.DecryptNew(ct), values); err != nil {
		panic(err)
	}
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

type GoldilocksComputer struct {
	params    ckks.Parameters
	eval      *bootstrapping.Evaluator
	polyEval  *polynomial.Evaluator
	limbBits  int
	limbCount int
	mods      uint64
	degEval   int
	mapping   map[int][]int
}

func NewGoldilocksComputer(params ckks.Parameters, eval *bootstrapping.Evaluator, evk *bootstrapping.EvaluationKeys, limbBits, totalBits int) (*GoldilocksComputer, error) {
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

	pos := make([]int, params.MaxSlots())
	for i := range pos {
		pos[i] = i
	}

	return &GoldilocksComputer{
		params:    params,
		eval:      eval,
		polyEval:  polynomial.NewEvaluator(params, ckks.NewEvaluator(params, evk)),
		limbBits:  limbBits,
		limbCount: limbCount,
		mods:      mods,
		degEval:   degEval,
		mapping:   map[int][]int{0: pos},
	}, nil
}

func (c *GoldilocksComputer) decomposeBig(values []*big.Int, limbs int) [][]complex128 {
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

func (c *GoldilocksComputer) decomposeConst(value *big.Int, limbs int, slots int) [][]complex128 {
	values := make([]*big.Int, slots)
	for i := range values {
		values[i] = new(big.Int).Set(value)
	}
	return c.decomposeBig(values, limbs)
}

func (c *GoldilocksComputer) encryptDigits(encoder *ckks.Encoder, encryptor *rlwe.Encryptor, digits [][]complex128, level int) ([]*rlwe.Ciphertext, error) {
	ciphertexts := make([]*rlwe.Ciphertext, len(digits))
	for i := range digits {
		pt := ckks.NewPlaintext(c.params, level)
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

func (c *GoldilocksComputer) bootstrap(ct *rlwe.Ciphertext) (*rlwe.Ciphertext, float64, int, error) {
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

func (c *GoldilocksComputer) halfIntBoot(ct *rlwe.Ciphertext) (ctOut *rlwe.Ciphertext, bootCount int, err error) {
	ct = ct.CopyNew()
	if ct, _, err = c.eval.ScaleDown(ct); err != nil {
		return nil, 1, err
	}
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

func (c *GoldilocksComputer) mulFixedPointScalar(ct *rlwe.Ciphertext, value *big.Float, fpScale *big.Int) error {
	fixed := roundScaledBigFloat(value, fpScale)
	ringQ := c.params.RingQ().AtLevel(ct.Level())
	for i := range ct.Value {
		ringQ.MulScalarBigint(ct.Value[i], fixed, ct.Value[i])
	}
	ct.Scale = ct.Scale.Mul(rlwe.NewScale(fpScale))
	return nil
}

func (c *GoldilocksComputer) mulIntegerAtLevel(ct *rlwe.Ciphertext, value *big.Int) error {
	if value.Sign() == 0 || value.Cmp(big.NewInt(1)) == 0 {
		return nil
	}
	return c.eval.Evaluator.Mul(ct, value, ct)
}

func (c *GoldilocksComputer) intBootDigits(ct *rlwe.Ciphertext, limbs, adjustmentLevel int, residualScale *big.Float) ([]*rlwe.Ciphertext, int, error) {
	current := ct.CopyNew()
	out := make([]*rlwe.Ciphertext, limbs)
	bootCount := 0
	q0Scale := new(big.Float).SetPrec(160).SetInt(c.params.RingQ().ModulusAtLevel[0])
	targetLevel := current.Level()
	if adjustmentLevel <= targetLevel {
		return nil, 0, fmt.Errorf("adjustment level %d must be above digit correction level %d", adjustmentLevel, targetLevel)
	}

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

		bootInput := shifted.CopyNew()
		if bootInput.Level() > 0 {
			if err := c.eval.Rescale(bootInput, bootInput); err != nil {
				return nil, 0, err
			}
		}
		bootInput.Scale = rlwe.NewScale(q0Scale)
		traceCoeffsCiphertext(fmt.Sprintf("iter=%d boot-input", i), bootInput, 8)

		digit, used, err := c.halfIntBoot(bootInput)
		if err != nil {
			return nil, 0, err
		}
		bootCount += used
		traceSlotsCiphertext(fmt.Sprintf("iter=%d digit", i), digit, 8)
		out[i] = digit

		if i != limbs-1 {
			digitForStC := digit.CopyNew()
			if digitForStC.Level() > c.eval.SlotsToCoeffsParameters.LevelQ {
				digitForStC.Resize(digitForStC.Degree(), c.eval.SlotsToCoeffsParameters.LevelQ)
			}
			traceSlotsCiphertext(fmt.Sprintf("iter=%d digit-for-stc", i), digitForStC, 8)
			back, err := c.eval.SlotsToCoeffs(digitForStC, nil)
			if err != nil {
				return nil, 0, err
			}
			back.IsBatched = false
			traceCoeffsCiphertext(fmt.Sprintf("iter=%d raw-back", i), back, 8)

			scaleAdjust := new(big.Float).SetPrec(160).Quo(
				new(big.Float).SetPrec(160).Set(residualScale),
				new(big.Float).SetPrec(160).Set(&back.Scale.Value),
			)

			if back.Level() < adjustmentLevel {
				return nil, 0, fmt.Errorf("SlotsToCoeffs output level %d is below adjustment level %d", back.Level(), adjustmentLevel)
			}
			if back.Level() > adjustmentLevel {
				c.eval.DropLevel(back, back.Level()-adjustmentLevel)
			}

			adjustScale := big.NewInt(1)
			for level := targetLevel + 1; level <= adjustmentLevel; level++ {
				adjustScale.Mul(adjustScale, new(big.Int).SetUint64(c.params.RingQ().SubRings[level].Modulus))
			}
			if err := c.mulFixedPointScalar(back, scaleAdjust, adjustScale); err != nil {
				return nil, 0, err
			}
			for back.Level() > targetLevel {
				if err := c.eval.Rescale(back, back); err != nil {
					return nil, 0, err
				}
			}
			traceCoeffsCiphertext(fmt.Sprintf("iter=%d scaled-back-before-scale-reset", i), back, 8)
			back.Scale = rlwe.NewScale(residualScale)
			traceCoeffsCiphertext(fmt.Sprintf("iter=%d scaled-back-after-scale-reset", i), back, 8)

			if i > 0 {
				if err := c.mulIntegerAtLevel(back, intPowBig(c.mods, i)); err != nil {
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

func (c *GoldilocksComputer) reduceSmallDigits(digits []*rlwe.Ciphertext) ([]*rlwe.Ciphertext, int, error) {
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

func (c *GoldilocksComputer) subtractDigits(lhs, rhs []*rlwe.Ciphertext) ([]*rlwe.Ciphertext, int, error) {
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

func (c *GoldilocksComputer) subtractDigitsWithFlag(lhs, rhs []*rlwe.Ciphertext) ([]*rlwe.Ciphertext, *rlwe.Ciphertext, int, error) {
	if len(lhs) != len(rhs) {
		return nil, nil, 0, fmt.Errorf("mismatched limb counts: lhs=%d rhs=%d", len(lhs), len(rhs))
	}

	out := make([]*rlwe.Ciphertext, len(lhs))
	for i := 0; i < len(lhs); i++ {
		ct, err := c.eval.SubNew(lhs[i], rhs[i])
		if err != nil {
			return nil, nil, 0, err
		}
		out[i] = ct
	}

	_, scaleDiff, bootCount, err := c.bootstrap(out[0].CopyNew())
	if err != nil {
		return nil, nil, 0, err
	}

	var borrow *rlwe.Ciphertext
	var flag *rlwe.Ciphertext
	for i := range out {
		current := out[i].CopyNew()
		if i != 0 {
			if err := c.eval.Evaluator.Add(current, borrow, current); err != nil {
				return nil, nil, 0, err
			}
		}

		remainder := current.CopyNew()
		if err := c.eval.Mul(current, scaleDiff/float64(c.mods), current); err != nil {
			return nil, nil, 0, err
		}
		if err := c.eval.Rescale(current, current); err != nil {
			return nil, nil, 0, err
		}

		current, ratio, used, err := c.bootstrap(current)
		if err != nil {
			return nil, nil, 0, err
		}
		bootCount += used
		if ratio != 0 {
			scaleDiff = ratio
		}
		out[i] = current.CopyNew()

		if err := c.eval.Evaluator.Sub(remainder, current, remainder); err != nil {
			return nil, nil, 0, err
		}
		if err := c.eval.Evaluator.Mul(remainder, scaleDiff/float64(c.mods*c.mods), remainder); err != nil {
			return nil, nil, 0, err
		}
		if err := c.eval.Rescale(remainder, remainder); err != nil {
			return nil, nil, 0, err
		}
		remainder, err = c.eval.AddNew(remainder, 0.5)
		if err != nil {
			return nil, nil, 0, err
		}

		remainder, ratio, used, err = c.bootstrap(remainder)
		if err != nil {
			return nil, nil, 0, err
		}
		bootCount += used
		if ratio != 0 {
			scaleDiff = ratio
		}

		borrow, err = c.eval.SubNew(remainder, float64(c.mods/2))
		if err != nil {
			return nil, nil, 0, err
		}
		if i == len(out)-1 {
			flag, err = c.eval.AddNew(borrow, 1.0)
			if err != nil {
				return nil, nil, 0, err
			}
		}
	}

	return out, flag, bootCount, nil
}

func (c *GoldilocksComputer) compareGE(lhs, rhs []*rlwe.Ciphertext) (*rlwe.Ciphertext, int, error) {
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

func (c *GoldilocksComputer) SignTopBitZeroGoldilocks(digits []*rlwe.Ciphertext, threshold []*rlwe.Ciphertext) (*rlwe.Ciphertext, int, error) {
	if len(digits) < 16 {
		return nil, 0, fmt.Errorf("expected at least 16 digits, got %d", len(digits))
	}
	if len(threshold) != 1 {
		return nil, 0, fmt.Errorf("expected a one-limb threshold, got %d", len(threshold))
	}

	highBitFlag, bootCount, err := c.compareGE([]*rlwe.Ciphertext{digits[15]}, threshold)
	if err != nil {
		return nil, 0, err
	}

	sign, err := c.eval.SubNew(highBitFlag, 1.0)
	if err != nil {
		return nil, 0, err
	}
	if err := c.eval.Mul(sign, -1.0, sign); err != nil {
		return nil, 0, err
	}

	return sign, bootCount, nil
}

func (c *GoldilocksComputer) selectDigits(base, alt []*rlwe.Ciphertext, flag *rlwe.Ciphertext) ([]*rlwe.Ciphertext, error) {
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

func (c *GoldilocksComputer) blockDigits(src []*rlwe.Ciphertext, start, width int, zero *rlwe.Ciphertext) []*rlwe.Ciphertext {
	out := make([]*rlwe.Ciphertext, c.limbCount)
	for i := range out {
		out[i] = zero.CopyNew()
	}
	for i := 0; i < width && i < c.limbCount; i++ {
		if start+i < len(src) {
			out[i] = src[start+i].CopyNew()
		}
	}
	return out
}

func (c *GoldilocksComputer) addDigits(a, b []*rlwe.Ciphertext) ([]*rlwe.Ciphertext, error) {
	if len(a) != len(b) {
		return nil, fmt.Errorf("mismatched limb counts: lhs=%d rhs=%d", len(a), len(b))
	}
	out := make([]*rlwe.Ciphertext, len(a))
	for i := range a {
		ct, err := c.eval.AddNew(a[i], b[i])
		if err != nil {
			return nil, err
		}
		out[i] = ct
	}
	return out, nil
}

func (c *GoldilocksComputer) consumeBootstrapBudget(digits []*rlwe.Ciphertext) (int, error) {
	bootCount := 0
	for i := range digits {
		_, err := c.eval.Bootstrap(digits[i].CopyNew())
		if err != nil {
			return 0, err
		}
		bootCount++
	}
	return bootCount, nil
}

func (c *GoldilocksComputer) modRaiseCenteredToLevel(ctIn *rlwe.Ciphertext, targetLevel int) (*rlwe.Ciphertext, error) {
	baseLevel := ctIn.Level()
	if baseLevel < 0 {
		return nil, errors.New("input ciphertext has invalid level")
	}
	if targetLevel < baseLevel {
		return nil, fmt.Errorf("target level %d is smaller than input level %d", targetLevel, baseLevel)
	}
	if targetLevel > c.params.MaxLevel() {
		return nil, fmt.Errorf("target level %d exceeds max level %d", targetLevel, c.params.MaxLevel())
	}

	ringBase := c.params.RingQ().AtLevel(baseLevel)
	ringTarget := c.params.RingQ().AtLevel(targetLevel)
	out := ckks.NewCiphertext(c.params, ctIn.Degree(), targetLevel)
	*out.MetaData = *ctIn.MetaData
	out.IsBatched = ctIn.IsBatched

	coeffs := make([]*big.Int, ringBase.N())
	for i := range coeffs {
		coeffs[i] = new(big.Int)
	}
	tmp := new(big.Int)
	for polyIndex := range ctIn.Value {
		polyBase := *ctIn.Value[polyIndex].CopyNew()
		ringBase.INTT(polyBase, polyBase)
		ringBase.PolyToBigintCentered(polyBase, 1, coeffs)

		for level, qi := range ringTarget.ModuliChain()[:targetLevel+1] {
			qBig := new(big.Int).SetUint64(qi)
			for j := 0; j < ringTarget.N(); j++ {
				tmp.Mod(coeffs[j], qBig)
				out.Value[polyIndex].Coeffs[level][j] = tmp.Uint64()
			}
		}
		ringTarget.NTT(out.Value[polyIndex], out.Value[polyIndex])
	}

	return out, nil
}

func (c *GoldilocksComputer) modRaiseCentered(ctIn *rlwe.Ciphertext) (*rlwe.Ciphertext, error) {
	return c.modRaiseCenteredToLevel(ctIn, c.params.MaxLevel())
}

func (c *GoldilocksComputer) prepareCoeffInputGoldilocks(ctCoeff *rlwe.Ciphertext, placementFactor *big.Float, publicOffsetCoeffs []*big.Float, targetLevel, adjustmentLevel int, residualScale *big.Float) (*rlwe.Ciphertext, error) {
	if adjustmentLevel <= targetLevel {
		return nil, fmt.Errorf("adjustment level %d must be above target level %d", adjustmentLevel, targetLevel)
	}

	cRaised, err := c.modRaiseCenteredToLevel(ctCoeff, adjustmentLevel)
	if err != nil {
		return nil, err
	}
	cRaised.IsBatched = false

	adjustScale := big.NewInt(1)
	for level := targetLevel + 1; level <= adjustmentLevel; level++ {
		adjustScale.Mul(adjustScale, new(big.Int).SetUint64(c.params.RingQ().SubRings[level].Modulus))
	}
	if err := c.mulFixedPointScalar(cRaised, placementFactor, adjustScale); err != nil {
		return nil, err
	}
	for cRaised.Level() > targetLevel {
		if err := c.eval.Rescale(cRaised, cRaised); err != nil {
			return nil, err
		}
	}
	cRaised.Scale = rlwe.NewScale(residualScale)

	if err := c.eval.Add(cRaised, publicOffsetCoeffs, cRaised); err != nil {
		return nil, err
	}
	cRaised.IsBatched = false

	if cRaised.Level() > targetLevel {
		c.eval.DropLevel(cRaised, cRaised.Level()-targetLevel)
	}
	cRaised.IsBatched = false

	return cRaised, nil
}

func (c *GoldilocksComputer) ReduceGoldilocks(t, modulus []*rlwe.Ciphertext, zero *rlwe.Ciphertext) ([]*rlwe.Ciphertext, *rlwe.Ciphertext, int, error) {
	requiredLimbs := c.limbCount
	if len(t) != requiredLimbs {
		return nil, nil, 0, fmt.Errorf("expected %d limbs, got %d", requiredLimbs, len(t))
	}

	if *flagTraceLevels {
		fmt.Printf("level trace: input t min=%d modulus min=%d\n", minLevel(t), minLevel(modulus))
	}

	low := make([]*rlwe.Ciphertext, c.limbCount)
	addHigh := make([]*rlwe.Ciphertext, c.limbCount)
	subHigh := make([]*rlwe.Ciphertext, c.limbCount)
	for i := 0; i < c.limbCount; i++ {
		low[i] = zero.CopyNew()
		addHigh[i] = zero.CopyNew()
		subHigh[i] = zero.CopyNew()
	}
	for i := 0; i < c.limbCount && i < 16; i++ {
		low[i] = t[i].CopyNew()
	}
	for i := 16; i < c.limbCount; i++ {
		addHigh[i-8] = t[i].CopyNew()
		subHigh[i-16] = t[i].CopyNew()
	}

	sum, err := c.addDigits(low, addHigh)
	if err != nil {
		return nil, nil, 0, err
	}
	if *flagTraceLevels {
		fmt.Printf("level trace: after add-high min=%d\n", minLevel(sum))
	}

	// Since 16^16 = 2^64 ≡ 2^32 - 1 = 16^8 - 1 mod p, every limb above
	// the sixteenth folds into limbs shifted by eight and zero positions.
	z, bootFold, err := c.subtractDigits(sum, subHigh)
	if err != nil {
		return nil, nil, 0, err
	}
	if *flagTraceLevels {
		fmt.Printf("level trace: after fold-subtract min=%d\n", minLevel(z))
	}

	diff, flag, bootSub, err := c.subtractDigitsWithFlag(z, modulus)
	if err != nil {
		return nil, nil, 0, err
	}
	if *flagTraceLevels {
		fmt.Printf("level trace: after final subtract min=%d\n", minLevel(diff))
	}
	if *flagTraceLevels {
		fmt.Printf("level trace: compare flag level=%d\n", flag.Level())
	}

	out, err := c.selectDigits(z, diff, flag)
	if err != nil {
		return nil, nil, 0, err
	}
	if *flagTraceLevels {
		fmt.Printf("level trace: final out min=%d\n", minLevel(out))
	}

	return out, flag, bootFold + bootSub, nil
}

func (c *GoldilocksComputer) HackedConvBtDGoldilocks(radixEncoded, modulus []*rlwe.Ciphertext, zero *rlwe.Ciphertext) (out, decomposed []*rlwe.Ciphertext, reduceFlag *rlwe.Ciphertext, bootCount int, err error) {
	bootDecomp, err := c.consumeBootstrapBudget(radixEncoded)
	if err != nil {
		return nil, nil, nil, 0, err
	}

	decomposed = make([]*rlwe.Ciphertext, len(radixEncoded))
	for i := range radixEncoded {
		decomposed[i] = radixEncoded[i].CopyNew()
	}

	out, reduceFlag, bootReduce, err := c.ReduceGoldilocks(decomposed, modulus, zero)
	if err != nil {
		return nil, nil, nil, 0, err
	}

	return out, decomposed, reduceFlag, bootDecomp + bootReduce, nil
}

func (c *GoldilocksComputer) ConvBtDGoldilocksFromCoeffInput(ctCoeff *rlwe.Ciphertext, modulus []*rlwe.Ciphertext, zero *rlwe.Ciphertext, placementFactor *big.Float, publicOffsetCoeffs []*big.Float, targetLevel, adjustmentLevel int, residualScale *big.Float) (out, decomposed []*rlwe.Ciphertext, reduceFlag *rlwe.Ciphertext, bootCount int, err error) {
	ctCombined, err := c.prepareCoeffInputGoldilocks(ctCoeff, placementFactor, publicOffsetCoeffs, targetLevel, adjustmentLevel, residualScale)
	if err != nil {
		return nil, nil, nil, 0, err
	}

	decomposed, bootDecomp, err := c.intBootDigits(ctCombined, c.limbCount, adjustmentLevel, residualScale)
	if err != nil {
		return nil, nil, nil, 0, err
	}

	out, reduceFlag, bootReduce, err := c.ReduceGoldilocks(decomposed, modulus, zero)
	if err != nil {
		return nil, nil, nil, 0, err
	}

	return out, decomposed, reduceFlag, bootDecomp + bootReduce, nil
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
		if digit < 0 {
			digit = 0
		}
		acc.Add(acc, big.NewInt(digit))
	}
	return acc
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

func modularMetrics(decodedLimbs [][]complex128, want []*big.Int, modulus *big.Int, limbBits int) (exact int, maxAbsErr *big.Int) {
	exact = 0
	maxAbsErr = new(big.Int)
	tmp := new(big.Int)
	halfModulus := new(big.Int).Rsh(new(big.Int).Set(modulus), 1)

	for slot := range want {
		got := reconstructSlotValue(decodedLimbs, slot, limbBits)
		got.Mod(got, modulus)
		if got.Cmp(want[slot]) == 0 {
			exact++
			continue
		}

		tmp.Sub(got, want[slot])
		tmp.Abs(tmp)
		if tmp.Cmp(halfModulus) > 0 {
			tmp.Sub(modulus, tmp)
		}
		if tmp.Cmp(maxAbsErr) > 0 {
			maxAbsErr.Set(tmp)
		}
	}

	return exact, maxAbsErr
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

func referenceReduceGoldilocks(value, modulus *big.Int) *big.Int {
	return new(big.Int).Mod(value, modulus)
}

func signTopBitZeroGoldilocks(value *big.Int) *big.Int {
	if value.Bit(63) == 0 {
		return big.NewInt(1)
	}
	return big.NewInt(0)
}

func compareGEBit(lhs, rhs *big.Int) *big.Int {
	if lhs.Cmp(rhs) >= 0 {
		return big.NewInt(1)
	}
	return big.NewInt(0)
}

func main() {
	flag.Parse()

	logN := 16
	if *flagShort {
		logN -= 4
	}

	logDefaultScale := 50
	q0 := []int{54, 54}
	inputLevel := len(q0) - 1
	adjustmentLevel := inputLevel + 2
	qiSlotsToCoeffs := []int{54, 54, 43}
	qiCircuitSlots := []int{50, 50, 50, 50, 50, 50, 50, 50, 50, 50}
	qiEvalMod := []int{50, 50, 50, 50, 50, 50, 50, 50}
	qiCoeffsToSlots := []int{47, 47, 47}
	logP := []int{50, 50, 50, 50, 50}
	coeffsLevels := []int{1, 1, 1}
	slotsLevels := []int{1, 1, 1}

	logQ := append(q0, qiSlotsToCoeffs...)
	logQ = append(logQ, qiCircuitSlots...)
	logQ = append(logQ, qiEvalMod...)
	logQ = append(logQ, qiCoeffsToSlots...)

	params, err := ckks.NewParametersFromLiteral(ckks.ParametersLiteral{
		LogN:            logN,
		LogQ:            logQ,
		LogP:            logP,
		LogDefaultScale: logDefaultScale,
		Xs:              ring.Ternary{H: 192},
	})
	if err != nil {
		panic(err)
	}

	coeffsToSlots := dft.MatrixLiteral{
		Type:         dft.HomomorphicEncode,
		Format:       dft.RepackImagAsReal,
		LogSlots:     params.LogMaxSlots(),
		LevelQ:       params.MaxLevelQ(),
		LevelP:       params.MaxLevelP(),
		LogBSGSRatio: 1,
		Levels:       coeffsLevels,
	}

	mod1Params := mod1.ParametersLiteral{
		LevelQ:          params.MaxLevel() - coeffsToSlots.Depth(true),
		LogScale:        logDefaultScale,
		Mod1Type:        mod1.CosDiscrete,
		Mod1Degree:      30,
		DoubleAngle:     3,
		K:               16,
		LogMessageRatio: 0,
		Mod1InvDegree:   0,
	}

	slotsToCoeffs := dft.MatrixLiteral{
		Type:         dft.HomomorphicDecode,
		LogSlots:     params.LogMaxSlots(),
		LogBSGSRatio: 1,
		LevelP:       params.MaxLevelP(),
		Levels:       slotsLevels,
	}
	slotsToCoeffs.LevelQ = adjustmentLevel + len(slotsToCoeffs.Levels)

	btpParams := bootstrapping.Parameters{
		ResidualParameters:      params,
		BootstrappingParameters: params,
		SlotsToCoeffsParameters: slotsToCoeffs,
		Mod1ParametersLiteral:   mod1Params,
		CoeffsToSlotsParameters: coeffsToSlots,
		EphemeralSecretWeight:   32,
		CircuitOrder:            bootstrapping.DecodeThenModUp,
	}

	fmt.Printf("Bootstrapping parameters: logN=%d, logSlots=%d, H(%d; %d), sigma=%f, logQP=%f, levels=%d, scale=2^%d\n",
		btpParams.BootstrappingParameters.LogN(),
		btpParams.BootstrappingParameters.LogMaxSlots(),
		btpParams.BootstrappingParameters.XsHammingWeight(),
		btpParams.EphemeralSecretWeight,
		btpParams.BootstrappingParameters.Xe(),
		btpParams.BootstrappingParameters.LogQP(),
		btpParams.BootstrappingParameters.QCount(),
		btpParams.BootstrappingParameters.LogDefaultScale())

	kgen := rlwe.NewKeyGenerator(params)
	sk, pk := kgen.GenKeyPairNew()

	encoder := ckks.NewEncoder(params, 128)
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

	eval, err := bootstrapping.NewEvaluator(btpParams, evk)
	if err != nil {
		panic(err)
	}

	computer, err := NewGoldilocksComputer(params, eval, evk, 4, 72)
	if err != nil {
		panic(err)
	}

	modulus := new(big.Int).Lsh(big.NewInt(1), 64)
	modulus.Sub(modulus, new(big.Int).Lsh(big.NewInt(1), 32))
	modulus.Add(modulus, big.NewInt(1))

	fmt.Printf("Running ConvBtD + comparison + sign evaluation for Goldilocks prime p=%s using 2^64 ≡ 2^32 - 1 mod p, beta=%d\n", modulus.String(), computer.mods)
	fmt.Println("Timing starts from high-precision coefficient-encoded input; ConvBtD includes centered modraise, placement, and public pK offset.")

	level := slotsToCoeffs.LevelQ + 2
	modulusDigits := computer.decomposeConst(modulus, computer.limbCount, params.MaxSlots())
	topBitThresholdDigits := computer.decomposeConst(big.NewInt(8), 1, params.MaxSlots())
	zeroDigits := make([][]complex128, 1)
	zeroDigits[0] = make([]complex128, params.MaxSlots())

	cModulus, err := computer.encryptDigits(encoder, encryptor, modulusDigits, level)
	if err != nil {
		panic(err)
	}
	cTopBitThreshold, err := computer.encryptDigits(encoder, encryptor, topBitThresholdDigits, level)
	if err != nil {
		panic(err)
	}
	cZero, err := computer.encryptDigits(encoder, encryptor, zeroDigits, level)
	if err != nil {
		panic(err)
	}

	totalMaxErr := 0.0
	totalMeanErr := 0.0
	totalMeanSignErr := 0.0
	totalMeanCompareErr := 0.0
	numIter := *flagNumIter
	if numIter <= 0 {
		panic(fmt.Sprintf("num-iter must be positive, got %d", numIter))
	}
	operation := strings.ToLower(*flagOperation)
	switch operation {
	case "compare", "comparison", "internal-compare", "integer-compare", "dckks-compare", "kim25-comparison":
		operation = "kim25-compare"
	case "bfv-comparison", "end-to-end-compare", "end-to-end-comparison":
		operation = "bfv-compare"
	case "sign", "internal-sign", "dckks-sign":
		operation = "kim25-sign"
	case "end-to-end-sign":
		operation = "bfv-sign"
	}
	switch operation {
	case "all", "conversion", "kim25-compare", "bfv-compare", "kim25-sign", "bfv-sign":
	default:
		panic(fmt.Sprintf("unsupported operation %q: use all, conversion, kim25-compare, bfv-compare, kim25-sign, or bfv-sign", *flagOperation))
	}
	fmt.Println("Selected operation:", operation)
	totalOperationTime := time.Duration(0)
	inputNormalizer := new(big.Float).SetPrec(160).SetInt(intPowBig(computer.mods, computer.limbCount))
	modulusFloat := new(big.Float).SetPrec(160).SetInt(modulus)
	qBaseFloat := new(big.Float).SetPrec(160).SetInt(params.RingQ().ModulusAtLevel[inputLevel])
	inputScaleFloat := new(big.Float).SetPrec(160).Set(qBaseFloat)
	residualScale := new(big.Float).SetPrec(160).Quo(qBaseFloat, inputNormalizer)
	baseMessageRatio := new(big.Float).SetPrec(160).Quo(qBaseFloat, inputScaleFloat)
	placementFactor := new(big.Float).SetPrec(160).Mul(modulusFloat, baseMessageRatio)
	placementFactor.Quo(placementFactor, inputNormalizer)
	publicOffsetK := int64(*flagOffsetMultiplier)
	if publicOffsetK <= 0 {
		// The centered-modraise bound is the Mod1 K scaled by the ratio
		// between the base modulus and the input scale. The public offset adds
		// this many multiples of p before digit extraction.
		publicOffsetKFloat := new(big.Float).SetPrec(160).Mul(new(big.Float).SetFloat64(float64(btpParams.Mod1ParametersLiteral.K)), baseMessageRatio)
		publicOffsetK, _ = publicOffsetKFloat.Int64()
		if new(big.Float).SetInt64(publicOffsetK).Cmp(publicOffsetKFloat) < 0 {
			publicOffsetK++
		}
		// One extra public multiple of p protects the approximate
		// coefficient-carrier path from landing just below zero at the
		// 72-bit lazy-radix boundary.
		publicOffsetK++
		publicOffsetK++
	}
	baseRatioFloat, _ := baseMessageRatio.Float64()
	residualScaleFloat, _ := residualScale.Float64()
	residualLogScale := math.Log2(residualScaleFloat)
	fmt.Printf("Input base message ratio q_base/scale≈%.4f, residual scale≈2^%.2f, public offset multiplier=%d\n", baseRatioFloat, residualLogScale, publicOffsetK)
	publicOffset := new(big.Float).SetPrec(160).SetInt(modulus)
	publicOffset.Mul(publicOffset, new(big.Float).SetPrec(160).SetInt64(publicOffsetK))
	publicOffsetCoeffs := make([]*big.Float, params.N())
	for i := range publicOffsetCoeffs {
		publicOffsetCoeffs[i] = new(big.Float).SetPrec(160).Set(publicOffset)
	}
	logSlots := params.LogMaxSlots()

	sampleResidueInput := func() (want, signWant []*big.Int, coeffValues []*big.Float, err error) {
		want = make([]*big.Int, params.MaxSlots())
		signWant = make([]*big.Int, params.MaxSlots())
		coeffValues = make([]*big.Float, params.N())
		for i := range coeffValues {
			coeffValues[i] = new(big.Float).SetPrec(160)
		}

		for i := range want {
			mVal, err := rand.Int(rand.Reader, modulus)
			if err != nil {
				return nil, nil, nil, err
			}
			want[i] = new(big.Int).Set(mVal)
			signWant[i] = signTopBitZeroGoldilocks(want[i])
			scaledInput := new(big.Float).SetPrec(160).SetInt(mVal)
			scaledInput.Quo(scaledInput, modulusFloat)
			coeffValues[int(utils.BitReverse64(uint64(i), logSlots))].Set(scaledInput)
		}

		return want, signWant, coeffValues, nil
	}

	encryptCoeffInput := func(coeffValues []*big.Float) (*rlwe.Ciphertext, error) {
		coeffPt := ckks.NewPlaintext(params, inputLevel)
		coeffPt.LogDimensions = ring.Dimensions{Rows: 0, Cols: logSlots}
		coeffPt.IsBatched = false
		coeffPt.Scale = rlwe.NewScale(inputScaleFloat)
		if err := encoder.Encode(coeffValues, coeffPt); err != nil {
			return nil, err
		}
		ctCoeff, err := encryptor.EncryptNew(coeffPt)
		if err != nil {
			return nil, err
		}
		ctCoeff.IsBatched = false
		return ctCoeff, nil
	}

	for iter := 0; iter < numIter; iter++ {
		want, signWant, coeffValues, err := sampleResidueInput()
		if err != nil {
			panic(err)
		}
		rightWant, _, rightCoeffValues, err := sampleResidueInput()
		if err != nil {
			panic(err)
		}
		compareWant := make([]*big.Int, params.MaxSlots())
		for i := range compareWant {
			compareWant[i] = compareGEBit(want[i], rightWant[i])
		}

		cT, err := encryptCoeffInput(coeffValues)
		if err != nil {
			panic(err)
		}
		cRight, err := encryptCoeffInput(rightCoeffValues)
		if err != nil {
			panic(err)
		}

		var preparedSlot0 *big.Int
		if *flagTraceLevels {
			prepared, err := computer.prepareCoeffInputGoldilocks(cT, placementFactor, publicOffsetCoeffs, inputLevel, adjustmentLevel, residualScale)
			if err != nil {
				panic(err)
			}
			preparedValues := make([]*big.Float, params.N())
			for i := range preparedValues {
				preparedValues[i] = new(big.Float).SetPrec(160)
			}
			if err := encoder.Decode(decryptor.DecryptNew(prepared), preparedValues); err != nil {
				panic(err)
			}
			preparedSlot0, _ = preparedValues[0].Int(nil)
			scaledApprox, _ := preparedValues[0].Float64()
			fmt.Printf("trace prepared slot0: value ~= %.4f, want mod p=%s\n", scaledApprox, want[0].String())
		}

		var start time.Time
		if operation == "all" || operation == "conversion" || operation == "bfv-compare" || operation == "bfv-sign" {
			start = time.Now()
		}
		out, decomposed, reduceFlag, bootLeftConv, err := computer.ConvBtDGoldilocksFromCoeffInput(cT, cModulus, cZero[0], placementFactor, publicOffsetCoeffs, inputLevel, adjustmentLevel, residualScale)
		if err != nil {
			panic(err)
		}
		if operation == "conversion" {
			elapsed := time.Since(start)
			totalOperationTime += elapsed
			fmt.Printf("ConvBtD conversion time: %s\n", elapsed)
			fmt.Printf("Bootstrapping breakdown: conversion=%d, total=%d\n", bootLeftConv, bootLeftConv)
		}

		var rightOut []*rlwe.Ciphertext
		var rightReduceFlag *rlwe.Ciphertext
		var compare, sign *rlwe.Ciphertext
		bootRightConv := 0
		bootCompare := 0
		bootSign := 0

		if operation == "all" || operation == "kim25-compare" || operation == "bfv-compare" {
			rightOut, _, rightReduceFlag, bootRightConv, err = computer.ConvBtDGoldilocksFromCoeffInput(cRight, cModulus, cZero[0], placementFactor, publicOffsetCoeffs, inputLevel, adjustmentLevel, residualScale)
			if err != nil {
				panic(err)
			}
		}
		if operation == "kim25-compare" {
			start = time.Now()
		}
		if operation == "all" || operation == "kim25-compare" || operation == "bfv-compare" {
			compare, bootCompare, err = computer.compareGE(out, rightOut)
			if err != nil {
				panic(err)
			}
			if operation == "kim25-compare" {
				elapsed := time.Since(start)
				totalOperationTime += elapsed
				fmt.Printf("Kim25 compare time: %s\n", elapsed)
				fmt.Printf("Bootstrapping breakdown: Kim25 compare=%d, total=%d\n", bootCompare, bootCompare)
			}
			if operation == "bfv-compare" {
				elapsed := time.Since(start)
				totalOperationTime += elapsed
				fmt.Printf("End-to-end BFV comparison time: %s\n", elapsed)
				fmt.Printf("Bootstrapping breakdown: lhs ConvBtD=%d, rhs ConvBtD=%d, Kim25 compare=%d, total=%d\n",
					bootLeftConv, bootRightConv, bootCompare, bootLeftConv+bootRightConv+bootCompare)
			}
		}
		if operation == "kim25-sign" {
			start = time.Now()
		}
		if operation == "all" || operation == "kim25-sign" || operation == "bfv-sign" {
			sign, bootSign, err = computer.SignTopBitZeroGoldilocks(out, cTopBitThreshold)
			if err != nil {
				panic(err)
			}
			if operation == "kim25-sign" {
				elapsed := time.Since(start)
				totalOperationTime += elapsed
				fmt.Printf("Kim25 sign time: %s\n", elapsed)
				fmt.Printf("Bootstrapping breakdown: Kim25 sign=%d, total=%d\n", bootSign, bootSign)
			}
			if operation == "bfv-sign" {
				elapsed := time.Since(start)
				totalOperationTime += elapsed
				fmt.Printf("End-to-end BFV sign time: %s\n", elapsed)
				fmt.Printf("Bootstrapping breakdown: ConvBtD=%d, Kim25 sign=%d, total=%d\n",
					bootLeftConv, bootSign, bootLeftConv+bootSign)
			}
		}
		bootCount := bootLeftConv + bootRightConv + bootCompare + bootSign
		if operation == "all" {
			elapsed := time.Since(start)
			totalOperationTime += elapsed
			fmt.Printf("ConvBtD + comparison + sign time: %s\n", elapsed)
			fmt.Printf("Bootstrapping breakdown: lhs ConvBtD=%d, rhs ConvBtD=%d, Kim25 compare=%d, Kim25 sign=%d, total=%d\n",
				bootLeftConv, bootRightConv, bootCompare, bootSign, bootCount)
		}

		outDecoded := make([][]complex128, len(out))
		decompDecoded := make([][]complex128, len(decomposed))
		for i := range out {
			outDecoded[i] = decodeCiphertext(params, out[i], decryptor, encoder)
		}
		var rightOutDecoded [][]complex128
		if rightOut != nil {
			rightOutDecoded = make([][]complex128, len(rightOut))
			for i := range rightOut {
				rightOutDecoded[i] = decodeCiphertext(params, rightOut[i], decryptor, encoder)
			}
		}
		for i := range decomposed {
			decompDecoded[i] = decodeCiphertext(params, decomposed[i], decryptor, encoder)
		}
		var signDecoded []complex128
		if sign != nil {
			signDecoded = decodeCiphertext(params, sign, decryptor, encoder)
		}
		var compareDecoded []complex128
		if compare != nil {
			compareDecoded = decodeCiphertext(params, compare, decryptor, encoder)
		}

		exactOut, maxOutErr := integerMetrics(outDecoded, want, computer.limbBits)
		exactDecompMod, maxDecompModErr := modularMetrics(decompDecoded, want, modulus, computer.limbBits)
		exactRightOut := 0
		maxRightOutErr := new(big.Int)
		if rightOutDecoded != nil {
			exactRightOut, maxRightOutErr = integerMetrics(rightOutDecoded, rightWant, computer.limbBits)
		}
		exactSign := 0
		maxSignErr := new(big.Int)
		if signDecoded != nil {
			exactSign, maxSignErr = integerMetrics([][]complex128{signDecoded}, signWant, 1)
		}
		exactCompare := 0
		maxCompareErr := new(big.Int)
		if compareDecoded != nil {
			exactCompare, maxCompareErr = integerMetrics([][]complex128{compareDecoded}, compareWant, 1)
		}
		wantDigits := computer.decomposeBig(want, len(out))
		maxNoise, meanNoise := digitNoiseMetrics(outDecoded, wantDigits)
		rightWantDigits := [][]complex128(nil)
		maxRightNoise := 0.0
		meanRightNoise := 0.0
		if rightOutDecoded != nil {
			rightWantDigits = computer.decomposeBig(rightWant, len(rightOut))
			maxRightNoise, meanRightNoise = digitNoiseMetrics(rightOutDecoded, rightWantDigits)
		}
		maxOutputErr := new(big.Int).Set(maxOutErr)
		if maxRightOutErr.Cmp(maxOutputErr) > 0 {
			maxOutputErr.Set(maxRightOutErr)
		}

		if *flagShort {
			flagVec := decodeCiphertext(params, reduceFlag, decryptor, encoder)
			fmt.Printf("sample lhs reduce flag: got=%0.4f\n", real(flagVec[0]))
			if rightReduceFlag != nil {
				rightFlagVec := decodeCiphertext(params, rightReduceFlag, decryptor, encoder)
				fmt.Printf("sample rhs reduce flag: got=%0.4f\n", real(rightFlagVec[0]))
			}
			if signDecoded != nil {
				fmt.Printf("sample sign: got=%0.4f want=%0.4f\n", real(signDecoded[0]), float64(signWant[0].Uint64()))
			}
			if compareDecoded != nil {
				fmt.Printf("sample compare lhs>=rhs: got=%0.4f want=%0.4f (lhs=%s rhs=%s)\n",
					real(compareDecoded[0]), float64(compareWant[0].Uint64()), want[0].String(), rightWant[0].String())
			}
			if preparedSlot0 != nil {
				fmt.Print("sample decomp limbs: ")
				tmpPrepared := new(big.Int).Set(preparedSlot0)
				mask := big.NewInt(int64(computer.mods - 1))
				limit := 8
				if limit > len(decompDecoded) {
					limit = len(decompDecoded)
				}
				for limb := 0; limb < limit; limb++ {
					if limb != 0 {
						fmt.Print(", ")
					}
					fmt.Printf("%d:%0.4f/%d", limb, real(decompDecoded[limb][0]), new(big.Int).And(tmpPrepared, mask).Uint64())
					tmpPrepared.Rsh(tmpPrepared, uint(computer.limbBits))
				}
				fmt.Println()
			}
			fmt.Printf("sample lhs limb %d: got=%0.4f want=%0.4f\n", 0, real(outDecoded[0][0]), real(wantDigits[0][0]))
			if rightOutDecoded != nil {
				fmt.Printf("sample rhs limb %d: got=%0.4f want=%0.4f\n", 0, real(rightOutDecoded[0][0]), real(rightWantDigits[0][0]))
			}
		}

		maxOutErrFloat, _ := new(big.Float).SetInt(maxOutputErr).Float64()
		maxDecompModErrFloat, _ := new(big.Float).SetInt(maxDecompModErr).Float64()
		fmt.Printf("Extracted value mod p matches: %d/%d, max modular error=%s", exactDecompMod, len(want), maxDecompModErr.String())
		if maxDecompModErr.Sign() > 0 {
			fmt.Printf(" (Log2 %.4f)\n", math.Log2(maxDecompModErrFloat))
		} else {
			fmt.Println(" (Log2 -Inf)")
		}
		fmt.Printf("Exact lhs output matches: %d/%d, max |out-want|=%s\n", exactOut, len(want), maxOutErr.String())
		if rightOutDecoded != nil {
			fmt.Printf("Exact rhs output matches: %d/%d, max |out-want|=%s\n", exactRightOut, len(rightWant), maxRightOutErr.String())
		}
		if compareDecoded != nil {
			fmt.Printf("Exact comparison matches: %d/%d, max |compare-want|=%s\n", exactCompare, len(compareWant), maxCompareErr.String())
		}
		if signDecoded != nil {
			fmt.Printf("Exact sign matches: %d/%d, max |sign-want|=%s\n", exactSign, len(signWant), maxSignErr.String())
		}
		if maxOutputErr.Sign() > 0 {
			fmt.Println("Max integer error in Log 2:", math.Log2(maxOutErrFloat))
		} else {
			fmt.Println("Max integer error in Log 2: -Inf")
		}
		maxCombinedNoise := math.Max(maxNoise, maxRightNoise)
		if maxCombinedNoise > 0 {
			fmt.Println("Max digit noise in Log 2:", math.Log2(maxCombinedNoise))
		} else {
			fmt.Println("Max digit noise in Log 2: -Inf")
		}
		meanCombinedNoise := 0.5 * (meanNoise + meanRightNoise)
		if meanCombinedNoise > 0 {
			fmt.Println("Mean digit noise in Log 2:", math.Log2(meanCombinedNoise))
		} else {
			fmt.Println("Mean digit noise in Log 2: -Inf")
		}
		totalMaxErr = math.Max(totalMaxErr, maxOutErrFloat)
		outputSlots := len(want)
		outputMatches := exactOut
		if rightOutDecoded != nil {
			outputSlots += len(rightWant)
			outputMatches += exactRightOut
		}
		totalMeanErr += float64(outputSlots-outputMatches) / float64(outputSlots)
		if signDecoded != nil {
			totalMeanSignErr += float64(len(signWant)-exactSign) / float64(len(signWant))
		}
		if compareDecoded != nil {
			totalMeanCompareErr += float64(len(compareWant)-exactCompare) / float64(len(compareWant))
		}
	}

	totalMeanErr /= float64(numIter)
	if operation == "all" || operation == "kim25-sign" || operation == "bfv-sign" {
		totalMeanSignErr /= float64(numIter)
	}
	if operation == "all" || operation == "kim25-compare" || operation == "bfv-compare" {
		totalMeanCompareErr /= float64(numIter)
	}
	fmt.Println("-----------------------------------")
	fmt.Println()
	if totalMaxErr > 0 {
		fmt.Println("Total Max Integer Error in Log 2", math.Log2(totalMaxErr))
	} else {
		fmt.Println("Total Max Integer Error in Log 2 -Inf")
	}
	fmt.Println("Average output mismatch rate", totalMeanErr)
	if operation == "all" || operation == "kim25-sign" || operation == "bfv-sign" {
		fmt.Println("Average sign mismatch rate", totalMeanSignErr)
	}
	if operation == "all" || operation == "kim25-compare" || operation == "bfv-compare" {
		fmt.Println("Average comparison mismatch rate", totalMeanCompareErr)
	}
	averageOperationTime := totalOperationTime / time.Duration(numIter)
	switch operation {
	case "conversion":
		fmt.Println("Total measured conversion time", totalOperationTime)
		fmt.Println("Average conversion time", averageOperationTime)
	case "kim25-compare":
		fmt.Println("Total measured Kim25 compare time", totalOperationTime)
		fmt.Println("Average Kim25 compare time", averageOperationTime)
	case "bfv-compare":
		fmt.Println("Total measured BFV comparison time", totalOperationTime)
		fmt.Println("Average BFV comparison time", averageOperationTime)
	case "kim25-sign":
		fmt.Println("Total measured Kim25 sign time", totalOperationTime)
		fmt.Println("Average Kim25 sign time", averageOperationTime)
	case "bfv-sign":
		fmt.Println("Total measured BFV sign time", totalOperationTime)
		fmt.Println("Average BFV sign time", averageOperationTime)
	default:
		fmt.Println("Total measured homomorphic operation time", totalOperationTime)
		fmt.Println("Average homomorphic operation time", averageOperationTime)
	}
}
