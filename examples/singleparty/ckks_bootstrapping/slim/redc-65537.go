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
	"time"

	"github.com/tuneinsight/lattigo/v6/circuits/ckks/bootstrapping"
	"github.com/tuneinsight/lattigo/v6/circuits/ckks/dft"
	"github.com/tuneinsight/lattigo/v6/circuits/ckks/mod1"
	"github.com/tuneinsight/lattigo/v6/circuits/ckks/polynomial"
	"github.com/tuneinsight/lattigo/v6/core/rlwe"
	"github.com/tuneinsight/lattigo/v6/ring"
	"github.com/tuneinsight/lattigo/v6/schemes/ckks"
	"github.com/tuneinsight/lattigo/v6/utils/bignum"
)

var flagShort = flag.Bool("short", false, "run the example with a smaller and insecure ring degree.")
var flagNumIter = flag.Int("num-iter", 1, "number of randomized homomorphic-operation iterations to run.")
var flagTraceLevels = flag.Bool("trace-levels", false, "print ciphertext levels through the reduction stages.")

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

type Fermat65537Computer struct {
	params    ckks.Parameters
	eval      *bootstrapping.Evaluator
	polyEval  *polynomial.Evaluator
	limbBits  int
	limbCount int
	mods      uint64
	degEval   int
	mapping   map[int][]int
}

func NewFermat65537Computer(params ckks.Parameters, eval *bootstrapping.Evaluator, evk *bootstrapping.EvaluationKeys, limbBits, totalBits int) (*Fermat65537Computer, error) {
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

	return &Fermat65537Computer{
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

func (c *Fermat65537Computer) decomposeBig(values []*big.Int, limbs int) [][]complex128 {
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

func (c *Fermat65537Computer) decomposeConst(value *big.Int, limbs int, slots int) [][]complex128 {
	values := make([]*big.Int, slots)
	for i := range values {
		values[i] = new(big.Int).Set(value)
	}
	return c.decomposeBig(values, limbs)
}

func (c *Fermat65537Computer) encryptDigits(encoder *ckks.Encoder, encryptor *rlwe.Encryptor, digits [][]complex128, level int) ([]*rlwe.Ciphertext, error) {
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

func (c *Fermat65537Computer) bootstrap(ct *rlwe.Ciphertext) (*rlwe.Ciphertext, float64, int, error) {
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

func (c *Fermat65537Computer) reduceSmallDigits(digits []*rlwe.Ciphertext) ([]*rlwe.Ciphertext, int, error) {
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

func (c *Fermat65537Computer) subtractDigits(lhs, rhs []*rlwe.Ciphertext) ([]*rlwe.Ciphertext, int, error) {
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

func (c *Fermat65537Computer) subtractDigitsWithFlag(lhs, rhs []*rlwe.Ciphertext) ([]*rlwe.Ciphertext, *rlwe.Ciphertext, int, error) {
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

func (c *Fermat65537Computer) compareGE(lhs, rhs []*rlwe.Ciphertext) (*rlwe.Ciphertext, int, error) {
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

func (c *Fermat65537Computer) selectDigits(base, alt []*rlwe.Ciphertext, flag *rlwe.Ciphertext) ([]*rlwe.Ciphertext, error) {
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

func (c *Fermat65537Computer) blockDigits(src []*rlwe.Ciphertext, start, width int, zero *rlwe.Ciphertext) []*rlwe.Ciphertext {
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

func (c *Fermat65537Computer) addDigits(a, b []*rlwe.Ciphertext) ([]*rlwe.Ciphertext, error) {
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

func (c *Fermat65537Computer) Reduce65537(t, modulus []*rlwe.Ciphertext, zero *rlwe.Ciphertext) ([]*rlwe.Ciphertext, *rlwe.Ciphertext, int, error) {
	requiredLimbs := 2*c.limbCount - 1
	if len(t) != requiredLimbs {
		return nil, nil, 0, fmt.Errorf("expected %d limbs, got %d", requiredLimbs, len(t))
	}

	if *flagTraceLevels {
		fmt.Printf("level trace: input t min=%d modulus min=%d\n", minLevel(t), minLevel(modulus))
	}

	low := c.blockDigits(t, 0, 4, zero)
	mid := c.blockDigits(t, 4, 4, zero)
	high := c.blockDigits(t, 8, 4, zero)

	sum, err := c.addDigits(low, high)
	if err != nil {
		return nil, nil, 0, err
	}
	sum, err = c.addDigits(sum, modulus)
	if err != nil {
		return nil, nil, 0, err
	}
	if *flagTraceLevels {
		fmt.Printf("level trace: after fold-add min=%d\n", minLevel(sum))
	}

	// z = block0 - block1 + block2 + p, which always lies in [2, 2p-1] for t < p^2.
	z, bootFold, err := c.subtractDigits(sum, mid)
	if err != nil {
		return nil, nil, 0, err
	}
	if *flagTraceLevels {
		fmt.Printf("level trace: after folded subtract min=%d\n", minLevel(z))
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

func referenceReduce65537(value, modulus *big.Int) *big.Int {
	return new(big.Int).Mod(value, modulus)
}

func main() {
	flag.Parse()

	logN := 16
	if *flagShort {
		logN -= 4
	}

	logDefaultScale := 50
	q0 := []int{50}
	qiSlotsToCoeffs := []int{43, 43, 43}
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
	slotsToCoeffs.LevelQ = len(slotsToCoeffs.Levels)

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

	encoder := ckks.NewEncoder(params)
	decryptor := rlwe.NewDecryptor(params, sk)
	encryptor := rlwe.NewEncryptor(params, pk)

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

	computer, err := NewFermat65537Computer(params, eval, evk, 4, 20)
	if err != nil {
		panic(err)
	}

	modulus := big.NewInt(65537)
	radix := new(big.Int).Lsh(big.NewInt(1), 16)
	limit := new(big.Int).Mul(modulus, modulus)

	fmt.Printf("Running specialized reduction for p=%s using 2^16 ≡ -1 mod p, beta=%d, radix=%s\n", modulus.String(), computer.mods, radix.String())

	level := slotsToCoeffs.LevelQ + 2
	modulusDigits := computer.decomposeConst(modulus, computer.limbCount, params.MaxSlots())
	zeroDigits := make([][]complex128, 1)
	zeroDigits[0] = make([]complex128, params.MaxSlots())

	cModulus, err := computer.encryptDigits(encoder, encryptor, modulusDigits, level)
	if err != nil {
		panic(err)
	}
	cZero, err := computer.encryptDigits(encoder, encryptor, zeroDigits, level)
	if err != nil {
		panic(err)
	}

	totalMaxErr := 0.0
	totalMeanErr := 0.0
	numIter := *flagNumIter
	if numIter <= 0 {
		panic(fmt.Sprintf("num-iter must be positive, got %d", numIter))
	}
	totalOperationTime := time.Duration(0)

	for iter := 0; iter < numIter; iter++ {
		T := make([]*big.Int, params.MaxSlots())
		want := make([]*big.Int, params.MaxSlots())
		for i := range T {
			T[i], err = rand.Int(rand.Reader, limit)
			if err != nil {
				panic(err)
			}
			want[i] = referenceReduce65537(T[i], modulus)
		}

		// Since p^2 = 0x100020001, every T < p^2 fits in exactly 9 base-16 limbs.
		tDigits := computer.decomposeBig(T, 2*computer.limbCount-1)
		cT, err := computer.encryptDigits(encoder, encryptor, tDigits, level)
		if err != nil {
			panic(err)
		}

		start := time.Now()
		out, flag, bootCount, err := computer.Reduce65537(cT, cModulus, cZero[0])
		if err != nil {
			panic(err)
		}
		elapsed := time.Since(start)
		totalOperationTime += elapsed
		fmt.Printf("Reduction time: %s\n", elapsed)
		fmt.Println("Number of bootstrapping used: ", bootCount)

		outDecoded := make([][]complex128, len(out))
		for i := range out {
			outDecoded[i] = decodeCiphertext(params, out[i], decryptor, encoder)
		}

		exactOut, maxOutErr := integerMetrics(outDecoded, want, computer.limbBits)
		wantDigits := computer.decomposeBig(want, len(out))
		maxNoise, meanNoise := digitNoiseMetrics(outDecoded, wantDigits)

		if *flagShort {
			flagVec := decodeCiphertext(params, flag, decryptor, encoder)
			fmt.Printf("sample flag: got=%0.4f\n", real(flagVec[0]))
			fmt.Printf("sample limb %d: got=%0.4f want=%0.4f\n", 0, real(outDecoded[0][0]), real(wantDigits[0][0]))
		}

		maxOutErrFloat, _ := new(big.Float).SetInt(maxOutErr).Float64()
		fmt.Printf("Exact output matches: %d/%d, max |out-want|=%s\n", exactOut, len(want), maxOutErr.String())
		if maxOutErr.Sign() > 0 {
			fmt.Println("Max integer error in Log 2:", math.Log2(maxOutErrFloat))
		} else {
			fmt.Println("Max integer error in Log 2: -Inf")
		}
		if maxNoise > 0 {
			fmt.Println("Max digit noise in Log 2:", math.Log2(maxNoise))
		} else {
			fmt.Println("Max digit noise in Log 2: -Inf")
		}
		if meanNoise > 0 {
			fmt.Println("Mean digit noise in Log 2:", math.Log2(meanNoise))
		} else {
			fmt.Println("Mean digit noise in Log 2: -Inf")
		}
		totalMaxErr = math.Max(totalMaxErr, maxOutErrFloat)
		totalMeanErr += float64(len(want)-exactOut) / float64(len(want))
	}

	totalMeanErr /= float64(numIter)
	fmt.Println("-----------------------------------")
	fmt.Println()
	if totalMaxErr > 0 {
		fmt.Println("Total Max Integer Error in Log 2", math.Log2(totalMaxErr))
	} else {
		fmt.Println("Total Max Integer Error in Log 2 -Inf")
	}
	fmt.Println("Average mismatch rate", totalMeanErr)
	fmt.Println("Average homomorphic operation time", totalOperationTime/time.Duration(numIter))
}
