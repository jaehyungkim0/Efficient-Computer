// Acknowledgement: Some standard helper functions( e.g. CRT, FFT) are written with the help of ChatGPT.

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
var flagTraceLevels = flag.Bool("trace-levels", false, "print ciphertext levels through REDC stages.")

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

type REDCComputer struct {
	params    ckks.Parameters
	eval      *bootstrapping.Evaluator
	polyEval  *polynomial.Evaluator
	limbBits  int
	limbCount int
	mods      uint64
	degEval   int
	mapping   map[int][]int
}

func NewREDCComputer(params ckks.Parameters, eval *bootstrapping.Evaluator, evk *bootstrapping.EvaluationKeys, limbBits, totalBits int) (*REDCComputer, error) {
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

	return &REDCComputer{
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

func (c *REDCComputer) multiplyLow(lhs, rhs []*rlwe.Ciphertext) ([]*rlwe.Ciphertext, int, error) {
	out := make([]*rlwe.Ciphertext, c.limbCount+1)
	for i := 0; i < c.limbCount; i++ {
		for j := 0; j <= i; j++ {
			ctmp, err := c.eval.MulRelinNew(lhs[j], rhs[i-j])
			if err != nil {
				return nil, 0, err
			}
			if j == 0 {
				out[i] = ctmp.CopyNew()
			} else {
				if out[i], err = c.eval.AddNew(out[i], ctmp); err != nil {
					return nil, 0, err
				}
			}
		}
		if err := c.eval.Rescale(out[i], out[i]); err != nil {
			return nil, 0, err
		}
	}
	zero, err := c.eval.SubNew(lhs[0], lhs[0])
	if err != nil {
		return nil, 0, err
	}
	out[c.limbCount] = zero

	reduced, bootCount, err := c.reduceProductDigits(out)
	if err != nil {
		return nil, 0, err
	}

	return reduced[:c.limbCount], bootCount, nil
}

func (c *REDCComputer) multiplyExt(lhs, rhs []*rlwe.Ciphertext, zero *rlwe.Ciphertext) ([]*rlwe.Ciphertext, error) {
	out := make([]*rlwe.Ciphertext, 2*c.limbCount)
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
	q, bootQ, err := c.multiplyLow(t[:c.limbCount], modulusInv)
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

	return out, q, u, flag, bootQ + bootNorm + bootSub + bootCmp + bootOut, nil
}

func standardMontgomeryREDC(t, modulus, radix, modulusInv *big.Int) (q, u, out *big.Int) {
	q = new(big.Int).Mul(t, modulusInv)
	q.Mod(q, radix)

	u = new(big.Int).Mul(q, modulus)
	u.Add(u, t)
	u.Div(u, radix)

	out = new(big.Int).Set(u)
	if out.Cmp(modulus) >= 0 {
		out.Sub(out, modulus)
	}

	return q, u, out
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

func main() {
	flag.Parse()

	LogN := 16
	if *flagShort {
		LogN -= 4
	}

	LogDefaultScale := 50
	q0 := []int{50}
	qiSlotsToCoeffs := []int{43, 43, 43}
	qiCircuitSlots := []int{50, 50, 50, 50, 50, 50, 50, 50, 50, 50}
	qiEvalMod := []int{50, 50, 50, 50, 50, 50, 50, 50}
	qiCoeffsToSlots := []int{47, 47, 47}
	logP := []int{50, 50, 50, 50, 50}
	coeffsLevels := []int{1, 1, 1}
	slotsLevels := []int{1, 1, 1}

	LogQ := append(q0, qiSlotsToCoeffs...)
	LogQ = append(LogQ, qiCircuitSlots...)
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
		LogScale:        LogDefaultScale,
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

	computer, err := NewREDCComputer(params, eval, evk, 4, 20)
	if err != nil {
		panic(err)
	}

	// Example modulus for Algorithm 2 (IntCom.REDC_p): a small odd prime, coprime with beta.
	modulus := big.NewInt(65521)
	R := new(big.Int).Exp(big.NewInt(int64(computer.mods)), big.NewInt(int64(computer.limbCount)), nil)
	modulusInv := new(big.Int).ModInverse(modulus, R)
	modulusInv.Neg(modulusInv)
	modulusInv.Mod(modulusInv, R)
	limit := new(big.Int).Mul(modulus, R)

	fmt.Printf("Running REDC_p for p=%s, beta=%d, R=%s\n", modulus.String(), computer.mods, R.String())

	level := slotsToCoeffs.LevelQ + 2
	modulusDigits := computer.decomposeConst(modulus, computer.limbCount, params.MaxSlots())
	modulusInvDigits := computer.decomposeConst(modulusInv, computer.limbCount, params.MaxSlots())
	zeroDigits := make([][]complex128, 1)
	zeroDigits[0] = make([]complex128, params.MaxSlots())

	cModulus, err := computer.encryptDigits(encoder, encryptor, modulusDigits, level)
	if err != nil {
		panic(err)
	}
	cModulusInv, err := computer.encryptDigits(encoder, encryptor, modulusInvDigits, level)
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
		qWant := make([]*big.Int, params.MaxSlots())
		uWant := make([]*big.Int, params.MaxSlots())
		for i := range T {
			T[i], err = rand.Int(rand.Reader, limit)
			if err != nil {
				panic(err)
			}
			qWant[i], uWant[i], want[i] = standardMontgomeryREDC(T[i], modulus, R, modulusInv)
		}

		tDigits := computer.decomposeBig(T, 2*computer.limbCount)
		cT, err := computer.encryptDigits(encoder, encryptor, tDigits, level)
		if err != nil {
			panic(err)
		}

		start := time.Now()
		out, qDigits, uDigits, flag, bootCount, err := computer.REDCP(cT, cModulus, cModulusInv, cZero[0])
		if err != nil {
			panic(err)
		}
		elapsed := time.Since(start)
		totalOperationTime += elapsed
		fmt.Printf("REDC time: %s\n", elapsed)
		fmt.Println("Number of bootstrapping used: ", bootCount)

		outDecoded := make([][]complex128, len(out))
		qDecoded := make([][]complex128, len(qDigits))
		uDecoded := make([][]complex128, len(uDigits))
		for i := range out {
			outDecoded[i] = decodeCiphertext(params, out[i], decryptor, encoder)
		}
		for i := range qDigits {
			qDecoded[i] = decodeCiphertext(params, qDigits[i], decryptor, encoder)
		}
		for i := range uDigits {
			uDecoded[i] = decodeCiphertext(params, uDigits[i], decryptor, encoder)
		}

		exactOut, maxOutErr := integerMetrics(outDecoded, want, computer.limbBits)
		exactQ, maxQErr := integerMetrics(qDecoded, qWant, computer.limbBits)
		exactU, maxUErr := integerMetrics(uDecoded, uWant, computer.limbBits)
		wantDigits := computer.decomposeBig(want, len(out))
		maxNoise, meanNoise := digitNoiseMetrics(outDecoded, wantDigits)

		if *flagShort {
			qWantDigits := computer.decomposeBig(qWant, computer.limbCount)
			uWantDigits := computer.decomposeBig(uWant, len(uDigits))
			flagVec := decodeCiphertext(params, flag, decryptor, encoder)
			fmt.Printf("sample flag: got=%0.4f\n", real(flagVec[0]))
			for limb := 0; limb < computer.limbCount; limb++ {
				fmt.Printf("sample q limb %d: got=%0.4f want=%0.4f\n", limb, real(qDecoded[limb][0]), real(qWantDigits[limb][0]))
				fmt.Printf("sample u limb %d: got=%0.4f want=%0.4f\n", limb, real(uDecoded[limb][0]), real(uWantDigits[limb][0]))
			}
		}
		if *flagShort && len(outDecoded) > 0 {
			wantDigits := computer.decomposeBig(want, len(out))
			fmt.Printf("sample limb %d: got=%0.4f want=%0.4f\n", 0, real(outDecoded[0][0]), real(wantDigits[0][0]))
		}

		maxOutErrFloat, _ := new(big.Float).SetInt(maxOutErr).Float64()
		fmt.Printf("Exact q matches: %d/%d, max |q-qWant|=%s\n", exactQ, len(qWant), maxQErr.String())
		fmt.Printf("Exact u matches: %d/%d, max |u-uWant|=%s\n", exactU, len(uWant), maxUErr.String())
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
