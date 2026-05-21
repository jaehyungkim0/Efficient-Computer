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
var flagPrimePreset = flag.String("prime", "65537", "prime preset: 65537, 8191, or 8179.")
var flagTraceLevels = flag.Bool("trace-levels", false, "print ciphertext levels through REDC stages.")
var flagTraceDecomp = flag.Bool("trace-decomp", false, "decrypt and trace ConvBtD intermediates.")

var traceParams ckks.Parameters
var traceDecryptor *rlwe.Decryptor
var traceEncoder *ckks.Encoder

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

func HermiteInterpolationValues(values []float64, deg int) []complex128 {
	n := len(values)
	z := cmplx.Exp(2 * math.Pi * 1i / complex(float64(n), 0))

	A := make([][]complex128, 2*n)
	b := make([]complex128, 2*n)

	for i := 0; i < n; i++ {
		zi := cmplx.Pow(z, complex(float64(i), 0))

		A[i] = make([]complex128, 2*n)
		for j := 0; j < 2*n; j++ {
			A[i][j] = cmplx.Pow(zi, complex(float64(j), 0))
		}
		b[i] = complex(values[i], 0)

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
	limbBits  int
	limbCount int
	mods      uint64
	degEval   int
	mapping   map[int][]int
}

type REDCStepBreakdown struct {
	MultExtRho int
	MultEta    int
	MultExtP   int
	High       int
	CondSub    int
}

func (b REDCStepBreakdown) Total() int {
	return b.MultExtRho + b.MultEta + b.MultExtP + b.High + b.CondSub
}

type ConvBtDBreakdown struct {
	DigitExtraction int
	REDC            REDCStepBreakdown
}

func (b ConvBtDBreakdown) Total() int {
	return b.DigitExtraction + b.REDC.Total()
}

func printConvBtDBreakdown(label string, b ConvBtDBreakdown) {
	fmt.Printf("%s ConvBtD substeps: digit extraction=%d, REDC MultExt(x,rho)=%d, REDC Mult(Low(T),eta)=%d, REDC MultExt(n,p)=%d, REDC High(T+MultExt(n,p))=%d, REDC CondSub(y,p)=%d, total=%d\n",
		label,
		b.DigitExtraction,
		b.REDC.MultExtRho,
		b.REDC.MultEta,
		b.REDC.MultExtP,
		b.REDC.High,
		b.REDC.CondSub,
		b.Total())
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

func (c *REDCComputer) bootstrapLookup(ct *rlwe.Ciphertext, values []float64) (*rlwe.Ciphertext, int, error) {
	var err error

	if ct, err = c.eval.SlotsToCoeffs(ct, nil); err != nil {
		return nil, 1, err
	}
	if ct, _, err = c.eval.ScaleDown(ct); err != nil {
		return nil, 1, err
	}
	if ct, err = c.eval.ModUp(ct); err != nil {
		return nil, 1, err
	}

	real, imag, err := c.eval.CoeffsToSlots(ct)
	if err != nil {
		return nil, 1, err
	}
	if imag, err = c.eval.EvalModAndScale(real, 2*math.Pi); err != nil {
		return nil, 1, err
	}
	if real, err = c.eval.EvalElseAndScale(real, 2*math.Pi); err != nil {
		return nil, 1, err
	}
	if err = c.eval.Evaluator.Mul(imag, 1i, imag); err != nil {
		return nil, 1, err
	}
	if err = c.eval.Evaluator.Add(real, imag, ct); err != nil {
		return nil, 1, err
	}
	ct.IsBatched = true

	polys, err := polynomial.NewPolynomialVector([]bignum.Polynomial{
		bignum.NewPolynomial(0, HermiteInterpolationValues(values, c.degEval), nil),
	}, c.mapping)
	if err != nil {
		return nil, 1, err
	}

	ctOut, err := c.polyEval.Evaluate(ct, polys, c.params.DefaultScale())
	if err != nil {
		return nil, 1, err
	}
	ctOut.IsBatched = true

	return ctOut, 1, nil
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

func (c *REDCComputer) multiplyByConstExt(lhs []*rlwe.Ciphertext, constant *big.Int, zero *rlwe.Ciphertext) ([]*rlwe.Ciphertext, error) {
	if len(lhs) != c.limbCount {
		return nil, fmt.Errorf("expected %d input limbs, got %d", c.limbCount, len(lhs))
	}

	base := big.NewInt(int64(c.mods))
	constDigits := make([]float64, c.limbCount)
	tmp := new(big.Int).Set(constant)
	rem := new(big.Int)
	for i := 0; i < c.limbCount; i++ {
		tmp.QuoRem(tmp, base, rem)
		constDigits[i] = float64(rem.Int64())
	}

	out := make([]*rlwe.Ciphertext, 2*c.limbCount)
	for i := range out {
		out[i] = zero.CopyNew()
	}

	for i := range out {
		for j := 0; j < c.limbCount; j++ {
			k := i - j
			if k < 0 || k >= len(lhs) || constDigits[j] == 0 {
				continue
			}
			ctmp := lhs[k].CopyNew()
			if err := c.eval.Mul(ctmp, constDigits[j], ctmp); err != nil {
				return nil, err
			}
			if err := c.eval.Add(out[i], ctmp, out[i]); err != nil {
				return nil, err
			}
		}
	}

	return out, nil
}

func (c *REDCComputer) intComMultExtPublic(lhs []*rlwe.Ciphertext, constant *big.Int, zero *rlwe.Ciphertext) ([]*rlwe.Ciphertext, int, error) {
	out, err := c.multiplyByConstExt(lhs, constant, zero)
	if err != nil {
		return nil, 0, err
	}
	// Public-constant MultExt intentionally returns a lazy extended product.
	// The following High step normalizes T + MultExt(n,p) only once.
	return out, 0, nil
}

func (c *REDCComputer) intComLow(ctT []*rlwe.Ciphertext) ([]*rlwe.Ciphertext, error) {
	if len(ctT) < c.limbCount {
		return nil, fmt.Errorf("Low expects at least %d limbs, got %d", c.limbCount, len(ctT))
	}
	low := make([]*rlwe.Ciphertext, c.limbCount)
	for i := range low {
		low[i] = ctT[i].CopyNew()
	}
	return low, nil
}

func (c *REDCComputer) intComMult(lhs, rhs []*rlwe.Ciphertext) ([]*rlwe.Ciphertext, int, error) {
	return c.multiplyLow(lhs, rhs)
}

func (c *REDCComputer) intComMultExt(lhs, rhs []*rlwe.Ciphertext, zero *rlwe.Ciphertext) ([]*rlwe.Ciphertext, int, error) {
	out, err := c.multiplyExt(lhs, rhs, zero)
	if err != nil {
		return nil, 0, err
	}
	// This optimized proof-of-concept keeps MultExt lazy and lets High perform
	// the single carry normalization after adding the two extended products.
	return out, 0, nil
}

func (c *REDCComputer) intComHighOfMontgomerySum(ctT, ctNP []*rlwe.Ciphertext) ([]*rlwe.Ciphertext, int, error) {
	if len(ctT) > len(ctNP) {
		return nil, 0, fmt.Errorf("High expects T length <= MultExt(n,p) length, got T=%d np=%d", len(ctT), len(ctNP))
	}

	var err error
	sum := make([]*rlwe.Ciphertext, len(ctNP))
	for i := range sum {
		if i < len(ctT) {
			if sum[i], err = c.eval.AddNew(ctNP[i], ctT[i]); err != nil {
				return nil, 0, err
			}
			continue
		}
		sum[i] = ctNP[i].CopyNew()
	}
	if *flagTraceLevels {
		fmt.Printf("level trace: after T+MultExt(n,p) min=%d\n", minLevel(sum))
	}

	normalized, bootHigh, err := c.reduceProductDigits(sum)
	if err != nil {
		return nil, 0, err
	}
	if *flagTraceLevels {
		fmt.Printf("level trace: after High carry normalization min=%d\n", minLevel(normalized))
	}

	y := make([]*rlwe.Ciphertext, len(normalized)-c.limbCount)
	for i := range y {
		y[i] = normalized[i+c.limbCount].CopyNew()
	}

	return y, bootHigh, nil
}

func (c *REDCComputer) intComCondSub(y, modulus []*rlwe.Ciphertext, zero *rlwe.Ciphertext) ([]*rlwe.Ciphertext, *rlwe.Ciphertext, int, error) {
	modulusPadded := make([]*rlwe.Ciphertext, len(y))
	for i := range modulusPadded {
		if i < len(modulus) {
			modulusPadded[i] = modulus[i].CopyNew()
			continue
		}
		modulusPadded[i] = zero.CopyNew()
	}

	diff, flag, bootCondSub, err := c.subtractDigitsWithFlag(y, modulusPadded)
	if err != nil {
		return nil, nil, 0, err
	}
	if *flagTraceLevels {
		fmt.Printf("level trace: CondSub diff min=%d flag level=%d\n", minLevel(diff), flag.Level())
	}

	out, err := c.selectDigits(y, diff, flag)
	if err != nil {
		return nil, nil, 0, err
	}

	return out, flag, bootCondSub, nil
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

func (c *REDCComputer) subtractDigitsWithFlag(lhs, rhs []*rlwe.Ciphertext) ([]*rlwe.Ciphertext, *rlwe.Ciphertext, int, error) {
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

func (c *REDCComputer) addDigits(lhs, rhs []*rlwe.Ciphertext) ([]*rlwe.Ciphertext, error) {
	if len(lhs) != len(rhs) {
		return nil, fmt.Errorf("mismatched limb counts: lhs=%d rhs=%d", len(lhs), len(rhs))
	}

	out := make([]*rlwe.Ciphertext, len(lhs))
	for i := range lhs {
		ct, err := c.eval.AddNew(lhs[i], rhs[i])
		if err != nil {
			return nil, err
		}
		out[i] = ct
	}
	return out, nil
}

func (c *REDCComputer) Reduce65537Small(t, modulus []*rlwe.Ciphertext, zero *rlwe.Ciphertext) (out []*rlwe.Ciphertext, reduceFlag *rlwe.Ciphertext, bootCount int, err error) {
	if len(t) != c.limbCount {
		return nil, nil, 0, fmt.Errorf("expected %d limbs, got %d", c.limbCount, len(t))
	}
	if len(modulus) != c.limbCount {
		return nil, nil, 0, fmt.Errorf("expected modulus with %d limbs, got %d", c.limbCount, len(modulus))
	}

	if *flagTraceLevels {
		fmt.Printf("level trace: input t min=%d modulus min=%d\n", minLevel(t), minLevel(modulus))
	}

	low := make([]*rlwe.Ciphertext, c.limbCount)
	topFold := make([]*rlwe.Ciphertext, c.limbCount)
	for i := 0; i < c.limbCount; i++ {
		low[i] = zero.CopyNew()
		topFold[i] = zero.CopyNew()
	}
	for i := 0; i < c.limbCount && i < 4; i++ {
		low[i] = t[i].CopyNew()
	}
	for i := 4; i < c.limbCount; i++ {
		topFold[i-4] = t[i].CopyNew()
	}

	sum, err := c.addDigits(low, modulus)
	if err != nil {
		return nil, nil, 0, err
	}
	if *flagTraceLevels {
		fmt.Printf("level trace: after add-p min=%d\n", minLevel(sum))
	}

	// Since 16^4 = 2^16 ≡ -1 mod 65537, every digit above the fourth folds
	// back as a subtraction shifted by four radix positions.
	z, bootFold, err := c.subtractDigits(sum, topFold)
	if err != nil {
		return nil, nil, 0, err
	}
	if *flagTraceLevels {
		fmt.Printf("level trace: after fold-subtract min=%d\n", minLevel(z))
	}

	diff, reduceFlag, bootSub, err := c.subtractDigitsWithFlag(z, modulus)
	if err != nil {
		return nil, nil, 0, err
	}
	if *flagTraceLevels {
		fmt.Printf("level trace: after final subtract min=%d\n", minLevel(diff))
		fmt.Printf("level trace: reduce flag level=%d\n", reduceFlag.Level())
	}

	out, err = c.selectDigits(z, diff, reduceFlag)
	if err != nil {
		return nil, nil, 0, err
	}
	if *flagTraceLevels {
		fmt.Printf("level trace: final out min=%d\n", minLevel(out))
	}

	return out, reduceFlag, bootFold + bootSub, nil
}

func (c *REDCComputer) Reduce8191Small(t, modulus []*rlwe.Ciphertext, zero *rlwe.Ciphertext) (out []*rlwe.Ciphertext, reduceFlag *rlwe.Ciphertext, bootCount int, err error) {
	if len(t) != c.limbCount {
		return nil, nil, 0, fmt.Errorf("expected %d limbs, got %d", c.limbCount, len(t))
	}
	if len(t) < 5 {
		return nil, nil, 0, fmt.Errorf("8191 reduction expects at least 5 input limbs, got %d", len(t))
	}
	if len(modulus) != c.limbCount {
		return nil, nil, 0, fmt.Errorf("expected modulus with %d limbs, got %d", c.limbCount, len(modulus))
	}

	if *flagTraceLevels {
		fmt.Printf("level trace: 8191 input t min=%d modulus min=%d\n", minLevel(t), minLevel(modulus))
	}

	// For p=2^13-1 and beta=16, the Mersenne split cuts digit 3:
	// t = low_13 + 2^13 * high, with high=floor(digit_3/2)+8*digit_4.
	_, scaleDiff, bootCount, err := c.bootstrap(t[0].CopyNew())
	if err != nil {
		return nil, nil, 0, err
	}

	halfInput := t[3].CopyNew()
	if err := c.eval.Mul(halfInput, scaleDiff/float64(c.mods), halfInput); err != nil {
		return nil, nil, 0, err
	}
	if err := c.eval.Rescale(halfInput, halfInput); err != nil {
		return nil, nil, 0, err
	}
	floorHalfValues := make([]float64, c.mods)
	for i := range floorHalfValues {
		floorHalfValues[i] = float64(i / 2)
	}
	highFromDigit3, used, err := c.bootstrapLookup(halfInput, floorHalfValues)
	if err != nil {
		return nil, nil, 0, err
	}
	bootCount += used

	twiceHigh := highFromDigit3.CopyNew()
	if err := c.eval.Mul(twiceHigh, 2.0, twiceHigh); err != nil {
		return nil, nil, 0, err
	}
	lowBitDigit3, err := c.eval.SubNew(t[3], twiceHigh)
	if err != nil {
		return nil, nil, 0, err
	}

	folded := make([]*rlwe.Ciphertext, c.limbCount)
	for i := range folded {
		folded[i] = zero.CopyNew()
	}
	folded[0], err = c.eval.AddNew(t[0], highFromDigit3)
	if err != nil {
		return nil, nil, 0, err
	}
	highDigit4 := t[4].CopyNew()
	if err := c.eval.Mul(highDigit4, 8.0, highDigit4); err != nil {
		return nil, nil, 0, err
	}
	if err := c.eval.Add(folded[0], highDigit4, folded[0]); err != nil {
		return nil, nil, 0, err
	}
	folded[1] = t[1].CopyNew()
	folded[2] = t[2].CopyNew()
	folded[3] = lowBitDigit3

	if *flagTraceLevels {
		fmt.Printf("level trace: 8191 after Mersenne fold min=%d\n", minLevel(folded))
	}

	normalized, bootNorm, err := c.reduceSmallDigits(folded)
	if err != nil {
		return nil, nil, 0, err
	}
	bootCount += bootNorm
	if *flagTraceLevels {
		fmt.Printf("level trace: 8191 after normalize min=%d\n", minLevel(normalized))
	}

	diff, reduceFlag, bootSub, err := c.subtractDigitsWithFlag(normalized, modulus)
	if err != nil {
		return nil, nil, 0, err
	}
	bootCount += bootSub

	out, err = c.selectDigits(normalized, diff, reduceFlag)
	if err != nil {
		return nil, nil, 0, err
	}
	if *flagTraceLevels {
		fmt.Printf("level trace: 8191 final out min=%d\n", minLevel(out))
	}

	return out, reduceFlag, bootCount, nil
}

func (c *REDCComputer) SignZero65537(digits []*rlwe.Ciphertext, threshold []*rlwe.Ciphertext) (*rlwe.Ciphertext, int, error) {
	if len(digits) < 4 {
		return nil, 0, fmt.Errorf("expected at least 4 digits, got %d", len(digits))
	}
	if len(threshold) != 1 {
		return nil, 0, fmt.Errorf("expected a one-limb threshold, got %d", len(threshold))
	}

	highBitFlag, bootCount, err := c.compareGE([]*rlwe.Ciphertext{digits[3]}, threshold)
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

func (c *REDCComputer) SignZeroTopBinaryLimb(digits []*rlwe.Ciphertext, topLimb int) (*rlwe.Ciphertext, int, error) {
	if len(digits) <= topLimb {
		return nil, 0, fmt.Errorf("expected at least %d digits, got %d", topLimb+1, len(digits))
	}

	sign, err := c.eval.SubNew(digits[topLimb], 1.0)
	if err != nil {
		return nil, 0, err
	}
	if err := c.eval.Mul(sign, -1.0, sign); err != nil {
		return nil, 0, err
	}

	return sign, 0, nil
}

func (c *REDCComputer) REDCP(t, modulus, modulusInv []*rlwe.Ciphertext, zero *rlwe.Ciphertext) ([]*rlwe.Ciphertext, []*rlwe.Ciphertext, []*rlwe.Ciphertext, *rlwe.Ciphertext, int, error) {
	if *flagTraceLevels {
		fmt.Printf("level trace: REDC T min=%d modulus min=%d eta min=%d\n", minLevel(t), minLevel(modulus), minLevel(modulusInv))
	}
	lowT, err := c.intComLow(t)
	if err != nil {
		return nil, nil, nil, nil, 0, err
	}

	n, bootN, err := c.intComMult(lowT, modulusInv)
	if err != nil {
		return nil, nil, nil, nil, 0, err
	}
	if *flagTraceLevels {
		fmt.Printf("level trace: after n=Mult(Low(T), eta) min=%d\n", minLevel(n))
	}

	np, bootNP, err := c.intComMultExt(n, modulus, zero)
	if err != nil {
		return nil, nil, nil, nil, 0, err
	}
	if *flagTraceLevels {
		fmt.Printf("level trace: after MultExt(n, p) min=%d\n", minLevel(np))
	}

	y, bootHigh, err := c.intComHighOfMontgomerySum(t, np)
	if err != nil {
		return nil, nil, nil, nil, 0, err
	}
	if *flagTraceLevels {
		fmt.Printf("level trace: y=High(...) min=%d\n", minLevel(y))
	}

	out, flag, bootCondSub, err := c.intComCondSub(y, modulus, zero)
	if err != nil {
		return nil, nil, nil, nil, 0, err
	}
	if *flagTraceLevels {
		fmt.Printf("level trace: REDC output=min %d\n", minLevel(out))
	}

	return out, n, y, flag, bootN + bootNP + bootHigh + bootCondSub, nil
}

func (c *REDCComputer) ReduceViaREDCWithBreakdown(t, modulus, modulusInv []*rlwe.Ciphertext, montgomeryFactor *big.Int, zero *rlwe.Ciphertext) (out []*rlwe.Ciphertext, reduceFlag *rlwe.Ciphertext, breakdown REDCStepBreakdown, err error) {
	if len(t) != c.limbCount {
		return nil, nil, breakdown, fmt.Errorf("expected %d limbs, got %d", c.limbCount, len(t))
	}
	if len(modulus) != c.limbCount || len(modulusInv) != c.limbCount {
		return nil, nil, breakdown, fmt.Errorf("expected %d-limb modulus and inverse, got modulus=%d inverse=%d", c.limbCount, len(modulus), len(modulusInv))
	}

	// ct_T <- IntCom.MultExt(ct, rho). Here rho=[R]_p is public, and this
	// proof-of-concept instantiates the step as a lazy public-constant product.
	ctT, bootT, err := c.intComMultExtPublic(t, montgomeryFactor, zero)
	if err != nil {
		return nil, nil, breakdown, err
	}
	breakdown.MultExtRho = bootT
	if *flagTraceLevels {
		fmt.Printf("level trace: after T=MultExt(x,rho) min=%d\n", minLevel(ctT))
	}

	lowT, err := c.intComLow(ctT)
	if err != nil {
		return nil, nil, breakdown, err
	}

	// ct_n <- IntCom.Mult(IntCom.Low(ct_T), eta).
	ctN, bootN, err := c.intComMult(lowT, modulusInv)
	if err != nil {
		return nil, nil, breakdown, err
	}
	breakdown.MultEta = bootN
	if *flagTraceLevels {
		fmt.Printf("level trace: after n=Mult(Low(T),eta) min=%d\n", minLevel(ctN))
	}

	// IntCom.MultExt(ct_n, p), which feeds the High step below.
	ctNP, bootNP, err := c.intComMultExt(ctN, modulus, zero)
	if err != nil {
		return nil, nil, breakdown, err
	}
	breakdown.MultExtP = bootNP
	if *flagTraceLevels {
		fmt.Printf("level trace: after MultExt(n,p) min=%d\n", minLevel(ctNP))
	}

	// ct_y <- IntCom.High(ct_T + IntCom.MultExt(ct_n, p)).
	ctY, bootHigh, err := c.intComHighOfMontgomerySum(ctT, ctNP)
	if err != nil {
		return nil, nil, breakdown, err
	}
	breakdown.High = bootHigh
	if *flagTraceLevels {
		fmt.Printf("level trace: y=High(...) min=%d\n", minLevel(ctY))
	}

	// ct_out <- IntCom.CondSub(ct_y, p).
	out, reduceFlag, bootCondSub, err := c.intComCondSub(ctY, modulus, zero)
	if err != nil {
		return nil, nil, breakdown, err
	}
	breakdown.CondSub = bootCondSub
	if *flagTraceLevels {
		fmt.Printf("level trace: REDC output=min %d\n", minLevel(out))
	}

	return out, reduceFlag, breakdown, nil
}

func (c *REDCComputer) ReduceViaREDC(t, modulus, modulusInv []*rlwe.Ciphertext, montgomeryFactor *big.Int, zero *rlwe.Ciphertext) (out []*rlwe.Ciphertext, reduceFlag *rlwe.Ciphertext, bootCount int, err error) {
	var breakdown REDCStepBreakdown
	out, reduceFlag, breakdown, err = c.ReduceViaREDCWithBreakdown(t, modulus, modulusInv, montgomeryFactor, zero)
	if err != nil {
		return nil, nil, 0, err
	}

	return out, reduceFlag, breakdown.Total(), nil
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

func (c *REDCComputer) prepareCoeffInputModP(ctCoeff *rlwe.Ciphertext, placementFactor float64, publicOffsetCoeffs []float64, tracePrefix string) (*rlwe.Ciphertext, error) {
	cRaised, err := c.eval.ModUp(ctCoeff.CopyNew())
	if err != nil {
		return nil, err
	}
	cRaised.IsBatched = false
	traceCoeffsCiphertext(tracePrefix+"/after-first-ModUp", cRaised, 8)

	if err := c.eval.Mul(cRaised, placementFactor, cRaised); err != nil {
		return nil, err
	}
	if err := c.eval.Rescale(cRaised, cRaised); err != nil {
		return nil, err
	}
	if err := c.eval.Add(cRaised, publicOffsetCoeffs, cRaised); err != nil {
		return nil, err
	}
	cRaised.IsBatched = false
	traceCoeffsCiphertext(tracePrefix+"/after-placement-and-offset", cRaised, 8)

	if cRaised.Level() > 0 {
		c.eval.DropLevel(cRaised, cRaised.Level())
	}
	cRaised.IsBatched = false
	traceCoeffsCiphertext(tracePrefix+"/conv-input-level0", cRaised, 8)

	return cRaised, nil
}

func (c *REDCComputer) ConvBtD65537(ctCombined *rlwe.Ciphertext, modulus []*rlwe.Ciphertext, zero *rlwe.Ciphertext) (out, decomposed []*rlwe.Ciphertext, reduceFlag *rlwe.Ciphertext, bootCount int, err error) {
	decomposed, bootDecomp, err := c.intBootDigits(ctCombined, c.limbCount)
	if err != nil {
		return nil, nil, nil, 0, err
	}

	out, reduceFlag, bootReduce, err := c.Reduce65537Small(decomposed, modulus, zero)
	if err != nil {
		return nil, nil, nil, 0, err
	}

	return out, decomposed, reduceFlag, bootDecomp + bootReduce, nil
}

func (c *REDCComputer) ConvBtD8191(ctCombined *rlwe.Ciphertext, modulus []*rlwe.Ciphertext, zero *rlwe.Ciphertext) (out, decomposed []*rlwe.Ciphertext, reduceFlag *rlwe.Ciphertext, bootCount int, err error) {
	decomposed, bootDecomp, err := c.intBootDigits(ctCombined, c.limbCount)
	if err != nil {
		return nil, nil, nil, 0, err
	}

	out, reduceFlag, bootReduce, err := c.Reduce8191Small(decomposed, modulus, zero)
	if err != nil {
		return nil, nil, nil, 0, err
	}

	return out, decomposed, reduceFlag, bootDecomp + bootReduce, nil
}

func (c *REDCComputer) ConvBtDGeneralREDC(ctCombined *rlwe.Ciphertext, modulus, modulusInv []*rlwe.Ciphertext, montgomeryFactor *big.Int, zero *rlwe.Ciphertext) (out, decomposed []*rlwe.Ciphertext, reduceFlag *rlwe.Ciphertext, bootCount int, err error) {
	var breakdown ConvBtDBreakdown
	out, decomposed, reduceFlag, breakdown, err = c.ConvBtDGeneralREDCWithBreakdown(ctCombined, modulus, modulusInv, montgomeryFactor, zero)
	if err != nil {
		return nil, nil, nil, 0, err
	}
	return out, decomposed, reduceFlag, breakdown.Total(), nil
}

func (c *REDCComputer) ConvBtDGeneralREDCWithBreakdown(ctCombined *rlwe.Ciphertext, modulus, modulusInv []*rlwe.Ciphertext, montgomeryFactor *big.Int, zero *rlwe.Ciphertext) (out, decomposed []*rlwe.Ciphertext, reduceFlag *rlwe.Ciphertext, breakdown ConvBtDBreakdown, err error) {
	decomposed, bootDecomp, err := c.intBootDigits(ctCombined, c.limbCount)
	if err != nil {
		return nil, nil, nil, breakdown, err
	}
	breakdown.DigitExtraction = bootDecomp

	out, reduceFlag, breakdown.REDC, err = c.ReduceViaREDCWithBreakdown(decomposed, modulus, modulusInv, montgomeryFactor, zero)
	if err != nil {
		return nil, nil, nil, breakdown, err
	}

	return out, decomposed, reduceFlag, breakdown, nil
}

func (c *REDCComputer) ConvBtD65537FromCoeffInput(ctCoeff *rlwe.Ciphertext, modulus []*rlwe.Ciphertext, zero *rlwe.Ciphertext, placementFactor float64, publicOffsetCoeffs []float64, tracePrefix string) (out, decomposed []*rlwe.Ciphertext, reduceFlag *rlwe.Ciphertext, bootCount int, err error) {
	ctCombined, err := c.prepareCoeffInputModP(ctCoeff, placementFactor, publicOffsetCoeffs, tracePrefix)
	if err != nil {
		return nil, nil, nil, 0, err
	}

	return c.ConvBtD65537(ctCombined, modulus, zero)
}

func (c *REDCComputer) ConvBtD8191FromCoeffInput(ctCoeff *rlwe.Ciphertext, modulus []*rlwe.Ciphertext, zero *rlwe.Ciphertext, placementFactor float64, publicOffsetCoeffs []float64, tracePrefix string) (out, decomposed []*rlwe.Ciphertext, reduceFlag *rlwe.Ciphertext, bootCount int, err error) {
	ctCombined, err := c.prepareCoeffInputModP(ctCoeff, placementFactor, publicOffsetCoeffs, tracePrefix)
	if err != nil {
		return nil, nil, nil, 0, err
	}

	return c.ConvBtD8191(ctCombined, modulus, zero)
}

func (c *REDCComputer) ConvBtDGeneralREDCFromCoeffInput(ctCoeff *rlwe.Ciphertext, modulus, modulusInv []*rlwe.Ciphertext, montgomeryFactor *big.Int, zero *rlwe.Ciphertext, placementFactor float64, publicOffsetCoeffs []float64, tracePrefix string) (out, decomposed []*rlwe.Ciphertext, reduceFlag *rlwe.Ciphertext, bootCount int, err error) {
	var breakdown ConvBtDBreakdown
	out, decomposed, reduceFlag, breakdown, err = c.ConvBtDGeneralREDCFromCoeffInputWithBreakdown(ctCoeff, modulus, modulusInv, montgomeryFactor, zero, placementFactor, publicOffsetCoeffs, tracePrefix)
	if err != nil {
		return nil, nil, nil, 0, err
	}
	return out, decomposed, reduceFlag, breakdown.Total(), nil
}

func (c *REDCComputer) ConvBtDGeneralREDCFromCoeffInputWithBreakdown(ctCoeff *rlwe.Ciphertext, modulus, modulusInv []*rlwe.Ciphertext, montgomeryFactor *big.Int, zero *rlwe.Ciphertext, placementFactor float64, publicOffsetCoeffs []float64, tracePrefix string) (out, decomposed []*rlwe.Ciphertext, reduceFlag *rlwe.Ciphertext, breakdown ConvBtDBreakdown, err error) {
	ctCombined, err := c.prepareCoeffInputModP(ctCoeff, placementFactor, publicOffsetCoeffs, tracePrefix)
	if err != nil {
		return nil, nil, nil, breakdown, err
	}

	return c.ConvBtDGeneralREDCWithBreakdown(ctCombined, modulus, modulusInv, montgomeryFactor, zero)
}

func (c *REDCComputer) ConvBtDSign65537(ctCombined *rlwe.Ciphertext, modulus, topBitThreshold []*rlwe.Ciphertext, zero *rlwe.Ciphertext) (out, decomposed []*rlwe.Ciphertext, reduceFlag, sign *rlwe.Ciphertext, bootCount int, err error) {
	out, decomposed, reduceFlag, bootConv, err := c.ConvBtD65537(ctCombined, modulus, zero)
	if err != nil {
		return nil, nil, nil, nil, 0, err
	}

	sign, bootSign, err := c.SignZero65537(out, topBitThreshold)
	if err != nil {
		return nil, nil, nil, nil, 0, err
	}

	return out, decomposed, reduceFlag, sign, bootConv + bootSign, nil
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

func referenceReduce65537(value, modulus *big.Int) *big.Int {
	return new(big.Int).Mod(value, modulus)
}

func signBitZero65537(value *big.Int) *big.Int {
	if value.Bit(15) == 0 {
		return big.NewInt(1)
	}
	return big.NewInt(0)
}

func signBitZeroAt(value *big.Int, bitIndex int) *big.Int {
	if value.Bit(bitIndex) == 0 {
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

	primePreset := strings.ToLower(*flagPrimePreset)
	modulus := big.NewInt(65537)
	totalBits := 24
	signBitIndex := 15
	signTopLimb := 3
	useLinearSign := false
	useMersenne8191Reduction := false
	useGeneralREDCReduction := false
	switch primePreset {
	case "65537", "fermat16", "2^16+1":
	case "8191", "mersenne13", "2^13-1":
		modulus = big.NewInt(8191)
		totalBits = 20
		signBitIndex = 12
		signTopLimb = 3
		useLinearSign = true
		useMersenne8191Reduction = true
	case "8179", "generic13", "general13", "13-bit", "13bit":
		modulus = big.NewInt(8179)
		totalBits = 20
		signBitIndex = 12
		signTopLimb = 3
		useLinearSign = true
		useGeneralREDCReduction = true
	default:
		panic(fmt.Sprintf("unsupported prime preset %q: use 65537, 8191, or 8179", *flagPrimePreset))
	}

	computer, err := NewREDCComputer(params, eval, evk, 4, totalBits)
	if err != nil {
		panic(err)
	}

	fmt.Printf("Running ConvBtD + comparison + sign evaluation for p=%s, beta=%d\n", modulus.String(), computer.mods)
	fmt.Println("Timing starts from coefficient-encoded level-0 input; ConvBtD includes the initial ModUp, placement, and public pK offset.")
	if useLinearSign {
		fmt.Printf("Sign uses linear top-bit extraction: output = 1 - limb[%d], with zero comparison bootstrappings.\n", signTopLimb)
	}
	if useGeneralREDCReduction {
		fmt.Println("Reduction uses the generic Montgomery REDC path.")
	}

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

	var cModulusInv []*rlwe.Ciphertext
	var montgomeryFactor *big.Int
	if useGeneralREDCReduction {
		radix := intPowBig(computer.mods, computer.limbCount)
		modulusInv := new(big.Int).ModInverse(modulus, radix)
		if modulusInv == nil {
			panic(fmt.Sprintf("modulus %s is not invertible modulo R=%s", modulus.String(), radix.String()))
		}
		modulusInv.Neg(modulusInv)
		modulusInv.Mod(modulusInv, radix)
		modulusInvDigits := computer.decomposeConst(modulusInv, computer.limbCount, params.MaxSlots())
		cModulusInv, err = computer.encryptDigits(encoder, encryptor, modulusInvDigits, level)
		if err != nil {
			panic(err)
		}
		montgomeryFactor = new(big.Int).Mod(radix, modulus)
		fmt.Printf("Generic REDC constants: R=%s, -p^{-1} mod R=%s, R mod p=%s\n",
			radix.String(), modulusInv.String(), montgomeryFactor.String())
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
	inputNormalizer := new(big.Float).SetInt(intPowBig(computer.mods, computer.limbCount))
	modulusFloat := new(big.Float).SetInt(modulus)
	placementFactor, _ := new(big.Float).Quo(modulusFloat, inputNormalizer).Float64()
	publicOffsetK := int64(btpParams.Mod1ParametersLiteral.K)
	publicOffset := new(big.Float).SetInt(modulus)
	publicOffset.Mul(publicOffset, new(big.Float).SetInt64(publicOffsetK))
	publicOffset.Quo(publicOffset, inputNormalizer)
	publicOffsetFloat, _ := publicOffset.Float64()
	publicOffsetCoeffs := make([]float64, params.N())
	for i := range publicOffsetCoeffs {
		publicOffsetCoeffs[i] = publicOffsetFloat
	}
	logSlots := params.LogMaxSlots()

	sampleResidueInput := func() (want, signWant []*big.Int, coeffValues []float64, err error) {
		want = make([]*big.Int, params.MaxSlots())
		signWant = make([]*big.Int, params.MaxSlots())
		coeffValues = make([]float64, params.N())

		for i := range want {
			mVal, err := rand.Int(rand.Reader, modulus)
			if err != nil {
				return nil, nil, nil, err
			}
			want[i] = new(big.Int).Set(mVal)
			signWant[i] = signBitZeroAt(want[i], signBitIndex)
			scaledInput := new(big.Float).SetInt(mVal)
			scaledInput.Quo(scaledInput, modulusFloat)
			scaledFloat, _ := scaledInput.Float64()
			coeffValues[int(utils.BitReverse64(uint64(i), logSlots))] = scaledFloat
		}

		return want, signWant, coeffValues, nil
	}

	encryptCoeffInput := func(tag string, coeffValues []float64) (*rlwe.Ciphertext, error) {
		coeffPt := ckks.NewPlaintext(params, 0)
		coeffPt.LogDimensions = ring.Dimensions{Rows: 0, Cols: logSlots}
		coeffPt.IsBatched = false
		if err := encoder.Encode(coeffValues, coeffPt); err != nil {
			return nil, err
		}
		ctCoeff, err := encryptor.EncryptNew(coeffPt)
		if err != nil {
			return nil, err
		}
		ctCoeff.IsBatched = false
		traceCoeffsCiphertext(tag+"/coeff-input", ctCoeff, 8)
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

		cCombined, err := encryptCoeffInput("lhs/input", coeffValues)
		if err != nil {
			panic(err)
		}
		cRightCombined, err := encryptCoeffInput("rhs/input", rightCoeffValues)
		if err != nil {
			panic(err)
		}

		var start time.Time
		if operation == "all" || operation == "conversion" || operation == "bfv-compare" || operation == "bfv-sign" {
			start = time.Now()
		}
		var out []*rlwe.Ciphertext
		var reduceFlag *rlwe.Ciphertext
		bootLeftConv := 0
		leftConvDetail := ConvBtDBreakdown{}
		leftHasConvDetail := false
		if useMersenne8191Reduction {
			out, _, reduceFlag, bootLeftConv, err = computer.ConvBtD8191FromCoeffInput(cCombined, cModulus, cZero[0], placementFactor, publicOffsetCoeffs, "lhs/input")
		} else if useGeneralREDCReduction {
			out, _, reduceFlag, leftConvDetail, err = computer.ConvBtDGeneralREDCFromCoeffInputWithBreakdown(cCombined, cModulus, cModulusInv, montgomeryFactor, cZero[0], placementFactor, publicOffsetCoeffs, "lhs/input")
			bootLeftConv = leftConvDetail.Total()
			leftHasConvDetail = true
		} else {
			out, _, reduceFlag, bootLeftConv, err = computer.ConvBtD65537FromCoeffInput(cCombined, cModulus, cZero[0], placementFactor, publicOffsetCoeffs, "lhs/input")
		}
		if err != nil {
			panic(err)
		}
		if operation == "conversion" {
			elapsed := time.Since(start)
			totalOperationTime += elapsed
			fmt.Printf("ConvBtD conversion time: %s\n", elapsed)
			fmt.Printf("Bootstrapping breakdown: conversion=%d, total=%d\n", bootLeftConv, bootLeftConv)
			if leftHasConvDetail {
				printConvBtDBreakdown("lhs", leftConvDetail)
			}
		}

		var rightOut []*rlwe.Ciphertext
		var rightReduceFlag *rlwe.Ciphertext
		var compare, sign *rlwe.Ciphertext
		bootRightConv := 0
		rightConvDetail := ConvBtDBreakdown{}
		rightHasConvDetail := false
		bootCompare := 0
		bootSign := 0

		if operation == "all" || operation == "kim25-compare" || operation == "bfv-compare" {
			if useMersenne8191Reduction {
				rightOut, _, rightReduceFlag, bootRightConv, err = computer.ConvBtD8191FromCoeffInput(cRightCombined, cModulus, cZero[0], placementFactor, publicOffsetCoeffs, "rhs/input")
			} else if useGeneralREDCReduction {
				rightOut, _, rightReduceFlag, rightConvDetail, err = computer.ConvBtDGeneralREDCFromCoeffInputWithBreakdown(cRightCombined, cModulus, cModulusInv, montgomeryFactor, cZero[0], placementFactor, publicOffsetCoeffs, "rhs/input")
				bootRightConv = rightConvDetail.Total()
				rightHasConvDetail = true
			} else {
				rightOut, _, rightReduceFlag, bootRightConv, err = computer.ConvBtD65537FromCoeffInput(cRightCombined, cModulus, cZero[0], placementFactor, publicOffsetCoeffs, "rhs/input")
			}
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
				if leftHasConvDetail {
					printConvBtDBreakdown("lhs", leftConvDetail)
				}
				if rightHasConvDetail {
					printConvBtDBreakdown("rhs", rightConvDetail)
				}
			}
		}
		if operation == "kim25-sign" {
			start = time.Now()
		}
		if operation == "all" || operation == "kim25-sign" || operation == "bfv-sign" {
			if useLinearSign {
				sign, bootSign, err = computer.SignZeroTopBinaryLimb(out, signTopLimb)
			} else {
				sign, bootSign, err = computer.SignZero65537(out, cTopBitThreshold)
			}
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
				if leftHasConvDetail {
					printConvBtDBreakdown("lhs", leftConvDetail)
				}
			}
		}
		bootCount := bootLeftConv + bootRightConv + bootCompare + bootSign
		if operation == "all" {
			elapsed := time.Since(start)
			totalOperationTime += elapsed
			fmt.Printf("ConvBtD + comparison + sign time: %s\n", elapsed)
			fmt.Printf("Bootstrapping breakdown: lhs ConvBtD=%d, rhs ConvBtD=%d, Kim25 compare=%d, Kim25 sign=%d, total=%d\n",
				bootLeftConv, bootRightConv, bootCompare, bootSign, bootCount)
			if leftHasConvDetail {
				printConvBtDBreakdown("lhs", leftConvDetail)
			}
			if rightHasConvDetail {
				printConvBtDBreakdown("rhs", rightConvDetail)
			}
		}

		outDecoded := make([][]complex128, len(out))
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
		var signDecoded []complex128
		if sign != nil {
			signDecoded = decodeCiphertext(params, sign, decryptor, encoder)
		}
		var compareDecoded []complex128
		if compare != nil {
			compareDecoded = decodeCiphertext(params, compare, decryptor, encoder)
		}

		exactOut, maxOutErr := integerMetrics(outDecoded, want, computer.limbBits)
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
			fmt.Printf("sample lhs limb %d: got=%0.4f want=%0.4f\n", 0, real(outDecoded[0][0]), real(wantDigits[0][0]))
			if rightOutDecoded != nil {
				fmt.Printf("sample rhs limb %d: got=%0.4f want=%0.4f\n", 0, real(rightOutDecoded[0][0]), real(rightWantDigits[0][0]))
			}
		}

		maxOutputErrFloat, _ := new(big.Float).SetInt(maxOutputErr).Float64()
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
			fmt.Println("Max integer error in Log 2:", math.Log2(maxOutputErrFloat))
		} else {
			fmt.Println("Max integer error in Log 2: -Inf")
		}
		if math.Max(maxNoise, maxRightNoise) > 0 {
			fmt.Println("Max digit noise in Log 2:", math.Log2(math.Max(maxNoise, maxRightNoise)))
		} else {
			fmt.Println("Max digit noise in Log 2: -Inf")
		}
		meanCombinedNoise := 0.5 * (meanNoise + meanRightNoise)
		if meanCombinedNoise > 0 {
			fmt.Println("Mean digit noise in Log 2:", math.Log2(meanCombinedNoise))
		} else {
			fmt.Println("Mean digit noise in Log 2: -Inf")
		}
		totalMaxErr = math.Max(totalMaxErr, maxOutputErrFloat)
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
