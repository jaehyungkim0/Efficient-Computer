// Acknowledgement: Some standard helper functions( e.g. CRT, FFT) are written with the help of ChatGPT.

// Use the flag -short to run the examples fast but with insecure parameters.
package main

import (
	"errors"
	"flag"
	"fmt"
	"math"
	"math/cmplx"
	"math/rand"
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
var flagNumIter = flag.Int("num-iter", 10, "number of randomized homomorphic-operation iterations to run.")

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

// firstKPrimes returns the first k prime numbers in an array
func firstKPrimes(k uint64) []uint64 {
	if k <= 0 {
		return []uint64{}
	}

	primes := []uint64{}
	num := uint64(2) // start from the first prime number

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

// FFT performs the Fast Fourier Transform on an array of complex numbers.
// If invert is true, it performs the inverse FFT.
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

// DFT performs a Discrete Fourier Transform, which is suitable for non-power-of-two sizes.
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

// isPowerOfTwo checks if a given integer n is a power of two.
func isPowerOfTwo(n int) bool {
	return (n > 0) && (n&(n-1)) == 0
}

// interpolate constructs the polynomial by evaluating the inverse FFT or DFT as needed.
func interpolate(values []complex128) []complex128 {
	n := len(values)
	if isPowerOfTwo(n) {
		coeffs := make([]complex128, n)
		copy(coeffs, values)
		FFT(coeffs, true) // Perform inverse FFT
		return coeffs
	} else {
		return DFT(values, true) // Use DFT for non-power-of-two sizes
	}
}

// generateRootsOfUnity generates the n-th roots of unity.
func generateRootsOfUnity(n int) []complex128 {
	roots := make([]complex128, n)
	for i := 0; i < n; i++ {
		angle := 2 * math.Pi * float64(i) / float64(n)
		roots[i] = cmplx.Exp(complex(0, angle))
	}
	return roots
}

// constructPolynomial finds the polynomial coefficients such that f(z^i) = i for 0 <= i < n.
func constructPolynomial(n int, deg int) []complex128 {
	// Step 1: Generate n-th roots of unity
	// roots := generateRootsOfUnity(n)

	// Step 2: Set up the values of f at each root
	values := make([]complex128, n)
	for i := 0; i < n; i++ {
		values[i] = complex(float64(i), 0)
	}

	// Step 3: Interpolate to find the coefficients, using DFT or FFT as needed
	coefficients := interpolate(values)
	result := make([]complex128, deg+1)
	for i := 0; i <= deg; i++ {
		if i >= n {
			result[i] = complex(0, 0)
		} else {
			result[i] = coefficients[i]
		}
	}
	return result
}

func cleanPolynomial(n int, deg int) []complex128 {
	coefficients := make([]complex128, deg+1)
	for i := 0; i <= deg; i++ {
		coefficients[i] = complex(0, 0)
	}
	coefficients[1] = complex(1.0/float64(n)+1.0, 0)
	coefficients[n+1] = complex(-1.0/float64(n), 0)
	return coefficients
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
		coeffs[i] = complex(0.0, 0.0)
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

type MultiPrecisionSubtractor struct {
	params    ckks.Parameters
	eval      *bootstrapping.Evaluator
	polyEval  *polynomial.Evaluator
	limbBits  int
	limbCount int
	mods      uint64
	degEval   int
	mapping   map[int][]int
}

type SubtractionResult struct {
	Ciphertexts []*rlwe.Ciphertext
	Bootstraps  int
}

func NewMultiPrecisionSubtractor(params ckks.Parameters, eval *bootstrapping.Evaluator, evk *bootstrapping.EvaluationKeys, limbBits, totalBits int) (*MultiPrecisionSubtractor, error) {
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

	return &MultiPrecisionSubtractor{
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

func (s *MultiPrecisionSubtractor) DecomposeUint64(values []uint64) [][]complex128 {
	digits := make([][]complex128, s.limbCount)
	for i := range digits {
		digits[i] = make([]complex128, len(values))
	}

	mask := uint64(s.mods - 1)
	for slot, value := range values {
		num := value
		for limb := 0; limb < s.limbCount; limb++ {
			digits[limb][slot] = complex(float64(num&mask), 0)
			num >>= s.limbBits
		}
	}

	return digits
}

func (s *MultiPrecisionSubtractor) EncryptDigits(encoder *ckks.Encoder, encryptor *rlwe.Encryptor, digits [][]complex128, level int) ([]*rlwe.Ciphertext, error) {
	if len(digits) != s.limbCount {
		return nil, fmt.Errorf("expected %d digit vectors, got %d", s.limbCount, len(digits))
	}

	ciphertexts := make([]*rlwe.Ciphertext, s.limbCount)
	for i := range digits {
		pt := ckks.NewPlaintext(s.params, level)
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

func (s *MultiPrecisionSubtractor) bootstrap(ct *rlwe.Ciphertext) (*rlwe.Ciphertext, float64, int, error) {
	var err error
	bootCount := 1

	if ct, err = s.eval.SlotsToCoeffs(ct, nil); err != nil {
		return nil, 0, bootCount, err
	}
	if ct, _, err = s.eval.ScaleDown(ct); err != nil {
		return nil, 0, bootCount, err
	}

	zeroScale := ct.Scale.Float64()
	targetScale := float64(s.params.RingQ().ModulusAtLevel[0].Uint64())

	if ct, err = s.eval.ModUp(ct); err != nil {
		return nil, 0, bootCount, err
	}

	real, imag, err := s.eval.CoeffsToSlots(ct)
	if err != nil {
		return nil, 0, bootCount, err
	}
	if imag, err = s.eval.EvalModAndScale(real, 2*math.Pi); err != nil {
		return nil, 0, bootCount, err
	}
	if real, err = s.eval.EvalElseAndScale(real, 2*math.Pi); err != nil {
		return nil, 0, bootCount, err
	}
	if err = s.eval.Evaluator.Mul(imag, 1i, imag); err != nil {
		return nil, 0, bootCount, err
	}
	if err = s.eval.Evaluator.Add(real, imag, ct); err != nil {
		return nil, 0, bootCount, err
	}

	polys, err := polynomial.NewPolynomialVector([]bignum.Polynomial{
		bignum.NewPolynomial(0, HermiteInterpolation(int(s.mods), s.degEval), nil),
	}, s.mapping)
	if err != nil {
		return nil, 0, bootCount, err
	}

	if ct, err = s.polyEval.Evaluate(ct, polys, s.params.DefaultScale()); err != nil {
		return nil, 0, bootCount, err
	}

	return ct, targetScale / zeroScale, bootCount, nil
}

func (s *MultiPrecisionSubtractor) Subtract(lhs, rhs []*rlwe.Ciphertext) (*SubtractionResult, error) {
	if len(lhs) != s.limbCount || len(rhs) != s.limbCount {
		return nil, fmt.Errorf("expected %d limbs on both sides, got lhs=%d rhs=%d", s.limbCount, len(lhs), len(rhs))
	}

	out := make([]*rlwe.Ciphertext, s.limbCount)
	for i := 0; i < s.limbCount; i++ {
		ct, err := s.eval.SubNew(lhs[i], rhs[i])
		if err != nil {
			return nil, err
		}
		out[i] = ct
	}

	_, scaleDiff, bootCount, err := s.bootstrap(out[0].CopyNew())
	if err != nil {
		return nil, err
	}

	var borrow *rlwe.Ciphertext
	for i := range out {
		current := out[i].CopyNew()
		if i != 0 {
			if err := s.eval.Evaluator.Add(current, borrow, current); err != nil {
				return nil, err
			}
		}

		remainder := current.CopyNew()
		if err := s.eval.Mul(current, scaleDiff/float64(s.mods), current); err != nil {
			return nil, err
		}
		if err := s.eval.Rescale(current, current); err != nil {
			return nil, err
		}

		current, ratio, used, err := s.bootstrap(current)
		if err != nil {
			return nil, err
		}
		bootCount += used
		if ratio != 0 {
			scaleDiff = ratio
		}
		out[i] = current

		if err := s.eval.Evaluator.Sub(remainder, current, remainder); err != nil {
			return nil, err
		}
		if err := s.eval.Evaluator.Mul(remainder, scaleDiff/float64(s.mods*s.mods), remainder); err != nil {
			return nil, err
		}
		if err := s.eval.Rescale(remainder, remainder); err != nil {
			return nil, err
		}

		remainder, err = s.eval.AddNew(remainder, 0.5)
		if err != nil {
			return nil, err
		}
		remainder, ratio, used, err = s.bootstrap(remainder)
		if err != nil {
			return nil, err
		}
		bootCount += used
		if ratio != 0 {
			scaleDiff = ratio
		}

		borrow, err = s.eval.SubNew(remainder, float64(s.mods/2))
		if err != nil {
			return nil, err
		}
	}

	return &SubtractionResult{Ciphertexts: out, Bootstraps: bootCount}, nil
}

func runSubtractionExperiment(params ckks.Parameters, encoder *ckks.Encoder, encryptor *rlwe.Encryptor, decryptor *rlwe.Decryptor, subtractor *MultiPrecisionSubtractor) error {
	totalMaxErr := 0.0
	totalMeanErr := 0.0
	numIter := *flagNumIter
	if numIter <= 0 {
		return fmt.Errorf("num-iter must be positive, got %d", numIter)
	}
	totalOperationTime := time.Duration(0)

	fmt.Printf("The modulus size in bits: %f\n", math.Log2(float64(subtractor.mods)))

	for iter := 0; iter < numIter; iter++ {
		large1 := make([]uint64, params.MaxSlots())
		large2 := make([]uint64, params.MaxSlots())
		largeWant := make([]uint64, params.MaxSlots())

		rand.Seed(time.Now().UnixNano())
		for i := range large1 {
			large1[i] = rand.Uint64()
			large2[i] = rand.Uint64()
			largeWant[i] = large1[i] - large2[i]
		}

		digits1 := subtractor.DecomposeUint64(large1)
		digits2 := subtractor.DecomposeUint64(large2)
		digitsWant := subtractor.DecomposeUint64(largeWant)

		level := subtractor.limbCount + 2
		cvec1, err := subtractor.EncryptDigits(encoder, encryptor, digits1, level)
		if err != nil {
			return err
		}
		cvec2, err := subtractor.EncryptDigits(encoder, encryptor, digits2, level)
		if err != nil {
			return err
		}

		start := time.Now()
		result, err := subtractor.Subtract(cvec1, cvec2)
		if err != nil {
			return err
		}
		elapsed := time.Since(start)
		totalOperationTime += elapsed

		fmt.Printf("Subtraction time: %s\n", elapsed)
		fmt.Println("Number of bootstrapping used: ", result.Bootstraps)

		maxErr := 0.0
		meanErr := 0.0
		for i := 0; i < subtractor.limbCount; i++ {
			vecTest := printDebug(params, result.Ciphertexts[i], digitsWant[i], decryptor, encoder)
			for j := 0; j < result.Ciphertexts[i].Slots(); j++ {
				tmp := vecTest[j]
				thisErrReal := math.Abs(real(tmp) - real(digitsWant[i][j]))
				thisErrImag := math.Abs(imag(tmp) - imag(digitsWant[i][j]))
				thisErr := math.Sqrt(thisErrReal*thisErrReal + thisErrImag*thisErrImag)
				meanErr += thisErr
				maxErr = math.Max(maxErr, thisErr)
			}
		}

		meanErr /= float64(subtractor.limbCount * result.Ciphertexts[0].Slots())
		fmt.Println("Max Error in Log 2: ", math.Log2(maxErr))
		fmt.Println("Mean Error in Log 2: ", math.Log2(meanErr))
		totalMaxErr = math.Max(maxErr, totalMaxErr)
		totalMeanErr += meanErr
	}

	totalMeanErr /= float64(numIter)
	fmt.Println("-----------------------------------")
	fmt.Println()
	fmt.Println("Total Max Error in Log 2", math.Log2(totalMaxErr))
	fmt.Println("Total Mean Error in Log 2", math.Log2(totalMeanErr))
	fmt.Println("Average homomorphic operation time", totalOperationTime/time.Duration(numIter))

	return nil
}

func main() {

	flag.Parse()

	// Default LogN, which with the following defined parameters
	// provides a security of 128-bit.
	LogN := 15

	if *flagShort {
		LogN -= 4
	}

	//============================
	//=== 1) SCHEME PARAMETERS ===
	//============================

	// In this example, for a pratical purpose, the residual parameters and bootstrapping
	// parameters are the same. But in practice the residual parameters would not contain the
	// moduli for the CoeffsToSlots and EvalMod steps.
	// With LogN=16, LogQP=1221 and H=192, these parameters achieve well over 128-bit of security.
	// For the purpose of the example, only one prime is allocated to the circuit in the slots domain
	// and no prime is allocated to the circuit in the coeffs domain.

	LogDefaultScale := 36

	q0 := []int{36}                  // 3) ScaleDown & 4) ModUp
	qiSlotsToCoeffs := []int{28, 28} // 1) SlotsToCoeffs
	qiCircuitSlots := []int{36, 36, 36, 36, 36, 36}
	qiEvalMod := []int{36, 36, 36, 36, 36, 36, 36, 36}
	qiCoeffsToSlots := []int{32, 32} // 5) CoeffsToSlots

	LogQ := append(q0, qiSlotsToCoeffs...)
	LogQ = append(LogQ, qiCircuitSlots...)
	LogQ = append(LogQ, qiEvalMod...)
	LogQ = append(LogQ, qiCoeffsToSlots...)

	params, err := ckks.NewParametersFromLiteral(ckks.ParametersLiteral{
		LogN:            LogN,              // Log2 of the ring degree
		LogQ:            LogQ,              // Log2 of the ciphertext modulus
		LogP:            []int{36, 36, 36}, // Log2 of the key-switch auxiliary prime moduli
		LogDefaultScale: LogDefaultScale,   // Log2 of the scale
		Xs:              ring.Ternary{H: 192},
	})

	if err != nil {
		panic(err)
	}

	//====================================
	//=== 2) BOOTSTRAPPING PARAMETERS ===
	//====================================

	// CoeffsToSlots parameters (homomorphic encoding)
	CoeffsToSlotsParameters := dft.MatrixLiteral{
		Type:         dft.HomomorphicEncode,
		Format:       dft.RepackImagAsReal, // Returns the real and imaginary part into separate ciphertexts
		LogSlots:     params.LogMaxSlots(),
		LevelQ:       params.MaxLevelQ(),
		LevelP:       params.MaxLevelP(),
		LogBSGSRatio: 1,
		Levels:       []int{1, 1}, //qiCoeffsToSlots
	}

	// Parameters of the homomorphic modular reduction x mod 1
	Mod1ParametersLiteral := mod1.ParametersLiteral{
		LevelQ:          params.MaxLevel() - CoeffsToSlotsParameters.Depth(true),
		LogScale:        36,               // Matches qiEvalMod
		Mod1Type:        mod1.CosDiscrete, // Multi-interval Chebyshev interpolation
		Mod1Degree:      30,               // Depth 5
		DoubleAngle:     3,                // Depth 3
		K:               16,               // With EphemeralSecretWeight = 32 and 2^{15} slots, ensures < 2^{-138.7} failure probability
		LogMessageRatio: 0,                // q/|m| = 1
		Mod1InvDegree:   0,                // Depth 0
	}

	// SlotsToCoeffs parameters (homomorphic decoding)
	SlotsToCoeffsParameters := dft.MatrixLiteral{
		Type:         dft.HomomorphicDecode,
		LogSlots:     params.LogMaxSlots(),
		LogBSGSRatio: 1,
		LevelP:       params.MaxLevelP(),
		Levels:       []int{1, 1}, // qiSlotsToCoeffs
	}

	SlotsToCoeffsParameters.LevelQ = len(SlotsToCoeffsParameters.Levels)

	// Custom bootstrapping.Parameters.
	// All fields are public and can be manually instantiated.
	btpParams := bootstrapping.Parameters{
		ResidualParameters:      params,
		BootstrappingParameters: params,
		SlotsToCoeffsParameters: SlotsToCoeffsParameters,
		Mod1ParametersLiteral:   Mod1ParametersLiteral,
		CoeffsToSlotsParameters: CoeffsToSlotsParameters,
		EphemeralSecretWeight:   32, // > 128bit secure for LogN=16 and LogQP = 115.
		CircuitOrder:            bootstrapping.DecodeThenModUp,
	}

	// We pring some information about the bootstrapping parameters (which are identical to the residual parameters in this example).
	// We can notably check that the LogQP of the bootstrapping parameters is smaller than 1550, which ensures
	// 128-bit of security as explained above.
	fmt.Printf("Bootstrapping parameters: logN=%d, logSlots=%d, H(%d; %d), sigma=%f, logQP=%f, levels=%d, scale=2^%d\n",
		btpParams.BootstrappingParameters.LogN(),
		btpParams.BootstrappingParameters.LogMaxSlots(),
		btpParams.BootstrappingParameters.XsHammingWeight(),
		btpParams.EphemeralSecretWeight,
		btpParams.BootstrappingParameters.Xe(),
		btpParams.BootstrappingParameters.LogQP(),
		btpParams.BootstrappingParameters.QCount(),
		btpParams.BootstrappingParameters.LogDefaultScale())

	//===========================
	//=== 3) KEYGEN & ENCRYPT ===
	//===========================

	// Now that both the residual and bootstrapping parameters are instantiated, we can
	// instantiate the usual necessary object to encode, encrypt and decrypt.

	// Scheme context and keys
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

	var eval *bootstrapping.Evaluator
	if eval, err = bootstrapping.NewEvaluator(btpParams, evk); err != nil {
		panic(err)
	}

	subtractor, err := NewMultiPrecisionSubtractor(params, eval, evk, 4, 64)
	if err != nil {
		panic(err)
	}

	if err := runSubtractionExperiment(params, encoder, encryptor, decryptor, subtractor); err != nil {
		panic(err)
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

	//fmt.Println()
	//fmt.Printf("Level: %d (logQ = %d)\n", ciphertext.Level(), params.LogQLvl(ciphertext.Level()))

	//fmt.Printf("Scale: 2^%f\n", math.Log2(ciphertext.Scale.Float64()))
	//fmt.Printf("ValuesTest: %10.14f %10.14f %10.14f %10.14f...\n", valuesTest[0], valuesTest[1], valuesTest[2], valuesTest[3])
	//fmt.Printf("ValuesWant: %10.14f %10.14f %10.14f %10.14f...\n", valuesWant[0], valuesWant[1], valuesWant[2], valuesWant[3])

	//precStats := ckks.GetPrecisionStats(params, encoder, nil, valuesWant, valuesTest, 0, false)

	//fmt.Println(precStats.String())
	//fmt.Println()

	return
}
