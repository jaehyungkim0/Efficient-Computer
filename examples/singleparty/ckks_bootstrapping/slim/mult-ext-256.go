// Acknowledgement: Some standard helper functions( e.g. CRT, FFT) are written with the help of ChatGPT.

// Use the flag -short to run the examples fast but with insecure parameters.
package main

import (
	"flag"
	"fmt"
	"math"
	"math/cmplx"
	"time"
	"crypto/rand"
	"math/big"

	"github.com/tuneinsight/lattigo/v6/circuits/ckks/polynomial"
	"github.com/tuneinsight/lattigo/v6/circuits/ckks/bootstrapping"
	"github.com/tuneinsight/lattigo/v6/circuits/ckks/dft"
	"github.com/tuneinsight/lattigo/v6/circuits/ckks/mod1"
	"github.com/tuneinsight/lattigo/v6/core/rlwe"
	"github.com/tuneinsight/lattigo/v6/ring"
	"github.com/tuneinsight/lattigo/v6/schemes/ckks"
	"github.com/tuneinsight/lattigo/v6/utils/bignum"
)

var flagShort = flag.Bool("short", false, "run the example with a smaller and insecure ring degree.")

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
	for i:=0; i<int(k); i++ {
		tmp := list[i]
		for tmp * list[i] <= n {
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
	result := make([]complex128, deg + 1)
	for i := 0; i <= deg; i++ {
		if i >= n {
			result[i] = complex(0,0)
		} else {
			result[i] = coefficients[i]
		}
	}
	return result
}

func cleanPolynomial(n int, deg int) []complex128 {
	coefficients := make([]complex128, deg + 1)
	for i := 0; i <= deg; i++ {
		coefficients[i] = complex(0,0)
	}
	coefficients[1] = complex(1.0 / float64(n) + 1.0, 0)
	coefficients[n+1] = complex(-1.0 / float64(n), 0)
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
	for i := 2*n; i <= deg; i++ {
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

func main() {

	flag.Parse()

	// Default LogN, which with the following defined parameters
	// provides a security of 128-bit.
	LogN := 16

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

	LogDefaultScale := 50

	q0 := []int{50}                                    // 3) ScaleDown & 4) ModUp
	qiSlotsToCoeffs := []int{43, 43, 43}               // 1) SlotsToCoeffs
	qiCircuitSlots := []int{50, 50, 50, 50, 50, 50, 50, 50, 50, 50}
	qiEvalMod := []int{50, 50, 50, 50, 50, 50, 50, 50}
	qiCoeffsToSlots := []int{47, 47, 47}           // 5) CoeffsToSlots

	LogQ := append(q0, qiSlotsToCoeffs...)
	LogQ = append(LogQ, qiCircuitSlots...)
	LogQ = append(LogQ, qiEvalMod...)
	LogQ = append(LogQ, qiCoeffsToSlots...)

	params, err := ckks.NewParametersFromLiteral(ckks.ParametersLiteral{
		LogN:            LogN,                      // Log2 of the ring degree
		LogQ:            LogQ,                      // Log2 of the ciphertext modulus
		LogP:            []int{50, 50, 50, 50, 50}, // Log2 of the key-switch auxiliary prime moduli
		LogDefaultScale: LogDefaultScale,           // Log2 of the scale
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
		Levels:       []int{1, 1, 1}, //qiCoeffsToSlots
	}

	// Parameters of the homomorphic modular reduction x mod 1
	Mod1ParametersLiteral := mod1.ParametersLiteral{
		LevelQ:          params.MaxLevel() - CoeffsToSlotsParameters.Depth(true),
		LogScale:        50,               // Matches qiEvalMod
		Mod1Type:        mod1.CosDiscrete, // Multi-interval Chebyshev interpolation
		Mod1Degree:      30,               // Depth 5
		DoubleAngle:     3,                // Depth 3
		K:               16,               // With EphemeralSecretWeight = 32 and 2^{15} slots, ensures < 2^{-138.7} failure probability
		LogMessageRatio: 0,               // q/|m| = 1
		Mod1InvDegree:   0,                // Depth 0
	}

	// SlotsToCoeffs parameters (homomorphic decoding)
	SlotsToCoeffsParameters := dft.MatrixLiteral{
		Type:         dft.HomomorphicDecode,
		LogSlots:     params.LogMaxSlots(),
		LogBSGSRatio: 1,
		LevelP:       params.MaxLevelP(),
		Levels:       []int{1, 1, 1}, // qiSlotsToCoeffs
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

	//========================
	//=== 4) BOOTSTRAPPING ===
	//========================
	var zeroScale float64
	var targetScale float64

	// Instantiates the bootstrapper
	var eval *bootstrapping.Evaluator
	if eval, err = bootstrapping.NewEvaluator(btpParams, evk); err != nil {
		panic(err)
	}

	// Define Computer Parameters
	l := 8
	k := 256
	expk := new(big.Int).Lsh(big.NewInt(1), uint(k))

	// Define Modulo Parameters
	n := 1 << l
	mods := uint64(1 << l)
	deg_eval := 2*n-1
	sum := math.Log2(float64(mods))
	fmt.Printf("The modulus size in bits: %f\n", float64(sum))

	total_max_err := 0.0
	total_mean_err := 0.0
	num_iter := 10

	for iter := 0; iter < num_iter; iter++ {

	pvec1 := make([]*rlwe.Plaintext, k/l)
	pvec2 := make([]*rlwe.Plaintext, k/l)

	large1 := make([]*big.Int, params.MaxSlots())
	large2 := make([]*big.Int, params.MaxSlots())
	largeWant := make([]*big.Int, params.MaxSlots())

	for i := range large1 {
	large1[i], err = rand.Int(rand.Reader, expk)
	large2[i], err = rand.Int(rand.Reader, expk)
	largeWant[i] = new(big.Int).Mul(large1[i], large2[i])
	}
	
	vec1 := make([][]complex128, k/l)
	vec2 := make([][]complex128, k/l)
	vecWant := make([][]complex128, 2 * k/l)
	
	for i := range vec1 {
	vec1[i] = make([]complex128, params.MaxSlots())
	vec2[i] = make([]complex128, params.MaxSlots())
	for j := range vec1[i] {
	
	// num1
	num1 := large1[j]
	// Decompose into base-16 digits
	digits1 := make([]uint64, k/l)
	for t := 0; t < k/l; t++ {
		digits1[t] = new(big.Int).And(num1, big.NewInt(255)).Uint64()
		num1 = new(big.Int).Rsh(num1, 8)
	}
	vec1[i][j] = complex(float64(digits1[i]), 0)
	
	// num2
	num2 := large2[j]
	// Decompose into base-16 digits
	digits2 := make([]uint64, k/l)
	for t := 0; t < k/l; t++ {
		digits2[t] = new(big.Int).And(num2, big.NewInt(255)).Uint64()
		num2 = new(big.Int).Rsh(num2, 8)
	}
	vec2[i][j] = complex(float64(digits2[i]), 0)

	}
	}

	vecZero := make([]complex128, params.MaxSlots())
	for i := range vec1[0] {
		vecZero[i] = complex(0, 0)
	}
	
	for i := range vecWant {
	vecWant[i] = make([]complex128, params.MaxSlots())
	for j := range vecWant[i] {
	// numWant
	numWant := largeWant[j]
	digitsWant := make([]uint64, 2 * k/l)
	for t := 0; t < 2 * k/l; t++ {
		digitsWant[t] = new(big.Int).And(numWant, big.NewInt(255)).Uint64()
		numWant = new(big.Int).Rsh(numWant, 8)
	}
	vecWant[i][j] = complex(float64(digitsWant[i]), 0)
	}
	}

	ptZero := ckks.NewPlaintext(params, SlotsToCoeffsParameters.LevelQ + 2)
	if err := encoder.Encode(vecZero, ptZero); err != nil {
		panic(err)
	}
	
	for i := range vec1 {
	// We encrypt at level 0
	pvec1[i] = ckks.NewPlaintext(params, SlotsToCoeffsParameters.LevelQ + 2)
	pvec2[i] = ckks.NewPlaintext(params, SlotsToCoeffsParameters.LevelQ + 2)
	if err := encoder.Encode(vec1[i], pvec1[i]); err != nil {
		panic(err)
	}
	if err := encoder.Encode(vec2[i], pvec2[i]); err != nil {
		panic(err)
	}
	}

	

	cvec1 := make([]*rlwe.Ciphertext, k/l)
	cvec2 := make([]*rlwe.Ciphertext, k/l)
	cvec := make([]*rlwe.Ciphertext, 2 * k/l)
	var ctZero *rlwe.Ciphertext

	ctZero, err = encryptor.EncryptNew(ptZero)
	if err != nil {
		panic(err)
	}

	for i := 0; i < k/l; i++ {
	// Encrypt
	cvec1[i], err = encryptor.EncryptNew(pvec1[i])
	if err != nil {
		panic(err)
	}
	cvec2[i], err = encryptor.EncryptNew(pvec2[i])
	if err != nil {
		panic(err)
	}	
	}
	start := time.Now()
	
	for i := 0; i < 2 * k/l - 1; i++ {
	lowbound := 0
	if i >= k/l {
		lowbound = i - (k/l) + 1
	}
	for j := lowbound; j <= (i - lowbound); j++ {
	ctmp, err := eval.MulRelinNew(cvec1[j], cvec2[i-j])
	if err != nil {
		panic(err)
	}
	if j == lowbound {
		cvec[i] = ctmp.CopyNew()
	} else {
		if cvec[i], err = eval.AddNew(cvec[i], ctmp); err != nil {
			panic(err)
		}
	}
	}
	if err := eval.Rescale(cvec[i], cvec[i]); err != nil {
		panic(err)
	}
	}
	cvec[2 * k/l - 1] = ctZero
	
	var ciphertext *rlwe.Ciphertext
	var ciphertext2 *rlwe.Ciphertext
	var ciphertext3 *rlwe.Ciphertext

	// Define mapping
	pos := make([][]int, 1)
	for i:=0; i < 1; i++ {
		pos[i] = make([]int, cvec[0].Slots())
		for j:=0; j < cvec[0].Slots(); j++ {
			pos[i][j] = (cvec[0].Slots()) * i + j
		}
	}

	mapping := make(map[int][]int)
	for i:=0; i < 1; i++ {
		mapping[i] = pos[i]
	}

	boot_count := 0
	Bootstrap := func() {
	boot_count += 1
	// Step 1 : SlotsToCoeffs (Homomorphic decoding)
	if ciphertext, err = eval.SlotsToCoeffs(ciphertext, nil); err != nil {
		panic(err)
	}

	// Step 2: scale to q/|m|
	if ciphertext, _, err = eval.ScaleDown(ciphertext); err != nil {
		panic(err)
	}

	zeroScale = ciphertext.Scale.Float64()
	targetScale = float64(params.RingQ().ModulusAtLevel[0].Uint64())

	// Step 3 : Extend the basis from q to Q
	if ciphertext, err = eval.ModUp(ciphertext); err != nil {
		panic(err)
	}

	// Step 4 : CoeffsToSlots (Homomorphic encoding)
	// Note: expects the result to be given in bit-reversed order
	// Also, we need the homomorphic encoding to split the real and
	// imaginary parts into two pure real ciphertexts, because the
	// homomorphic modular reduction is only defined on the reals.
	// The `imag` ciphertext can be ignored if the original input
	// is purely real.
	var real, imag *rlwe.Ciphertext
	if real, imag, err = eval.CoeffsToSlots(ciphertext); err != nil {
		panic(err)
	}

	// Step 5 : EvalMod (Homomorphic modular reduction)
	if imag, err = eval.EvalModAndScale(real, 2 * math.Pi); err != nil {
		panic(err)
	}

	if real, err = eval.EvalElseAndScale(real, 2 * math.Pi); err != nil {
		panic(err)
	}

	// Recombines the real and imaginary part
	if err = eval.Evaluator.Mul(imag, 1i, imag); err != nil {
		panic(err)
	}

	if err = eval.Evaluator.Add(real, imag, ciphertext); err != nil {
		panic(err)
	}

	// Evaluator
	opeval := ckks.NewEvaluator(params, evk)
	// Instantiates the polynomial evaluator
	polyEval := polynomial.NewEvaluator(params, opeval)

	// Step 6 : Polynomial Evaluation
	var polys polynomial.PolynomialVector
	eval_poly_vec := make([]bignum.Polynomial, 1)
	for i:=0; i < 1; i++ {
		eval_poly_vec[i] = bignum.NewPolynomial(0, HermiteInterpolation(int(mods), deg_eval), nil)
	}
        if polys, err = polynomial.NewPolynomialVector(eval_poly_vec, mapping); err != nil {
                panic(err)
        }
	if ciphertext, err = polyEval.Evaluate(ciphertext, polys, params.DefaultScale()); err != nil {
		panic(err)
	}
	}

	ciphertext = cvec[0].CopyNew()
	Bootstrap()
	scale_diff := targetScale / zeroScale

	Reduction := func() {
	fmt.Println("----------------------------------")
	for i := range cvec {
	ciphertext = cvec[i].CopyNew()
	if i != 0 {
	if err = eval.Evaluator.Add(ciphertext, ciphertext2, ciphertext); err != nil {
		panic(err)
	}
	}
	ciphertext2 = ciphertext.CopyNew()
	if err := eval.Mul(ciphertext, scale_diff / float64(mods), ciphertext); err != nil {
		panic(err)
	}
	if err := eval.Rescale(ciphertext, ciphertext); err != nil {
		panic(err)
	}
	Bootstrap()
	cvec[i] = ciphertext.CopyNew()
	if i != len(cvec) - 1 {
	if err = eval.Evaluator.Sub(ciphertext2, ciphertext, ciphertext2); err != nil {
		panic(err)
	}
	ciphertext3 = ciphertext2.CopyNew()
	if err = eval.Evaluator.Mul(ciphertext2, scale_diff / float64(mods * mods), ciphertext2); err != nil {
		panic(err)
	}
	if err := eval.Rescale(ciphertext2, ciphertext2); err != nil {
		panic(err)
	}
	ciphertext = ciphertext2.CopyNew()
	Bootstrap()
	ciphertext2 = ciphertext.CopyNew()
	if err = eval.Evaluator.Mul(ciphertext2, mods, ciphertext); err != nil {
		panic(err)
	}
	if err = eval.Evaluator.Sub(ciphertext3, ciphertext, ciphertext3); err != nil {
		panic(err)
	}
	if err = eval.Evaluator.Mul(ciphertext3, scale_diff / float64(mods * mods * mods), ciphertext3); err != nil {
		panic(err)
	}
	if err := eval.Rescale(ciphertext3, ciphertext3); err != nil {
		panic(err)
	}
	ciphertext = ciphertext3.CopyNew()
	Bootstrap()
	ciphertext3 = ciphertext.CopyNew()
	if err = eval.Evaluator.Mul(ciphertext3, mods, ciphertext3); err != nil {
		panic(err)
	}
	if i != 0 {
	if err = eval.Evaluator.Add(ciphertext2, ciphertext3, ciphertext2); err != nil {
		panic(err)
	}
	}
	}
	}
	}

	boot_count = 0
	Reduction()
	elapsed := time.Since(start)
	fmt.Printf("Multiplication time: %s\n", elapsed)
	fmt.Println("Number of bootstrapping used: ", boot_count)

	//==================
	//=== 5) DECRYPT ===
	//==================

	max_err := 0.0
	mean_err := 0.0
	// Decrypt, print and compare with the plaintext values
	for i := 0; i < 2 * k/l; i++ {
	vecTest := printDebug(params, cvec[i], vecWant[i], decryptor, encoder)
		for j := 0; j < cvec[i].Slots(); j++ {
			tmp := vecTest[j]
			this_err_real := math.Abs(real(tmp) - real(vecWant[i][j]))
			this_err_imag := math.Abs(imag(tmp) - imag(vecWant[i][j]))
			this_err := math.Sqrt(this_err_real * this_err_real + this_err_imag * this_err_imag)
			mean_err += this_err
			max_err = math.Max(max_err, this_err)
	}
	}
	mean_err /= float64(2 * (k/l) * cvec[0].Slots())
	fmt.Println("Max Error in Log 2: ", math.Log2(max_err))
	fmt.Println("Mean Error in Log 2: ", math.Log2(mean_err))
	total_max_err = math.Max(max_err, total_max_err)
	total_mean_err += mean_err
}
	total_mean_err /= float64(num_iter)
	fmt.Println("-----------------------------------")
	fmt.Println()
	fmt.Println("Total Max Error in Log 2", math.Log2(total_max_err))
	fmt.Println("Total Mean Error in Log 2", math.Log2(total_mean_err))
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
