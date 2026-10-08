package returnpath

import (
	"fmt"
	"math"
	"math/big"

	"github.com/tuneinsight/lattigo/v6/circuits/ckks/dft"
	"github.com/tuneinsight/lattigo/v6/core/rlwe"
	"github.com/tuneinsight/lattigo/v6/schemes/ckks"
	"github.com/tuneinsight/lattigo/v6/utils"
	"github.com/tuneinsight/lattigo/v6/utils/bignum"
)

// GBFVBitReturn implements ConvDtG for comparison bits. Only the least
// significant digit of each CPL25 word is extracted; all other GBFV digits
// are zero. Evaluation has no access to a secret key.
type GBFVBitReturn struct {
	params          ckks.Parameters
	eval            *ckks.Evaluator
	dft             *dft.Evaluator
	matrix          dft.Matrix
	packer          *rlwe.RingPackingEvaluator
	inverseT        *rlwe.Plaintext
	batch, capacity int
}

func GBFVReturnDFT(params ckks.Parameters) dft.MatrixLiteral {
	return dft.MatrixLiteral{Type: dft.HomomorphicDecode, LogSlots: params.LogMaxSlots(),
		LevelQ: 5, LevelP: params.MaxLevelP(), Levels: []int{1, 1, 1}, LogBSGSRatio: 1}
}

func NewGBFVBitReturn(params ckks.Parameters, keys rlwe.EvaluationKeySet, packer *rlwe.RingPackingEvaluator, base, digits, batch int) (*GBFVBitReturn, error) {
	return NewGBFVBitReturnWithEvaluator(params, ckks.NewEvaluator(params, keys), packer, base, digits, batch)
}

// NewGBFVBitReturnWithEvaluator reuses work buffers for sequential evaluation.
// The caller must not use eval concurrently with the returned converter.
func NewGBFVBitReturnWithEvaluator(params ckks.Parameters, eval *ckks.Evaluator, packer *rlwe.RingPackingEvaluator, base, digits, batch int) (*GBFVBitReturn, error) {
	if base < 2 || digits < 2 || params.N()%digits != 0 || batch <= 0 || packer == nil || eval == nil || !params.Equal(eval.GetParameters()) {
		return nil, fmt.Errorf("invalid GBFV return layout")
	}
	literal := GBFVReturnDFT(params)
	matrix, err := dft.NewMatrixFromLiteral(params, literal, ckks.NewEncoder(params))
	if err != nil {
		return nil, err
	}
	// In R[X]/(X^N+1), 1/(b-X^h) = sum_j b^(D-1-j) X^(jh)/(b^D+1).
	// This is the public polynomial multiplication and modulus switch of
	// ConvCtG, also used by the public GBFV-to-CKKS-2 implementation.
	p := new(big.Int).Exp(big.NewInt(int64(base)), big.NewInt(int64(digits)), nil)
	p.Add(p, big.NewInt(1))
	q1 := new(big.Int).SetUint64(params.Q()[1])
	h := params.N() / digits
	coefficients := make([]*big.Int, params.N())
	for i := range coefficients {
		coefficients[i] = new(big.Int)
	}
	power := big.NewInt(1)
	for j := digits - 1; j >= 0; j-- {
		bignum.DivRound(new(big.Int).Mul(q1, power), p, coefficients[j*h])
		power.Mul(power, big.NewInt(int64(base)))
	}
	pt := ckks.NewPlaintext(params, 1)
	pt.IsBatched = false
	pt.Scale = rlwe.NewScale(q1)
	rq := params.RingQ().AtLevel(1)
	rq.SetCoefficientsBigint(coefficients, pt.Value)
	rq.NTT(pt.Value, pt.Value)
	return &GBFVBitReturn{params: params, eval: eval, dft: dft.NewEvaluator(params, eval),
		matrix: matrix, packer: packer, inverseT: pt, batch: batch, capacity: h}, nil
}

func (r *GBFVBitReturn) RequiredLevel() int { return r.matrix.LevelQ + 2 }

func (r *GBFVBitReturn) Evaluate(bits []*rlwe.Ciphertext) (*rlwe.Ciphertext, error) {
	if len(bits) == 0 || len(bits)*r.batch > r.capacity {
		return nil, fmt.Errorf("invalid GBFV comparison tuple size")
	}
	var combined *rlwe.Ciphertext
	for block, ct := range bits {
		if ct == nil || ct.Level() < r.RequiredLevel() {
			return nil, fmt.Errorf("GBFV return needs level %d before cleaning", r.RequiredLevel())
		}
		clean, err := CleanBit(r.eval, ct)
		if err != nil {
			return nil, err
		}
		coeff, err := r.dft.SlotsToCoeffsNew(clean, nil, r.matrix)
		if err != nil {
			return nil, err
		}
		coeff.IsBatched = false
		// Actual multiply/rescale leaves two Q primes. A q0-scaled integer
		// cannot be packed at level zero: it would vanish modulo q0.
		if err = alignCoefficientScale(r.params, r.eval, coeff, rlwe.NewScale(r.params.Q()[0])); err != nil {
			return nil, err
		}
		if coeff.Level() != 1 {
			return nil, fmt.Errorf("GBFV return packing needs level 1, got %d", coeff.Level())
		}
		indices := make(map[int]bool, r.batch)
		for slot := 0; slot < r.batch; slot++ {
			indices[int(utils.BitReverse64(uint64(slot), r.params.LogMaxSlots()))] = true
		}
		extracted, err := r.packer.ExtractNaive(coeff, indices)
		if err != nil {
			return nil, err
		}
		permuted := make(map[int]*rlwe.Ciphertext, r.batch)
		for slot := 0; slot < r.batch; slot++ {
			permuted[block*r.batch+slot] = extracted[int(utils.BitReverse64(uint64(slot), r.params.LogMaxSlots()))]
		}
		// Repack zeroes non-selected coefficients. Each block is packed
		// separately to bound the number of live extracted ciphertexts.
		part, err := r.packer.Repack(permuted)
		if err != nil {
			return nil, err
		}
		part.IsBatched = false
		part.Scale = coeff.Scale
		if combined == nil {
			combined = part
		} else if err = r.eval.Add(combined, part, combined); err != nil {
			return nil, err
		}
	}
	out, err := r.eval.MulNew(combined, r.inverseT)
	if err != nil {
		return nil, err
	}
	if err = r.eval.Rescale(out, out); err != nil {
		return nil, err
	}
	out.IsBatched = false
	if out.Level() != 0 {
		return nil, fmt.Errorf("GBFV return must end at level zero")
	}
	return out, nil
}

// alignCoefficientScale multiplies the phase by round(q_i*target/current)
// and explicitly rescales once. SetScale's RescaleTo may skip that rescale
// when target exceeds the multiplication-prime size, so it is not used here.
func alignCoefficientScale(params ckks.Parameters, eval *ckks.Evaluator, ct *rlwe.Ciphertext, target rlwe.Scale) error {
	if ct.Level() < 1 {
		return fmt.Errorf("scale alignment needs a rescaling prime")
	}
	currentRat, _ := ct.Scale.Value.Rat(nil)
	targetRat, _ := target.Value.Rat(nil)
	ratio := new(big.Rat).Quo(targetRat, currentRat)
	ratio.Mul(ratio, new(big.Rat).SetInt(new(big.Int).SetUint64(params.Q()[ct.Level()])))
	multiplier := new(big.Int)
	bignum.DivRound(ratio.Num(), ratio.Denom(), multiplier)
	if err := eval.Mul(ct, multiplier, ct); err != nil {
		return err
	}
	if err := eval.Rescale(ct, ct); err != nil {
		return err
	}
	ct.Scale = target
	return nil
}

// CheckGBFVBits uses the GBFV rule: center the coefficient phase, round
// (b-X^h)*phase/q0 coefficientwise, then evaluate X^h=b modulo b^D+1.
// It does not decode CKKS slots or trust the ciphertext scale metadata.
func CheckGBFVBits(params ckks.Parameters, decryptor *rlwe.Decryptor, ct *rlwe.Ciphertext, base, digits int, want []*big.Int) (BFVBitMetrics, error) {
	m := BFVBitMetrics{Total: len(want)}
	if ct == nil || ct.Level() != 0 || digits < 2 || params.N()%digits != 0 || len(want) > params.N()/digits {
		return m, fmt.Errorf("invalid GBFV bit check input")
	}
	h := params.N() / digits
	q := new(big.Int).SetUint64(params.Q()[0])
	b := big.NewInt(int64(base))
	p := new(big.Int).Exp(b, big.NewInt(int64(digits)), nil)
	p.Add(p, big.NewInt(1))
	pt := decryptor.DecryptNew(ct)
	rq := params.RingQ().AtLevel(0)
	if pt.IsNTT {
		rq.INTT(pt.Value, pt.Value)
	}
	phase := make([]*big.Int, params.N())
	for i := range phase {
		phase[i] = new(big.Int)
	}
	rq.PolyToBigintCentered(pt.Value, 1, phase)
	for slot := 0; slot < h; slot++ {
		value := new(big.Int)
		for j := digits - 1; j >= 0; j-- {
			num := new(big.Int).Mul(b, phase[j*h+slot])
			if j == 0 {
				num.Add(num, phase[(digits-1)*h+slot])
			} else {
				num.Sub(num, phase[(j-1)*h+slot])
			}
			digit := new(big.Int)
			bignum.DivRound(num, q, digit)
			value.Mul(value, b).Add(value, digit)
			diff := new(big.Int).Sub(num, new(big.Int).Mul(digit, q))
			noise, _ := new(big.Float).SetPrec(128).Quo(new(big.Float).SetInt(diff), new(big.Float).SetInt(q)).Float64()
			noise = math.Abs(noise)
			m.MaxNoise = math.Max(m.MaxNoise, noise)
			m.MeanNoise += noise / float64(params.N())
		}
		value.Mod(value, p)
		if slot < len(want) {
			if value.Cmp(want[slot]) == 0 {
				m.Exact++
			}
		} else if value.Sign() != 0 {
			m.InactiveFailures++
		}
	}
	return m, nil
}
