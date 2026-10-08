// Package returnpath implements the coefficient-encoded outputs of the paper's
// comparison and sign experiments. Evaluation never receives a secret key.
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

// BFVBitReturn converts N/2 real CKKS bits to the first N/2 BFV coefficients,
// in the same bit-reversed order as the input carriers. The upper half is zero.
type BFVBitReturn struct {
	params      ckks.Parameters
	eval        *ckks.Evaluator
	dft         *dft.Evaluator
	matrix      dft.Matrix
	outputLevel int
	outputScale rlwe.Scale
}

func NewBFVBitReturn(params ckks.Parameters, keys rlwe.EvaluationKeySet, outputLevel int, p *big.Int) (*BFVBitReturn, error) {
	if outputLevel < 0 || outputLevel+6 > params.MaxLevel() || p == nil || p.Sign() <= 0 {
		return nil, fmt.Errorf("invalid BFV return level or plaintext modulus")
	}
	eval := ckks.NewEvaluator(params, keys)
	literal := dft.MatrixLiteral{
		Type: dft.HomomorphicDecode, LogSlots: params.LogMaxSlots(),
		LevelQ: outputLevel + 4, LevelP: params.MaxLevelP(),
		LogBSGSRatio: 1, Levels: []int{1, 1, 1},
	}
	for _, galEl := range literal.GaloisElements(params) {
		if _, err := keys.GetGaloisKey(galEl); err != nil {
			return nil, fmt.Errorf("BFV return DFT key: %w", err)
		}
	}
	matrix, err := dft.NewMatrixFromLiteral(params, literal, ckks.NewEncoder(params))
	if err != nil {
		return nil, err
	}
	q := params.RingQ().ModulusAtLevel[outputLevel]
	scale := new(big.Float).SetPrec(192).Quo(new(big.Float).SetPrec(192).SetInt(q), new(big.Float).SetPrec(192).SetInt(p))
	if scale.Cmp(big.NewFloat(1)) <= 0 {
		return nil, fmt.Errorf("BFV output modulus must exceed plaintext modulus")
	}
	return &BFVBitReturn{params: params, eval: eval, dft: dft.NewEvaluator(params, eval), matrix: matrix, outputLevel: outputLevel, outputScale: rlwe.NewScale(scale)}, nil
}

// CleanBit evaluates h(x)=x^2(3-2x), spending two levels and no bootstrapping.
func CleanBit(eval *ckks.Evaluator, ct *rlwe.Ciphertext) (*rlwe.Ciphertext, error) {
	if ct == nil || ct.Level() < 2 {
		return nil, fmt.Errorf("bit cleaning needs two levels")
	}
	square, err := eval.MulRelinNew(ct, ct)
	if err != nil {
		return nil, err
	}
	if err = eval.Rescale(square, square); err != nil {
		return nil, err
	}
	factor, err := eval.MulNew(ct, -2)
	if err != nil {
		return nil, err
	}
	if err = eval.Add(factor, 3, factor); err != nil {
		return nil, err
	}
	clean, err := eval.MulRelinNew(square, factor)
	if err != nil {
		return nil, err
	}
	if err = eval.Rescale(clean, clean); err != nil {
		return nil, err
	}
	return clean, nil
}

func (r *BFVBitReturn) Evaluate(bit *rlwe.Ciphertext) (*rlwe.Ciphertext, error) {
	if bit == nil || bit.Level() < r.matrix.LevelQ+2 {
		return nil, fmt.Errorf("BFV return needs level %d before cleaning", r.matrix.LevelQ+2)
	}
	clean, err := CleanBit(r.eval, bit)
	if err != nil {
		return nil, err
	}
	coeff, err := r.dft.SlotsToCoeffsNew(clean, nil, r.matrix)
	if err != nil {
		return nil, err
	}
	coeff.IsBatched = false
	// SetScale performs actual public multiplication and rescaling, not just
	// a metadata change. One adjustment prime remains after the DFT.
	if err = r.eval.SetScale(coeff, r.outputScale); err != nil {
		return nil, err
	}
	if coeff.Level() != r.outputLevel {
		return nil, fmt.Errorf("BFV return ended at level %d, expected %d", coeff.Level(), r.outputLevel)
	}
	return coeff, nil
}

// BFVBitMetrics is computed outside the homomorphic timer. Noise is measured
// before rounding, in plaintext units; InactiveFailures covers all upper zeros.
type BFVBitMetrics struct {
	Exact, Total, InactiveFailures int
	MaxNoise, MeanNoise            float64
}

// CheckBFVBits decrypts with round(p * phase / q) mod p using exact integers.
// It deliberately ignores CKKS scale metadata and slot decoding.
func CheckBFVBits(params ckks.Parameters, decryptor *rlwe.Decryptor, ct *rlwe.Ciphertext, p *big.Int, want []*big.Int) (BFVBitMetrics, error) {
	m := BFVBitMetrics{Total: len(want)}
	if ct == nil || len(want) != params.MaxSlots() {
		return m, fmt.Errorf("BFV bit check expects N/2 values")
	}
	pt := decryptor.DecryptNew(ct)
	ringQ := params.RingQ().AtLevel(ct.Level())
	if pt.IsNTT {
		ringQ.INTT(pt.Value, pt.Value)
	}
	phase := make([]*big.Int, params.N())
	ringQ.PolyToBigint(pt.Value, 1, phase)
	q := ringQ.ModulusAtLevel[ct.Level()]
	for pos, a := range phase {
		expected := new(big.Int)
		if pos < params.MaxSlots() {
			expected.Set(want[int(utils.BitReverse64(uint64(pos), params.LogMaxSlots()))])
		}
		numerator := new(big.Int).Mul(a, p)
		decoded := new(big.Int)
		bignum.DivRound(numerator, q, decoded)
		decoded.Mod(decoded, p)
		if pos < params.MaxSlots() {
			if decoded.Cmp(expected) == 0 {
				m.Exact++
			}
		} else if decoded.Sign() != 0 {
			m.InactiveFailures++
		}
		// Center the phase error modulo q before dividing by q/p.
		diff := new(big.Int).Sub(numerator, new(big.Int).Mul(expected, q))
		period := new(big.Int).Mul(q, p)
		diff.Mod(diff, period)
		if new(big.Int).Lsh(new(big.Int).Set(diff), 1).Cmp(period) > 0 {
			diff.Sub(diff, period)
		}
		noise, _ := new(big.Float).SetPrec(192).Quo(new(big.Float).SetPrec(192).SetInt(diff), new(big.Float).SetPrec(192).SetInt(q)).Float64()
		noise = math.Abs(noise)
		m.MaxNoise = math.Max(m.MaxNoise, noise)
		m.MeanNoise += noise / float64(params.N())
	}
	return m, nil
}

func (m BFVBitMetrics) Report(label string) error {
	fmt.Printf("Final BFV %s coefficients: %d/%d; nonzero inactive coefficients=%d\n", label, m.Exact, m.Total, m.InactiveFailures)
	fmt.Printf("Final BFV %s decoded noise: max Log2=%g, mean Log2=%g\n", label, math.Log2(m.MaxNoise), math.Log2(m.MeanNoise))
	if m.Exact != m.Total || m.InactiveFailures != 0 || m.MaxNoise >= 0.5 {
		return fmt.Errorf("final BFV %s decryption check failed", label)
	}
	return nil
}
