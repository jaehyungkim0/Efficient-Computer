// Package carrier provides the coefficient-ciphertext interface for conversion.
package carrier

import (
	"fmt"
	"math/big"

	"github.com/tuneinsight/lattigo/v6/core/rlwe"
	"github.com/tuneinsight/lattigo/v6/schemes/ckks"
)

// LiftKeys generates input-modulus encapsulation keys. The sparse output key
// is exposed only at Q[:baseLevel+1]*P[0]; the reverse key uses the dense secret.
// This generalizes the bootstrapper's one-prime encapsulation to CRT inputs.
func LiftKeys(params ckks.Parameters, dense *rlwe.SecretKey, baseLevel, targetLevel, weight int) (toSparse, toDense *rlwe.EvaluationKey, err error) {
	if baseLevel < 0 || targetLevel <= baseLevel || targetLevel > params.MaxLevel() || weight <= 0 || params.PCount() == 0 {
		return nil, nil, fmt.Errorf("invalid input-lift key parameters")
	}
	kgen := rlwe.NewKeyGenerator(params)
	sparse := kgen.GenSecretKeyWithHammingWeightNew(weight)
	levelP := 0
	toSparse = kgen.GenEvaluationKeyNew(dense, sparse, rlwe.EvaluationKeyParameters{LevelQ: &baseLevel, LevelP: &levelP})
	toDense = kgen.GenEvaluationKeyNew(sparse, dense, rlwe.EvaluationKeyParameters{LevelQ: &targetLevel, LevelP: &levelP})
	return
}

// Lift first switches at the original modulus, so the lifting polynomial is
// governed by the sparse secret, not the dense computation key. CRT centering
// is exact, and the two key switches do not change the scale or consume levels.
// No secret key or plaintext-dependent correction is used during evaluation.
func Lift(params ckks.Parameters, ct *rlwe.Ciphertext, targetLevel int, toSparse, toDense *rlwe.EvaluationKey) (*rlwe.Ciphertext, error) {
	return LiftWithEvaluator(params, rlwe.NewEvaluator(params, nil), ct, targetLevel, toSparse, toDense)
}

// LiftWithEvaluator reuses an existing evaluator's buffers. The evaluator must
// have matching parameters and must not be used concurrently with this call.
func LiftWithEvaluator(params ckks.Parameters, eval *rlwe.Evaluator, ct *rlwe.Ciphertext, targetLevel int, toSparse, toDense *rlwe.EvaluationKey) (*rlwe.Ciphertext, error) {
	if eval == nil || !params.GetRLWEParameters().Equal(eval.GetRLWEParameters()) {
		return nil, fmt.Errorf("input lift needs an evaluator with matching parameters")
	}
	if ct == nil || ct.Degree() != 1 || !ct.IsNTT || targetLevel <= ct.Level() || targetLevel > params.MaxLevel() {
		return nil, fmt.Errorf("invalid centered-lift ciphertext or target level")
	}
	if toSparse == nil || toDense == nil || toSparse.LevelQ() != ct.Level() || toDense.LevelQ() < targetLevel {
		return nil, fmt.Errorf("input lift needs encapsulation keys at the input and target levels")
	}
	work := ct.CopyNew()
	if err := eval.ApplyEvaluationKey(work, toSparse, work); err != nil {
		return nil, err
	}
	base, target := params.RingQ().AtLevel(work.Level()), params.RingQ().AtLevel(targetLevel)
	coefficients := make([]*big.Int, params.N())
	for i := range coefficients {
		coefficients[i] = new(big.Int)
	}
	out := ckks.NewCiphertext(params, 1, targetLevel)
	*out.MetaData = *ct.MetaData
	for i := range work.Value {
		base.INTT(work.Value[i], work.Value[i])
		base.PolyToBigintCentered(work.Value[i], 1, coefficients)
		target.SetCoefficientsBigint(coefficients, out.Value[i])
		target.NTT(out.Value[i], out.Value[i])
	}
	if err := eval.ApplyEvaluationKey(out, toDense, out); err != nil {
		return nil, err
	}
	return out, nil
}
