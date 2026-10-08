package carrier

import (
	"testing"

	"github.com/stretchr/testify/require"
	"github.com/tuneinsight/lattigo/v6/circuits/ckks/bootstrapping"
	"github.com/tuneinsight/lattigo/v6/circuits/ckks/dft"
	"github.com/tuneinsight/lattigo/v6/circuits/ckks/mod1"
	"github.com/tuneinsight/lattigo/v6/core/rlwe"
	"github.com/tuneinsight/lattigo/v6/ring"
	"github.com/tuneinsight/lattigo/v6/schemes/ckks"
	"github.com/tuneinsight/lattigo/v6/utils"
)

func TestCompactDecompositionBuffers(t *testing.T) {
	// Insecure small rings exercise the same multi-prime decomposition shape.
	params, err := ckks.NewParametersFromLiteral(ckks.ParametersLiteral{LogN: 10,
		LogQ: []int{40, 40, 40, 40, 40, 40, 40, 40, 40}, LogP: []int{40, 40, 40},
		LogDefaultScale: 30, Xs: ring.Ternary{H: 192}})
	require.NoError(t, err)
	kgen := rlwe.NewKeyGenerator(params)
	sk := kgen.GenSecretKeyNew()
	sparse := kgen.GenSecretKeyWithHammingWeightNew(32)
	up := kgen.GenEvaluationKeyNew(sk, sparse, rlwe.EvaluationKeyParameters{LevelQ: utils.Pointy(0), LevelP: utils.Pointy(0)})
	down := kgen.GenEvaluationKeyNew(sparse, sk)
	gal := params.GaloisElementForRotation(1)
	keys := rlwe.NewMemEvaluationKeySet(kgen.GenRelinearizationKeyNew(sk), kgen.GenGaloisKeyNew(gal, sk))
	fresh, compact := ckks.NewEvaluator(params, keys), ckks.NewEvaluator(params, keys)
	view := compact.WithKey(keys)
	require.NoError(t, CompactDecompositionBuffers(compact.Evaluator, keys, up, down))
	require.Len(t, compact.BuffDecompQP, 3)
	require.Len(t, view.BuffDecompQP, 3)

	for level := 0; level <= params.MaxLevelQ(); level++ {
		ct := ckks.NewCiphertext(params, 1, level)
		require.NoError(t, rlwe.NewEncryptor(params, sk).EncryptZero(ct))
		want, err := fresh.RotateNew(ct, 1)
		require.NoError(t, err)
		got := ct.CopyNew()
		compact.DecomposeNTT(level, params.MaxLevelP(), params.PCount(), ct.Value[1], true, compact.BuffDecompQP)
		require.NoError(t, compact.AutomorphismHoisted(level, ct, compact.BuffDecompQP, gal, got))
		require.Equal(t, want, got)
	}

	mp, err := mod1.NewParametersFromLiteral(params, mod1.ParametersLiteral{
		LevelQ: 8, LogScale: 40, Mod1Type: mod1.CosDiscrete, Mod1Degree: 31,
		DoubleAngle: 3, K: 16, LogMessageRatio: 4})
	require.NoError(t, err)
	btp := &bootstrapping.Evaluator{Parameters: bootstrapping.Parameters{
		BootstrappingParameters: params, ResidualParameters: params, EphemeralSecretWeight: 32,
		CoeffsToSlotsParameters: dft.MatrixLiteral{LogSlots: params.LogMaxSlots()}},
		Evaluator: fresh, Mod1Parameters: mp,
		EvaluationKeys: &bootstrapping.EvaluationKeys{MemEvaluationKeySet: keys, EvkDenseToSparse: up, EvkSparseToDense: down}}
	ct := ckks.NewCiphertext(params, 1, 0)
	require.NoError(t, rlwe.NewEncryptor(params, sk).EncryptZero(ct))
	want, err := btp.ModUp(ct.CopyNew())
	require.NoError(t, err)
	btp.Evaluator = compact
	got, err := btp.ModUp(ct.CopyNew())
	require.NoError(t, err)
	require.Equal(t, want, got, "unused scratch blocks must not change ModUp")

	// A P[0]-only key at the full Q modulus needs every original block.
	wide := kgen.GenEvaluationKeyNew(sk, sk, rlwe.EvaluationKeyParameters{LevelP: utils.Pointy(0)})
	require.Error(t, CompactDecompositionBuffers(compact.Evaluator, keys, wide))
	require.NoError(t, CompactDecompositionBuffers(fresh.Evaluator, keys, wide))
	require.Len(t, fresh.BuffDecompQP, params.QCount())
}
