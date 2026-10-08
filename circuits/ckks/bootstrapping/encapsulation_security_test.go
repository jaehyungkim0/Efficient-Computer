package bootstrapping

import (
	"testing"

	"github.com/stretchr/testify/require"
	"github.com/tuneinsight/lattigo/v6/core/rlwe"
	"github.com/tuneinsight/lattigo/v6/ring"
	"github.com/tuneinsight/lattigo/v6/schemes/ckks"
)

// This small test checks key structure, not the security of its test parameters.
func TestEncapsulationKeyModuli(t *testing.T) {
	params, err := ckks.NewParametersFromLiteral(ckks.ParametersLiteral{
		LogN: 10, LogQ: []int{40, 40, 40}, LogP: []int{40, 40},
		LogDefaultScale: 40, Xs: ring.Ternary{H: 192},
	})
	require.NoError(t, err)
	sk := rlwe.NewKeyGenerator(params).GenSecretKeyNew()
	btp := Parameters{BootstrappingParameters: params, EphemeralSecretWeight: 32}
	toSparse, toDense := btp.genEncapsulationEvaluationKeysNew(sk)
	// No public key may expose the sparse secret above its intended modulus.
	require.Equal(t, 0, toSparse.LevelQ())
	require.Equal(t, 0, toSparse.LevelP())
	require.Equal(t, params.MaxLevelQ(), toDense.LevelQ())
	require.Equal(t, params.MaxLevelP(), toDense.LevelP())

	ct := rlwe.NewCiphertext(params, 1, 0)
	require.NoError(t, rlwe.NewEncryptor(params, sk).EncryptZero(ct))
	eval := rlwe.NewEvaluator(params, nil)
	require.NoError(t, eval.ApplyEvaluationKey(ct, toSparse, ct))
	require.NoError(t, eval.ApplyEvaluationKey(ct, toDense, ct))
	pt := rlwe.NewDecryptor(params, sk).DecryptNew(ct)
	params.RingQ().AtLevel(0).INTT(pt.Value, pt.Value)
	require.Less(t, params.RingQ().AtLevel(0).Log2OfStandardDeviation(pt.Value), 12.0)

	// The full-modulus reverse key is encrypted under the dense secret.
	// Recover its encoded sparse plaintext only for this secret-key test.
	rq := params.RingQ()
	phase := rq.NewPoly()
	rq.MulCoeffsMontgomery(toDense.Value[0][0][1].Q, sk.Value.Q, phase)
	rq.Add(phase, toDense.Value[0][0][0].Q, phase)
	// At Q[2], outside the first P-sized gadget block, it encrypts zero.
	rq.IMForm(phase, phase)
	rq.INTT(phase, phase)
	q := params.Q()[2]
	for _, v := range phase.Coeffs[2] {
		if v > q/2 {
			v = q - v
		}
		require.LessOrEqual(t, v, uint64(20))
	}
}
