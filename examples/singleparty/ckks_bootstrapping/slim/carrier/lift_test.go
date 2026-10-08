package carrier

import (
	"math/big"
	"testing"

	"github.com/stretchr/testify/require"
	"github.com/tuneinsight/lattigo/v6/core/rlwe"
	"github.com/tuneinsight/lattigo/v6/ring"
	"github.com/tuneinsight/lattigo/v6/schemes/ckks"
	"github.com/tuneinsight/lattigo/v6/utils/bignum"
)

// These small-ring parameters test exact CRT lifting, not security.
func TestEncapsulatedLift(t *testing.T) {
	params, err := ckks.NewParametersFromLiteral(ckks.ParametersLiteral{LogN: 10,
		LogQ: []int{50, 50, 50, 50}, LogP: []int{50}, LogDefaultScale: 40, Xs: ring.Ternary{H: 192}})
	require.NoError(t, err)
	sk := rlwe.NewKeyGenerator(params).GenSecretKeyNew()
	for _, level := range []int{0, 1} {
		t.Run(string(rune('0'+level)), func(t *testing.T) {
			up, down, err := LiftKeys(params, sk, level, level+2, 32)
			require.NoError(t, err)
			require.Equal(t, level, up.LevelQ())
			require.Equal(t, 0, up.LevelP())
			ct := ckks.NewCiphertext(params, 1, level)
			ct.IsBatched = false
			require.NoError(t, rlwe.NewEncryptor(params, sk).EncryptZero(ct))
			out, err := Lift(params, ct, level+2, up, down)
			require.NoError(t, err)
			eval := rlwe.NewEvaluator(params, nil)
			shared, err := LiftWithEvaluator(params, eval, ct, level+2, up, down)
			require.NoError(t, err)
			require.Equal(t, out, shared, "buffer reuse must not change any ciphertext coefficient")
			_, err = LiftWithEvaluator(params, nil, ct, level+2, up, down)
			require.Error(t, err)
			require.Equal(t, ct.Scale, out.Scale)
			require.Equal(t, level, ct.Level())
			require.False(t, out.IsBatched)
			rq := params.RingQ().AtLevel(out.Level())
			pt := rlwe.NewDecryptor(params, sk).DecryptNew(out)
			rq.INTT(pt.Value, pt.Value)
			coefficients := make([]*big.Int, params.N())
			for i := range coefficients {
				coefficients[i] = new(big.Int)
			}
			rq.PolyToBigintCentered(pt.Value, 1, coefficients)
			q := params.RingQ().ModulusAtLevel[level]
			for _, c := range coefficients {
				lift := new(big.Int)
				bignum.DivRound(c, q, lift)
				// H=32 centered summands give the deterministic bound 16.5;
				// the small key-switching noise is negligible relative to q.
				require.LessOrEqual(t, new(big.Int).Abs(lift).Int64(), int64(17))
				noise := new(big.Int).Sub(c, new(big.Int).Mul(lift, q))
				require.Less(t, new(big.Int).Abs(noise).BitLen(), 20)
			}
		})
	}
}
