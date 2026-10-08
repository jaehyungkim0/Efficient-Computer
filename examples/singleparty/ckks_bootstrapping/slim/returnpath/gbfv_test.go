package returnpath

import (
	"fmt"
	"math/big"
	"testing"

	"github.com/tuneinsight/lattigo/v6/core/rlwe"
	"github.com/tuneinsight/lattigo/v6/examples/singleparty/ckks_bootstrapping/slim/carrier"
	"github.com/tuneinsight/lattigo/v6/schemes/ckks"
	"github.com/tuneinsight/lattigo/v6/utils"
)

func TestGBFVBitReturn(t *testing.T) {
	for _, digits := range []int{4, 16, 64, 256} {
		for _, blocks := range []int{1, 8} {
			t.Run(fmt.Sprintf("D%d/blocks%d", digits, blocks), func(t *testing.T) {
				// Explicitly insecure unit-test parameters, including ring switching.
				params, err := ckks.NewParametersFromLiteral(ckks.ParametersLiteral{LogN: 11, LogQ: []int{48, 44, 44, 44, 44, 44, 44, 44}, LogP: []int{48}, LogDefaultScale: 44})
				if err != nil {
					t.Fatal(err)
				}
				kgen := rlwe.NewKeyGenerator(params)
				sk := kgen.GenSecretKeyNew()
				literal := GBFVReturnDFT(params)
				galKeys := kgen.GenGaloisKeysNew(literal.GaloisElements(params), sk, rlwe.EvaluationKeyParameters{
					LevelQ: utils.Pointy(literal.LevelQ), LevelP: utils.Pointy(literal.LevelP),
				})
				for _, key := range galKeys {
					if key.LevelQ() != literal.LevelQ {
						t.Fatalf("return-only key level: got %d, want %d", key.LevelQ(), literal.LevelQ)
					}
				}
				keys := rlwe.NewMemEvaluationKeySet(kgen.GenRelinearizationKeyNew(sk), galKeys...)
				packer, err := carrier.NewRingPackingEvaluator(params, sk, 9, 1, 0)
				if err != nil {
					t.Fatal(err)
				}
				batch := params.N() / digits / 8
				eval := ckks.NewEvaluator(params, keys)
				ret, err := NewGBFVBitReturnWithEvaluator(params, eval, packer, 16, digits, batch)
				if err != nil {
					t.Fatal(err)
				}
				if ret.eval != eval {
					t.Fatal("return converter did not reuse the supplied evaluator")
				}
				bits := make([]*rlwe.Ciphertext, blocks)
				want := make([]*big.Int, blocks*batch)
				for block := range bits {
					values := make([]float64, params.MaxSlots())
					for slot := range values {
						values[slot] = float64((block*batch+slot%batch)/3%2) + float64(slot%5-2)*1e-5
					}
					for slot := 0; slot < batch; slot++ {
						want[block*batch+slot] = big.NewInt(int64((block*batch + slot) / 3 % 2))
					}
					pt := ckks.NewPlaintext(params, 7)
					if err = ckks.NewEncoder(params).Encode(values, pt); err != nil {
						t.Fatal(err)
					}
					if bits[block], err = rlwe.NewEncryptor(params, sk).EncryptNew(pt); err != nil {
						t.Fatal(err)
					}
				}
				out, err := ret.Evaluate(bits)
				if err != nil {
					t.Fatal(err)
				}
				m, err := CheckGBFVBits(params, rlwe.NewDecryptor(params, sk), out, 16, digits, want)
				if err != nil {
					t.Fatal(err)
				}
				if m.Exact != m.Total || m.InactiveFailures != 0 || m.MaxNoise > 1e-3 {
					t.Fatalf("GBFV round trip: %+v", m)
				}
			})
		}
	}
}
