package returnpath

import (
	"math/big"
	"testing"

	"github.com/tuneinsight/lattigo/v6/circuits/ckks/dft"
	"github.com/tuneinsight/lattigo/v6/core/rlwe"
	"github.com/tuneinsight/lattigo/v6/schemes/ckks"
)

func TestBFVBitReturn(t *testing.T) {
	for _, bits := range []int{16, 64} {
		t.Run(big.NewInt(int64(bits)).String(), func(t *testing.T) {
			baseLevel := 0
			p := big.NewInt(65537)
			logQ := []int{50, 43, 43, 43, 50, 50, 50, 50, 50}
			if bits == 64 {
				baseLevel = 1
				p = new(big.Int).SetUint64(18446744069414584321)
				logQ = []int{54, 54, 54, 54, 43, 50, 50, 50, 50, 50}
			}
			// Small, explicitly insecure test-only ring; no experiment timings.
			params, err := ckks.NewParametersFromLiteral(ckks.ParametersLiteral{LogN: 10, LogQ: logQ, LogP: []int{50}, LogDefaultScale: 50})
			if err != nil {
				t.Fatal(err)
			}
			kgen := rlwe.NewKeyGenerator(params)
			sk := kgen.GenSecretKeyNew()
			literal := dft.MatrixLiteral{Type: dft.HomomorphicDecode, LogSlots: params.LogMaxSlots(), LevelQ: baseLevel + 4, LevelP: params.MaxLevelP(), Levels: []int{1, 1, 1}, LogBSGSRatio: 1}
			keys := rlwe.NewMemEvaluationKeySet(kgen.GenRelinearizationKeyNew(sk), kgen.GenGaloisKeysNew(literal.GaloisElements(params), sk)...)
			ret, err := NewBFVBitReturn(params, keys, baseLevel, p)
			if err != nil {
				t.Fatal(err)
			}
			values := make([]float64, params.MaxSlots())
			want := make([]*big.Int, len(values))
			for i := range values {
				want[i] = big.NewInt(int64((i / 3) % 2))
				values[i] = float64(want[i].Int64()) + float64(i%5-2)*1e-5
			}
			pt := ckks.NewPlaintext(params, baseLevel+6)
			if err = ckks.NewEncoder(params).Encode(values, pt); err != nil {
				t.Fatal(err)
			}
			ct, err := rlwe.NewEncryptor(params, sk).EncryptNew(pt)
			if err != nil {
				t.Fatal(err)
			}
			out, err := ret.Evaluate(ct)
			if err != nil {
				t.Fatal(err)
			}
			metrics, err := CheckBFVBits(params, rlwe.NewDecryptor(params, sk), out, p, want)
			if err != nil {
				t.Fatal(err)
			}
			if err = metrics.Report("unit test"); err != nil {
				t.Fatal(err)
			}
		})
	}
}
