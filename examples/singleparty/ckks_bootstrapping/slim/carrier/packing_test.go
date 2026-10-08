package carrier

import (
	"fmt"
	"math"
	"testing"

	"github.com/tuneinsight/lattigo/v6/core/rlwe"
	"github.com/tuneinsight/lattigo/v6/schemes/ckks"
)

func TestActiveRingPackingBuffers(t *testing.T) {
	// Small, insecure parameters test allocation levels and coefficient order.
	params, err := ckks.NewParametersFromLiteral(ckks.ParametersLiteral{
		LogN: 10, LogQ: []int{35, 35, 35, 35, 35, 35}, LogP: []int{36, 36}, LogDefaultScale: 25,
	})
	if err != nil {
		t.Fatal(err)
	}
	sk := rlwe.NewKeyGenerator(params).GenSecretKeyNew()
	for _, level := range []int{0, 1} {
		for _, minLogN := range []int{9, 10} {
			t.Run(fmt.Sprintf("level%d/logN%d", level, minLogN), func(t *testing.T) {
				packer, err := NewRingPackingEvaluator(params, sk, minLogN, level, 0)
				if err != nil {
					t.Fatal(err)
				}
				for logN, eval := range packer.Evaluators {
					p := eval.GetRLWEParameters()
					if p.MaxLevelQ() != level || p.MaxLevelP() != 0 || eval.BuffQP[0].LevelQ() != level || len(eval.BuffDecompQP) != level+1 {
						t.Fatalf("logN%d retains buffers above active packing moduli", logN)
					}
				}
				indices := []int{0, 1, 11, 32, 69, params.N()/2 + 13, params.N() - 1}
				values := make([]float64, params.N())
				selected := map[int]bool{}
				for i, index := range indices {
					values[index] = float64(i + 1)
					selected[index] = true
				}
				encoder := ckks.NewEncoder(params)
				pt := ckks.NewPlaintext(params, level)
				pt.IsBatched = false
				if err = encoder.Encode(values, pt); err != nil {
					t.Fatal(err)
				}
				ct, err := rlwe.NewEncryptor(params, sk).EncryptNew(pt)
				if err != nil {
					t.Fatal(err)
				}
				extracted, err := packer.ExtractNaive(ct, selected)
				if err != nil {
					t.Fatal(err)
				}
				permuted := map[int]*rlwe.Ciphertext{}
				want := make([]float64, params.N())
				for i, index := range indices {
					permuted[3*i] = extracted[index]
					want[3*i] = values[index]
				}
				out, err := packer.Repack(permuted)
				if err != nil {
					t.Fatal(err)
				}
				out.IsBatched = false
				got := make([]float64, params.N())
				if err = encoder.Decode(rlwe.NewDecryptor(params, sk).DecryptNew(out), got); err != nil {
					t.Fatal(err)
				}
				for i := range got {
					if math.Abs(got[i]-want[i]) > 0.01 {
						t.Fatalf("coefficient%d: got%g want%g", i, got[i], want[i])
					}
				}
			})
		}
	}
}
