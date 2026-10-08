package main

import (
	"math"
	"math/cmplx"
	"testing"

	"github.com/stretchr/testify/require"
	"github.com/tuneinsight/lattigo/v6/core/rlwe"
	"github.com/tuneinsight/lattigo/v6/schemes/ckks"
)

// Run explicitly with conv-gbfv-to-cpl25.go; the directory has multiple demos.
func TestLeveledCarrySymbolCleaning(t *testing.T) {
	params, err := ckks.NewParametersFromLiteral(ckks.ParametersLiteral{
		LogN: 10, LogQ: []int{48, 44, 44, 44}, LogP: []int{48}, LogDefaultScale: 44})
	require.NoError(t, err)
	kgen := rlwe.NewKeyGenerator(params)
	sk := kgen.GenSecretKeyNew()
	keys := rlwe.NewMemEvaluationKeySet(kgen.GenRelinearizationKeyNew(sk),
		kgen.GenGaloisKeyNew(params.GaloisElementForComplexConjugation(), sk))
	encoder := ckks.NewEncoder(params)
	cc := PackedRadixContext{params: &params, eval: ckks.NewEvaluator(params, keys), encoder: encoder}
	values, symbols := make([]complex128, params.MaxSlots()), []complex128{0, 0.5, 1i}
	for i := range values {
		dr, di := float64(i%17-8)/800, float64((i/17)%17-8)/800
		values[i] = symbols[i%3] + complex(dr, di)
	}
	pt := ckks.NewPlaintext(params, params.MaxLevel())
	require.NoError(t, encoder.Encode(values, pt))
	ct, err := rlwe.NewEncryptor(params, sk).EncryptNew(pt)
	require.NoError(t, err)
	unchanged := ct.CopyNew()
	clean, err := cleanPackedCarrySymbols(ct, cc)
	require.NoError(t, err)
	require.Equal(t, ct.Level()-2, clean.Level())
	require.InDelta(t, params.DefaultScale().Log2(), clean.Scale.Log2(), 1e-6)
	require.Equal(t, unchanged, ct)
	got := decodeCiphertext(params, clean, rlwe.NewDecryptor(params, sk), encoder)
	for i, z := range values {
		r, v := real(z), imag(z)
		want := complex(6*r*r-8*r*r*r, 3*v*v-2*v*v*v)
		require.Less(t, cmplx.Abs(got[i]-want), 1e-7)
		e := cmplx.Abs(z - symbols[i%3])
		// Coordinate errors are at most e. This bounds both cubic residuals.
		bound := math.Hypot(6*e*e+8*e*e*e, 3*e*e+2*e*e*e)
		require.LessOrEqual(t, cmplx.Abs(got[i]-symbols[i%3]), bound+1e-7)
	}
	_, err = cleanPackedCarrySymbols(nil, cc)
	require.Error(t, err)
}
