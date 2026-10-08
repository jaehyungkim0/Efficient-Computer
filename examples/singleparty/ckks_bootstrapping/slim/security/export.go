// Run from the repository root: go run ./examples/singleparty/ckks_bootstrapping/slim/security
package main

import (
	"crypto/sha256"
	"encoding/json"
	"fmt"
	"math/bits"
	"os"

	"github.com/tuneinsight/lattigo/v6/ring"
	"github.com/tuneinsight/lattigo/v6/schemes/ckks"
)

type parameterSet struct {
	Name         string   `json:"name"`
	N            int      `json:"n"`
	Q            []uint64 `json:"Q"`
	P            []uint64 `json:"P"`
	LogQP        float64  `json:"log2_QP"`
	SecretWeight int      `json:"secret_weight"`
	Sigma        float64  `json:"sigma"`
	ErrorBound   float64  `json:"error_bound"`
	Source       string   `json:"source"`
	SourceSHA256 string   `json:"source_sha256"`
}

func repeat(x, n int) (out []int) {
	for i := 0; i < n; i++ {
		out = append(out, x)
	}
	return
}

func main() {
	const dir = "examples/singleparty/ckks_bootstrapping/slim/"
	var results []parameterSet
	add := func(name, source string, logQ, logP []int, scale int) {
		p, err := ckks.NewParametersFromLiteral(ckks.ParametersLiteral{LogN: 16, LogQ: logQ, LogP: logP, LogDefaultScale: scale, Xs: ring.Ternary{H: 192}})
		if err != nil {
			panic(err)
		}
		data, err := os.ReadFile(dir + source)
		if err != nil {
			panic(err)
		}
		xe := p.Xe().(ring.DiscreteGaussian)
		results = append(results, parameterSet{name, p.N(), p.Q(), p.P(), p.LogQP(), 192, xe.Sigma, xe.Bound, source, fmt.Sprintf("%x", sha256.Sum256(data))})
	}
	// These literals mirror the full-size experimental drivers, not -short.
	q := append([]int{50, 43, 43, 43}, repeat(50, 18)...)
	q = append(q, 47, 47, 47)
	add("bfv-65537-and-8179", "conv-btd-sign-65537.go", q, repeat(50, 5), 50)
	q = append([]int{54, 54, 54, 54, 43}, repeat(50, 18)...)
	q = append(q, 47, 47, 47)
	add("bfv-goldilocks", "conv-btd-goldilocks.go", q, repeat(50, 5), 50)
	for _, lambda := range []int{16, 64, 256, 1024} {
		d := lambda / 4
		packedDigitLog := bits.Len(uint(2*d)) - 1
		circuit := packedDigitLog + 3
		maxCircuit := (1548-68)/38 - 27
		if circuit > maxCircuit {
			circuit = maxCircuit
		}
		if d >= 256 && circuit > packedDigitLog {
			circuit = packedDigitLog
		}
		scale := (1548 - 68) / (27 + circuit)
		q = append([]int{scale + 4, scale}, repeat(scale, 3+circuit+6)...)
		q = append(q, repeat(scale+4, 11)...)
		add(fmt.Sprintf("gbfv-%d", lambda), "conv-gbfv-to-cpl25.go", q, repeat(scale+4, 5), scale)
	}
	e := json.NewEncoder(os.Stdout)
	e.SetIndent("", "  ")
	if err := e.Encode(results); err != nil {
		panic(err)
	}
}
