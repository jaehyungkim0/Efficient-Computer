package returnpath

import (
	"fmt"
	"math/big"
	"testing"

	"github.com/stretchr/testify/require"
)

func TestBoundarySamplesPreserveRandomInputs(t *testing.T) {
	for _, bits := range []uint{16, 64, 256, 1024} {
		p := new(big.Int).Add(new(big.Int).Lsh(big.NewInt(1), bits), big.NewInt(1))
		for _, size := range []int{0, 1, 2, 8, 16, 32, 256, 4096} {
			t.Run(fmt.Sprintf("bits=%d/size=%d", bits, size), func(t *testing.T) {
				left, right := make([]*big.Int, size), make([]*big.Int, size)
				initial := new(big.Int).Quo(p, big.NewInt(3))
				for i := range left {
					left[i], right[i] = new(big.Int).Set(initial), new(big.Int).Set(initial)
				}
				selected := boundarySamples(size, p)
				require.LessOrEqual(t, len(selected), size/2)
				AddBoundaryMessages(left, p)
				AddComparisonBoundaries(left, right, p)
				for i := range left {
					if i < len(selected) {
						require.Zero(t, left[i].Cmp(selected[i]))
						require.Zero(t, right[i].Cmp(BoundaryRHS(left[i], p, i)))
					} else {
						require.Zero(t, left[i].Cmp(initial))
						require.Zero(t, right[i].Cmp(initial))
					}
				}
				if len(selected) >= 4 {
					for i, want := range BoundaryValues(p, p.BitLen()-2)[:4] {
						require.Zero(t, selected[i].Cmp(want))
					}
				}
				if len(selected) > 5 {
					require.LessOrEqual(t, selected[4].BitLen(), 4)
					require.GreaterOrEqual(t, selected[len(selected)-1].BitLen(), int(bits)-1)
				}
			})
		}
	}
}
