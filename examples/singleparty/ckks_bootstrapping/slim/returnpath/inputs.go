package returnpath

import "math/big"

// BoundaryValues supplements random inputs with zero, the largest residues,
// radix carry boundaries, and the two sides of the measured sign threshold.
func BoundaryValues(p *big.Int, signBit int) []*big.Int {
	values := []*big.Int{big.NewInt(0), big.NewInt(1), new(big.Int).Sub(p, big.NewInt(1)), new(big.Int).Sub(p, big.NewInt(2))}
	for i := 0; i < p.BitLen(); i++ {
		if i%4 != 0 && i != signBit {
			continue
		}
		power := new(big.Int).Lsh(big.NewInt(1), uint(i))
		for _, delta := range []int64{-1, 0, 1} {
			v := new(big.Int).Add(power, big.NewInt(delta))
			if v.Sign() >= 0 && v.Cmp(p) < 0 {
				values = append(values, v)
			}
		}
	}
	return values
}

// BoundaryRHS covers equality, less-than, and greater-than at the same edges.
func BoundaryRHS(lhs, p *big.Int, index int) *big.Int {
	rhs := new(big.Int).Set(lhs)
	switch index % 3 {
	case 1:
		rhs.Sub(rhs, big.NewInt(1))
	case 2:
		rhs.Add(rhs, big.NewInt(1))
	}
	return rhs.Mod(rhs, p)
}

// boundarySamples reserves at least half the batch for random inputs. Keep
// the four endpoint cases first, then sample carry edges across the bit range.
func boundarySamples(size int, p *big.Int) []*big.Int {
	boundaries := BoundaryValues(p, p.BitLen()-2)
	n := size / 2
	if n >= len(boundaries) {
		return boundaries
	}
	if n <= 4 {
		return boundaries[:n]
	}
	selected := append([]*big.Int(nil), boundaries[:4]...)
	remaining := n - 4
	for i := 0; i < remaining; i++ {
		index := len(boundaries) - 1
		if remaining > 1 {
			index = 4 + i*(len(boundaries)-5)/(remaining-1)
		}
		selected = append(selected, boundaries[index])
	}
	return selected
}

func AddBoundaryMessages(values []*big.Int, p *big.Int) {
	boundaries := boundarySamples(len(values), p)
	for i := range boundaries {
		values[i].Set(boundaries[i])
	}
}

func AddComparisonBoundaries(lhs, rhs []*big.Int, p *big.Int) {
	n := len(boundarySamples(len(lhs), p))
	for i := 0; i < n && i < len(lhs) && i < len(rhs); i++ {
		rhs[i].Set(BoundaryRHS(lhs[i], p, i))
	}
}
