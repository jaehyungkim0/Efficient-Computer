package carrier

import (
	"fmt"

	"github.com/tuneinsight/lattigo/v6/core/rlwe"
	"github.com/tuneinsight/lattigo/v6/schemes/ckks"
	"github.com/tuneinsight/lattigo/v6/utils"
)

// NewRingPackingEvaluator creates keys and work buffers only at the active
// packing moduli. The caller remains responsible for checking the security
// of minLogN and Q[:levelQ+1]*P[:levelP+1].
func NewRingPackingEvaluator(params ckks.Parameters, sk *rlwe.SecretKey, minLogN, levelQ, levelP int) (*rlwe.RingPackingEvaluator, error) {
	if minLogN < 4 || minLogN > params.LogN() || levelQ < 0 || levelQ > params.MaxLevelQ() || levelP < 0 || levelP > params.MaxLevelP() || sk == nil || sk.LevelQ() < levelQ || sk.LevelP() < levelP || sk.Value.Q.N() != params.N() {
		return nil, fmt.Errorf("invalid active ring-packing parameters")
	}
	literal := params.ParametersLiteral()
	literal.Q, literal.P = literal.Q[:levelQ+1], literal.P[:levelP+1]
	active, err := ckks.NewParametersFromLiteral(literal)
	if err != nil {
		return nil, err
	}
	// The key generator maps every supplied RNS limb. Give it a matching
	// prefix copy, retaining exactly the same secret at the active moduli.
	activeSK := rlwe.NewSecretKey(active)
	activeSK.Value.CopyLvl(levelQ, levelP, sk.Value)
	epk := rlwe.EvaluationKeyParameters{LevelQ: utils.Pointy(levelQ), LevelP: utils.Pointy(levelP)}
	rpk := &rlwe.RingPackingEvaluationKey{}
	if minLogN < active.LogN() {
		ski, err := rpk.GenRingSwitchingKeys(&active, activeSK, minLogN, epk)
		if err != nil {
			return nil, err
		}
		rpk.GenRepackEvaluationKeys(rpk.Parameters[minLogN], ski[minLogN], epk)
		rpk.GenRepackEvaluationKeys(rpk.Parameters[active.LogN()], activeSK, epk)
	} else {
		rpk.Parameters = map[int]rlwe.ParameterProvider{active.LogN(): &active}
		rpk.GenRepackEvaluationKeys(&active, activeSK, epk)
	}
	return rlwe.NewRingPackingEvaluator(rpk), nil
}
