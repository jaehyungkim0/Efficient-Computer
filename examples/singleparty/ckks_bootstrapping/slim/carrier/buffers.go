package carrier

import (
	"fmt"

	"github.com/tuneinsight/lattigo/v6/core/rlwe"
	"github.com/tuneinsight/lattigo/v6/ring/ringqp"
)

// CompactDecompositionBuffers retains the scratch blocks needed by a fixed
// evaluation-key set, including explicitly supplied encapsulation keys. The
// caller must list every key used with this evaluator, including WithKey views,
// and must not subsequently use a larger decomposition or replace these keys.
// No key, modulus, or ciphertext is modified. Call only before evaluation.
func CompactDecompositionBuffers(eval *rlwe.Evaluator, keys rlwe.EvaluationKeySet, extra ...*rlwe.EvaluationKey) error {
	if eval == nil || keys == nil {
		return fmt.Errorf("buffer compaction requires an evaluator and its complete key set")
	}
	p := eval.GetRLWEParameters()
	needed := p.BaseRNSDecompositionVectorSize(p.MaxLevelQ(), p.MaxLevelP())
	include := func(key *rlwe.GadgetCiphertext) error {
		if key == nil || key.LevelQ() > p.MaxLevelQ() || key.LevelP() > p.MaxLevelP() {
			return fmt.Errorf("evaluation key exceeds evaluator moduli")
		}
		count := p.BaseRNSDecompositionVectorSize(key.LevelQ(), key.LevelP())
		if count != len(key.Value) {
			return fmt.Errorf("unexpected evaluation-key decomposition")
		}
		if count > needed {
			needed = count
		}
		return nil
	}
	rlk, err := keys.GetRelinearizationKey()
	if err != nil {
		return err
	}
	if err = include(&rlk.GadgetCiphertext); err != nil {
		return err
	}
	for _, galEl := range keys.GetGaloisKeysList() {
		key, err := keys.GetGaloisKey(galEl)
		if err != nil {
			return err
		}
		if err = include(&key.GadgetCiphertext); err != nil {
			return err
		}
	}
	for _, key := range extra {
		if key == nil {
			return fmt.Errorf("nil explicit evaluation key")
		}
		if err = include(&key.GadgetCiphertext); err != nil {
			return err
		}
	}
	if needed > len(eval.BuffDecompQP) {
		return fmt.Errorf("evaluation keys need %d scratch blocks, evaluator has %d", needed, len(eval.BuffDecompQP))
	}
	// Copy the slice itself so the old backing array cannot retain unused
	// polynomial buffers. Existing blocks remain unchanged and full-sized.
	eval.BuffDecompQP = append([]ringqp.Poly(nil), eval.BuffDecompQP[:needed]...)
	return nil
}
