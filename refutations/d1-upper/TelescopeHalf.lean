/-
Refutation for the increment sum on the time simplices used in the proof of
`P:d1-upper` (main TeX lines 5486-5487 at edf7085f: "the increments sum to the
two terminal times and therefore to at most `2t`").  Package theorem
`StratonovichHAMSecondMoment.TwoSimplexTime.sum_incr_le` (shared with
`P:low-alpha-upper` since the L13 integration; used by `D1Upper`).

Wrong variant: the increments sum to at most `t` (one chain's worth).
Counterexample in the manuscript domain: `m = n = 1`, `t = 1`,
`s = (4/5, 4/5)`: each chain has its own root, so the increments are
`4/5, 4/5`, with sum `8/5 > 1`.  `telescopeHalf_contrast` is the package bound
`2t`.  Class (a): manuscript-claim perturbation in the manuscript domain.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.D1Upper

set_option autoImplicit false

open StratonovichHAMSecondMoment DiagramModel D1Upper
open StratonovichHAMSecondMoment.TwoSimplexTime (sum_incr_le)

namespace Refutations.D1Upper.TelescopeHalf

/-- The witness lies in `[0,1]^1_< × [0,1]^1_<`. -/
theorem witness_mem : (![4 / 5, 4 / 5] : Fin (1 + 1) → ℝ) ∈ twoSimplex 1 1 1 := by
  intro i
  fin_cases i <;> simp [predVal, pred] <;> norm_num

/-- Its increments sum to `8/5`. -/
theorem witness_sum : ∑ i, incr 1 (![4 / 5, 4 / 5] : Fin (1 + 1) → ℝ) i = 8 / 5 := by
  simp [incr, predVal, pred, Fin.sum_univ_two]
  norm_num

/-- The package: the increments sum to at most `2t`. -/
theorem telescopeHalf_contrast : ∀ t : ℝ, 0 < t → ∀ s : Fin (1 + 1) → ℝ,
    s ∈ twoSimplex 1 1 t → ∑ i, incr 1 s i ≤ 2 * t :=
  fun _ ht _ hs => sum_incr_le ht.le hs

/-- The bound `t` in place of `2t` is false. -/
theorem telescopeHalf_refuted : ¬ (∀ t : ℝ, 0 < t → ∀ s : Fin (1 + 1) → ℝ,
    s ∈ twoSimplex 1 1 t → ∑ i, incr 1 s i ≤ t) := by
  intro H
  have := H 1 one_pos _ witness_mem
  rw [witness_sum] at this
  norm_num at this

end Refutations.D1Upper.TelescopeHalf
