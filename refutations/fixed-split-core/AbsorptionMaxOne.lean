/-
Refutation for the absorption into `C_split` (`E:split-explicit-constant`,
main TeX lines 4043-4046 at 39f2597a), package theorem
`StratonovichHAMSecondMoment.FixedSplitCore.beforeFactor_le`
(`beforeFactor ≤ (max{1, 12δ^{-2}} R)^{k_i} splitFactor`).

Wrong variant: dropping the `max{1, ·}`, i.e. the constant `12δ^{-2}` alone.
Counterexample: a cross color (`k_i = 1`, `(r_i, q_i) = (1, 1)`) with
`α = 2`, `σ = h = R = λ = 1` and `δ = 4`: the left side is `1` and the
right side is `12/16`.  `absorption_contrast` is the package bound at the
same point.  No junk-value reliance (`λ^{α-2} = 1^0 = 1`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.FixedSplitCore

set_option autoImplicit false

namespace Refutations.FixedSplitCore

open StratonovichHAMSecondMoment.FixedSplitCore StratonovichHAMSecondMoment.IntervalScalar

/-- `C_split` without `max{1, ·}` does not absorb a cross color. -/
theorem absorption_max_one_refuted :
    ¬ (∀ (alpha δ R σ h lam : ℝ) (κ : ℕ) (p : ℕ × ℕ), 0 < δ → 0 < σ → 0 < R → 0 < h →
        0 < lam → alpha ≤ 3 →
        beforeFactor alpha δ R σ h lam κ p ≤
          (12 / δ ^ 2 * R) ^ κ * splitFactor alpha σ h lam κ p) := by
  intro hall
  have h1 := hall 2 4 1 1 1 1 1 (1, 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  simp [beforeFactor, splitFactor] at h1
  norm_num at h1

/-- The package bound at the same point. -/
theorem absorption_contrast :
    beforeFactor 2 4 1 1 1 1 1 (1, 1) ≤
      (max 1 (12 / (4 : ℝ) ^ 2) * 1) ^ 1 * splitFactor 2 1 1 1 1 (1, 1) :=
  beforeFactor_le 2 4 1 1 1 1 1 (1, 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

end Refutations.FixedSplitCore
