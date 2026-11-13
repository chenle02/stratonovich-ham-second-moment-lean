/-
Refutation for the support of the masks of `P:variational-remove-mask`
(`notes/integrated_unmasked_variational.tex` lines 185-189 at a284420),
package theorem `StratonovichHAMSecondMoment.RemoveMask.mask_eq_zero`
(`m_R = 0` on `|x| ≥ 2R`).

Wrong variant: support in the ball of radius `R` instead of `2R`, i.e.
`m_R(x) = 0` whenever `|x| ≥ R`.  Counterexample: `d = 1`, `R = 1`,
`x = e_0` with `|x| = 1`, where `m_1(x) = χ(1) = 1`.  `mask_support_contrast`
is the package theorem at `R = 1`, `|x| = 2`.  No junk-value reliance
(`R = 1 > 0`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.RemoveMask

set_option autoImplicit false

namespace Refutations.RemoveMask

open StratonovichHAMSecondMoment StratonovichHAMSecondMoment.RemoveMask

/-- Support of `m_R` inside the ball of radius `R` is false. -/
theorem mask_support_radius_refuted :
    ¬ (∀ R : ℝ, 0 < R → ∀ x : HomogHypothesis.Rd 1, R ≤ ‖x‖ → mask R x = 0) := by
  intro h
  have hx : ‖(EuclideanSpace.single 0 (1 : ℝ) : HomogHypothesis.Rd 1)‖ = 1 := by simp
  have h0 := h 1 one_pos _ hx.ge
  rw [mask_eq_one one_pos hx.le] at h0
  norm_num at h0

/-- The package support bound at `R = 1`, `|x| = 2`. -/
theorem mask_support_contrast :
    mask 1 (EuclideanSpace.single 0 (2 : ℝ) : HomogHypothesis.Rd 1) = 0 :=
  mask_eq_zero one_pos (by simp)

end Refutations.RemoveMask
