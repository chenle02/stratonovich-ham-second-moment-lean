/-
Refutation for the monotonicity of the masks of `P:variational-remove-mask`
(`notes/integrated_unmasked_variational.tex` line 191 at a284420), package
theorem `StratonovichHAMSecondMoment.RemoveMask.mask_mono`
(`m_R ≤ m_{R'}` for `0 < R ≤ R'`).

Wrong variant: the hypothesis `0 < R` dropped.  Counterexample: `d = 1`,
`R = -1`, `R' = 1`, `x = 3 e_0`: `m_{-1}(x) = χ(-3) = 1` and
`m_1(x) = χ(3) = 0`.  `mask_sign_contrast` is the package theorem at
`R = 1`, `R' = 2`.  No junk-value reliance (the division `|x|/R` is by
`R = -1 ≠ 0`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.RemoveMask

set_option autoImplicit false

namespace Refutations.RemoveMask

open StratonovichHAMSecondMoment StratonovichHAMSecondMoment.RemoveMask

/-- Monotonicity of `R ↦ m_R(x)` over all real `R` is false. -/
theorem mask_mono_all_real_refuted :
    ¬ (∀ R R' : ℝ, R ≤ R' → ∀ x : HomogHypothesis.Rd 1, mask R x ≤ mask R' x) := by
  intro h
  have hx : ‖(EuclideanSpace.single 0 (3 : ℝ) : HomogHypothesis.Rd 1)‖ = 3 := by simp
  have h1 := h (-1) 1 (by norm_num) (EuclideanSpace.single 0 (3 : ℝ))
  have e1 : mask (-1) (EuclideanSpace.single 0 (3 : ℝ) : HomogHypothesis.Rd 1) = 1 := by
    rw [mask, hx]; exact chi_eq_one (by norm_num)
  have e2 : mask 1 (EuclideanSpace.single 0 (3 : ℝ) : HomogHypothesis.Rd 1) = 0 :=
    mask_eq_zero one_pos (by rw [hx]; norm_num)
  rw [e1, e2] at h1
  norm_num at h1

/-- The package monotonicity at `R = 1 ≤ R' = 2`. -/
theorem mask_sign_contrast (x : HomogHypothesis.Rd 1) : mask 1 x ≤ mask 2 x :=
  mask_mono one_pos (by norm_num) x

end Refutations.RemoveMask
