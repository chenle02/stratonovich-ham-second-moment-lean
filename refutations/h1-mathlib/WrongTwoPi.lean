/-
Refutation for the norm convention of the `H^1` identification (wave L13, item
K5a), package theorem `StratonovichHAMSecondMoment.H1Mathlib.norm_toH1_sq`.

Manuscript side: the manuscript's `H^1` norm is `‖u‖₂² + ‖∇u‖₂²`
(`notes/integrated_signed_static.tex`, `P:signed-closed-form`, line 85 at
edf7085f: `q_V = z² - b² - v_V(u,u)` with `z = ‖u‖_{H^1}`, `b = ‖u‖₂`, i.e.
`‖∇u‖₂² = z² - b²`), on the real profiles of the main TeX lines 748-750.

Wrong variant: Mathlib's bundled `H^{1}(ℝ^d)` norm is the manuscript norm,
`‖f‖²_{H^{1}} = ‖f‖₂² + ‖∇f‖₂²` (no `2π` factor). Counterexample: `d = 1`,
the test function `cutoff 0` (equal to `1` on the unit ball), whose gradient
energy is positive (`integral_norm_grad_sq_pos`); the true value carries the
factor `(2π)⁻² < 1`. Class (a): perturbation of the manuscript norm claim in
the manuscript domain (a real `H^1` profile). `wrong_two_pi_contrast` is the
package identity with `(2π)⁻²`.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.H1Mathlib

set_option autoImplicit false

namespace Refutations.H1Mathlib

open StratonovichHAMSecondMoment StratonovichHAMSecondMoment.H1Mathlib
open StratonovichHAMSecondMoment.WeakSobolev MeasureTheory
open HomogHypothesis (Rd)
open VariationalFloor (grad)
open scoped Real

/-- The test function `χ(x) = cutBump(x)`, equal to one on the unit ball of `ℝ¹`. -/
theorem cutoff_test : IsTestFunction (H1Density.cutoff (d := 1) 0) :=
  ⟨H1Density.cutoff_contDiff 0, H1Density.cutoff_hasCompactSupport 0⟩

theorem cutoff_ne_zero : ∃ x : Rd 1, H1Density.cutoff 0 x ≠ 0 :=
  ⟨0, by rw [H1Density.cutoff_eq_one (by simp)]; norm_num⟩

/-- Mathlib's `H^1` norm is not the manuscript's `‖f‖₂² + ‖∇f‖₂²`. -/
theorem wrong_two_pi :
    ¬ ∀ (f : Rd 1 → ℝ) (h : MemH1 f) (g : Rd 1 → Rd 1), MemLp g 2 volume →
      HasWeakGradient f g → ‖toH1 h‖ ^ 2 = (∫ x, f x ^ 2) + ∫ x, ‖g x‖ ^ 2 := by
  intro H
  have hT := cutoff_test
  have h1 := H _ (memH1_of_test hT) _ (VariationalFloor.memLp_grad hT)
    (VariationalFloor.hasWeakGradient_of_test hT)
  have h2 := norm_toH1_sq (memH1_of_test hT) (VariationalFloor.memLp_grad hT)
    (VariationalFloor.hasWeakGradient_of_test hT)
  have hB := integral_norm_grad_sq_pos hT one_pos cutoff_ne_zero
  have hpi : 1 < (2 * π) ^ 2 := by nlinarith [Real.pi_gt_three]
  have hc : ((2 * π) ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hpi
  rw [h1] at h2
  change (∫ x, H1Density.cutoff 0 x ^ 2) + ∫ x, ‖grad (H1Density.cutoff 0) x‖ ^ 2 =
    (∫ x, H1Density.cutoff 0 x ^ 2) +
      ((2 * π) ^ 2)⁻¹ * ∫ x, ‖grad (H1Density.cutoff 0) x‖ ^ 2 at h2
  nlinarith

/-- Contrast: the package identity, with Mathlib's factor `(2π)⁻²`. -/
theorem wrong_two_pi_contrast :
    ∀ (f : Rd 1 → ℝ) (h : MemH1 f) (g : Rd 1 → Rd 1), MemLp g 2 volume →
      HasWeakGradient f g →
        ‖toH1 h‖ ^ 2 = (∫ x, f x ^ 2) + ((2 * π) ^ 2)⁻¹ * ∫ x, ‖g x‖ ^ 2 :=
  fun _ h _ hg hw => norm_toH1_sq h hg hw

end Refutations.H1Mathlib
