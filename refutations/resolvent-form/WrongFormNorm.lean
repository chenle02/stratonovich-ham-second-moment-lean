/-
Refutation for the norm used in the form bounds (wave L13, item K5b), package theorems
`StratonovichHAMSecondMoment.ResolventForm.msNormSq_toH1` and `signed_form_bounds`.

Manuscript side: `E:signed-form-bounds` (`notes/integrated_signed_static.tex`, lines 58-59 at
39f2597a) is stated in the manuscript norm `z² = ‖u‖₂² + ‖∇u‖₂²` (line 85), not in Mathlib's
`H^{1}` norm (wave L13 decision 5).

Wrong variant: the manuscript norm `msNormSq` of a real `H^1` profile equals Mathlib's
`‖toH1 h‖²`. Counterexample: `d = 1`, the test function `cutoff 0`, whose gradient energy is
positive; Mathlib's norm carries `(2π)⁻²` in front of it. Class (a): perturbation of the norm in
which the manuscript's form bounds are stated, on a real profile of the manuscript domain.
`wrong_form_norm_contrast` is the package identity `z² = ∫ f² + ∫ ‖g‖²`.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.ResolventForm

set_option autoImplicit false

namespace Refutations.ResolventForm

open StratonovichHAMSecondMoment StratonovichHAMSecondMoment.ResolventForm
open StratonovichHAMSecondMoment.H1Mathlib StratonovichHAMSecondMoment.WeakSobolev MeasureTheory
open HomogHypothesis (Rd)
open VariationalFloor (grad)
open scoped Real BesselPotentialSpace

/-- The test function `cutoff 0` on `ℝ¹`. -/
theorem cutoff_test' : IsTestFunction (H1Density.cutoff (d := 1) 0) :=
  ⟨H1Density.cutoff_contDiff 0, H1Density.cutoff_hasCompactSupport 0⟩

/-- The manuscript norm of the form bounds is not Mathlib's `H^{1}` norm. -/
theorem wrong_form_norm :
    ¬ ∀ (f : Rd 1 → ℝ) (h : MemH1 f), msNormSq (toH1 h) = ‖toH1 h‖ ^ 2 := by
  intro H
  have hT := cutoff_test'
  have hne : ∃ x : Rd 1, H1Density.cutoff 0 x ≠ 0 :=
    ⟨0, by rw [H1Density.cutoff_eq_one (by simp)]; norm_num⟩
  have hg := VariationalFloor.memLp_grad hT
  have hw := VariationalFloor.hasWeakGradient_of_test hT
  have h1 := H _ (memH1_of_test hT)
  rw [msNormSq_toH1 (memH1_of_test hT) hg hw, norm_toH1_sq (memH1_of_test hT) hg hw,
    manuscriptH1NormSq] at h1
  have hB := integral_norm_grad_sq_pos hT one_pos hne
  have hpi : 1 < (2 * π) ^ 2 := by nlinarith [Real.pi_gt_three]
  have hc : ((2 * π) ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hpi
  nlinarith

/-- Contrast: on real profiles the manuscript norm is `∫ f² + ∫ ‖g‖²`. -/
theorem wrong_form_norm_contrast :
    ∀ (f : Rd 1 → ℝ) (h : MemH1 f) (g : Rd 1 → Rd 1), MemLp g 2 volume →
      HasWeakGradient f g → msNormSq (toH1 h) = (∫ x, f x ^ 2) + ∫ x, ‖g x‖ ^ 2 :=
  fun _ h _ hg hw => msNormSq_toH1 h hg hw

end Refutations.ResolventForm
