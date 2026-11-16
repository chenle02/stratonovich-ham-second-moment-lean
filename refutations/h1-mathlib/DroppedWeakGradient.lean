/-
Refutation for the weak-gradient hypothesis of the norm identity (wave L13,
item K5a), package theorem
`StratonovichHAMSecondMoment.H1Mathlib.norm_toH1_sq`.

Wrong variant: the norm identity
`‖f‖²_{H^{1}} = ‖f‖₂² + (2π)⁻² ‖g‖₂²` for every `g ∈ L²`, without the
hypothesis that `g` is a weak gradient of `f`. Counterexample: `d = 1`,
`f = cutoff 0` with `g = ∇f` and with `g = 0`: the two right sides differ by
`(2π)⁻² ∫ ‖∇f‖² > 0` while the left side is the same. Class (b): a Lean-route
control (the identity is the foundation's bridge, not a manuscript display).
`dropped_weak_gradient_contrast` is the package identity, with the
hypothesis.

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

/-- The norm identity fails for an `L²` field `g` that is not a weak gradient. -/
theorem dropped_weak_gradient :
    ¬ ∀ (f : Rd 1 → ℝ) (h : MemH1 f) (g : Rd 1 → Rd 1), MemLp g 2 volume →
      ‖toH1 h‖ ^ 2 = (∫ x, f x ^ 2) + ((2 * π) ^ 2)⁻¹ * ∫ x, ‖g x‖ ^ 2 := by
  intro H
  have hT : IsTestFunction (H1Density.cutoff (d := 1) 0) :=
    ⟨H1Density.cutoff_contDiff 0, H1Density.cutoff_hasCompactSupport 0⟩
  have hne : ∃ x : Rd 1, H1Density.cutoff 0 x ≠ 0 :=
    ⟨0, by rw [H1Density.cutoff_eq_one (by simp)]; norm_num⟩
  have h1 := H _ (memH1_of_test hT) _ (VariationalFloor.memLp_grad hT)
  have h0 := H _ (memH1_of_test hT) (fun _ => 0) MemLp.zero
  have hB := integral_norm_grad_sq_pos hT one_pos hne
  have hpi : 0 < ((2 * π) ^ 2)⁻¹ := by positivity
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    integral_zero, mul_zero, add_zero] at h0
  rw [h0] at h1
  nlinarith

/-- Contrast: with `g` a weak gradient of `f` the identity holds. -/
theorem dropped_weak_gradient_contrast :
    ∀ (f : Rd 1 → ℝ) (h : MemH1 f) (g : Rd 1 → Rd 1), MemLp g 2 volume →
      HasWeakGradient f g →
        ‖toH1 h‖ ^ 2 = (∫ x, f x ^ 2) + ((2 * π) ^ 2)⁻¹ * ∫ x, ‖g x‖ ^ 2 :=
  fun _ h _ hg hw => norm_toH1_sq h hg hw

end Refutations.H1Mathlib
