/-
Refutation for the constants of the embedding of `H¹` into Mathlib's `H^{1}` (wave L14, item O),
package theorem `StratonovichHAMSecondMoment.ClassOH1.norm_toMH1_sub_sq`.

Manuscript side: the TeX's `H¹` norm is `‖f‖₂² + ‖∇f‖₂²` (main TeX lines 748-750;
`notes/integrated_signed_static.tex` line 85 at revision 39f2597a) and the TeX identifies `H¹`
with the graph `f ↦ (f, ∇f)` in `L²` (`integrated_spatial_occupation.tex` lines 356-358).

Wrong variant: `toMH1 : H1R → H^{1}` is an isometry for the manuscript norm,
`‖toMH1 p - toMH1 q‖² = ‖f_p - f_q‖₂² + ‖g_p - g_q‖₂²`. Counterexample: `d = 1`, `p` the class of
the test function `cutoff 0` (positive gradient energy, `H1Mathlib.integral_norm_grad_sq_pos`)
and `q = 0`; the true identity carries `(2π)⁻² < 1` on the gradient term. Class (b): a Lean-route
control (Mathlib's `2π` convention of the embedding used for the topology; the TeX makes no
claim about Mathlib's norm). The contrast is the package identity.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.ClassOBridge

set_option autoImplicit false

namespace Refutations.ClassOBridge

open StratonovichHAMSecondMoment StratonovichHAMSecondMoment.ClassOH1 MeasureTheory
open HomogHypothesis (Rd)
open WeakSobolev (IsTestFunction)
open scoped Real

/-- The embedding is not an isometry for the manuscript norm (the `2π` factor). -/
theorem embedding_without_two_pi :
    ¬ ∀ p q : H1R 1, ‖toMH1 p - toMH1 q‖ ^ 2 =
      ‖(p : L2R 1 × L2V 1).1 - (q : L2R 1 × L2V 1).1‖ ^ 2 +
        ‖(p : L2R 1 × L2V 1).2 - (q : L2R 1 × L2V 1).2‖ ^ 2 := by
  intro H
  have hT : IsTestFunction (H1Density.cutoff (d := 1) 0) :=
    ⟨H1Density.cutoff_contDiff 0, H1Density.cutoff_hasCompactSupport 0⟩
  have hne : ∃ x : Rd 1, H1Density.cutoff 0 x ≠ 0 :=
    ⟨0, by rw [H1Density.cutoff_eq_one (by simp)]; norm_num⟩
  have hP := SpatialFourLinear.isH1Pair_test hT
  set p := ofPair hP
  have h1 := H p ClassOBridge.zeroH1
  rw [norm_toMH1_sub_sq] at h1
  set b := ‖(p : L2R 1 × L2V 1).2 - ((ClassOBridge.zeroH1 : H1R 1) : L2R 1 × L2V 1).2‖
  have hc : ((2 * π) ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith [Real.pi_gt_three])
  have hb0 : b ^ 2 = 0 := by nlinarith [sq_nonneg b]
  have hbI : b ^ 2 = ∫ x, ‖VariationalFloor.grad (H1Density.cutoff (d := 1) 0) x‖ ^ 2 := by
    rw [← integral_norm_sub_sq]
    refine integral_congr_ae ?_
    filter_upwards [grd_ofPair hP, Lp.coeFn_zero (Rd 1) 2 volume] with x hx hz
    change ‖grd p x - ((0 : L2V 1) : Rd 1 → Rd 1) x‖ ^ 2 = _
    rw [hx, hz, Pi.zero_apply, sub_zero]
  have hpos := H1Mathlib.integral_norm_grad_sq_pos hT one_pos hne
  linarith

/-- Contrast: the identity holds with the factor `(2π)⁻²` on the gradient term. -/
theorem embedding_without_two_pi_contrast :
    ∀ p q : H1R 1, ‖toMH1 p - toMH1 q‖ ^ 2 =
      ‖(p : L2R 1 × L2V 1).1 - (q : L2R 1 × L2V 1).1‖ ^ 2 +
        ((2 * π) ^ 2)⁻¹ * ‖(p : L2R 1 × L2V 1).2 - (q : L2R 1 × L2V 1).2‖ ^ 2 :=
  norm_toMH1_sub_sq

end Refutations.ClassOBridge
