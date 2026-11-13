/-
Refutation for the assembly step of `E:variational-unmasked-point-lower`
(`notes/integrated_unmasked_variational.tex` lines 175-178 and 214-218 at
a284420), package theorem
`StratonovichHAMSecondMoment.RemoveMask.le_liminf_of_tendsto`
(`J R → I` and `2 J R - v/2 ≤ liminf L` for large `R` give
`2 I - v/2 ≤ liminf L`).

Wrong variant: coefficient `3` in place of `2` in the conclusion.
Counterexample: `J ≡ 1`, `I = 1`, `v = 0`, `L ≡ 2`: the hypothesis is
`2 ≤ 2`, the variant asks `3 ≤ 2`.  `point_coefficient_contrast` is the
package theorem at the same data.  No junk-value reliance (the liminf is in
`EReal`, and of a constant).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.RemoveMask

set_option autoImplicit false

open Filter Topology

namespace Refutations.RemoveMask

open StratonovichHAMSecondMoment.RemoveMask

theorem liminf_two : liminf (fun _ : ℝ => ((2 : ℝ) : EReal)) atTop = ((2 : ℝ) : EReal) :=
  liminf_const _

/-- The coefficient `3` in the point-moment assembly is false. -/
theorem point_coefficient_three_refuted :
    ¬ (∀ (J : ℝ → ℝ) (I v : ℝ) (L : ℝ → ℝ), Tendsto J atTop (𝓝 I) →
      (∀ᶠ R in atTop, ((2 * J R - v / 2 : ℝ) : EReal) ≤
        liminf (fun T => (L T : EReal)) atTop) →
      ((3 * I - v / 2 : ℝ) : EReal) ≤ liminf (fun T => (L T : EReal)) atTop) := by
  intro h
  have h1 := h (fun _ => 1) 1 0 (fun _ => 2) tendsto_const_nhds
    (Eventually.of_forall fun _ => by rw [liminf_two]; norm_num)
  rw [liminf_two, EReal.coe_le_coe_iff] at h1
  norm_num at h1

/-- The package assembly at the same data: `2 ≤ liminf L = 2`. -/
theorem point_coefficient_contrast :
    ((2 * 1 - 0 / 2 : ℝ) : EReal) ≤ liminf (fun _ : ℝ => (((2 : ℝ) : ℝ) : EReal)) atTop :=
  le_liminf_of_tendsto (J := fun _ => 1) (L := fun _ => 2) tendsto_const_nhds
    (Eventually.of_forall fun _ => by rw [liminf_two]; norm_num)

end Refutations.RemoveMask
