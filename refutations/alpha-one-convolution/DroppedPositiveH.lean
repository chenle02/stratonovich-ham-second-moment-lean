import StratonovichHAMSecondMoment.AlphaOneConvolution

/-!
Refutation for the lower bound `0 ≤ I_a(h,v)` in the proof of
`L:alpha-one-convolution` (main TeX lines 5702-5703; the lemma assumes `h > 0`),
package theorem `StratonovichHAMSecondMoment.AlphaOneConvolution.alpha_one_radial`
(hypothesis `0 ≤ h`).

Wrong variant: the hypothesis `h ≥ 0` dropped. Witness: `a = 1/4`, `h = -1`, `v = 0`:
`I_a(-1,0) = -I_a(1,0) < 0` (`Ia_neg_h`, oddness of `sin`), with `I_a(1,0) > 0` from
`boxConv_zero_ge`. No junk value is involved (the radial integrand is integrable).
The contrast theorem applies the package bound at `h = 1` and the oddness at `h = -1`.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

open MeasureTheory Set Real

namespace Refutations.AlphaOneConvolution

open StratonovichHAMSecondMoment.AlphaOneConvolution

/-- Contrast: `I_{1/4}(-1,0) < 0 < I_{1/4}(1,0)`. -/
theorem dropped_positive_h_contrast :
    Ia (1 / 4) (-1) 0 < 0 ∧ 0 < Ia (1 / 4) 1 0 := by
  obtain ⟨-, -, hId, -, -⟩ := alpha_one_radial (1 / 4) 1 0 (by norm_num) zero_le_one
  have hb := boxConv_zero_ge (1 / 4) 1 (by norm_num) zero_le_one
  have hg : 0 < gauss1 (1 / 4) 1 := by unfold gauss1; positivity
  have hpos : 0 < Ia (1 / 4) 1 0 := by rw [hId]; nlinarith [Real.pi_pos]
  exact ⟨by rw [Ia_neg_h]; linarith, hpos⟩

/-- The wrong variant (nonnegativity without `h ≥ 0`) is false. -/
theorem dropped_positive_h :
    ¬ ∀ a h v : ℝ, 0 < a → 0 ≤ Ia a h v := by
  intro H
  have := H (1 / 4) (-1) 0 (by norm_num)
  linarith [dropped_positive_h_contrast.1]

end Refutations.AlphaOneConvolution
