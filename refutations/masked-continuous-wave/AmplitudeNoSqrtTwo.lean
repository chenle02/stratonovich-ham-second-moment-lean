/-
Refutation for `StratonovichHAMSecondMoment.MaskedContinuousWave.amp_bound`
(auxiliary to the Lean proof route of `L:masked-continuous-wave`; TeX line 393
at a284420: for `r ≥ 1`, `b_r` is a sine times "a coefficient at most `√2`").

Wrong variant: the per-factor envelope with the factor `√2` dropped, i.e. the
amplitude of `b_r` bounded by `1 + T` on `[0, T]`. Witness `r = 1`, `T = 0`,
`t = 0`: the amplitude of `b_1` is the coefficient `⟨1⟩/1 = √2 > 1`. So the
coefficient `⟨r⟩/r`, which reaches `√2` at `r = 1`, must be paid for; this is
why the envelope is `(M+hD)² ≤ 4(1+T)⁴`, giving the factor `4` of `C₁`. No junk
value is involved. The contrast theorem bounds the same amplitude by
`√2 (1 + T)` through the package lemma `bracket_div_le_sqrt_two`.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.MaskedContinuousWave

set_option autoImplicit false

namespace Refutations.MaskedContinuousWave

open Set StratonovichHAMSecondMoment.MaskedTrigProducts
  StratonovichHAMSecondMoment.MaskedContinuousWave

/-- The amplitude of `b_1` is not bounded by `1 + T` on `[0, T]`. -/
theorem amplitude_no_sqrt_two :
    ¬ ∀ T : ℝ, 0 ≤ T → ∀ t ∈ Icc 0 T, |amp .b 1 t| ≤ 1 + T := by
  intro H
  have h1 := H 0 le_rfl 0 ⟨le_rfl, le_rfl⟩
  simp only [amp, lt_irrefl, ite_false, div_one, bracket] at h1
  norm_num at h1
  have : (1 : ℝ) < √2 := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rw [abs_of_pos (by positivity)] at h1
  linarith

/-- Contrast: the same amplitude is at most `√2 (1 + 0)`. -/
theorem amplitude_no_sqrt_two_contrast : |amp .b 1 0| ≤ √2 * (1 + 0) := by
  have hb := bracket_div_le_sqrt_two (r := 1) le_rfl
  have hp : 0 < bracket 1 / 1 := by have := bracket_pos 1; positivity
  simp only [amp, lt_irrefl, ite_false]
  rw [abs_of_pos hp]
  linarith

end Refutations.MaskedContinuousWave
