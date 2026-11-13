/-
Refutation for `L:masked-continuous-wave` in the concrete `H_a`
(`notes/integrated_covariance_foundation.tex` lines 378-390, display 385-389 at
a284420), package theorem
`StratonovichHAMSecondMoment.MaskedContinuousWaveCompleted.masked_continuous_wave_completed_paper`.

Wrong variant: the power `h^{2-a}` replaced by `h^{3-a}` (one more factor of `h`), i.e.
`‖1_I F_r G_ρ‖_a² ≤ C₁(a) (1+T)⁴ h^{3-a} 𝒬_h(r,ρ)`.
Counterexample: `a = 1/2`, `T = 1`, `s = 0`, `h = 1/10000`, `F = G = c`, `r = ρ = 0`
(so `1_I F_r G_ρ = 1_{[0,h]}`): the left side is `(8/3) h^{3/2}` (package calibration
`norm_sq_waveFn_cc_zero`), the right side is at most `4·3·32·16·2·h·h^{3/2} =
12288 h · h^{3/2} < (8/3) h^{3/2}`.  `extra_power_contrast` is the package bound at
the same point.
No junk-value reliance (`h > 0`; all integrands integrable).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.MaskedContinuousWaveCompleted

set_option autoImplicit false

open MeasureTheory Set
open StratonovichHAMSecondMoment MaskedTrigProducts MaskedContinuousWave TimeCompletion
  MaskedContinuousWaveCompleted

namespace Refutations.MaskedContinuousWaveCompleted

/-- The parameters `a = 1/2`, `T = 1`. -/
noncomputable abbrev pH : TimeParams := ⟨1 / 2, 1, by norm_num, by norm_num, by norm_num⟩

/-- `𝒬_h(0,0) = 2`. -/
theorem frequencyPair_zero (a h : ℝ) : frequencyPair a h 0 0 = 2 := by
  simp [frequencyPair, bracket]; norm_num

/-- `C₁(1/2) ≤ 384`. -/
theorem C₁_half_le : C₁ (1 / 2) ≤ 384 := by
  have h3 : (3 : ℝ) ^ (1 - 1 / 2 : ℝ) ≤ 3 := by
    calc (3 : ℝ) ^ (1 - 1 / 2 : ℝ) ≤ (3 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 3 := Real.rpow_one 3
  unfold C₁ C₀
  nlinarith

/-- The package bound at the counterexample point. -/
theorem extra_power_contrast (hp : waveFn (Icc 0 (0 + 1 / 10000)) .c .c 0 0 ∈ L2fun pH.T) :
    ‖emb pH ⟨waveFn (Icc 0 (0 + 1 / 10000)) .c .c 0 0, hp⟩‖ ^ 2 ≤
      C₁ (1 / 2) * (1 + 1) ^ 4 * (1 / 10000 : ℝ) ^ (2 - 1 / 2 : ℝ) *
        frequencyPair (1 / 2) (1 / 10000) 0 0 :=
  (masked_continuous_wave_completed_paper (1 / 2) 1 0 (1 / 10000) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num) 0 0 le_rfl le_rfl .c .c).2 hp

/-- The power `h^{3-a}` in place of `h^{2-a}` is false. -/
theorem extra_power_refuted :
    ¬ (∀ h : ℝ, 0 < h → h ≤ 1 → ∀ hp : waveFn (Icc 0 (0 + h)) .c .c 0 0 ∈ L2fun pH.T,
        ‖emb pH ⟨waveFn (Icc 0 (0 + h)) .c .c 0 0, hp⟩‖ ^ 2 ≤
          C₁ (1 / 2) * (1 + 1) ^ 4 * h ^ (3 - 1 / 2 : ℝ) * frequencyPair (1 / 2) h 0 0) := by
  intro H
  set h : ℝ := 1 / 10000 with hh
  have hpos : 0 < h := by norm_num [hh]
  have hp := (masked_continuous_wave_completed_paper (1 / 2) 1 0 h (by norm_num) (by norm_num)
    (by norm_num) hpos (by norm_num [hh]) le_rfl (by norm_num [hh]) 0 0 le_rfl le_rfl .c .c).1
  have h1 := H h hpos (by norm_num [hh]) hp
  have hcal := norm_sq_waveFn_cc_zero pH hpos.le (by norm_num [hh])
    (by simpa using hp)
  simp only [zero_add] at h1
  rw [hcal, frequencyPair_zero] at h1
  have hX : 0 < h ^ (2 - 1 / 2 : ℝ) := Real.rpow_pos_of_pos hpos _
  have hsplit : h ^ (3 - 1 / 2 : ℝ) = h * h ^ (2 - 1 / 2 : ℝ) := by
    rw [show (3 - 1 / 2 : ℝ) = 1 + (2 - 1 / 2) by norm_num, Real.rpow_add hpos, Real.rpow_one]
  rw [hsplit] at h1
  have hC := C₁_half_le
  have hC0 : 0 ≤ C₁ (1 / 2) := by unfold C₁ C₀; positivity
  norm_num at h1
  nlinarith

end Refutations.MaskedContinuousWaveCompleted
