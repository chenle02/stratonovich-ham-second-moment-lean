/-
Refutation for `L:masked-continuous-wave` in the concrete `H_a`
(`notes/integrated_covariance_foundation.tex` lines 378-390, display 385-389 at
a284420), package theorem
`StratonovichHAMSecondMoment.MaskedContinuousWaveCompleted.masked_continuous_wave_completed_paper`.

Wrong variant: the power `h^{2-a}` replaced by `h^2` (the loss `h^{-a}` from the
singular kernel `|t-u|^{-a}` dropped), i.e.
`‖1_I F_r G_ρ‖_a² ≤ C₁(a) (1+T)⁴ h² 𝒬_h(r,ρ)`.
Counterexample: `a = 1/2`, `T = 1`, `s = 0`, `h = 10^{-8}`, `F = G = c`, `r = ρ = 0`
(so `1_I F_r G_ρ = 1_{[0,h]}`): the left side is `(8/3) h^{3/2}` (package calibration
`norm_sq_waveFn_cc_zero`), the right side is at most
`12288 h² = 12288 h^{1/2} h^{3/2} = 1.2288 h^{3/2} < (8/3) h^{3/2}`.
`kernel_gain_contrast` is the package bound at the same point.
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
noncomputable abbrev pK : TimeParams := ⟨1 / 2, 1, by norm_num, by norm_num, by norm_num⟩

/-- The package bound at the counterexample point. -/
theorem kernel_gain_contrast
    (hp : waveFn (Icc 0 (0 + (1 / 10000) ^ 2)) .c .c 0 0 ∈ L2fun pK.T) :
    ‖emb pK ⟨waveFn (Icc 0 (0 + (1 / 10000) ^ 2)) .c .c 0 0, hp⟩‖ ^ 2 ≤
      C₁ (1 / 2) * (1 + 1) ^ 4 * ((1 / 10000 : ℝ) ^ 2) ^ (2 - 1 / 2 : ℝ) *
        frequencyPair (1 / 2) ((1 / 10000) ^ 2) 0 0 :=
  (masked_continuous_wave_completed_paper (1 / 2) 1 0 ((1 / 10000) ^ 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num) 0 0 le_rfl
    le_rfl .c .c).2 hp

/-- The power `h²` in place of `h^{2-a}` is false. -/
theorem kernel_gain_refuted :
    ¬ (∀ h : ℝ, 0 < h → h ≤ 1 → ∀ hp : waveFn (Icc 0 (0 + h)) .c .c 0 0 ∈ L2fun pK.T,
        ‖emb pK ⟨waveFn (Icc 0 (0 + h)) .c .c 0 0, hp⟩‖ ^ 2 ≤
          C₁ (1 / 2) * (1 + 1) ^ 4 * h ^ 2 * frequencyPair (1 / 2) h 0 0) := by
  intro H
  set q : ℝ := 1 / 10000 with hq
  have hq0 : 0 < q := by norm_num [hq]
  set h : ℝ := q ^ 2 with hh
  have hpos : 0 < h := by positivity
  have hle : h ≤ 1 := by norm_num [hh, hq]
  have hp := (masked_continuous_wave_completed_paper (1 / 2) 1 0 h (by norm_num) (by norm_num)
    (by norm_num) hpos hle le_rfl (by simpa using hle) 0 0 le_rfl le_rfl .c .c).1
  have h1 := H h hpos hle hp
  have hcal := norm_sq_waveFn_cc_zero pK hpos.le (by simpa using hle) (by simpa using hp)
  simp only [zero_add] at h1
  have hQ : frequencyPair (1 / 2) h 0 0 = 2 := by
    simp [frequencyPair, MaskedTrigProducts.bracket]; norm_num
  rw [hcal, hQ] at h1
  have hX : 0 < h ^ (2 - 1 / 2 : ℝ) := Real.rpow_pos_of_pos hpos _
  have hhalf : h ^ (1 / 2 : ℝ) = q := by
    rw [hh, show (1 / 2 : ℝ) = ((2 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.pow_rpow_inv_natCast hq0.le two_ne_zero
  have hsplit : h ^ 2 = q * h ^ (2 - 1 / 2 : ℝ) := by
    rw [← hhalf, ← Real.rpow_add hpos, ← Real.rpow_natCast]
    norm_num
  rw [hsplit] at h1
  have hC : C₁ (1 / 2) ≤ 384 := by
    have h3 : (3 : ℝ) ^ (1 - 1 / 2 : ℝ) ≤ 3 := by
      calc (3 : ℝ) ^ (1 - 1 / 2 : ℝ) ≤ (3 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 3 := Real.rpow_one 3
    unfold C₁ C₀
    nlinarith
  have hC0 : 0 ≤ C₁ (1 / 2) := by unfold C₁ C₀; positivity
  norm_num at h1
  nlinarith

end Refutations.MaskedContinuousWaveCompleted
