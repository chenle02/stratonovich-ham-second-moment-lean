/-
Refutation for the time exponent of `E:variance-kernel-time-bound`
(`notes/integrated_wave_variance.tex` at a284420, lines 390-393:
`‖1_I 𝒦_ij(·;ξ,η)‖²_{H_a} ≤ A_T h^{2-a} Φ_h(ξ,η)`), package theorems
`StratonovichHAMSecondMoment.WaveTwoVariances.norm_kerH_sq_le` and
`StratonovichHAMSecondMoment.WaveTwoVariances.kerH_eq_smul_emb`.

Wrong variant: the exponent `2 - a` replaced by `2` (the temporal singularity `a = α₀`
dropped), i.e. `‖1_I 𝒦_ij‖² ≤ K h² Φ_h` for some constant `K` and all `0 < h ≤ 1`. At
`a = 1/2`, `T = 1`, `I = [0,h]`, `ξ = η = 0`, `(i,j) = (2,1)` (Lean `(1,0)`, the entry
`c_0 c_0 = 1`): the left side is exactly `2h^{3/2}/((1/2)(3/2)) = (8/3) h^{3/2}`
(`MaskedContinuousWaveCompleted.norm_sq_waveFn_cc_zero`) and `Φ_h(0,0) = 2`, so the
wrong bound would give `4/3 ≤ K h^{1/2}` for all small `h`, false at
`h = (|K|+1)^{-2}`. No junk value is involved (`h > 0`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.WaveTwoVariances

set_option autoImplicit false

open MeasureTheory Set
open StratonovichHAMSecondMoment
open StratonovichHAMSecondMoment.MaskedTrigProducts (bracket frequencyPair)
open StratonovichHAMSecondMoment.FrequencyRow (rowKernel)
open StratonovichHAMSecondMoment.HomogHypothesis (Rd)
open StratonovichHAMSecondMoment.TimeCompletion (TimeParams emb L2fun)
open StratonovichHAMSecondMoment.MaskedContinuousWave (waveFn)
open StratonovichHAMSecondMoment.WaveTwoVariances

namespace Refutations.WaveTwoVariances

/-- The parameters `a = 1/2`, `T = 1`. -/
noncomputable def p0 : TimeParams := ⟨1 / 2, 1, by norm_num, by norm_num, by norm_num⟩

/-- The exact value `‖1_{[0,h]} 𝒦_{21}(·;0,0)‖² = (8/3) h^{3/2}` for `0 < h ≤ 1`. -/
theorem norm_kerH_zero {h : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) :
    ‖kerH p0 0 h 1 0 (0 : Rd 1) 0‖ ^ 2 = 8 / 3 * h ^ ((3 : ℝ) / 2) := by
  obtain ⟨hw, -⟩ := MaskedContinuousWaveCompleted.masked_continuous_wave_completed_paper
    p0.a p0.T 0 h p0.ha0 p0.ha1 p0.hT hh0 hh1 le_rfl (by simp [p0]; linarith)
    ‖(0 : Rd 1)‖ ‖(0 : Rd 1)‖ (norm_nonneg _) (norm_nonneg _) (rowWave 1) (colWave 0)
  have e : waveFn (Icc 0 (0 + h)) (rowWave 1) (colWave 0) ‖(0 : Rd 1)‖ ‖(0 : Rd 1)‖ =
      waveFn (Icc 0 h) .c .c 0 0 := by
    simp [rowWave, colWave]
  have hw' : waveFn (Icc 0 h) .c .c 0 0 ∈ L2fun p0.T := e ▸ hw
  have hsub : (⟨_, hw⟩ : L2fun p0.T) = ⟨_, hw'⟩ := Subtype.ext e
  have hb0 : bracket ‖(0 : Rd 1)‖ = 1 := by simp [bracket]
  rw [kerH_eq_smul_emb p0 0 h 1 0 0 0 hw, hsub, norm_smul, mul_pow,
    MaskedContinuousWaveCompleted.norm_sq_waveFn_cc_zero p0 hh0.le (by simp [p0]; linarith)]
  simp only [hb0, mul_one, Real.sqrt_one, rowSign, Matrix.cons_val_one, div_one, p0]
  norm_num
  ring

/-- `Φ_h(0,0) = 2` at `a = 1/2`. -/
theorem rowKernel_zero (h : ℝ) : rowKernel (1 / 2) h (0 : Rd 1) 0 = 2 := by
  simp [rowKernel, frequencyPair, bracket]
  norm_num

/-- Dropping the singular time exponent: `‖1_I 𝒦_ij‖² ≤ K h² Φ_h` is false. -/
theorem time_exponent_two_fails :
    ¬ ∃ K : ℝ, ∀ h : ℝ, 0 < h → h ≤ 1 →
      ‖kerH p0 0 h 1 0 (0 : Rd 1) 0‖ ^ 2 ≤ K * h ^ (2 : ℕ) * rowKernel p0.a h (0 : Rd 1) 0 := by
  rintro ⟨K, hK⟩
  set t : ℝ := 1 / (|K| + 1) with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := by rw [ht, div_le_one (by positivity)]; linarith [abs_nonneg K]
  have hh0 : 0 < t ^ 2 := by positivity
  have hh1 : t ^ 2 ≤ 1 := by nlinarith
  have := hK (t ^ 2) hh0 hh1
  rw [norm_kerH_zero hh0 hh1, show p0.a = 1 / 2 from rfl, rowKernel_zero] at this
  have h32 : (t ^ 2) ^ ((3 : ℝ) / 2) = t ^ 3 := by
    rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht0.le]; norm_num
  rw [h32] at this
  -- `(8/3) t³ ≤ 2 K t⁴`, i.e. `4/3 ≤ K t < 1`
  have hKt : K * t < 1 := by
    rw [ht, mul_one_div, div_lt_one (by positivity)]; linarith [le_abs_self K]
  have ht3 : 0 < t ^ 3 := by positivity
  nlinarith [mul_lt_mul_of_pos_right hKt ht3]

/-- Contrast: the package bound at the same point, with the exponent `2 - a`. -/
theorem time_exponent_contrast {h : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) :
    ‖kerH p0 0 h 1 0 (0 : Rd 1) 0‖ ^ 2 ≤
      MaskedContinuousWave.C₁ p0.a * (1 + p0.T) ^ 4 * h ^ (2 - p0.a) * rowKernel p0.a h (0 : Rd 1) 0 :=
  norm_kerH_sq_le p0 hh0 hh1 le_rfl (by simp [p0]; linarith) 1 0 0 0

end Refutations.WaveTwoVariances
