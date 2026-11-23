/-
Refutation for the hypothesis `Σ_l h_l ≤ 2t` of `E:d1-spatial-max`
(`L:d1-spatial`, main TeX lines 5372-5374 at edf7085f; proof lines 5417-5432).
Package theorem `StratonovichHAMSecondMoment.D1Spatial.d1_spatial_white_max`.

Wrong variant: `E:d1-spatial-max` without the hypothesis on the sum of the
increments, `S_{D,ε}(h) ≤ K_sp^k t^{bk}/k^{bk}` for every `t > 0` (white case:
`b = 1`, `K_sp = c_δ`).  Counterexample in the manuscript domain: `c_δ = 2`,
`ε = 1`, `k = 1`, the self-pairing of one chain (`m = 2`, `n = 0`), `h = (12, 1)`,
`t = 1`: `S ≥ 4 > 2 = c_δ t`.  `droppedSumHypothesis_contrast` is the package
statement with the hypothesis `Σ_l h_l ≤ 2t`.
Class (a): manuscript-claim perturbation in the manuscript domain.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.D1Spatial

set_option autoImplicit false

open MeasureTheory StratonovichHAMSecondMoment D1Spatial DiagramModel
open HomogHypothesis (Rd)
open WaveGreen (waveGreen)
open WhiteModel (whiteCov)
open scoped ENNReal

namespace Refutations.D1Spatial.DroppedSumHypothesis

/-- The heat density `p_1` is at least `1/6` on the unit ball
(`(2π)^{-1/2} ≥ 9^{-1/2} = 1/3` and `e^{-|v|²/2} ≥ 1/2`). -/
theorem heat_ge (v : Rd 1) (hv : ‖v‖ < 1) : 1 / 6 ≤ LowAlphaConvolution.heatDens 1 v := by
  unfold LowAlphaConvolution.heatDens
  simp only [Nat.cast_one]
  have h1 : (1 : ℝ) / 3 ≤ (2 * Real.pi * 1) ^ (-((1 : ℝ) / 2)) := by
    have hle : 2 * Real.pi * 1 ≤ 9 := by nlinarith [Real.pi_lt_four]
    have := Real.rpow_le_rpow_of_nonpos (by positivity) hle (by norm_num : -((1 : ℝ) / 2) ≤ 0)
    have h9 : (9 : ℝ) ^ (-((1 : ℝ) / 2)) = 1 / 3 := by
      rw [show (9 : ℝ) = 3 ^ (2 : ℝ) by rw [Real.rpow_two]; norm_num,
        ← Real.rpow_mul (by norm_num), show (2 : ℝ) * -(1 / 2) = -1 by norm_num,
        Real.rpow_neg_one]
      norm_num
    linarith
  have h2 : (1 : ℝ) / 2 ≤ Real.exp (-(‖v‖ ^ 2 / (2 * 1))) := by
    have := Real.add_one_le_exp (-(‖v‖ ^ 2 / (2 * 1)))
    have : ‖v‖ ^ 2 < 1 := by nlinarith [norm_nonneg v]
    linarith
  calc (1 : ℝ) / 6 = 1 / 3 * (1 / 2) := by norm_num
    _ ≤ _ := mul_le_mul h1 h2 (by norm_num) (by positivity)

/-- The smallest white diagram (`c = 2`, `ε = 1`, `h = (h₀, 1)`) is at least
`h₀/3`: `S = h₀ ∫ G_1(dv) 2 p_1(v)` and `p_1 ≥ 1/6` on `(-1, 1)`. -/
theorem white_selfPair_ge (h0 : ℝ) (hh0 : 0 ≤ h0) :
    ENNReal.ofReal (h0 / 3) ≤
      spatialPair (waveGreen 1) (fun _ => covEps (whiteCov 2) 1) 2 selfPair ![h0, 1] := by
  rw [spatialPair_selfPair _ _ (measurable_covEps_white 2 1)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [WaveGreen.waveGreen_mass 1 (Or.inl rfl) h0 hh0]
  have hb : volume (Metric.ball (0 : Rd 1) 1) = ENNReal.ofReal 2 := by
    rw [WaveGreen.ball_eq_preimage_coordOne,
      WaveGreen.coordOne_mp.measure_preimage measurableSet_Ioo.nullMeasurableSet,
      Real.volume_Ioo]
    norm_num
  have hI : ENNReal.ofReal (1 / 3) ≤ ∫⁻ v, covEps (whiteCov 2) 1 (-v) ∂waveGreen 1 1 := by
    rw [show waveGreen 1 1 = ENNReal.ofReal (1 / 2) • volume.restrict (Metric.ball 0 1) from rfl,
      lintegral_smul_measure]
    calc ENNReal.ofReal (1 / 3)
        = ENNReal.ofReal (1 / 2) * (ENNReal.ofReal (2 * (1 / 6)) * ENNReal.ofReal 2) := by
          rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]
          norm_num
      _ ≤ ENNReal.ofReal (1 / 2) * ∫⁻ v in Metric.ball 0 1, covEps (whiteCov 2) 1 (-v) := by
          gcongr
          rw [← hb, ← setLIntegral_const]
          refine setLIntegral_mono' Metric.isOpen_ball.measurableSet fun v hv => ?_
          rw [covEps_whiteCov, ← ENNReal.ofReal_mul (by norm_num)]
          refine ENNReal.ofReal_le_ofReal ?_
          have := heat_ge (-v) (by rw [norm_neg]; simpa using hv)
          linarith
  calc ENNReal.ofReal (h0 / 3) = ENNReal.ofReal h0 * ENNReal.ofReal (1 / 3) := by
        rw [← ENNReal.ofReal_mul hh0]; ring_nf
    _ ≤ _ := by gcongr

/-- The package: with `Σ_l h_l ≤ 2t`. -/
theorem droppedSumHypothesis_contrast : ∀ c : ℝ, 0 < c → ∀ ε : ℝ, 0 < ε →
    ∀ h : Fin 2 → ℝ, (∀ i, 0 < h i) → ∀ t : ℝ, ∑ i, h i ≤ 2 * t →
      spatialPair (waveGreen 1) (fun _ => covEps (whiteCov c) ε) 2 selfPair h ≤
        ENNReal.ofReal (c ^ 1 * t ^ 1 / ((1 : ℕ) : ℝ) ^ 1) :=
  fun _ hc ε hε _ hh _ hsum => d1_spatial_white_max (εs := fun _ => ε) hc.le le_rfl
    (by norm_num) 2 selfPair_mem (fun _ => hε) (fun i => (hh i).le) hsum

/-- Without `Σ_l h_l ≤ 2t` the maximum form is false. -/
theorem droppedSumHypothesis_refuted : ¬ (∀ c : ℝ, 0 < c → ∀ ε : ℝ, 0 < ε →
    ∀ h : Fin 2 → ℝ, (∀ i, 0 < h i) → ∀ t : ℝ, 0 < t →
      spatialPair (waveGreen 1) (fun _ => covEps (whiteCov c) ε) 2 selfPair h ≤
        ENNReal.ofReal (c ^ 1 * t ^ 1 / ((1 : ℕ) : ℝ) ^ 1)) := by
  intro H
  have h1 := H 2 (by norm_num) 1 (by norm_num) ![12, 1] (by intro i; fin_cases i <;> simp) 1
    (by norm_num)
  have h2 := (white_selfPair_ge 12 (by norm_num)).trans h1
  have h3 := (ENNReal.ofReal_le_ofReal_iff (by norm_num)).1 h2
  norm_num at h3

end Refutations.D1Spatial.DroppedSumHypothesis
