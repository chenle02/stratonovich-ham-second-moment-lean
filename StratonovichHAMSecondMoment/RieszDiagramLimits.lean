module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L18, item A (approved by Le on 2026-11-21, decision 3): the named input
`D1Upper.DiagramLimits 1 (volume.withDensity (riesz c α)) α₀ t` (the Riesz case of
`L:joint-fixed-order` in `d = 1`) is **proved**, for every order and every `t ≥ 0`, with nothing
supplied.  TeX lines at revision edf7085f (book 1.1.3), main file
`notes/notes_stratonovich_ham_second_moment.tex`:
* `E:mixed-diagram` and its regularization conventions, lines 814-832;
* `P:riesz-small` (`d = 1`, `γ = c_α|y|^{-α}`), statement lines 5125-5172;
* `P:d1-upper`, statement lines 5454-5466, proof lines 5468-5550 (Step 3, lines 5532-5538:
  "By Lemma L:joint-fixed-order, each smoothed factor converges ... so it passes to `A_k(t)`").

**Route difference (disclosed, decision 3).**  The TeX obtains the limit of every diagram from
`L:joint-fixed-order` (spatial Wick measures, weak convergence, temporal tails; TeX 1853-1966).
Here, in the Riesz case `d = 1` only, the limit is obtained by **domination**:
1. `covEps_riesz_le`: `(p_ε * c|·|^{-α})(x) ≤ C_α c|x|^{-α}` for `x ≠ 0`, uniformly in `ε > 0`,
   with `C_α = 2 + 16/(1-α)` (`CA`);
2. `tendsto_covEps_riesz`: `(p_ε * c|·|^{-α})(x) → c|x|^{-α}` as `ε ↓ 0`, for `x ≠ 0`;
3. both hold off the pair diagonals `{y_i = y_{D i}}`, a Lebesgue-null set (`ae_offDiag`), so
   dominated convergence over the Green boxes gives convergence of the spatial parts
   (`tendsto_spatial`), uniformly dominated on the time simplex (`spatial_riesz_le_Csp`);
4. dominated convergence in time (`RieszFourDiagrams.tendsto_diagram_of_spatial`) gives
   `tendsto_diagram_riesz`, whence `diagramLimits_riesz` and the identification
   `diagramLim_riesz_eq` (the measure-form limit is the density diagram, every order).
The model is `DiagramModel` (M4): one common noise width `ε`, exact time kernel.

Consequences: `coeffALim_riesz_le'` (`E:d1-coefficient` for the limit `A_k(t)`, Riesz case,
no supplied input; successor of `D1Upper.coeffALim_riesz_le`) and the wrapper
`d1_upper_paper_riesz'` (the coefficient displays of `P:d1-upper` with the manuscript's
hypotheses and no supplied input, modelled on `D1Upper.d1_upper_paper_white'`).  The moment
display `E:d1-upper` is about `u` and stays in `D1Upper.d1_upper_paper_riesz` with the supplied
input `MixedMoment` (its moment clauses are stochastic).
-/

public import Mathlib
public import StratonovichHAMSecondMoment.RieszFourDiagrams
public import StratonovichHAMSecondMoment.D1Upper

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Filter Topology Set
open scoped ENNReal Nat

namespace StratonovichHAMSecondMoment.RieszDiagramLimits

open HomogHypothesis (Rd)
open WaveGreen (waveGreen)
open VariationalMean (heatK)
open HigherRieszTwo (riesz lintegral_heatK measurable_riesz)
open DiagramModel
open RieszFourDiagrams
open TwoSimplexTime (Zc Zc_pos)
open D1Spatial (Ksp)

/-! ### Real-variable facts -/

theorem heatK_one_dim {ε : ℝ} (hε : 0 < ε) (z : Rd 1) :
    heatK ε z = (Real.sqrt (2 * Real.pi * ε))⁻¹ * Real.exp (-(‖z‖ ^ 2 / (2 * ε))) := by
  unfold heatK
  congr 1
  rw [Nat.cast_one, Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity)]

/-- `v e^{-v²/2} ≤ 1`. -/
theorem mul_exp_neg_sq_le (v : ℝ) : v * Real.exp (-(v ^ 2 / 2)) ≤ 1 := by
  have h1 := Real.add_one_le_exp (v ^ 2 / 2)
  have hpos := Real.exp_pos (v ^ 2 / 2)
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hpos]
  nlinarith [sq_nonneg (v - 1)]

/-- For `|z| ≥ r`: `p_ε(z) ≤ ε^{-1/2} e^{-(r/√ε)²/2}`. -/
theorem heatK_le_of_le_norm {ε r : ℝ} (hε : 0 < ε) (hr : 0 ≤ r) {z : Rd 1} (hz : r ≤ ‖z‖) :
    heatK ε z ≤ (Real.sqrt ε)⁻¹ * Real.exp (-((r / Real.sqrt ε) ^ 2 / 2)) := by
  rw [heatK_one_dim hε]
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have h1 : (Real.sqrt (2 * Real.pi * ε))⁻¹ ≤ (Real.sqrt ε)⁻¹ := by
    refine inv_anti₀ hs (Real.sqrt_le_sqrt ?_)
    nlinarith [Real.pi_gt_three]
  have h2 : Real.exp (-(‖z‖ ^ 2 / (2 * ε))) ≤ Real.exp (-((r / Real.sqrt ε) ^ 2 / 2)) := by
    refine Real.exp_le_exp.2 (neg_le_neg ?_)
    rw [div_pow, Real.sq_sqrt hε.le, div_div, mul_comm ε 2]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hr hz 2) (by positivity)
  exact mul_le_mul h1 h2 (Real.exp_pos _).le (inv_nonneg.2 hs.le)

/-- The final real inequality of the domination lemma. -/
theorem dom_real {c α ε ρ : ℝ} (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα : α < 1) (hε : 0 < ε) (hρ : 0 < ρ) :
    (Real.sqrt ε)⁻¹ * Real.exp (-(((ρ / 2) / Real.sqrt ε) ^ 2 / 2)) *
        (2 * (c * (2 * (2 * ρ)) ^ (1 - α) / (1 - α))) ≤
      16 / (1 - α) * (c * ρ ^ (-α)) := by
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have h1α : 0 < 1 - α := by linarith
  set v := (ρ / 2) / Real.sqrt ε with hv
  have hv0 : 0 ≤ v := by positivity
  have hkey := mul_exp_neg_sq_le v
  have h4 : (2 * (2 * ρ)) ^ (1 - α) ≤ 4 * (ρ * ρ ^ (-α)) := by
    rw [show 2 * (2 * ρ) = 4 * ρ by ring, Real.mul_rpow (by norm_num) hρ.le]
    have e : ρ ^ (1 - α) = ρ * ρ ^ (-α) := by
      rw [sub_eq_add_neg, Real.rpow_add hρ, Real.rpow_one]
    rw [e]
    gcongr
    calc (4 : ℝ) ^ (1 - α) ≤ 4 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 4 := Real.rpow_one 4
  have hρs : ρ * (Real.sqrt ε)⁻¹ = 2 * v := by rw [hv]; field_simp
  have hE := Real.exp_pos (-(v ^ 2 / 2))
  have hρa : 0 ≤ ρ ^ (-α) := Real.rpow_nonneg hρ.le _
  calc (Real.sqrt ε)⁻¹ * Real.exp (-(v ^ 2 / 2)) * (2 * (c * (2 * (2 * ρ)) ^ (1 - α) / (1 - α)))
      ≤ (Real.sqrt ε)⁻¹ * Real.exp (-(v ^ 2 / 2)) * (2 * (c * (4 * (ρ * ρ ^ (-α))) / (1 - α))) := by
        gcongr
    _ = 8 / (1 - α) * (c * ρ ^ (-α)) * ((ρ * (Real.sqrt ε)⁻¹) * Real.exp (-(v ^ 2 / 2))) := by
        ring
    _ = 16 / (1 - α) * (c * ρ ^ (-α)) * (v * Real.exp (-(v ^ 2 / 2))) := by
        rw [hρs]; ring
    _ ≤ 16 / (1 - α) * (c * ρ ^ (-α)) * 1 := by
        gcongr
    _ = 16 / (1 - α) * (c * ρ ^ (-α)) := mul_one _

/-- `c (ρ/2)^{-α} ≤ 2 c ρ^{-α}` for `α < 1`. -/
theorem half_rpow_le {c α ρ : ℝ} (hc : 0 ≤ c) (hα : α < 1) (hρ : 0 < ρ) :
    c * (ρ / 2) ^ (-α) ≤ 2 * (c * ρ ^ (-α)) := by
  rw [Real.div_rpow hρ.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
  have h2 : (2 : ℝ) ^ α ≤ 2 := by
    calc (2 : ℝ) ^ α ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hα.le
      _ = 2 := Real.rpow_one 2
  have := Real.rpow_nonneg hρ.le (-α)
  nlinarith [mul_nonneg hc this]

/-- The domination constant `C_α = 2 + 16/(1-α)`. -/
def CA (α : ℝ) : ℝ := 2 + 16 / (1 - α)

/-! ### The domination lemma -/

/-- **Domination** (d = 1): `(p_ε * c|·|^{-α})(x) ≤ C_α c|x|^{-α}` for `x ≠ 0`, uniformly in
`ε > 0`. -/
theorem covEps_riesz_le {c α ε : ℝ} (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα : α < 1) (hε : 0 < ε)
    {x : Rd 1} (hx : x ≠ 0) :
    covEps ((volume : Measure (Rd 1)).withDensity (riesz c α)) ε x ≤
      ENNReal.ofReal (CA α) * riesz c α x := by
  rw [covEps_riesz]
  set ρ := ‖x‖ with hρdef
  have hρ : 0 < ρ := norm_pos_iff.2 hx
  set S := Metric.ball x (ρ / 2) with hS
  have hSm : MeasurableSet S := Metric.isOpen_ball.measurableSet
  have hFm : Measurable fun z : Rd 1 => riesz c α (x - z) :=
    (measurable_riesz c α).comp (measurable_const.sub measurable_id)
  have hHm : Measurable fun z : Rd 1 => ENNReal.ofReal (heatK ε z) :=
    (HigherRieszTwo.measurable_heatK ε).ennreal_ofReal
  set A := (Real.sqrt ε)⁻¹ * Real.exp (-(((ρ / 2) / Real.sqrt ε) ^ 2 / 2)) with hA
  set B := 2 * (c * (2 * (2 * ρ)) ^ (1 - α) / (1 - α)) with hB
  -- the part near the singularity `z = x`
  have hnear : ∫⁻ z in S, ENNReal.ofReal (heatK ε z) * riesz c α (x - z) ≤
      ENNReal.ofReal A * ENNReal.ofReal B := by
    calc ∫⁻ z in S, ENNReal.ofReal (heatK ε z) * riesz c α (x - z)
        ≤ ∫⁻ z in S, ENNReal.ofReal A * riesz c α (x - z) := by
          refine setLIntegral_mono' hSm fun z hz => ?_
          gcongr
          refine heatK_le_of_le_norm hε (by positivity) ?_
          have hz' : ‖z - x‖ < ρ / 2 := by rw [← dist_eq_norm]; exact hz
          have := norm_sub_norm_le x (x - z)
          rw [sub_sub_cancel] at this
          have h2 : ‖x - z‖ = ‖z - x‖ := norm_sub_rev x z
          linarith
      _ = ENNReal.ofReal A * ∫⁻ z in S, riesz c α (x - z) :=
          lintegral_const_mul _ hFm
      _ ≤ ENNReal.ofReal A * ∫⁻ z in Metric.ball (0 : Rd 1) (2 * ρ), riesz c α (x - z) := by
          gcongr
          intro z hz
          rw [mem_ball_zero_iff]
          have hz' : ‖z - x‖ < ρ / 2 := by rw [← dist_eq_norm]; exact hz
          have := norm_le_insert' z x
          linarith [norm_sub_rev z x]
      _ ≤ ENNReal.ofReal A * ENNReal.ofReal B := by
          gcongr
          exact lintegral_ball_riesz_le hc hα0 hα (by positivity) x
  -- the part away from the singularity
  have hfar : ∫⁻ z in Sᶜ, ENNReal.ofReal (heatK ε z) * riesz c α (x - z) ≤
      ENNReal.ofReal (c * (ρ / 2) ^ (-α)) := by
    calc ∫⁻ z in Sᶜ, ENNReal.ofReal (heatK ε z) * riesz c α (x - z)
        ≤ ∫⁻ z in Sᶜ, ENNReal.ofReal (heatK ε z) * ENNReal.ofReal (c * (ρ / 2) ^ (-α)) := by
          refine setLIntegral_mono' hSm.compl fun z hz => ?_
          gcongr
          rw [riesz]
          refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hc)
          have hz' : ρ / 2 ≤ ‖x - z‖ := by
            rw [hS, mem_compl_iff, Metric.mem_ball, not_lt, dist_eq_norm, norm_sub_rev] at hz
            exact hz
          exact Real.rpow_le_rpow_of_nonpos (by positivity) hz' (by linarith)
      _ ≤ ∫⁻ z, ENNReal.ofReal (heatK ε z) * ENNReal.ofReal (c * (ρ / 2) ^ (-α)) :=
          setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (c * (ρ / 2) ^ (-α)) := by
          rw [lintegral_mul_const _ hHm, lintegral_heatK hε, one_mul]
  rw [← lintegral_add_compl _ hSm]
  calc (∫⁻ z in S, ENNReal.ofReal (heatK ε z) * riesz c α (x - z)) +
        ∫⁻ z in Sᶜ, ENNReal.ofReal (heatK ε z) * riesz c α (x - z)
      ≤ ENNReal.ofReal A * ENNReal.ofReal B + ENNReal.ofReal (c * (ρ / 2) ^ (-α)) :=
        add_le_add hnear hfar
    _ ≤ ENNReal.ofReal (16 / (1 - α) * (c * ρ ^ (-α))) +
          ENNReal.ofReal (2 * (c * ρ ^ (-α))) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        exact add_le_add (ENNReal.ofReal_le_ofReal (dom_real hc hα0 hα hε hρ))
          (ENNReal.ofReal_le_ofReal (half_rpow_le hc hα hρ))
    _ = ENNReal.ofReal (CA α) * riesz c α x := by
        have h1α : 0 < 1 - α := by linarith
        have hp : 0 ≤ c * ρ ^ (-α) := mul_nonneg hc (Real.rpow_nonneg hρ.le _)
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), riesz, ← hρdef,
          ← ENNReal.ofReal_mul (by unfold CA; positivity), CA]
        congr 1
        ring

/-! ### Pointwise convergence off `0` -/

/-- For `0 < ε < 1/2` and `|z| ≥ r > 0`: `p_ε(z) ≤ (4√ε/r²) p_1(z)`. -/
theorem heatK_le_ratio {ε r : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (hr : 0 < r) {z : Rd 1}
    (hz : r ≤ ‖z‖) : heatK ε z ≤ 4 * Real.sqrt ε / r ^ 2 * heatK 1 z := by
  rw [heatK_one_dim hε, heatK_one_dim one_pos]
  simp only [mul_one]
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi) ε]
  set P := Real.sqrt (2 * Real.pi) with hP
  have hPpos : 0 < P := Real.sqrt_pos.2 (by positivity)
  set s := Real.sqrt ε with hs
  have hspos : 0 < s := Real.sqrt_pos.2 hε
  have hss : s * s = ε := Real.mul_self_sqrt hε.le
  set q := ‖z‖ ^ 2 with hq
  have hrq : r ^ 2 ≤ q := pow_le_pow_left₀ hr.le hz 2
  have hqpos : 0 < q := lt_of_lt_of_le (by positivity) hrq
  set Y := q / (4 * ε) with hY
  have hYpos : 0 < Y := by positivity
  have hy : Real.exp (-(q / (2 * ε))) ≤ 4 * ε / r ^ 2 * Real.exp (-(q / 2)) := by
    have e1 : Real.exp (-(q / (2 * ε))) =
        Real.exp (-(q / (2 * ε)) + q / 2) * Real.exp (-(q / 2)) := by
      rw [← Real.exp_add]; ring_nf
    rw [e1]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    have h2Y : q / (2 * ε) = 2 * Y := by rw [hY]; field_simp; ring
    have hq2 : q / 2 ≤ Y := div_le_div_of_nonneg_left hqpos.le (by positivity) (by linarith)
    have h3 : -(q / (2 * ε)) + q / 2 ≤ -Y := by rw [h2Y]; linarith
    have h4 : Real.exp (-Y) ≤ Y⁻¹ := by
      rw [Real.exp_neg]
      exact inv_anti₀ hYpos (by linarith [Real.add_one_le_exp Y])
    have h5 : Y⁻¹ ≤ 4 * ε / r ^ 2 := by
      rw [hY, inv_div]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hrq
    exact (Real.exp_le_exp.2 h3).trans (h4.trans h5)
  calc (P * s)⁻¹ * Real.exp (-(q / (2 * ε)))
      ≤ (P * s)⁻¹ * (4 * ε / r ^ 2 * Real.exp (-(q / 2))) :=
        mul_le_mul_of_nonneg_left hy (by positivity)
    _ = 4 * s / r ^ 2 * (P⁻¹ * Real.exp (-(q / 2))) := by
        rw [← hss]; field_simp

/-- **Pointwise convergence** (d = 1): `(p_ε * c|·|^{-α})(x) → c|x|^{-α}` as `ε ↓ 0`, for
`x ≠ 0`. -/
theorem tendsto_covEps_riesz {c α : ℝ} (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα : α < 1) {x : Rd 1}
    (hx : x ≠ 0) :
    Tendsto (fun ε => covEps ((volume : Measure (Rd 1)).withDensity (riesz c α)) ε x)
      (𝓝[>] 0) (𝓝 (riesz c α x)) := by
  set r := ‖x‖ / 2 with hrdef
  have hr : 0 < r := by have := norm_pos_iff.2 hx; positivity
  set F : Rd 1 → ℝ≥0∞ := fun z => riesz c α (x - z) with hFdef
  have hFm : Measurable F := (measurable_riesz c α).comp (measurable_const.sub measurable_id)
  set B0 := Metric.ball (0 : Rd 1) r with hB0
  have hB0m : MeasurableSet B0 := Metric.isOpen_ball.measurableSet
  set F1 := B0.indicator F with hF1
  set F2 := B0ᶜ.indicator F with hF2
  have hF1m : Measurable F1 := hFm.indicator hB0m
  have hF2m : Measurable F2 := hFm.indicator hB0m.compl
  have hHm : ∀ ε : ℝ, Measurable fun z : Rd 1 => ENNReal.ofReal (heatK ε z) :=
    fun ε => (HigherRieszTwo.measurable_heatK ε).ennreal_ofReal
  have hsplit : ∀ ε, covEps ((volume : Measure (Rd 1)).withDensity (riesz c α)) ε x =
      (∫⁻ z, ENNReal.ofReal (heatK ε z) * F1 z) + ∫⁻ z, ENNReal.ofReal (heatK ε z) * F2 z := by
    intro ε
    have hm : Measurable fun z => ENNReal.ofReal (heatK ε z) * F1 z := (hHm ε).mul hF1m
    calc covEps ((volume : Measure (Rd 1)).withDensity (riesz c α)) ε x
        = ∫⁻ z, ENNReal.ofReal (heatK ε z) * F1 z + ENNReal.ofReal (heatK ε z) * F2 z := by
          rw [covEps_riesz]
          refine lintegral_congr fun z => ?_
          rw [← mul_add, hF1, hF2, Set.indicator_self_add_compl_apply]
      _ = _ := lintegral_add_left hm _
  -- the bounded part
  have hF1B : ∀ z, F1 z ≤ ENNReal.ofReal (c * r ^ (-α)) := by
    intro z
    by_cases hz : z ∈ B0
    · rw [hF1, indicator_of_mem hz, hFdef]
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hc)
      have hz' : ‖z‖ < r := by rw [hB0, mem_ball_zero_iff] at hz; exact hz
      have := norm_sub_norm_le x z
      exact Real.rpow_le_rpow_of_nonpos hr (by linarith) (by linarith)
    · rw [hF1, indicator_of_notMem hz]; exact bot_le
  have hev : F =ᶠ[𝓝 0] F1 :=
    Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
      fun z hz => (indicator_of_mem hz F).symm
  have hF10 : F1 0 = riesz c α x := by
    rw [hF1, indicator_of_mem (Metric.mem_ball_self hr), hFdef]; simp only [sub_zero]
  have hFc : ContinuousAt F 0 := by
    have h : ContinuousAt (fun z : Rd 1 => c * ‖x - z‖ ^ (-α)) 0 := by
      refine continuousAt_const.mul (ContinuousAt.rpow_const (by fun_prop) (Or.inl ?_))
      simpa using hx
    exact ENNReal.continuous_ofReal.continuousAt.comp h
  have hF1c : Tendsto F1 (𝓝 0) (𝓝 (F1 0)) := by
    have h1 : F1 0 = F 0 := by rw [hF10, hFdef]; simp only [sub_zero]
    rw [h1]
    exact hFc.tendsto.congr' hev
  have hI1 := tendsto_heat_avg hF1m ENNReal.ofReal_ne_top hF1B hF1c
  rw [hF10] at hI1
  -- the tail part
  have hM : ENNReal.ofReal (CA α) * riesz c α x ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hbound : ∀ ε ∈ Ioo (0 : ℝ) (1 / 2), ∫⁻ z, ENNReal.ofReal (heatK ε z) * F2 z ≤
      ENNReal.ofReal (4 * Real.sqrt ε / r ^ 2) * (ENNReal.ofReal (CA α) * riesz c α x) := by
    rintro ε ⟨h0, h1⟩
    calc ∫⁻ z, ENNReal.ofReal (heatK ε z) * F2 z
        ≤ ∫⁻ z, ENNReal.ofReal (4 * Real.sqrt ε / r ^ 2) * (ENNReal.ofReal (heatK 1 z) * F z) := by
          refine lintegral_mono fun z => ?_
          by_cases hz : z ∈ B0
          · rw [hF2, indicator_of_notMem (show z ∉ B0ᶜ from fun h => h hz), mul_zero]; exact bot_le
          · rw [hF2, indicator_of_mem hz, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
            refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) (zero_le)
            refine heatK_le_ratio h0 h1 hr ?_
            rw [hB0, mem_ball_zero_iff, not_lt] at hz
            exact hz
      _ = ENNReal.ofReal (4 * Real.sqrt ε / r ^ 2) * ∫⁻ z, ENNReal.ofReal (heatK 1 z) * F z :=
          lintegral_const_mul _ ((hHm 1).mul hFm)
      _ ≤ ENNReal.ofReal (4 * Real.sqrt ε / r ^ 2) * (ENNReal.ofReal (CA α) * riesz c α x) := by
          refine mul_le_mul_of_nonneg_left ?_ (zero_le)
          have := covEps_riesz_le hc hα0 hα one_pos hx
          rw [covEps_riesz] at this
          exact this
  have hsq : Tendsto (fun ε : ℝ => 4 * Real.sqrt ε / r ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous fun ε : ℝ => 4 * Real.sqrt ε / r ^ 2 := by fun_prop
    have h := hcont.tendsto 0
    simp only [Real.sqrt_zero, mul_zero, zero_div] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hup : Tendsto (fun ε : ℝ => ENNReal.ofReal (4 * Real.sqrt ε / r ^ 2) *
      (ENNReal.ofReal (CA α) * riesz c α x)) (𝓝[>] 0) (𝓝 0) := by
    have h := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal hsq) (Or.inr hM)
    rwa [ENNReal.ofReal_zero, zero_mul] at h
  have hI2 : Tendsto (fun ε => ∫⁻ z, ENNReal.ofReal (heatK ε z) * F2 z) (𝓝[>] 0) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
      (Eventually.of_forall fun _ => zero_le)
      (by filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with ε hε
          using hbound ε hε)
  have h := hI1.add hI2
  rw [add_zero] at h
  exact h.congr fun ε => (hsplit ε).symm

/-! ### Spatial parts -/

/-- The spatial part as a box integral. -/
theorem spatial_eq_box (γ : Rd 1 → ℝ≥0∞) (m : ℕ) {N : ℕ} (D : Fin N → Fin N) (h : Fin N → ℝ) :
    spatial (waveGreen 1) γ m D h = ENNReal.ofReal (1 / 2) ^ N *
      ∫⁻ w in Set.univ.pi (fun i => Metric.ball (0 : Rd 1) (h i)), covWeight γ D (pos m w) := by
  unfold spatial
  rw [DiagramBridge.pi_waveGreen_one, lintegral_smul_measure, smul_eq_mul]

/-- Off the pair diagonals, a.e. -/
theorem ae_offDiag (m : ℕ) {N : ℕ} (D : Fin N → Fin N) :
    ∀ᵐ w ∂(volume : Measure (Fin N → Rd 1)), ∀ i ∈ openers D, pos m w i ≠ pos m w (D i) := by
  rw [eventually_all_finset]
  intro i hi
  exact measure_eq_zero_iff_ae_notMem.1 (volume_pos_eq_null (m := m) hi)

theorem covWeight_covEps_le {c α ε : ℝ} (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα : α < 1) (hε : 0 < ε)
    {N : ℕ} (D : Fin N → Fin N) (y : Fin N → Rd 1) (hy : ∀ i ∈ openers D, y i ≠ y (D i)) :
    covWeight (covEps ((volume : Measure (Rd 1)).withDensity (riesz c α)) ε) D y ≤
      ENNReal.ofReal (CA α) ^ (openers D).card * covWeight (riesz c α) D y := by
  unfold covWeight
  rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod fun i hi =>
    covEps_riesz_le hc hα0 hα hε (sub_ne_zero.2 (hy i hi))

theorem tendsto_covWeight {c α : ℝ} (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα : α < 1)
    {N : ℕ} (D : Fin N → Fin N) (y : Fin N → Rd 1) (hy : ∀ i ∈ openers D, y i ≠ y (D i)) :
    Tendsto (fun ε => covWeight (covEps ((volume : Measure (Rd 1)).withDensity (riesz c α)) ε) D y)
      (𝓝[>] 0) (𝓝 (covWeight (riesz c α) D y)) :=
  ENNReal.tendsto_finsetProd_of_ne_top _
    (fun i hi => tendsto_covEps_riesz hc hα0 hα (sub_ne_zero.2 (hy i hi)))
    (fun _ _ => ENNReal.ofReal_ne_top)

/-- Uniform domination of the spatial parts. -/
theorem spatial_covEps_le {c α ε : ℝ} (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα : α < 1) (hε : 0 < ε)
    (m : ℕ) {N : ℕ} (D : Fin N → Fin N) (h : Fin N → ℝ) :
    spatial (waveGreen 1) (covEps ((volume : Measure (Rd 1)).withDensity (riesz c α)) ε) m D h ≤
      ENNReal.ofReal (CA α) ^ (openers D).card * spatial (waveGreen 1) (riesz c α) m D h := by
  rw [spatial_eq_box, spatial_eq_box, mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ (zero_le)
  rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
  exact lintegral_mono_ae ((ae_restrict_of_ae (ae_offDiag m D)).mono fun w hw =>
    covWeight_covEps_le hc hα0 hα hε D _ hw)

/-- Convergence of the spatial parts by dominated convergence over the Green box. -/
theorem tendsto_spatial {c α : ℝ} (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα : α < 1)
    (m : ℕ) {N : ℕ} (D : Fin N → Fin N) (h : Fin N → ℝ)
    (hfin : spatial (waveGreen 1) (riesz c α) m D h ≠ ⊤) :
    Tendsto (fun ε => spatial (waveGreen 1)
        (covEps ((volume : Measure (Rd 1)).withDensity (riesz c α)) ε) m D h)
      (𝓝[>] 0) (𝓝 (spatial (waveGreen 1) (riesz c α) m D h)) := by
  simp only [spatial_eq_box]
  refine ENNReal.Tendsto.const_mul ?_ (Or.inr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))
  have hbox : ∫⁻ w in Set.univ.pi (fun i => Metric.ball (0 : Rd 1) (h i)),
      covWeight (riesz c α) D (pos m w) ≠ ⊤ := by
    intro hI
    apply hfin
    rw [spatial_eq_box, hI,
      ENNReal.mul_top (pow_ne_zero _ (ENNReal.ofReal_pos.2 (by norm_num)).ne')]
  refine tendsto_lintegral_filter_of_dominated_convergence
    (fun w => ENNReal.ofReal (CA α) ^ (openers D).card * covWeight (riesz c α) D (pos m w))
    (eventually_nhdsWithin_of_forall fun ε _ =>
      measurable_covWeight_pos m (measurable_covEps_riesz c α ε) D)
    (eventually_nhdsWithin_of_forall fun ε hε => (ae_restrict_of_ae (ae_offDiag m D)).mono
      fun w hw => covWeight_covEps_le hc hα0 hα hε D _ hw) ?_
    ((ae_restrict_of_ae (ae_offDiag m D)).mono fun w hw => tendsto_covWeight hc hα0 hα D _ hw)
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
  exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hbox

/-! ### The diagram limits -/

/-- The cube bound of the Riesz spatial parts on the time simplex (as inside
`diagram_riesz_ne_top`). -/
def Csp (c α t : ℝ) (N k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / 2) ^ N *
    (ENNReal.ofReal (2 * (c * (2 * ((N : ℝ) * t)) ^ (1 - α) / (1 - α))) ^ k *
      volume (Metric.ball (0 : Rd 1) ((N : ℝ) * t)) ^ k)

theorem Csp_ne_top (c α t : ℝ) (N k : ℕ) : Csp c α t N k ≠ ⊤ :=
  ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.pow_ne_top measure_ball_lt_top.ne))

theorem spatial_riesz_le_Csp {c α : ℝ} (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα : α < 1) {m n : ℕ}
    {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n) {t : ℝ} (ht : 0 ≤ t) {s : Fin (m + n) → ℝ}
    (hs : s ∈ twoSimplex m n t) :
    spatial (waveGreen 1) (riesz c α) m D (incr m s) ≤ Csp c α t (m + n) (openers D).card := by
  have hR : (0 : ℝ) ≤ (m + n : ℕ) * t := mul_nonneg (Nat.cast_nonneg _) ht
  refine (spatial_le_cube m D ht fun i => (incr_lt_of_mem hs i).le).trans ?_
  unfold Csp
  gcongr
  exact lintegral_cube_covWeight_le hc hα0 hα hR (mem_Pi2.1 hD)

/-- **The Riesz diagrams converge** (d = 1, every order): `J_{m,n,D}(t)` with `γ_ε = p_ε * Γ`,
`Γ(dy) = c|y|^{-α} dy`, converges as `ε ↓ 0` to the density diagram. -/
theorem tendsto_diagram_riesz {c α α₀ : ℝ} (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα : α < 1)
    (h0 : 0 ≤ α₀) (h1 : α₀ < 1) {m n : ℕ} {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n)
    {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun ε => diagram (waveGreen 1)
        (covEps ((volume : Measure (Rd 1)).withDensity (riesz c α)) ε) α₀ m n D t)
      (𝓝[>] 0) (𝓝 (diagram (waveGreen 1) (riesz c α) α₀ m n D t)) :=
  tendsto_diagram_of_spatial (fun ε _ => measurable_covEps_riesz c α ε)
    (K := ENNReal.ofReal (CA α) ^ (openers D).card * Csp c α t (m + n) (openers D).card)
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (Csp_ne_top _ _ _ _ _))
    (lintegral_twoSimplex_timeWeight_ne_top h0 h1 ht (mem_Pi2.1 hD))
    (fun _ hε _ hs => (spatial_covEps_le hc hα0 hα hε m D _).trans
      (mul_le_mul_of_nonneg_left (spatial_riesz_le_Csp hc hα0 hα hD ht hs) (zero_le)))
    (fun _ hs => tendsto_spatial hc hα0 hα m D _
      (ne_top_of_le_ne_top (Csp_ne_top _ _ _ _ _) (spatial_riesz_le_Csp hc hα0 hα hD ht hs)))

/-- **`DiagramLimits` holds in the Riesz case** (d = 1), with nothing supplied. -/
theorem diagramLimits_riesz {c α α₀ t : ℝ} (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα : α < 1)
    (h0 : 0 ≤ α₀) (h1 : α₀ < 1) (ht : 0 ≤ t) :
    D1Upper.DiagramLimits 1 ((volume : Measure (Rd 1)).withDensity (riesz c α)) α₀ t := by
  intro m n D hD
  have h := tendsto_diagram_riesz hc hα0 hα h0 h1 hD ht
  rw [diagramLim, h.limUnder_eq]
  exact h

/-- The identification of the measure-form limit with the density diagram, every order. -/
theorem diagramLim_riesz_eq {c α α₀ t : ℝ} (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα : α < 1)
    (h0 : 0 ≤ α₀) (h1 : α₀ < 1) (ht : 0 ≤ t) {m n : ℕ} {D : Fin (m + n) → Fin (m + n)}
    (hD : D ∈ Pi2 m n) :
    diagramLim 1 ((volume : Measure (Rd 1)).withDensity (riesz c α)) α₀ m n D t =
      diagram (waveGreen 1) (riesz c α) α₀ m n D t :=
  (tendsto_diagram_riesz hc hα0 hα h0 h1 hD ht).limUnder_eq

/-- Successor of `D1Upper.coeffALim_riesz_le` with `DiagramLimits` discharged. -/
theorem coeffALim_riesz_le' {c α α₀ t : ℝ} (hc : 0 ≤ c) (hα0 : 0 < α) (hα1 : α < 1)
    (h0 : 0 ≤ α₀) (ha1 : α₀ < 1) (ht : 0 < t) {k : ℕ} (hk : 1 ≤ k) :
    coeffALim 1 (volume.withDensity (riesz c α)) α₀ k t ≤
        ENNReal.ofReal ((2 * Zc α₀ * Ksp c α) ^ k *
          t ^ ((4 - α - α₀) * k) / (k ! * (k : ℝ) ^ ((2 - α) * k))) ∧
      coeffALim 1 (volume.withDensity (riesz c α)) α₀ k t ≤
        ENNReal.ofReal ((2 * Zc α₀ * Ksp c α) ^ k *
          t ^ ((4 - α - α₀) * k) / (k ! : ℝ) ^ (3 - α)) :=
  D1Upper.coeffALim_riesz_le hc hα0 hα1 ha1 ht
    (diagramLimits_riesz hc hα0.le hα1 h0 ha1 ht.le) hk

/-- **`P:d1-upper`, Riesz case, the coefficient displays with no supplied input** (TeX lines
5454-5466 at revision edf7085f (book 1.1.3), proof Step 3 lines 5532-5538; `γ = c_α|y|^{-α}`):
with the manuscript's hypotheses `0 < α₀ < 1`, `c_α > 0`, `0 < α < 1`, `t > 0`, both
inequalities of `E:d1-coefficient` hold at every width `ε > 0` and for the limit `A_k(t)`
(`DiagramLimits` discharged by `diagramLimits_riesz`, domination route).  The moment display
`E:d1-upper` is not included (it is about `u`; see `D1Upper.d1_upper_paper_riesz`, which needs
`MixedMoment`).  `0 < α₀` is used only as `0 ≤ α₀` (time integrability in
`diagramLimits_riesz`; the binder keeps the frozen name `_hα₀0`); `c_α > 0` is used only as
`c_α ≥ 0`. -/
theorem d1_upper_paper_riesz' {c α α₀ t : ℝ} (_hα₀0 : 0 < α₀) (hα₀1 : α₀ < 1) (hc : 0 < c)
    (hα0 : 0 < α) (hα1 : α < 1) (ht : 0 < t) :
    (∀ ε : ℝ, 0 < ε → ∀ k : ℕ, 1 ≤ k →
      coeffA (waveGreen 1) (covEps (volume.withDensity (riesz c α)) ε) α₀ k t ≤
        ENNReal.ofReal ((2 * Zc α₀ * Ksp c α) ^ k * t ^ ((4 - α - α₀) * k) /
          (k ! * (k : ℝ) ^ ((2 - α) * k))) ∧
      coeffA (waveGreen 1) (covEps (volume.withDensity (riesz c α)) ε) α₀ k t ≤
        ENNReal.ofReal ((2 * Zc α₀ * Ksp c α) ^ k * t ^ ((4 - α - α₀) * k) / (k ! : ℝ) ^ (3 - α))) ∧
    (∀ k : ℕ, 1 ≤ k →
      coeffALim 1 (volume.withDensity (riesz c α)) α₀ k t ≤
        ENNReal.ofReal ((2 * Zc α₀ * Ksp c α) ^ k * t ^ ((4 - α - α₀) * k) /
          (k ! * (k : ℝ) ^ ((2 - α) * k))) ∧
      coeffALim 1 (volume.withDensity (riesz c α)) α₀ k t ≤
        ENNReal.ofReal ((2 * Zc α₀ * Ksp c α) ^ k * t ^ ((4 - α - α₀) * k) /
          (k ! : ℝ) ^ (3 - α))) :=
  ⟨fun _ hε _ hk => ⟨D1Upper.coeffA_riesz_le hc.le hα0 hα1 hα₀1 ht hε hk,
      D1Upper.coeffA_riesz_le_factorial hc.le hα0 hα1 hα₀1 ht hε hk⟩,
    fun _ hk => coeffALim_riesz_le' hc.le hα0 hα1 _hα₀0.le hα₀1 ht hk⟩

end StratonovichHAMSecondMoment.RieszDiagramLimits
