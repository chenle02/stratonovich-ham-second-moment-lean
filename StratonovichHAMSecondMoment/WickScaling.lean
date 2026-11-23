module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L18, item L18-C, part 3: the scaling of the spatial Wick measures, the frozen target
`WickInterface.RhoScalingTarget` (Step 5 of the proof of `L:spatial-wick-measures`, TeX lines
1831-1838 at revision edf7085f (book 1.1.3)): `ρ_{ε,D}(cA) = c^{(4-α)k} ρ_{ε/c²,D}(A)`.

Formalized (all proved, nothing supplied):
* `heatDens_smul`: `p_b(cw) = c^{-d} p_{b/c²}(w)`;
* `covEps_smul`: `γ_b(cx) = c^{-α} γ_{b/c²}(x)` from `H:homog`'s `Γ(cA) = c^{d-α} Γ(A)`;
* `waveGreen_mul`: `G_{cs} = c · (z ↦ cz)_* G_s` (from `WaveGreen.waveGreen_scaling`, TeX
  1836, 6131-6132; also for `s ≤ 0`, where both sides vanish);
* `wickJ_smul`: `J_{ε,D}(cr) = c^{2k} c^{-αk} J_{ε/c²,D}(r)` (the `2k` Green factors and the `k`
  covariance factors);
* `rho_scaling` (`RhoScalingTarget d`): with the `2k` time Jacobians of `r ↦ cr`.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.WickInterface

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal Real Pointwise

namespace StratonovichHAMSecondMoment.WickScaling

open HomogHypothesis (Rd HomogCovariance)
open LowAlphaConvolution (heatDens)
open DiagramModel (Pi2 openers covEps pos)
open WaveGreen (waveGreen)
open WickInterface

variable {d : ℕ}

/-! ### The heat kernel and the smoothed covariance -/

/-- `p_b(cw) = c^{-d} p_{b/c²}(w)` for `b, c > 0`. -/
theorem heatDens_smul {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (w : Rd d) :
    heatDens b (c • w) = c ^ (-(d : ℝ)) * heatDens (b / c ^ 2) w := by
  unfold heatDens
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  have h1 : 2 * π * (b / c ^ 2) = (2 * π * b) * (c ^ 2)⁻¹ := by ring
  have h2 : ((c ^ 2)⁻¹ : ℝ) ^ (-((d : ℝ) / 2)) = c ^ (d : ℝ) := by
    rw [Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity), neg_neg,
      ← Real.rpow_natCast c 2, ← Real.rpow_mul hc.le]
    congr 1; push_cast; ring
  rw [h1, Real.mul_rpow (x := 2 * π * b) (by positivity) (by positivity), h2]
  have h3 : -((c * ‖w‖) ^ 2 / (2 * b)) = -(‖w‖ ^ 2 / (2 * (b / c ^ 2))) := by
    field_simp
  rw [h3]
  have h4 : c ^ (-(d : ℝ)) * c ^ (d : ℝ) = 1 := by
    rw [← Real.rpow_add hc]; simp
  calc (2 * π * b) ^ (-((d : ℝ) / 2)) * Real.exp (-(‖w‖ ^ 2 / (2 * (b / c ^ 2))))
      = (c ^ (-(d : ℝ)) * c ^ (d : ℝ)) * ((2 * π * b) ^ (-((d : ℝ) / 2)) *
          Real.exp (-(‖w‖ ^ 2 / (2 * (b / c ^ 2))))) := by rw [h4, one_mul]
    _ = _ := by ring

section Cov

variable {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}

/-- `H:homog`'s scaling as a push-forward: `(z ↦ c⁻¹z)_* Γ = c^{d-α} Γ`. -/
theorem map_inv_smul_Γ (hH : HomogCovariance d alpha α₀ Γ μ) {c : ℝ} (hc : 0 < c) :
    Γ.map (fun z => c⁻¹ • z) = ENNReal.ofReal (c ^ ((d : ℝ) - alpha)) • Γ := by
  ext A hA
  rw [Measure.map_apply (measurable_const_smul _) hA, Measure.smul_apply, smul_eq_mul,
    ← hH.scaling A hA c hc]
  congr 1
  ext z
  simp only [mem_preimage]
  exact (mem_smul_set_iff_inv_smul_mem₀ hc.ne' A z).symm

/-- **The scaling of the smoothed covariance** (TeX 1831-1838): `γ_b(cx) = c^{-α} γ_{b/c²}(x)`
for `b, c > 0`. -/
theorem covEps_smul (hH : HomogCovariance d alpha α₀ Γ μ) {b c : ℝ} (hb : 0 < b) (hc : 0 < c)
    (x : Rd d) :
    covEps Γ b (c • x) = ENNReal.ofReal (c ^ (-alpha)) * covEps Γ (b / c ^ 2) x := by
  let e : Rd d ≃ᵐ Rd d := (Homeomorph.smulOfNeZero c⁻¹ (inv_ne_zero hc.ne')).toMeasurableEquiv
  have he : (⇑e : Rd d → Rd d) = fun z => c⁻¹ • z := rfl
  have key := lintegral_map_equiv (fun z' : Rd d => ENNReal.ofReal (heatDens b (c • (x - z'))))
    e (μ := Γ)
  have hm : Γ.map e = ENNReal.ofReal (c ^ ((d : ℝ) - alpha)) • Γ := by
    rw [he]; exact map_inv_smul_Γ hH hc
  rw [hm, lintegral_smul_measure, smul_eq_mul] at key
  unfold covEps
  have h1 : ∀ z : Rd d, ENNReal.ofReal (heatDens b (c • x - z)) =
      ENNReal.ofReal (heatDens b (c • (x - c⁻¹ • z))) := fun z => by
    rw [smul_sub, smul_inv_smul₀ hc.ne']
  simp_rw [h1]
  change ∫⁻ z, (fun z' : Rd d => ENNReal.ofReal (heatDens b (c • (x - z')))) (e z) ∂Γ = _
  rw [← key]
  simp_rw [heatDens_smul hb hc]
  have h2 : ∀ z : Rd d, ENNReal.ofReal (c ^ (-(d : ℝ)) * heatDens (b / c ^ 2) (x - z)) =
      ENNReal.ofReal (c ^ (-(d : ℝ))) * ENNReal.ofReal (heatDens (b / c ^ 2) (x - z)) :=
    fun z => ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _)
  simp_rw [h2]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _), ← Real.rpow_add hc]
  congr 3
  ring

end Cov

/-! ### The Green measures -/

/-- **`G_{cs} = c · (z ↦ cz)_* G_s`** for `c > 0` and every `s` (TeX 1836, 6131-6132). -/
theorem waveGreen_mul (hd : d = 1 ∨ d = 2 ∨ d = 3) {c : ℝ} (hc : 0 < c) (s : ℝ) :
    waveGreen d (c * s) = ENNReal.ofReal c • (waveGreen d s).map (fun z => c • z) := by
  rcases le_or_gt s 0 with hs | hs
  · rw [WaveGreen.waveGreen_of_nonpos d s hs, WaveGreen.waveGreen_of_nonpos d _
      (mul_nonpos_of_nonneg_of_nonpos hc.le hs)]
    simp
  ext A hA
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply (measurable_const_smul _) hA]
  have hpre : (fun z : Rd d => c • z) ⁻¹' A = c⁻¹ • A := by
    ext z
    simp only [mem_preimage]
    rw [mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hc.ne'), inv_inv]
  rw [hpre]
  have hcs : 0 < c * s := mul_pos hc hs
  have hA1 : MeasurableSet ((c * s)⁻¹ • A) := hA.const_smul₀ _
  have hA2 : MeasurableSet (s⁻¹ • c⁻¹ • A) := (hA.const_smul₀ _).const_smul₀ _
  have e1 : A = (c * s) • ((c * s)⁻¹ • A) := by rw [smul_inv_smul₀ hcs.ne']
  have e2 : c⁻¹ • A = s • (s⁻¹ • c⁻¹ • A) := by rw [smul_inv_smul₀ hs.ne']
  have e3 : (c * s)⁻¹ • A = s⁻¹ • c⁻¹ • A := by rw [smul_smul, mul_inv, mul_comm]
  conv_lhs => rw [e1]
  rw [e2, WaveGreen.waveGreen_scaling d hd _ hcs _ hA1, WaveGreen.waveGreen_scaling d hd _ hs _ hA2,
    e3, ← mul_assoc, ← ENNReal.ofReal_mul hc.le]

/-! ### The spatial part -/

section Spatial

variable {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}

/-- The positions of scaled increments are the scaled positions. -/
theorem pos_smul (m : ℕ) {N : ℕ} (c : ℝ) (w : Fin N → Rd d) : pos m (c • w) = c • pos m w := by
  funext i
  simp only [pos, Pi.smul_apply, Finset.smul_sum]

/-- The vertexwise covariance product at scaled positions:
`∏ γ_{ε_j+ε_h}(c(y_j - y_h)) = c^{-αk} ∏ γ_{(ε_j+ε_h)/c²}(y_j - y_h)`. -/
theorem covW_smul (hH : HomogCovariance d alpha α₀ Γ μ) {m n k : ℕ} (hmn : m + n = 2 * k)
    {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n) {ε : Fin (m + n) → ℝ}
    (hε : ∀ i, 0 < ε i) {c : ℝ} (hc : 0 < c) (y : Fin (m + n) → Rd d) :
    covW Γ ε D (c • y) =
      ENNReal.ofReal (c ^ (-alpha)) ^ k * covW Γ (fun i => ε i / c ^ 2) D y := by
  unfold covW
  rw [← DiagramModel.card_openers hD hmn, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply]
  rw [← smul_sub, covEps_smul hH (add_pos (hε i) (hε (D i))) hc, add_div]

/-- **The scaling of `J_{ε,D}`**: `J_{ε,D}(cr) = c^{2k} c^{-αk} J_{ε/c²,D}(r)` for `c > 0` and
every `r`. -/
theorem wickJ_smul (hH : HomogCovariance d alpha α₀ Γ μ) {m n k : ℕ} (hmn : m + n = 2 * k)
    {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n) {ε : Fin (m + n) → ℝ}
    (hε : ∀ i, 0 < ε i) {c : ℝ} (hc : 0 < c) (r : Fin (m + n) → ℝ) :
    wickJ (waveGreen d) Γ ε m D (c • r) =
      ENNReal.ofReal c ^ (m + n) * ENNReal.ofReal (c ^ (-alpha)) ^ k *
        wickJ (waveGreen d) Γ (fun i => ε i / c ^ 2) m D r := by
  have hfin : ∀ s, IsFiniteMeasure (waveGreen d s) := WaveGreen.isFiniteMeasure_waveGreen d
  have hpi : Measure.pi (fun i => waveGreen d ((c • r) i)) =
      ENNReal.ofReal c ^ (m + n) •
        (Measure.pi fun i => waveGreen d (r i)).map (fun w => c • w) := by
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply (measurable_const_smul _)
      (MeasurableSet.univ_pi hs)]
    have hpre : (fun w : Fin (m + n) → Rd d => c • w) ⁻¹' univ.pi s =
        univ.pi fun i => (fun z : Rd d => c • z) ⁻¹' s i := by
      ext w; simp [Pi.smul_apply]
    have hpow : ENNReal.ofReal c ^ (m + n) = ∏ _i : Fin (m + n), ENNReal.ofReal c := by simp
    rw [hpre, Measure.pi_pi, hpow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, waveGreen_mul hH.dim hc, Measure.smul_apply, smul_eq_mul,
      Measure.map_apply (measurable_const_smul _) (hs i)]
  unfold wickJ
  rw [hpi, lintegral_smul_measure, smul_eq_mul]
  let e : (Fin (m + n) → Rd d) ≃ᵐ (Fin (m + n) → Rd d) :=
    (Homeomorph.smulOfNeZero c hc.ne').toMeasurableEquiv
  have he : (⇑e : (Fin (m + n) → Rd d) → (Fin (m + n) → Rd d)) = fun w => c • w := rfl
  rw [← he, lintegral_map_equiv, he]
  simp_rw [pos_smul, covW_smul hH hmn hD hε hc]
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top), mul_assoc]

end Spatial

/-! ### The scaling of `ρ_{ε,D}` -/

/-- **The scaling of `ρ_{ε,D}`** (`RhoScalingTarget`; Step 5, TeX lines 1831-1838 at revision
edf7085f (book 1.1.3)): under `H:homog`, for Borel `A` and `c > 0`,
`ρ_{ε,D}(cA) = c^{(4-α)k} ρ_{ε/c²,D}(A)`: `c^{2k}` from the time Jacobian of `r ↦ cr`, `c^{2k}`
from the Green masses (`G_{cs} = c (c·)_* G_s`) and `c^{-αk}` from the covariances
(`γ_b(cx) = c^{-α} γ_{b/c²}(x)`). -/
theorem rho_scaling (d : ℕ) : RhoScalingTarget d := by
  intro alpha α₀ Γ μ hH m n k hmn hk D hD ε hε c hc A hA
  have hO : MeasurableSet (posOrthant (m + n)) := MeasurableSet.univ_pi fun _ => measurableSet_Ioi
  have hcA : MeasurableSet (c • A) := hA.const_smul₀ c
  unfold wickRho
  rw [withDensity_apply _ hcA, withDensity_apply _ hA, Measure.restrict_restrict hcA,
    Measure.restrict_restrict hA, ← lintegral_indicator (hcA.inter hO),
    ← lintegral_indicator (hA.inter hO)]
  -- the change of variables `r = c r'`
  have hmap := Measure.map_addHaar_smul (volume : Measure (Fin (m + n) → ℝ)) hc.ne'
  rw [Module.finrank_fin_fun] at hmap
  have hcv : ∀ F : (Fin (m + n) → ℝ) → ℝ≥0∞,
      ∫⁻ r, F r = ENNReal.ofReal (c ^ (m + n)) * ∫⁻ r, F (c • r) := by
    intro F
    let e : (Fin (m + n) → ℝ) ≃ᵐ (Fin (m + n) → ℝ) := (Homeomorph.smulOfNeZero c hc.ne').toMeasurableEquiv
    have he : (⇑e : (Fin (m + n) → ℝ) → (Fin (m + n) → ℝ)) = fun r => c • r := rfl
    have h1 := lintegral_map_equiv F e (μ := (volume : Measure (Fin (m + n) → ℝ)))
    rw [he, hmap, lintegral_smul_measure, smul_eq_mul] at h1
    rw [show (∫⁻ r, F (c • r)) = ∫⁻ r, F (e r) from rfl, he, ← h1, ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity), abs_of_pos (by positivity),
      mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]
  rw [hcv]
  have hpt : ∀ r : Fin (m + n) → ℝ, ((c • A) ∩ posOrthant (m + n)).indicator
      (wickJ (waveGreen d) Γ ε m D) (c • r) =
      ENNReal.ofReal c ^ (m + n) * ENNReal.ofReal (c ^ (-alpha)) ^ k *
        (A ∩ posOrthant (m + n)).indicator (wickJ (waveGreen d) Γ (fun i => ε i / c ^ 2) m D) r := by
    intro r
    have hmem : c • r ∈ (c • A) ∩ posOrthant (m + n) ↔ r ∈ A ∩ posOrthant (m + n) := by
      rw [mem_inter_iff, mem_inter_iff, smul_mem_smul_set_iff₀ hc.ne']
      refine and_congr Iff.rfl ?_
      simp only [posOrthant, Set.mem_pi, mem_univ, mem_Ioi, forall_const, Pi.smul_apply,
        smul_eq_mul]
      exact forall_congr' fun i => mul_pos_iff_of_pos_left hc
    by_cases hr : r ∈ A ∩ posOrthant (m + n)
    · rw [indicator_of_mem (hmem.2 hr), indicator_of_mem hr, wickJ_smul hH hmn hD hε hc]
    · rw [indicator_of_notMem (mt hmem.1 hr), indicator_of_notMem hr, mul_zero]
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)), ← mul_assoc, ← mul_assoc]
  congr 1
  rw [← ENNReal.ofReal_pow hc.le, ← ENNReal.ofReal_pow (Real.rpow_nonneg hc.le _),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hc.le,
    ← Real.rpow_add hc, ← Real.rpow_add hc]
  congr 1
  rw [hmn]
  push_cast
  ring

end StratonovichHAMSecondMoment.WickScaling
