module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Lemma `L:higher-riesz` (Riesz spatial maxima) of the main TeX file
`notes/notes_stratonovich_ham_second_moment.tex` at revision edf7085f
(statement lines 6103-6112, proof 6114-6190), the dimension-two clause in full
and the steps shared with dimension three; and Hypothesis `H:spatial-maximum`
(lines 5919-5929, with the section's notation, lines 5912-5917).  All main-TeX
line numbers below are at edf7085f.

Definitions (new; `heatK` is `VariationalMean.heatK`, `G_h` is
`WaveGreen.waveGreen d h`):
* `riesz c α` is `γ(x) = c|x|^{-α}` (line 6104), `ℝ≥0∞`-valued;
* `smoothCov g ε` is `γ_ε = p_ε * γ` (line 5916) and `smoothGreen ν η` is
  `G_{h,η} = p_η * G_h`, `G_{h,0} = G_h` (lines 5916-5917), both through lower
  Lebesgue integrals; `pairing` is `∫ G_{h,η}(dy) γ_ε(y + z)`;
* `SpatialMaximum d g δ M` is `H:spatial-maximum` for `G_h = waveGreen d h` and
  a covariance with density `g`: `M > 0` and
  `∫ G_{h,η}(dy) γ_ε(y + z) ≤ M h^{-δ}` for all `h > 0`, `z`, `ε > 0`, `η ≥ 0`.
  NARROWER than the TeX in one respect: the TeX's covariance is the
  `H:homog` measure `Γ`; here it must have a density (as in `L:higher-riesz`).
  The lower bound `0 ≤` is automatic for the lower integral, and
  `SpatialMaximum.real_form` gives the real-valued form with integrability;
* `M2 c α = c{4^α + (2α/(3/2-α)) 4^{α-3/2}}` (lines 6108-6111);
* `F3 v ρ = ((1+ρ)^v - |1-ρ|^v)/(2vρ)` (lines 6136-6138).

Formalized, nothing supplied:
* (a) `ball_mass_two`: `G_1^{(2)}(B(w,R)) ≤ 2R^{3/2}` for every `w ∈ ℝ²` and
  `0 < R ≤ 1/4` (lines 6152-6159);
* (b) `layer_cake_le`, `F2_le`: `F_2(w) ≤ 4^α + (2α/(3/2-α)) 4^{α-3/2}` for
  `0 < α < 3/2` and every `w` (lines 6160-6166);
* (c) `unsmoothed_scaling`: `∫ G_h(dy) γ(y + z) = c h^{1-α} F_d(z/h)` for
  `d ∈ {1,2,3}`, `h > 0`, `c ≥ 0` (lines 6131-6134);
* (d) `average_le`, `smoothed_average_le`: a bound on `∫ ν(dy) γ(y + x)`
  uniform in `x` passes to `∫ (p_η * ν)(dy) γ_ε(y + z)` for all `ε > 0`,
  `η ≥ 0` (lines 6172-6178), any `d`, any s-finite `ν`;
* `higher_riesz_two` and the wrapper `higher_riesz_two_paper`: in `d = 2`,
  `H:spatial-maximum` holds with `δ = α - 1` and `M = M_2` (the dimension-two
  clause of `L:higher-riesz`);
* (e) `F3_max`: for `1 < α < 2`, `F3 (2-α) ρ ≤ F3 (2-α) 1` for every `ρ > 0`
  and `F3 (2-α) 1 = 2^{1-α}/(2-α)` (lines 6140-6146);
* (f) `approx_identity`: for `f(y) = |y|^{-λ}` on `ℝ^j`, `0 < λ < j`, `x ≠ 0`,
  each `∫ p_ε(x - y) f(y) dy` (`ε > 0`) is integrable and tends to `f(x)` as
  `ε ↓ 0` (lines 6178-6186).

The dimension-three clause is in `HigherRieszThree` (wave L10-R3): the
identity `F_3(w) = F3 (2-α) |w|` by spherical coordinates (lines 6134-6138) is
`HigherRieszThree.F3w_eq`, `H:spatial-maximum` in `d = 3` with `M_3` is
`HigherRieszThree.higher_riesz_three`, and the optimality of `M_3` by Fatou's
lemma at a maximizing shift (lines 6186-6189) is
`HigherRieszThree.higher_riesz_three_optimal`.  Only the maximum of the closed
form is proved, not its monotonicity on each side of `ρ = 1`.

Differences from the TeX's proof route (statements unchanged):
* (a) a reflection (`Submodule.reflection_sub`) instead of a rotation; for
  `|w| < 1/2` the density bound `1/π` instead of `2/(π√7)`, giving mass `≤ R²`
  instead of `2R²/√7` (both `≤ 2R^{3/2}`); the slice bound by the closed form
  `2(√(L-a) - √(L-b)) ≤ 2√(b-a)`;
* (b) the layer cake in the level `t` directly instead of the radius
  `R = t^{-1/α}`;
* (d) two successive Tonelli averages (first the Green width, then the
  covariance width) instead of `p_ε * p_η = p_{ε+η}`;
* (e) the convexity of `ψ(ρ) = (1+ρ)^v - (1-ρ)^v` on `[0,1]` (second
  derivative) and subadditivity of `t ↦ t^v` for `ρ ≥ 1`, instead of the
  TeX's monotonicity argument;
* (f) a split at `|y| = 2|x|` and Mathlib's peak-function theorem
  (`tendsto_integral_comp_smul_smul_of_integrable'`) instead of the TeX's
  three regions.

Junk values: `riesz` at `x = 0` is `0` (Lean's `0^{-α} = 0`); `γ` is
integrated only against Lebesgue measure (in `smoothCov`) or the absolutely
continuous `G_h^{(2)}`, so the value at `0` does not matter.  All integrals in
the statements are lower integrals (never junk) or carry integrability.
Lemmas marked "Auxiliary to the Lean proof route" have no manuscript label.
-/

public import Mathlib
public import StratonovichHAMSecondMoment.HomogHypothesis
public import StratonovichHAMSecondMoment.VariationalMean
public import StratonovichHAMSecondMoment.WaveGreen

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Real Metric Filter
open scoped ENNReal NNReal Pointwise Topology

namespace StratonovichHAMSecondMoment.HigherRieszTwo

open HomogHypothesis (Rd HomogCovariance)
open VariationalMean (heatK heatK_pos)
open WaveGreen (waveGreen waveGreen_scaling isFiniteMeasure_waveGreen)

variable {d : ℕ}

/-! ### Definitions -/

/-- The Riesz covariance density `γ(x) = c|x|^{-α}` (main TeX line 6104), as an
`ℝ≥0∞`-valued function.  At `x = 0` Lean's real power gives `0^{-α} = 0`; the
point `0` is Lebesgue-null and `γ` is only ever integrated against Lebesgue
measure (in `smoothCov`) or against the absolutely continuous `G^{(2)}_h`. -/
def riesz (c α : ℝ) (x : Rd d) : ℝ≥0∞ :=
  ENNReal.ofReal (c * ‖x‖ ^ (-α))

/-- The smoothed covariance `γ_ε = p_ε * γ` (main TeX line 5916),
`γ_ε(x) = ∫ p_ε(x - y) γ(y) dy`, for an `ℝ≥0∞`-valued density `γ`, as a
lower Lebesgue integral (so it is never a junk value). -/
def smoothCov (g : Rd d → ℝ≥0∞) (ε : ℝ) (x : Rd d) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (heatK ε (x - y)) * g y

/-- The smoothed Green measure `G_{h,η} = p_η * G_h` with `G_{h,0} = G_h`
(main TeX lines 5916-5917), for a measure `ν` in place of `G_h`: for `η ≠ 0`
the Lebesgue measure with density `y ↦ ∫ p_η(y - y') ν(dy')`. -/
def smoothGreen (ν : Measure (Rd d)) (η : ℝ) : Measure (Rd d) :=
  if η = 0 then ν else
    volume.withDensity fun y => ∫⁻ y', ENNReal.ofReal (heatK η (y - y')) ∂ν

/-- The pairing `∫ G_{h,η}(dy) γ_ε(y + z)` of `E:higher-convolution`, for a
Green family `G`, as a lower Lebesgue integral. -/
def pairing (G : ℝ → Measure (Rd d)) (g : Rd d → ℝ≥0∞) (h η ε : ℝ) (z : Rd d) : ℝ≥0∞ :=
  ∫⁻ y, smoothCov g ε (y + z) ∂(smoothGreen (G h) η)

/-- Hypothesis `H:spatial-maximum` (main TeX lines 5919-5929) for the wave
Green measures `G_h = waveGreen d h` and a covariance with density `γ`:
there is `M > 0` with `∫ G_{h,η}(dy) γ_ε(y + z) ≤ M h^{-δ}` for every `h > 0`,
`z`, `ε > 0`, `η ≥ 0`.  The integral is the lower Lebesgue integral of the
nonnegative integrand, so the lower bound `0 ≤` of `E:higher-convolution` is
automatic and the upper bound forces finiteness;
`SpatialMaximum.real_form` gives the real-valued statement with
integrability. -/
def SpatialMaximum (d : ℕ) (g : Rd d → ℝ≥0∞) (δ M : ℝ) : Prop :=
  0 < M ∧ ∀ h : ℝ, 0 < h → ∀ z : Rd d, ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 ≤ η →
    pairing (waveGreen d) g h η ε z ≤ ENNReal.ofReal (M * h ^ (-δ))

/-- The constant `M_2 = c{4^α + (2α/(3/2-α)) 4^{α-3/2}}` of `L:higher-riesz`
(main TeX lines 6108-6111). -/
def M2 (c α : ℝ) : ℝ :=
  c * (4 ^ α + 2 * α / (3 / 2 - α) * 4 ^ (α - 3 / 2))

/-! ### The heat kernel -/

/-- Auxiliary to the Lean proof route: `p_ε` is continuous. -/
@[fun_prop]
theorem continuous_heatK (ε : ℝ) : Continuous (heatK ε : Rd d → ℝ) := by
  unfold heatK; fun_prop

/-- Auxiliary to the Lean proof route: `p_ε` is measurable. -/
@[fun_prop]
theorem measurable_heatK (ε : ℝ) : Measurable (heatK ε : Rd d → ℝ) :=
  (continuous_heatK ε).measurable

/-- Auxiliary to the Lean proof route: `∫ p_ε = 1` for `ε > 0` (Bochner form,
with integrability; the "mass-one" of line 6177). -/
theorem integral_heatK {ε : ℝ} (hε : 0 < ε) :
    Integrable (heatK ε : Rd d → ℝ) ∧ ∫ x, heatK ε (x : Rd d) = 1 := by
  have hI : ∫ x, heatK ε (x : Rd d) = 1 := by
    have e : ∀ x : Rd d, heatK ε x =
        (2 * π * ε) ^ (-((d : ℝ) / 2)) * Real.exp (-(1 / (2 * ε)) * ‖x‖ ^ 2) := by
      intro x; unfold heatK; congr 2; field_simp
    simp_rw [e]
    rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity)]
    simp only [finrank_euclideanSpace, Fintype.card_fin]
    have h2 : π / (1 / (2 * ε)) = 2 * π * ε := by field_simp
    rw [h2, Real.rpow_neg (by positivity), inv_mul_cancel₀ (by positivity)]
  exact ⟨Integrable.of_integral_ne_zero (by rw [hI]; norm_num), hI⟩

/-- Auxiliary to the Lean proof route: `∫ p_ε = 1` for `ε > 0`, as a lower integral. -/
theorem lintegral_heatK {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ x, ENNReal.ofReal (heatK ε (x : Rd d)) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integral_heatK hε).1
    (Eventually.of_forall fun x => (heatK_pos hε x).le), (integral_heatK hε).2,
    ENNReal.ofReal_one]

/-! ### Gaussian averaging (step (d)) -/

/-- Auxiliary to the Lean proof route: `γ_ε` is measurable. -/
theorem measurable_smoothCov {g : Rd d → ℝ≥0∞} (hg : Measurable g) (ε : ℝ) :
    Measurable (smoothCov g ε) := by
  have : Measurable fun p : Rd d × Rd d => ENNReal.ofReal (heatK ε (p.1 - p.2)) * g p.2 :=
    ((measurable_heatK ε).comp (measurable_fst.sub measurable_snd)).ennreal_ofReal.mul
      (hg.comp measurable_snd)
  exact this.lintegral_prod_right'

/-- Auxiliary to the Lean proof route: `γ_ε(x) = ∫ p_ε(b) γ(x - b) db`. -/
theorem smoothCov_eq (g : Rd d → ℝ≥0∞) (ε : ℝ) (x : Rd d) :
    smoothCov g ε x = ∫⁻ b, ENNReal.ofReal (heatK ε b) * g (x - b) := by
  unfold smoothCov
  rw [← lintegral_sub_left_eq_self
    (fun y => ENNReal.ofReal (heatK ε (x - y)) * g y) x]
  simp only [sub_sub_cancel]

/-- Step (d), one average (Tonelli, no semigroup property): if
`∫ γ(y + x) ν(dy) ≤ B` for every shift `x`, then
`∫ γ_ε(y + z) ν(dy) ≤ B` for every `z` and `ε > 0`.  General `d`, any
s-finite `ν`, any measurable `γ ≥ 0`. -/
theorem average_le {ν : Measure (Rd d)} [SFinite ν] {g : Rd d → ℝ≥0∞} (hg : Measurable g)
    {ε : ℝ} (hε : 0 < ε) {B : ℝ≥0∞} (hB : ∀ x, ∫⁻ y, g (y + x) ∂ν ≤ B) (z : Rd d) :
    ∫⁻ y, smoothCov g ε (y + z) ∂ν ≤ B := by
  have hmeas : Measurable (Function.uncurry fun (y b : Rd d) =>
      ENNReal.ofReal (heatK ε b) * g (y + (z - b))) :=
    ((measurable_heatK ε).comp measurable_snd).ennreal_ofReal.mul
      (hg.comp (measurable_fst.add (measurable_const.sub measurable_snd)))
  calc ∫⁻ y, smoothCov g ε (y + z) ∂ν
      = ∫⁻ y, (∫⁻ b, ENNReal.ofReal (heatK ε b) * g (y + (z - b))) ∂ν := by
        refine lintegral_congr fun y => ?_
        rw [smoothCov_eq]
        simp only [add_sub_assoc]
    _ = ∫⁻ b, (∫⁻ y, ENNReal.ofReal (heatK ε b) * g (y + (z - b)) ∂ν) :=
        lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ b, ENNReal.ofReal (heatK ε b) * ∫⁻ y, g (y + (z - b)) ∂ν := by
        refine lintegral_congr fun b => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ∫⁻ b, ENNReal.ofReal (heatK ε b) * B :=
        lintegral_mono fun b => mul_le_mul_right (hB _) _
    _ = B := by
        rw [lintegral_mul_const _ (measurable_heatK ε).ennreal_ofReal, lintegral_heatK hε,
          one_mul]

/-- Step (d), double average (main TeX lines 6172-6178, "Mass-one averaging
preserves both supremum bounds"): if `∫ γ(y + x) ν(dy) ≤ B` for every
shift `x`, then `∫ (p_η * ν)(dy) γ_ε(y + z) ≤ B` for every `z`, `ε > 0` and
`η ≥ 0`.  Proved by Tonelli and translation invariance of Lebesgue measure,
averaging first in the Green width and then in the covariance width; the
TeX combines the two widths with `p_ε * p_η = p_{ε+η}`, which this route does
not need. -/
theorem smoothed_average_le {ν : Measure (Rd d)} [SFinite ν] {g : Rd d → ℝ≥0∞}
    (hg : Measurable g) {ε η : ℝ} (hε : 0 < ε) (hη : 0 ≤ η) {B : ℝ≥0∞}
    (hB : ∀ x, ∫⁻ y, g (y + x) ∂ν ≤ B) (z : Rd d) :
    ∫⁻ y, smoothCov g ε (y + z) ∂(smoothGreen ν η) ≤ B := by
  rcases hη.lt_or_eq with hη | hη
  swap
  · subst hη
    simp only [smoothGreen, ite_true]
    exact average_le hg hε hB z
  have hS := measurable_smoothCov hg ε
  have hDm : Measurable fun y : Rd d => ∫⁻ y', ENNReal.ofReal (heatK η (y - y')) ∂ν :=
    (((measurable_heatK η).comp (measurable_fst.sub measurable_snd)).ennreal_ofReal :
      Measurable fun p : Rd d × Rd d => ENNReal.ofReal (heatK η (p.1 - p.2))).lintegral_prod_right'
  have hB' : ∀ x, ∫⁻ y, smoothCov g ε (y + x) ∂ν ≤ B := fun x => average_le hg hε hB x
  simp only [smoothGreen, hη.ne', ite_false]
  rw [lintegral_withDensity_eq_lintegral_mul _ hDm (g := fun y => smoothCov g ε (y + z))
    (hS.comp (measurable_add_const z))]
  have hm1 : Measurable (Function.uncurry fun (y y' : Rd d) =>
      ENNReal.ofReal (heatK η (y - y')) * smoothCov g ε (y + z)) :=
    ((measurable_heatK η).comp (measurable_fst.sub measurable_snd)).ennreal_ofReal.mul
      (hS.comp (measurable_fst.add_const z))
  have hm2 : Measurable (Function.uncurry fun (y' a : Rd d) =>
      ENNReal.ofReal (heatK η a) * smoothCov g ε (y' + (a + z))) :=
    ((measurable_heatK η).comp measurable_snd).ennreal_ofReal.mul
      (hS.comp (measurable_fst.add (measurable_snd.add_const z)))
  simp only [Pi.mul_apply]
  calc ∫⁻ y, (∫⁻ y', ENNReal.ofReal (heatK η (y - y')) ∂ν) * smoothCov g ε (y + z)
      = ∫⁻ y, (∫⁻ y', ENNReal.ofReal (heatK η (y - y')) * smoothCov g ε (y + z) ∂ν) := by
        refine lintegral_congr fun y => ?_
        rw [lintegral_mul_const _ (by fun_prop)]
    _ = ∫⁻ y', (∫⁻ y, ENNReal.ofReal (heatK η (y - y')) * smoothCov g ε (y + z)) ∂ν :=
        lintegral_lintegral_swap hm1.aemeasurable
    _ = ∫⁻ y', (∫⁻ a, ENNReal.ofReal (heatK η a) * smoothCov g ε (y' + (a + z))) ∂ν := by
        refine lintegral_congr fun y' => ?_
        rw [← lintegral_add_right_eq_self
          (fun y => ENNReal.ofReal (heatK η (y - y')) * smoothCov g ε (y + z)) y']
        refine lintegral_congr fun a => ?_
        simp only [add_sub_cancel_right]
        congr 2; abel
    _ = ∫⁻ a, (∫⁻ y', ENNReal.ofReal (heatK η a) * smoothCov g ε (y' + (a + z)) ∂ν) :=
        lintegral_lintegral_swap hm2.aemeasurable
    _ = ∫⁻ a, ENNReal.ofReal (heatK η a) * ∫⁻ y', smoothCov g ε (y' + (a + z)) ∂ν := by
        refine lintegral_congr fun a => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ∫⁻ a, ENNReal.ofReal (heatK η a) * B :=
        lintegral_mono fun a => mul_le_mul_right (hB' _) _
    _ = B := by
        rw [lintegral_mul_const _ (measurable_heatK η).ennreal_ofReal, lintegral_heatK hη,
          one_mul]

/-! ### Scaling (step (c)) -/

/-- Auxiliary to the Lean proof route: `G_h = h · (y ↦ h y)_* G_1` for `h > 0` and
`d ∈ {1,2,3}`, from the scaling `G_h(hA) = h G_1(A)` (`WaveGreen.waveGreen_scaling`). -/
theorem waveGreen_eq_smul_map (hd : d = 1 ∨ d = 2 ∨ d = 3) {h : ℝ} (hh : 0 < h) :
    waveGreen d h = ENNReal.ofReal h • (waveGreen d 1).map fun y => h • y := by
  ext A hA
  rw [Measure.smul_apply, Measure.map_apply (measurable_const_smul h) hA,
    Set.preimage_smul₀ hh.ne', smul_eq_mul,
    ← waveGreen_scaling d hd h hh _ (hA.const_smul₀ _), smul_inv_smul₀ hh.ne']

/-- Auxiliary to the Lean proof route: `y ↦ |y + w|^{-α}` is measurable. -/
theorem measurable_rpow_norm_add (α : ℝ) (w : Rd d) :
    Measurable fun y : Rd d => ‖y + w‖ ^ (-α) :=
  ((measurable_add_const w).norm).pow_const _

/-- Step (c) (main TeX lines 6131-6134): for `d ∈ {1,2,3}`, `h > 0` and
`c ≥ 0`, the unsmoothed convolution is
`∫ G_h(dy) γ(y + z) = c h^{1-α} F_d(z/h)` with
`F_d(w) = ∫ G_1(dy) |y + w|^{-α}`. -/
theorem unsmoothed_scaling (hd : d = 1 ∨ d = 2 ∨ d = 3) {c : ℝ} (hc : 0 ≤ c) (α : ℝ)
    {h : ℝ} (hh : 0 < h) (z : Rd d) :
    ∫⁻ y, riesz c α (y + z) ∂(waveGreen d h) =
      ENNReal.ofReal (c * h ^ (1 - α)) *
        ∫⁻ y, ENNReal.ofReal (‖y + h⁻¹ • z‖ ^ (-α)) ∂(waveGreen d 1) := by
  rw [waveGreen_eq_smul_map hd hh, lintegral_smul_measure,
    lintegral_map (by unfold riesz; fun_prop) (measurable_const_smul h)]
  have hpt : ∀ y : Rd d, riesz c α (h • y + z) =
      ENNReal.ofReal (c * h ^ (-α)) * ENNReal.ofReal (‖y + h⁻¹ • z‖ ^ (-α)) := by
    intro y
    have e : h • y + z = h • (y + h⁻¹ • z) := by
      rw [smul_add, smul_inv_smul₀ hh.ne']
    rw [riesz, e, norm_smul, Real.norm_eq_abs, abs_of_pos hh,
      Real.mul_rpow hh.le (norm_nonneg _), ← mul_assoc,
      ENNReal.ofReal_mul (mul_nonneg hc (Real.rpow_nonneg hh.le _))]
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul hh.le]
  congr 2
  rw [show (1 : ℝ) - α = 1 + -α by ring, Real.rpow_add hh, Real.rpow_one]
  ring

/-! ### Layer cake (step (b)) -/

/-- Step (b) (main TeX lines 6160-6166), for any measure `μ` of mass at most
one with the ball bound `μ(B(w,R)) ≤ 2R^{3/2}` for `0 < R ≤ 1/4`: for
`0 < α < 3/2` and every `w`,
`∫ μ(dy) |y + w|^{-α} ≤ 4^α + (2α/(3/2-α)) 4^{α-3/2}`.  The Lean route
applies the layer-cake formula in the level `t` of `|y + w|^{-α}` directly
(levels `t ≤ 4^α` cost at most the mass, levels `t > 4^α` use the ball of
radius `t^{-1/α} < 1/4`); the TeX writes the same integral in the radius
`R = t^{-1/α}`.  This holds for every `w` (the TeX's "centers outside the
disk"). -/
theorem layer_cake_le (μ : Measure (Rd d)) (hμ : μ univ ≤ 1)
    (hball : ∀ w : Rd d, ∀ R : ℝ, 0 < R → R ≤ 1 / 4 →
      μ (ball w R) ≤ ENNReal.ofReal (2 * R ^ (3 / 2 : ℝ)))
    {α : ℝ} (hα0 : 0 < α) (hα : α < 3 / 2) (w : Rd d) :
    ∫⁻ y, ENNReal.ofReal (‖y + w‖ ^ (-α)) ∂μ ≤
      ENNReal.ofReal (4 ^ α + 2 * α / (3 / 2 - α) * 4 ^ (α - 3 / 2)) := by
  set a : ℝ := (4 : ℝ) ^ α with ha_def
  set p : ℝ := 3 / (2 * α) with hp_def
  have ha : 0 < a := by positivity
  have hp1 : 1 < p := by rw [hp_def, lt_div_iff₀ (by positivity)]; linarith
  rw [lintegral_eq_lintegral_meas_lt μ
    (Eventually.of_forall fun y => Real.rpow_nonneg (norm_nonneg _) _)
    (measurable_rpow_norm_add α w).aemeasurable]
  rw [← Ioc_union_Ioi_eq_Ioi ha.le, lintegral_union measurableSet_Ioi (Ioc_disjoint_Ioi le_rfl)]
  -- small levels
  have h1 : ∫⁻ t in Ioc 0 a, μ {y | t < ‖y + w‖ ^ (-α)} ≤ ENNReal.ofReal a := by
    calc ∫⁻ t in Ioc 0 a, μ {y | t < ‖y + w‖ ^ (-α)}
        ≤ ∫⁻ _ in Ioc 0 a, (1 : ℝ≥0∞) :=
          setLIntegral_mono' measurableSet_Ioc fun t _ => (measure_mono (subset_univ _)).trans hμ
      _ = ENNReal.ofReal a := by
          rw [setLIntegral_const, one_mul, Real.volume_Ioc, sub_zero]
  -- large levels
  have hlev : ∀ t ∈ Ioi a, μ {y | t < ‖y + w‖ ^ (-α)} ≤ ENNReal.ofReal (2 * t ^ (-p)) := by
    intro t ht
    have ht0 : 0 < t := ha.trans ht
    set r : ℝ := t ^ (-1 / α) with hr_def
    have hneg : -1 / α < 0 := div_neg_of_neg_of_pos (by norm_num) hα0
    have hr0 : 0 < r := Real.rpow_pos_of_pos ht0 _
    have hr4 : r ≤ 1 / 4 := by
      have := Real.rpow_lt_rpow_of_neg ha ht hneg
      have e : a ^ (-1 / α) = 1 / 4 := by
        rw [ha_def, ← Real.rpow_mul (by norm_num), show α * (-1 / α) = -1 by field_simp,
          Real.rpow_neg_one]; norm_num
      linarith
    have hsub : {y | t < ‖y + w‖ ^ (-α)} ⊆ ball (-w) r := by
      intro y hy
      simp only [mem_ofPred_eq] at hy
      rw [mem_ball, dist_eq_norm, sub_neg_eq_add]
      have hs : 0 < ‖y + w‖ := by
        rcases (norm_nonneg (y + w)).lt_or_eq with h | h
        · exact h
        · rw [← h, Real.zero_rpow (neg_ne_zero.2 hα0.ne')] at hy; linarith
      have := Real.rpow_lt_rpow_of_neg ht0 hy hneg
      rwa [← Real.rpow_mul hs.le, show -α * (-1 / α) = 1 by field_simp, Real.rpow_one] at this
    calc μ {y | t < ‖y + w‖ ^ (-α)} ≤ μ (ball (-w) r) := measure_mono hsub
      _ ≤ ENNReal.ofReal (2 * r ^ (3 / 2 : ℝ)) := hball _ _ hr0 hr4
      _ = ENNReal.ofReal (2 * t ^ (-p)) := by
          rw [hr_def, ← Real.rpow_mul ht0.le, hp_def]
          congr 3; field_simp
  have hint : IntegrableOn (fun t : ℝ => 2 * t ^ (-p)) (Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) ha).const_mul 2
  have h2 : ∫⁻ t in Ioi a, μ {y | t < ‖y + w‖ ^ (-α)} ≤
      ENNReal.ofReal (2 * (-a ^ (-p + 1) / (-p + 1))) := by
    calc ∫⁻ t in Ioi a, μ {y | t < ‖y + w‖ ^ (-α)}
        ≤ ∫⁻ t in Ioi a, ENNReal.ofReal (2 * t ^ (-p)) :=
          setLIntegral_mono' measurableSet_Ioi hlev
      _ = ENNReal.ofReal (∫ t in Ioi a, 2 * t ^ (-p)) := by
          rw [ofReal_integral_eq_lintegral_ofReal hint]
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          have : 0 < t := ha.trans ht
          positivity
      _ = ENNReal.ofReal (2 * (-a ^ (-p + 1) / (-p + 1))) := by
          rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) ha]
  have hnn : 0 ≤ 2 * (-a ^ (-p + 1) / (-p + 1)) := by
    have : -p + 1 < 0 := by linarith
    have : 0 < a ^ (-p + 1) := Real.rpow_pos_of_pos ha _
    apply mul_nonneg (by norm_num)
    exact div_nonneg_of_nonpos (by linarith) (by linarith)
  calc _ ≤ ENNReal.ofReal a + ENNReal.ofReal (2 * (-a ^ (-p + 1) / (-p + 1))) := add_le_add h1 h2
    _ = ENNReal.ofReal (a + 2 * (-a ^ (-p + 1) / (-p + 1))) := (ENNReal.ofReal_add ha.le hnn).symm
    _ = _ := by
        congr 1
        have e1 : a ^ (-p + 1) = 4 ^ (α - 3 / 2) := by
          rw [ha_def, ← Real.rpow_mul (by norm_num), hp_def]
          congr 1; field_simp; ring
        rw [e1, hp_def]
        have hα1 : (3 : ℝ) / 2 - α ≠ 0 := by linarith
        have hα2 : -(3 / (2 * α)) + 1 ≠ 0 := by
          rw [show -(3 / (2 * α)) + 1 = (2 * α - 3) / (2 * α) by field_simp; ring]
          exact div_ne_zero (by linarith) (by positivity)
        have key : -(4 : ℝ) ^ (α - 3 / 2) / (-(3 / (2 * α)) + 1) =
            α / (3 / 2 - α) * 4 ^ (α - 3 / 2) := by
          have h3 : (3 : ℝ) - α * 2 ≠ 0 := (by linarith : (0 : ℝ) < 3 - α * 2).ne'
          have h4 : (3 : ℝ) - 2 * α ≠ 0 := (by linarith : (0 : ℝ) < 3 - 2 * α).ne'
          rw [div_eq_iff hα2]
          field_simp
          ring
        rw [key]
        ring

/-! ### The two-dimensional ball mass (step (a)) -/

/-- Auxiliary to the Lean proof route: the density of `G_1^{(2)}`,
`1_{|x|<1} (2π√(1-|x|²))⁻¹`, written exactly as in `WaveGreen.waveGreen 2 1`. -/
def dens2 : Rd 2 → ℝ≥0∞ :=
  (ball (0 : Rd 2) 1).indicator fun x =>
    ENNReal.ofReal ((2 * π * Real.sqrt (1 ^ 2 - ‖x‖ ^ 2))⁻¹)

/-- Auxiliary to the Lean proof route: `G_1^{(2)} = dens2 · Lebesgue` (definitional). -/
theorem waveGreen_two_one : waveGreen 2 1 = volume.withDensity dens2 := rfl

/-- Auxiliary to the Lean proof route. -/
theorem measurable_dens2 : Measurable dens2 :=
  Measurable.indicator (by fun_prop) measurableSet_ball

/-- Auxiliary to the Lean proof route: the density is radial. -/
theorem dens2_congr {x y : Rd 2} (h : ‖x‖ = ‖y‖) : dens2 x = dens2 y := by
  simp only [dens2, indicator, mem_ball_zero_iff, h]

/-- Auxiliary to the Lean proof route: `G_1^{(2)}` is invariant under linear
isometries ("Rotate `w = (A,0)`", main TeX line 6153; the route uses a
reflection). -/
theorem waveGreen_two_preimage (f : Rd 2 ≃ₗᵢ[ℝ] Rd 2) {S : Set (Rd 2)} (hS : MeasurableSet S) :
    waveGreen 2 1 (f ⁻¹' S) = waveGreen 2 1 S := by
  have hS' : MeasurableSet (f ⁻¹' S) := hS.preimage f.continuous.measurable
  rw [waveGreen_two_one, withDensity_apply _ hS', withDensity_apply _ hS,
    ← lintegral_indicator hS', ← lintegral_indicator hS]
  have hpt : ∀ x, (f ⁻¹' S).indicator dens2 x = S.indicator dens2 (f x) := by
    intro x
    by_cases hx : f x ∈ S
    · rw [indicator_of_mem (show x ∈ f ⁻¹' S from hx), indicator_of_mem hx,
        dens2_congr (f.norm_map x).symm]
    · rw [indicator_of_notMem (show x ∉ f ⁻¹' S from hx), indicator_of_notMem hx]
  simp_rw [hpt]
  exact f.measurePreserving.lintegral_comp (measurable_dens2.indicator hS)

/-- Auxiliary to the Lean proof route: the first coordinate vector `e₁ = (1, 0)`. -/
def e0 : Rd 2 := EuclideanSpace.single (0 : Fin 2) (1 : ℝ)

/-- Auxiliary to the Lean proof route: a linear isometry (a reflection) moves
`w` to `(|w|, 0)`. -/
theorem exists_isometry_axis (w : Rd 2) : ∃ f : Rd 2 ≃ₗᵢ[ℝ] Rd 2, f w = ‖w‖ • e0 := by
  refine ⟨Submodule.reflection (ℝ ∙ (w - ‖w‖ • e0))ᗮ, Submodule.reflection_sub ?_⟩
  simp [e0, norm_smul]

/-- Auxiliary to the Lean proof route: centers with `|w| < 1/2`.  The ball lies
in `|y| < 3/4`, where the density is at most `1/π`, so the mass is at most `R²`.
(The TeX uses the sharper density bound `2/(π√7)`, line 6154; `1/π` suffices.) -/
theorem ball_mass_small {w : Rd 2} (hw : ‖w‖ < 1 / 2) {R : ℝ} (hR0 : 0 < R) (hR : R ≤ 1 / 4) :
    waveGreen 2 1 (ball w R) ≤ ENNReal.ofReal (R ^ 2) := by
  rw [waveGreen_two_one, withDensity_apply _ measurableSet_ball]
  calc ∫⁻ x in ball w R, dens2 x ≤ ∫⁻ _ in ball w R, ENNReal.ofReal π⁻¹ := by
        refine setLIntegral_mono' measurableSet_ball fun x hx => ?_
        by_cases hx1 : x ∈ ball (0 : Rd 2) 1
        · rw [dens2, indicator_of_mem hx1]
          apply ENNReal.ofReal_le_ofReal
          have hxn : ‖x‖ < 3 / 4 := by
            have h1 : ‖x - w‖ < R := by rwa [mem_ball, dist_eq_norm] at hx
            have h2 : ‖x‖ ≤ ‖x - w‖ + ‖w‖ := by
              simpa using norm_add_le (x - w) w
            linarith
          have hs : 1 / 2 ≤ Real.sqrt (1 ^ 2 - ‖x‖ ^ 2) := by
            rw [show (1 : ℝ) / 2 = Real.sqrt ((1 / 2) ^ 2) by
              rw [Real.sqrt_sq (by norm_num)]]
            exact Real.sqrt_le_sqrt (by nlinarith [norm_nonneg x])
          have := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 2 * π)
          exact inv_anti₀ Real.pi_pos ((by ring : π = 2 * π * (1 / 2)).le.trans this)
        · rw [dens2, indicator_of_notMem hx1]; exact zero_le
    _ = ENNReal.ofReal π⁻¹ * volume (ball w R) := setLIntegral_const _ _
    _ = ENNReal.ofReal (R ^ 2) := by
        rw [EuclideanSpace.volume_ball_fin_two, ← ENNReal.ofReal_pow hR0.le,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp

/-- Auxiliary to the Lean proof route: `R² ≤ 2R^{3/2}` for `0 < R ≤ 1/4`. -/
theorem sq_le_two_rpow {R : ℝ} (hR0 : 0 < R) (hR : R ≤ 1 / 4) : R ^ 2 ≤ 2 * R ^ (3 / 2 : ℝ) := by
  have h := Real.rpow_le_rpow_of_exponent_ge hR0 (by linarith) (by norm_num : (3 / 2 : ℝ) ≤ 2)
  rw [Real.rpow_two] at h
  linarith [Real.rpow_nonneg hR0.le (3 / 2 : ℝ)]

/-- Auxiliary to the Lean proof route: the slice integral.  For `b ≤ L`,
`∫_{(a,b]} (L - x)^{-1/2} dx ≤ 2√(b - a)` (it equals `2(√(L-a) - √(L-b))`). -/
theorem slice_le {L a b : ℝ} (hbL : b ≤ L) :
    ∫⁻ u in Ioc a b, ENNReal.ofReal ((L - u) ^ (-(1 / 2 : ℝ))) ≤
      ENNReal.ofReal (2 * Real.sqrt (b - a)) := by
  rcases le_or_gt b a with hab | hab
  · rw [Ioc_eq_empty (not_lt.2 hab), Measure.restrict_empty, lintegral_zero_measure]
    exact zero_le
  have hII : IntervalIntegrable (fun u => (L - u) ^ (-(1 / 2 : ℝ))) volume a b := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := L - a) (b := L - b)
      (r := -(1 / 2 : ℝ)) (by norm_num)).comp_sub_left L
    simpa using this
  have hIoc : IntegrableOn (fun u => (L - u) ^ (-(1 / 2 : ℝ))) (Ioc a b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).1 hII
  rw [← ofReal_integral_eq_lintegral_ofReal hIoc]
  swap
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact Real.rpow_nonneg (by linarith [hu.2]) _
  apply ENNReal.ofReal_le_ofReal
  rw [← intervalIntegral.integral_of_le hab.le,
    intervalIntegral.integral_comp_sub_left (fun x => x ^ (-(1 / 2 : ℝ))) L,
    integral_rpow (Or.inl (by norm_num))]
  rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
    div_le_iff₀ (by norm_num)]
  have h1 : 0 ≤ L - b := by linarith
  have h2 : 0 ≤ b - a := by linarith
  have key : Real.sqrt (L - a) ≤ Real.sqrt (L - b) + Real.sqrt (b - a) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    nlinarith [Real.sq_sqrt h1, Real.sq_sqrt h2, Real.sqrt_nonneg (L - b),
      Real.sqrt_nonneg (b - a), mul_nonneg (Real.sqrt_nonneg (L - b)) (Real.sqrt_nonneg (b - a))]
  linarith

/-- Auxiliary to the Lean proof route: the coordinates `x ↦ (x₁, x₀)` of `ℝ²`
(second coordinate first), a measure-preserving equivalence. -/
def coordSwap : Rd 2 ≃ᵐ ℝ × ℝ :=
  ((MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow).trans
    MeasurableEquiv.prodComm

/-- Auxiliary to the Lean proof route. -/
theorem coordSwap_apply (x : Rd 2) : coordSwap x = (x 1, x 0) := rfl

/-- Auxiliary to the Lean proof route. -/
theorem coordSwap_mp : MeasurePreserving coordSwap volume volume := by
  have h1 := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)
  have h2 := MeasureTheory.volume_preserving_finTwoArrow ℝ
  have h3 : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume volume :=
    Measure.measurePreserving_swap
  exact (h3.comp h2).comp h1

/-- Auxiliary to the Lean proof route: `|x|² = x₀² + x₁²` in `ℝ²`. -/
theorem norm_sq_two (x : Rd 2) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
  simp [Real.norm_eq_abs, sq_abs]

/-- Auxiliary to the Lean proof route: centers `(A, 0)` with `A ≥ 1/2`
(main TeX lines 6155-6159).  On the ball, `|v| < R` and `A - R < x ≤ L`,
`L = √(1-v²)`; the density is at most `(2π)⁻¹ (L - x)^{-1/2}` since
`1 - |y|² = (L-x)(L+x)` with `L + x ≥ 1`; each slice integral is at most
`2√(2R)`, the `v`-range has length `2R`, and `(2√2/π) R^{3/2} ≤ 2R^{3/2}`.
The integral over `ℝ²` is bounded by the iterated integral
(`lintegral_prod_le`), which needs no measurability of the bounding function. -/
theorem ball_mass_axis {A : ℝ} (hA : 1 / 2 ≤ A) {R : ℝ} (hR0 : 0 < R) (hR : R ≤ 1 / 4) :
    waveGreen 2 1 (ball (A • e0) R) ≤ ENNReal.ofReal (2 * R ^ (3 / 2 : ℝ)) := by
  set c : Rd 2 := A • e0 with hc
  have hc0 : c 0 = A := by simp [hc, e0]
  have hc1 : c 1 = 0 := by simp [hc, e0]
  let k : ℝ × ℝ → ℝ≥0∞ := fun p =>
    if |p.1| < R ∧ p.2 ∈ Ioc (A - R) (min (A + R) (Real.sqrt (1 - p.1 ^ 2))) then
      ENNReal.ofReal (2 * π)⁻¹ *
        ENNReal.ofReal ((Real.sqrt (1 - p.1 ^ 2) - p.2) ^ (-(1 / 2 : ℝ)))
    else 0
  -- pointwise domination
  have hpt : ∀ x : Rd 2, (ball c R).indicator dens2 x ≤ k (coordSwap x) := by
    intro x
    by_cases hxc : x ∈ ball c R
    swap
    · rw [indicator_of_notMem hxc]; exact zero_le
    rw [indicator_of_mem hxc]
    by_cases hx1 : x ∈ ball (0 : Rd 2) 1
    swap
    · rw [dens2, indicator_of_notMem hx1]; exact zero_le
    rw [dens2, indicator_of_mem hx1, coordSwap_apply]
    set u := x 0 with hu_def
    set v := x 1 with hv_def
    have hn : ‖x‖ ^ 2 = u ^ 2 + v ^ 2 := norm_sq_two x
    have hdx : ‖x - c‖ ^ 2 = (u - A) ^ 2 + v ^ 2 := by
      rw [norm_sq_two]
      simp [hc0, hc1, hu_def, hv_def]
    have hx1' : u ^ 2 + v ^ 2 < 1 := by
      rw [← hn]
      have : ‖x‖ < 1 := by simpa using hx1
      nlinarith [norm_nonneg x]
    have hxc' : (u - A) ^ 2 + v ^ 2 < R ^ 2 := by
      rw [← hdx]
      have : ‖x - c‖ < R := by rwa [mem_ball, dist_eq_norm] at hxc
      nlinarith [norm_nonneg (x - c)]
    have hv : |v| < R := abs_lt_of_sq_lt_sq (by nlinarith) hR0.le
    have huA : |u - A| < R := abs_lt_of_sq_lt_sq (by nlinarith) hR0.le
    have hu1 : A - R < u := by linarith [(abs_lt.1 huA).1]
    have hu2 : u < A + R := by linarith [(abs_lt.1 huA).2]
    set L := Real.sqrt (1 - v ^ 2) with hL_def
    have hv2 : v ^ 2 < 1 / 16 := by nlinarith [abs_nonneg v, sq_abs v]
    have hLsq : L ^ 2 = 1 - v ^ 2 := Real.sq_sqrt (by linarith)
    have hL34 : 3 / 4 ≤ L := by
      rw [hL_def, show (3 : ℝ) / 4 = Real.sqrt ((3 / 4) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have hu3 : u < L := (Real.lt_sqrt (by linarith)).2 (by linarith)
    have hmem : |v| < R ∧ u ∈ Ioc (A - R) (min (A + R) L) :=
      ⟨hv, hu1, le_min hu2.le hu3.le⟩
    simp only [k]
    rw [ite_eq_left hmem, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hLu : 0 < L - u := by linarith
    rw [Real.rpow_neg hLu.le, ← Real.sqrt_eq_rpow, ← mul_inv]
    have hsq : Real.sqrt (L - u) ≤ Real.sqrt (1 ^ 2 - ‖x‖ ^ 2) := by
      apply Real.sqrt_le_sqrt
      rw [hn]
      nlinarith
    exact inv_anti₀ (by positivity) (by nlinarith [Real.pi_pos, Real.sqrt_pos.2 hLu])
  -- inner (slice) bound
  have hinner : ∀ v : ℝ, ∫⁻ u, k (v, u) ≤
      (Ioo (-R) R).indicator (fun _ => ENNReal.ofReal ((2 * π)⁻¹ * (2 * Real.sqrt (2 * R)))) v := by
    intro v
    by_cases hv : |v| < R
    · have hvI : v ∈ Ioo (-R) R := abs_lt.1 hv
      rw [indicator_of_mem hvI]
      set L := Real.sqrt (1 - v ^ 2)
      have hk : (fun u => k (v, u)) = (Ioc (A - R) (min (A + R) L)).indicator
          (fun u => ENNReal.ofReal (2 * π)⁻¹ * ENNReal.ofReal ((L - u) ^ (-(1 / 2 : ℝ)))) := by
        funext u
        by_cases hu : u ∈ Ioc (A - R) (min (A + R) L)
        · simp only [k, indicator_of_mem hu]; rw [ite_eq_left ⟨hv, hu⟩]
        · simp only [k, indicator_of_notMem hu]; rw [ite_eq_right (fun h => hu h.2)]
      calc ∫⁻ u, k (v, u)
          = ∫⁻ u in Ioc (A - R) (min (A + R) L),
              ENNReal.ofReal (2 * π)⁻¹ * ENNReal.ofReal ((L - u) ^ (-(1 / 2 : ℝ))) := by
            rw [show (∫⁻ u, k (v, u)) = ∫⁻ u, (fun u => k (v, u)) u from rfl, hk,
              lintegral_indicator measurableSet_Ioc]
        _ = ENNReal.ofReal (2 * π)⁻¹ *
              ∫⁻ u in Ioc (A - R) (min (A + R) L), ENNReal.ofReal ((L - u) ^ (-(1 / 2 : ℝ))) :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal (2 * π)⁻¹ *
              ENNReal.ofReal (2 * Real.sqrt (min (A + R) L - (A - R))) :=
            mul_le_mul_right (slice_le (min_le_right _ _)) _
        _ ≤ ENNReal.ofReal (2 * π)⁻¹ * ENNReal.ofReal (2 * Real.sqrt (2 * R)) := by
            gcongr
            linarith [min_le_left (A + R) L]
        _ = ENNReal.ofReal ((2 * π)⁻¹ * (2 * Real.sqrt (2 * R))) :=
            (ENNReal.ofReal_mul (by positivity)).symm
    · have hvI : v ∉ Ioo (-R) R := fun h => hv (abs_lt.2 h)
      rw [indicator_of_notMem hvI]
      have : ∀ u, k (v, u) = 0 := fun u => by simp only [k]; rw [ite_eq_right (fun h => hv h.1)]
      simp [this]
  -- assemble
  rw [waveGreen_two_one, withDensity_apply _ measurableSet_ball,
    ← lintegral_indicator measurableSet_ball]
  calc ∫⁻ x, (ball c R).indicator dens2 x
      ≤ ∫⁻ x, k (coordSwap x) := lintegral_mono hpt
    _ = ∫⁻ p, k p := coordSwap_mp.lintegral_comp_emb coordSwap.measurableEmbedding k
    _ ≤ ∫⁻ v, ∫⁻ u, k (v, u) := lintegral_prod_le k
    _ ≤ ∫⁻ v, (Ioo (-R) R).indicator
          (fun _ => ENNReal.ofReal ((2 * π)⁻¹ * (2 * Real.sqrt (2 * R)))) v :=
        lintegral_mono hinner
    _ = ENNReal.ofReal ((2 * π)⁻¹ * (2 * Real.sqrt (2 * R))) * ENNReal.ofReal (2 * R) := by
        rw [lintegral_indicator_const measurableSet_Ioo, Real.volume_Ioo]
        congr 2; ring
    _ ≤ ENNReal.ofReal (2 * R ^ (3 / 2 : ℝ)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have h32 : R ^ (3 / 2 : ℝ) = R * Real.sqrt R := by
          rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hR0, Real.rpow_one,
            Real.sqrt_eq_rpow]
        have hs2 : Real.sqrt 2 ≤ π := by
          have : Real.sqrt 2 < 2 := by
            rw [Real.sqrt_lt' (by norm_num)]; norm_num
          linarith [Real.pi_gt_three]
        rw [h32, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
        have hRs : 0 ≤ R * Real.sqrt R := by positivity
        rw [show (2 * π)⁻¹ * (2 * (Real.sqrt 2 * Real.sqrt R)) * (2 * R) =
            Real.sqrt 2 / π * (2 * (R * Real.sqrt R)) by field_simp]
        exact mul_le_of_le_one_left (by positivity) (div_le_one_of_le₀ hs2 Real.pi_pos.le)

/-- Step (a) (main TeX lines 6152-6159): `G_1^{(2)}(B(w,R)) ≤ 2R^{3/2}` for every
center `w` and `0 < R ≤ 1/4`. -/
theorem ball_mass_two (w : Rd 2) {R : ℝ} (hR0 : 0 < R) (hR : R ≤ 1 / 4) :
    waveGreen 2 1 (ball w R) ≤ ENNReal.ofReal (2 * R ^ (3 / 2 : ℝ)) := by
  rcases lt_or_ge ‖w‖ (1 / 2) with hw | hw
  · exact (ball_mass_small hw hR0 hR).trans (ENNReal.ofReal_le_ofReal (sq_le_two_rpow hR0 hR))
  obtain ⟨f, hf⟩ := exists_isometry_axis w
  have hpre : ball w R = f ⁻¹' ball (f w) R := by
    ext x; simp [mem_ball]
  rw [hpre, waveGreen_two_preimage f measurableSet_ball, hf]
  exact ball_mass_axis hw hR0 hR

/-! ### `F_2` and the unsmoothed bound -/

/-- Step (b) for `G_1^{(2)}` (main TeX lines 6160-6166): for `0 < α < 3/2` and
every `w ∈ ℝ²`, `F_2(w) = ∫ G_1(dy) |y + w|^{-α} ≤ M_2/c`, i.e.
`≤ 4^α + (2α/(3/2-α)) 4^{α-3/2}`. -/
theorem F2_le {α : ℝ} (hα0 : 0 < α) (hα : α < 3 / 2) (w : Rd 2) :
    ∫⁻ y, ENNReal.ofReal (‖y + w‖ ^ (-α)) ∂(waveGreen 2 1) ≤
      ENNReal.ofReal (4 ^ α + 2 * α / (3 / 2 - α) * 4 ^ (α - 3 / 2)) := by
  refine layer_cake_le _ ?_ (fun w R hR0 hR => ball_mass_two w hR0 hR) hα0 hα w
  rw [WaveGreen.mass_two 1 one_pos, ENNReal.ofReal_one]

/-- The unsmoothed bound in `d = 2` (steps (a)-(c)): for `c ≥ 0`, `0 < α < 3/2`,
`h > 0` and every `z`, `∫ G_h(dy) γ(y + z) ≤ M_2 h^{-(α-1)}`. -/
theorem riesz_two_unsmoothed {c α : ℝ} (hc : 0 ≤ c) (hα0 : 0 < α) (hα : α < 3 / 2)
    {h : ℝ} (hh : 0 < h) (z : Rd 2) :
    ∫⁻ y, riesz c α (y + z) ∂(waveGreen 2 h) ≤ ENNReal.ofReal (M2 c α * h ^ (-(α - 1))) := by
  rw [unsmoothed_scaling (Or.inr (Or.inl rfl)) hc α hh z]
  have hK : 0 ≤ 4 ^ α + 2 * α / (3 / 2 - α) * 4 ^ (α - 3 / 2) := by
    have : 0 < 3 / 2 - α := by linarith
    positivity
  calc ENNReal.ofReal (c * h ^ (1 - α)) *
        ∫⁻ y, ENNReal.ofReal (‖y + h⁻¹ • z‖ ^ (-α)) ∂(waveGreen 2 1)
      ≤ ENNReal.ofReal (c * h ^ (1 - α)) *
          ENNReal.ofReal (4 ^ α + 2 * α / (3 / 2 - α) * 4 ^ (α - 3 / 2)) :=
        mul_le_mul_right (F2_le hα0 hα _) _
    _ = ENNReal.ofReal (M2 c α * h ^ (-(α - 1))) := by
        rw [← ENNReal.ofReal_mul (by positivity), M2, show -(α - 1) = 1 - α by ring]
        ring_nf

/-! ### `H:spatial-maximum` in `d = 2` -/

/-- Auxiliary to the Lean proof route: `γ` is measurable. -/
theorem measurable_riesz (c α : ℝ) : Measurable (riesz c α : Rd d → ℝ≥0∞) := by
  unfold riesz; fun_prop

/-- `M_2 > 0` for `c > 0` and `0 < α < 3/2` (the `M > 0` of `H:spatial-maximum`). -/
theorem M2_pos {c α : ℝ} (hc : 0 < c) (hα0 : 0 < α) (hα : α < 3 / 2) : 0 < M2 c α := by
  have : 0 < 3 / 2 - α := by linarith
  unfold M2; positivity

/-- `L:higher-riesz` in dimension two (main TeX lines 6103-6190): for
`γ(x) = c|x|^{-α}`, `c > 0`, `0 < α < 3/2`, Hypothesis `H:spatial-maximum`
holds with `δ = α - 1` and `M = M_2 = c{4^α + (2α/(3/2-α)) 4^{α-3/2}}`.
(The TeX's range is `1 < α < 3/2`; the proof needs only `0 < α`.) -/
theorem higher_riesz_two {c α : ℝ} (hc : 0 < c) (hα0 : 0 < α) (hα : α < 3 / 2) :
    SpatialMaximum 2 (riesz c α) (α - 1) (M2 c α) := by
  refine ⟨M2_pos hc hα0 hα, fun h hh z ε hε η hη => ?_⟩
  have := isFiniteMeasure_waveGreen 2 h
  exact smoothed_average_le (measurable_riesz c α) hε hη
    (fun x => riesz_two_unsmoothed hc.le hα0 hα hh x) z

/-- The real-valued form of `H:spatial-maximum` (`E:higher-convolution` as
written, main TeX lines 5922-5925): for a measurable density, the integrand
`y ↦ γ_ε(y + z)` (real part of the lower integral) is integrable against
`G_{h,η}` and `0 ≤ ∫ G_{h,η}(dy) γ_ε(y + z) ≤ M h^{-δ}`. -/
theorem SpatialMaximum.real_form {g : Rd d → ℝ≥0∞} (hg : Measurable g) {δ M : ℝ}
    (hS : SpatialMaximum d g δ M) {h : ℝ} (hh : 0 < h) (z : Rd d) {ε : ℝ} (hε : 0 < ε)
    {η : ℝ} (hη : 0 ≤ η) :
    Integrable (fun y => (smoothCov g ε (y + z)).toReal) (smoothGreen (waveGreen d h) η) ∧
      0 ≤ ∫ y, (smoothCov g ε (y + z)).toReal ∂(smoothGreen (waveGreen d h) η) ∧
      ∫ y, (smoothCov g ε (y + z)).toReal ∂(smoothGreen (waveGreen d h) η) ≤ M * h ^ (-δ) := by
  have hb := hS.2 h hh z ε hε η hη
  have hm : Measurable fun y => smoothCov g ε (y + z) :=
    (measurable_smoothCov hg ε).comp (measurable_add_const z)
  have hfin : ∫⁻ y, smoothCov g ε (y + z) ∂(smoothGreen (waveGreen d h) η) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
  refine ⟨integrable_toReal_of_lintegral_ne_top hm.aemeasurable hfin,
    integral_nonneg fun _ => ENNReal.toReal_nonneg, ?_⟩
  rw [integral_toReal hm.aemeasurable (ae_lt_top hm hfin)]
  exact ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg hS.1.le (Real.rpow_nonneg hh.le _)) hb

/-- `L:higher-riesz`, the dimension-two clause, with the manuscript's hypotheses
(main TeX lines 6103-6112 and the section's standing assumptions, lines
5912-5917): `H:homog` for the covariance `Γ = γ dx` with `d = 2` and exponents
`α, α₀` (`HomogCovariance`; it contains `α₀ + α < 2`, i.e. the section's
`α < 2 - α₀`), `c > 0`, `1 < α < 3/2`.  Conclusion: Hypothesis
`H:spatial-maximum` with `δ = α - 1` and `M = M_2`.  The `H:homog` hypothesis is
carried but unused, and of `1 < α` only `0 < α` is used. -/
theorem higher_riesz_two_paper {c α α₀ : ℝ} {μ : Measure (Rd 2)}
    (_hH : HomogCovariance 2 α α₀ (volume.withDensity (riesz c α)) μ) (hc : 0 < c)
    (hα1 : 1 < α) (hα : α < 3 / 2) :
    SpatialMaximum 2 (riesz c α) (α - 1) (M2 c α) :=
  higher_riesz_two hc (by linarith) hα

/-! ### The `d = 3` closed form: its maximum (step (e)) -/

/-- The closed form `F_3 = ((1+ρ)^v - |1-ρ|^v)/(2vρ)` of main TeX lines 6136-6138,
as a function of `v = 2 - α` and `ρ = |w|` (the identity `F_3(w) = F3 v |w|`
is `HigherRieszThree.F3w_eq`). -/
def F3 (v ρ : ℝ) : ℝ :=
  ((1 + ρ) ^ v - |1 - ρ| ^ v) / (2 * v * ρ)

/-- Auxiliary to the Lean proof route: `ψ(ρ) = (1+ρ)^v - (1-ρ)^v` is convex on
`[0, 1]` for `0 < v < 1` (its second derivative is
`v(v-1)[(1+ρ)^{v-2} - (1-ρ)^{v-2}] ≥ 0`). -/
theorem psi_convexOn {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    ConvexOn ℝ (Icc 0 1) fun ρ : ℝ => (1 + ρ) ^ v - (1 - ρ) ^ v := by
  have hc1 : Continuous fun ρ : ℝ => (1 + ρ) ^ v :=
    (continuous_const.add continuous_id).rpow_const fun _ => Or.inr hv0.le
  have hc2 : Continuous fun ρ : ℝ => (1 - ρ) ^ v :=
    (continuous_const.sub continuous_id).rpow_const fun _ => Or.inr hv0.le
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1) (hc1.sub hc2).continuousOn
    (f' := fun x => v * (1 + x) ^ (v - 1) + v * (1 - x) ^ (v - 1))
    (f'' := fun x => v * (v - 1) * (1 + x) ^ (v - 2) - v * (v - 1) * (1 - x) ^ (v - 2))
    ?_ ?_ ?_
  · intro x hx
    rw [interior_Icc] at hx ⊢
    have h1 : HasDerivAt (fun y : ℝ => (1 + y) ^ v) (1 * v * (1 + x) ^ (v - 1)) x :=
      ((hasDerivAt_id' x).const_add 1).rpow_const (Or.inl (by linarith [hx.1]))
    have h2 : HasDerivAt (fun y : ℝ => (1 - y) ^ v) (-1 * v * (1 - x) ^ (v - 1)) x :=
      ((hasDerivAt_id' x).const_sub 1).rpow_const (Or.inl (by linarith [hx.2]))
    exact ((h1.sub h2).congr_deriv (by ring)).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx ⊢
    have h1 : HasDerivAt (fun y : ℝ => (1 + y) ^ (v - 1)) (1 * (v - 1) * (1 + x) ^ (v - 1 - 1)) x :=
      ((hasDerivAt_id' x).const_add 1).rpow_const (Or.inl (by linarith [hx.1]))
    have h2 : HasDerivAt (fun y : ℝ => (1 - y) ^ (v - 1))
        (-1 * (v - 1) * (1 - x) ^ (v - 1 - 1)) x :=
      ((hasDerivAt_id' x).const_sub 1).rpow_const (Or.inl (by linarith [hx.2]))
    refine (((h1.const_mul v).add (h2.const_mul v)).congr_deriv ?_).hasDerivWithinAt
    rw [show v - 1 - 1 = v - 2 by ring]; ring
  · intro x hx
    rw [interior_Icc] at hx
    have hle : (1 + x) ^ (v - 2) ≤ (1 - x) ^ (v - 2) :=
      Real.rpow_le_rpow_of_nonpos (by linarith [hx.2]) (by linarith [hx.1]) (by linarith)
    have hvv : v * (v - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hv0.le (by linarith)
    have : v * (v - 1) * (1 + x) ^ (v - 2) - v * (v - 1) * (1 - x) ^ (v - 2) =
        (v * (v - 1)) * ((1 + x) ^ (v - 2) - (1 - x) ^ (v - 2)) := by ring
    simp only [this]
    exact mul_nonneg_of_nonpos_of_nonpos hvv (by linarith)

/-- Auxiliary to the Lean proof route: `(1+ρ)^v - |1-ρ|^v ≤ 2^v ρ` for
`ρ > 0`, `0 < v < 1`.  For `ρ ≤ 1` by the convexity of `ψ` on `[0,1]`
(chord through `ψ(0) = 0`, `ψ(1) = 2^v`); for `ρ ≥ 1` by subadditivity
`(ρ+1)^v ≤ (ρ-1)^v + 2^v`.  The TeX proves the monotonicity of `F_3` on
each side of `ρ = 1` instead (the average of a convex function for `ρ < 1`,
distances for `ρ > 1`, lines 6140-6145); only the resulting maximum is
formalized. -/
theorem F3_num_le {v ρ : ℝ} (hv0 : 0 < v) (hv1 : v < 1) (hρ : 0 < ρ) :
    (1 + ρ) ^ v - |1 - ρ| ^ v ≤ 2 ^ v * ρ := by
  rcases le_or_gt ρ 1 with h1 | h1
  · rw [abs_of_nonneg (by linarith)]
    have h := (psi_convexOn hv0 hv1).2 (show (0 : ℝ) ∈ Icc 0 1 by simp)
      (show (1 : ℝ) ∈ Icc 0 1 by simp) (show 0 ≤ 1 - ρ by linarith) hρ.le (by ring)
    simp only [smul_eq_mul, mul_zero, mul_one, zero_add, add_zero, sub_zero, Real.one_rpow,
      sub_self, show (1 : ℝ) + 1 = 2 by norm_num, Real.zero_rpow hv0.ne'] at h
    linarith
  · rw [abs_of_neg (by linarith), neg_sub]
    have h := Real.rpow_add_le_add_rpow (p := v) (by linarith : 0 ≤ ρ - 1)
      (by norm_num : (0 : ℝ) ≤ 2) hv0.le hv1.le
    rw [show ρ - 1 + 2 = 1 + ρ by ring] at h
    have : (2 : ℝ) ^ v ≤ 2 ^ v * ρ := le_mul_of_one_le_right (by positivity) h1.le
    linarith

/-- Step (e) (main TeX lines 6134-6146): for `1 < α < 2` and `v = 2 - α`, the
closed form is maximal at `ρ = 1`: `F3 v ρ ≤ F3 v 1` for every `ρ > 0`, and
`F3 v 1 = 2^{1-α}/(2-α)`.  This is the scalar part of `M_3 = c2^{1-α}/(2-α)`;
the spherical-coordinates identity for `F_3(w)` is `HigherRieszThree.F3w_eq`. -/
theorem F3_max {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) :
    (∀ ρ : ℝ, 0 < ρ → F3 (2 - α) ρ ≤ F3 (2 - α) 1) ∧
      F3 (2 - α) 1 = 2 ^ (1 - α) / (2 - α) := by
  have hv0 : 0 < 2 - α := by linarith
  have hv1 : 2 - α < 1 := by linarith
  have h1 : F3 (2 - α) 1 = 2 ^ (1 - α) / (2 - α) := by
    have h2 : (2 : ℝ) ^ (2 - α) = 2 * 2 ^ (1 - α) := by
      rw [show (2 : ℝ) - α = 1 + (1 - α) by ring, Real.rpow_add (by norm_num), Real.rpow_one]
    unfold F3
    rw [sub_self, abs_zero, Real.zero_rpow hv0.ne', show (1 : ℝ) + 1 = 2 by norm_num, h2,
      sub_zero]
    field_simp
  refine ⟨fun ρ hρ => ?_, h1⟩
  rw [h1]
  unfold F3
  have hden : 0 < 2 * (2 - α) * ρ := by positivity
  rw [div_le_iff₀ hden]
  have h2 : (2 : ℝ) ^ (2 - α) = 2 * 2 ^ (1 - α) := by
    rw [show (2 : ℝ) - α = 1 + (1 - α) by ring, Real.rpow_add (by norm_num), Real.rpow_one]
  have := F3_num_le hv0 hv1 hρ
  rw [h2] at this
  calc (1 + ρ) ^ (2 - α) - |1 - ρ| ^ (2 - α) ≤ 2 * 2 ^ (1 - α) * ρ := this
    _ = 2 ^ (1 - α) / (2 - α) * (2 * (2 - α) * ρ) := by field_simp

/-! ### The approximate identity (step (f)) -/

/-- Auxiliary to the Lean proof route: `p_ε(w) = c^j p_1(c w)` with
`c = ε^{-1/2}`. -/
theorem heatK_scale {j : ℕ} {ε : ℝ} (hε : 0 < ε) (w : Rd j) :
    heatK ε w = ((Real.sqrt ε)⁻¹ ^ j * heatK 1 ((Real.sqrt ε)⁻¹ • w) : ℝ) := by
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hsq : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
  have hpow : Real.sqrt ε ^ j = ε ^ ((j : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hε.le]
    congr 1; ring
  unfold heatK
  have he : -(‖w‖ ^ 2 / (2 * ε)) = -(((Real.sqrt ε)⁻¹ * ‖w‖) ^ 2 / (2 * 1)) := by
    rw [mul_pow, inv_pow, hsq]; field_simp
  have e1 : (2 * π * ε) ^ (-((j : ℝ) / 2)) =
      ((2 * π) ^ ((j : ℝ) / 2))⁻¹ * (ε ^ ((j : ℝ) / 2))⁻¹ := by
    rw [Real.rpow_neg (by positivity), Real.mul_rpow (by positivity) hε.le, mul_inv]
  have e2 : (2 * π * 1) ^ (-((j : ℝ) / 2)) = ((2 * π) ^ ((j : ℝ) / 2))⁻¹ := by
    rw [mul_one, Real.rpow_neg (by positivity)]
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs, he, inv_pow, hpow, e1, e2]
  ring

/-- Auxiliary to the Lean proof route: `|w|^j p_1(w) → 0` at infinity (the decay
hypothesis of Mathlib's peak-function theorem). -/
theorem tendsto_norm_pow_mul_heatK {j : ℕ} :
    Tendsto (fun w : Rd j => ‖w‖ ^ j * heatK 1 w) (Bornology.cobounded (Rd j)) (𝓝 0) := by
  have hs : Tendsto (fun t : ℝ => t ^ j * Real.exp (-(t ^ 2 / (2 * 1)))) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero j) ?_ ?_
    · filter_upwards [eventually_ge_atTop 0] with t ht
      positivity
    · filter_upwards [eventually_ge_atTop 2] with t ht
      have : -(t ^ 2 / (2 * 1)) ≤ -t := by nlinarith
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 this) (by positivity)
  have := (hs.comp (tendsto_norm_cobounded_atTop (E := Rd j))).const_mul
    ((2 * π * 1) ^ (-((j : ℝ) / 2)))
  rw [mul_zero] at this
  refine this.congr fun w => ?_
  simp only [Function.comp_apply, heatK]
  ring

/-- Auxiliary to the Lean proof route: the Gaussian approximate identity at a
continuity point of an integrable `g` (Mathlib's
`tendsto_integral_comp_smul_smul_of_integrable'` with `p_1` rescaled). -/
theorem tendsto_heat_conv {j : ℕ} {g : Rd j → ℝ} (hg : Integrable g) {x : Rd j}
    (hgx : ContinuousAt g x) :
    Tendsto (fun ε => ∫ y, heatK ε (x - y) * g y) (𝓝[>] 0) (𝓝 (g x)) := by
  have hpeak := tendsto_integral_comp_smul_smul_of_integrable' (μ := (volume : Measure (Rd j)))
    (φ := heatK 1) (fun w => (heatK_pos one_pos w).le) (integral_heatK one_pos).2
    (by simpa [finrank_euclideanSpace] using tendsto_norm_pow_mul_heatK) hg hgx
  have hc : Tendsto (fun ε : ℝ => (Real.sqrt ε)⁻¹) (𝓝[>] 0) atTop := by
    refine tendsto_inv_nhdsGT_zero.comp ?_
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun ε hε =>
      Real.sqrt_pos.2 hε⟩
    have : Tendsto Real.sqrt (𝓝 0) (𝓝 (Real.sqrt 0)) := Real.continuous_sqrt.tendsto 0
    rw [Real.sqrt_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine (hpeak.comp hc).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  simp only [Function.comp_apply, finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [heatK_scale hε]

/-- Step (f) (main TeX lines 6178-6186): for `f(y) = |y|^{-λ}` on `ℝ^j`,
`0 < λ < j`, and `x ≠ 0`, every convolution `∫ p_ε(x - y) f(y) dy` (`ε > 0`)
is a genuine (integrable) integral and `p_ε * f(x) → f(x)` as `ε ↓ 0`.
Lean route: split `f` at the ball `|y| < 2|x|`; the inner part is integrable
(`integrableOn_ball_of_norm_le_rpow`) and continuous at `x`, so Mathlib's
peak-function theorem applies; the outer part is at most `(2|x|)^{-λ}` and
vanishes on `B(x,|x|)`, whose `p_ε`-mass at `x` tends to one.  The TeX splits
into a neighborhood of `x`, the ball `|y| < |x|/2` and the rest instead. -/
theorem approx_identity {j : ℕ} {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < j) {x : Rd j}
    (hx : x ≠ 0) :
    (∀ ε : ℝ, 0 < ε → Integrable fun y : Rd j => heatK ε (x - y) * ‖y‖ ^ (-lam)) ∧
      Tendsto (fun ε => ∫ y : Rd j, heatK ε (x - y) * ‖y‖ ^ (-lam)) (𝓝[>] 0)
        (𝓝 (‖x‖ ^ (-lam))) := by
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
  set r : ℝ := 2 * ‖x‖ with hr_def
  have hr : 0 < r := by positivity
  have hj : 1 ≤ Module.finrank ℝ (Rd j) := by
    rw [finrank_euclideanSpace, Fintype.card_fin]
    have : (0 : ℝ) < j := hlam0.trans hlam
    exact_mod_cast this
  have hfm : Measurable fun y : Rd j => ‖y‖ ^ (-lam) := (measurable_norm).pow_const _
  set f1 := (ball (0 : Rd j) r).indicator fun y : Rd j => ‖y‖ ^ (-lam) with hf1
  set f2 := (ball (0 : Rd j) r)ᶜ.indicator fun y : Rd j => ‖y‖ ^ (-lam) with hf2
  have hsplit : ∀ y, ‖y‖ ^ (-lam) = f1 y + f2 y := fun y => by
    rw [hf1, hf2, ← Pi.add_apply, indicator_self_add_compl]
  have hf1i : Integrable f1 := by
    rw [hf1, integrable_indicator_iff measurableSet_ball]
    refine integrableOn_ball_of_norm_le_rpow (C := 1) hj (by
      rwa [finrank_euclideanSpace, Fintype.card_fin]) (Eventually.of_forall fun y => ?_)
      hfm.aestronglyMeasurable
    rw [one_mul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  have hxball : x ∈ ball (0 : Rd j) r := by
    rw [mem_ball_zero_iff, hr_def]; linarith
  have hf1c : ContinuousAt f1 x := by
    have hfc : ContinuousAt (fun y : Rd j => ‖y‖ ^ (-lam)) x :=
      continuous_norm.continuousAt.rpow_const (Or.inl hxn.ne')
    refine hfc.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ball.mem_nhds hxball] with y hy
    rw [hf1, indicator_of_mem hy]
  set B : ℝ := r ^ (-lam) with hB_def
  have hf2b : ∀ y, 0 ≤ f2 y ∧ f2 y ≤ B := by
    intro y
    by_cases hy : y ∈ (ball (0 : Rd j) r)ᶜ
    · rw [hf2, indicator_of_mem hy]
      have : r ≤ ‖y‖ := by simpa using hy
      exact ⟨Real.rpow_nonneg (norm_nonneg _) _,
        Real.rpow_le_rpow_of_nonpos hr this (by linarith)⟩
    · rw [hf2, indicator_of_notMem hy]
      exact ⟨le_rfl, Real.rpow_nonneg hr.le _⟩
  have hf2m : Measurable f2 := hfm.indicator measurableSet_ball.compl
  set ind := (ball x ‖x‖).indicator fun _ : Rd j => (1 : ℝ) with hind
  have hindi : Integrable ind :=
    (integrable_indicator_iff measurableSet_ball).2 (integrableOn_const measure_ball_lt_top.ne)
  have hindc : ContinuousAt ind x := by
    refine (continuousAt_const : ContinuousAt (fun _ : Rd j => (1 : ℝ)) x).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hxn)] with y hy
    rw [hind, indicator_of_mem hy]
  have hdom : ∀ y, f2 y + B * ind y ≤ B := by
    intro y
    by_cases hy : y ∈ ball x ‖x‖
    · have hy0 : y ∈ ball (0 : Rd j) r := by
        rw [mem_ball, dist_eq_norm] at hy
        rw [mem_ball_zero_iff, hr_def]
        have h3 : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by simpa using norm_add_le (y - x) x
        linarith
      rw [hf2, indicator_of_notMem (by simpa using hy0), hind, indicator_of_mem hy]
      simp
    · rw [hind, indicator_of_notMem hy, mul_zero, add_zero]
      exact (hf2b y).2
  -- integrability of the pieces
  have hp : ∀ ε, 0 < ε → Integrable fun y : Rd j => heatK ε (x - y) :=
    fun ε hε => (integral_heatK hε).1.comp_sub_left x
  have hpb : ∀ ε, 0 < ε → ∀ y : Rd j, ‖heatK ε (x - y)‖ ≤ (2 * π * ε) ^ (-((j : ℝ) / 2)) := by
    intro ε hε y
    rw [Real.norm_eq_abs, abs_of_pos (heatK_pos hε _)]
    unfold heatK
    have : Real.exp (-(‖x - y‖ ^ 2 / (2 * ε))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ ‖x - y‖ ^ 2 / (2 * ε) := by positivity
      linarith
    calc _ ≤ (2 * π * ε) ^ (-((j : ℝ) / 2)) * 1 :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := mul_one _
  have hpm : ∀ ε, Measurable fun y : Rd j => heatK ε (x - y) := fun ε => by fun_prop
  have hI1 : ∀ ε, 0 < ε → Integrable fun y => heatK ε (x - y) * f1 y := fun ε hε =>
    hf1i.bdd_mul (hpm ε).aestronglyMeasurable (Eventually.of_forall (hpb ε hε))
  have hI2 : ∀ ε, 0 < ε → Integrable fun y => heatK ε (x - y) * f2 y := fun ε hε =>
    (hp ε hε).mul_bdd hf2m.aestronglyMeasurable (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf2b y).1]; exact (hf2b y).2)
  have hIi : ∀ ε, 0 < ε → Integrable fun y => heatK ε (x - y) * ind y := fun ε hε =>
    hindi.bdd_mul (hpm ε).aestronglyMeasurable (Eventually.of_forall (hpb ε hε))
  have hsum : ∀ ε, 0 < ε → ∫ y, heatK ε (x - y) * ‖y‖ ^ (-lam) =
      (∫ y, heatK ε (x - y) * f1 y) + ∫ y, heatK ε (x - y) * f2 y := by
    intro ε hε
    calc ∫ y, heatK ε (x - y) * ‖y‖ ^ (-lam)
        = ∫ y, (heatK ε (x - y) * f1 y + heatK ε (x - y) * f2 y) :=
          integral_congr_ae (Eventually.of_forall fun y => by
            simp only [← mul_add]; rw [← hsplit y])
      _ = _ := integral_add (hI1 ε hε) (hI2 ε hε)
  refine ⟨fun ε hε => ((hI1 ε hε).add (hI2 ε hε)).congr
    (Eventually.of_forall fun y => by simp only [Pi.add_apply, ← mul_add]; rw [← hsplit y]), ?_⟩
  -- the inner part
  have hlim1 : Tendsto (fun ε => ∫ y, heatK ε (x - y) * f1 y) (𝓝[>] 0) (𝓝 (‖x‖ ^ (-lam))) := by
    have := tendsto_heat_conv hf1i hf1c
    rwa [hf1, indicator_of_mem hxball] at this
  -- the outer part
  have hlimi := tendsto_heat_conv hindi hindc
  rw [hind, indicator_of_mem (mem_ball_self hxn)] at hlimi
  have hup : ∀ ε, 0 < ε → ∫ y, heatK ε (x - y) * f2 y ≤
      B - B * ∫ y, heatK ε (x - y) * ind y := by
    intro ε hε
    have h1 : ∫ y, heatK ε (x - y) * (f2 y + B * ind y) ≤ ∫ y, heatK ε (x - y) * B :=
      integral_mono ((hI2 ε hε).add ((hIi ε hε).const_mul B) |>.congr
        (Eventually.of_forall fun y => by simp only [Pi.add_apply]; ring))
        ((hp ε hε).mul_const B)
        fun y => mul_le_mul_of_nonneg_left (hdom y) (heatK_pos hε _).le
    have h2 : ∫ y, heatK ε (x - y) * (f2 y + B * ind y) =
        (∫ y, heatK ε (x - y) * f2 y) + B * ∫ y, heatK ε (x - y) * ind y := by
      rw [← integral_const_mul]
      calc ∫ y, heatK ε (x - y) * (f2 y + B * ind y)
          = ∫ y, (heatK ε (x - y) * f2 y + B * (heatK ε (x - y) * ind y)) :=
            integral_congr_ae (Eventually.of_forall fun y => by simp only; ring)
        _ = _ := integral_add (hI2 ε hε) ((hIi ε hε).const_mul B)
    have h3 : ∫ y, heatK ε (x - y) * B = B := by
      rw [integral_mul_const]
      have : ∫ y, heatK ε (x - y) = 1 := by
        rw [integral_sub_left_eq_self (fun y => heatK ε y) (μ := volume) x]
        exact (integral_heatK hε).2
      rw [this, one_mul]
    linarith
  have hlim2 : Tendsto (fun ε => ∫ y, heatK ε (x - y) * f2 y) (𝓝[>] 0) (𝓝 0) := by
    have hu : Tendsto (fun ε => B - B * ∫ y, heatK ε (x - y) * ind y) (𝓝[>] 0) (𝓝 0) := by
      have := (hlimi.const_mul B).const_sub B
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact integral_nonneg fun y => mul_nonneg (heatK_pos hε _).le (hf2b y).1
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact hup ε hε
  have := hlim1.add hlim2
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hsum ε hε).symm

end StratonovichHAMSecondMoment.HigherRieszTwo
