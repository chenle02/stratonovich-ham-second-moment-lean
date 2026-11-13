module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

The wave Green measures `G_s` of the main TeX file
`notes/notes_stratonovich_ham_second_moment.tex` (revision a284420), and
`L:damped-homogeneous-norms` (lines 803-919) with nothing supplied.

Sources at a284420:
* `d = 1`: `G(s,y) = ½ 1_{|y|<s}` (line 746, proof of `L:white-test`; again at
  lines 4128 and 7642);
* `d = 2, 3`: the proof of `L:higher-riesz` (lines 5179-5187), quoting
  Chen (2.5), p. 7: `G_h^{(2)}(dy) = 1_{|y|<h} dy / (2π√(h²-|y|²))` and
  `G_h^{(3)}(dy) = σ_h(dy)/(4πh)`, `σ_h` the surface measure of the radius-`h`
  sphere; "Both have mass `h` and satisfy `G_h(hA) = hG_1(A)`" (lines 5186-5187);
* list of notation (`notes/index/list-of-notation.tex`, line 102): "Wave Green
  measure, with mass `t` and support in the closed radius-`t` ball";
* the mass identity `G_s(ℝ^d) = s` is used at line 881 (proof of
  `L:damped-homogeneous-norms`), where `DampedNormsHomog` took it as the
  supplied input `GreenMass G`.

Definition (`waveGreen d s`, a measure on `ℝ^d`):
* `d = 1`: `(1/2) · Lebesgue` restricted to the open ball `|x| < s`;
* `d = 2`: Lebesgue with density `1_{|x|<s} (2π√(s²-|x|²))⁻¹`;
* `d = 3`: `(s/(4π)) · map (ω ↦ s ω) σ`, where `σ = volume.toSphere` is
  Mathlib's measure on the unit sphere (`Measure.toSphere`).  This is a
  DEFINITIONAL CHOICE (Le's decision 4 for wave L6): `toSphere` is taken to be
  the surface measure, and `σ_h = h² · map (ω ↦ hω) σ_1` is taken as the surface
  measure of the radius-`h` sphere, so `σ_h/(4πh) = (h/(4π)) · map (ω ↦ hω) σ_1`.
  Neither identification with a Hausdorff or Riemannian surface measure is
  proved here.  `toSphere` satisfies `σ(A) = 3 · vol{r ω : 0 < r < 1, ω ∈ A}` for
  measurable `A` (`Measure.toSphere_apply'`, the cone measure); its total mass
  `3 · vol(unit ball) = 4π` is used in `mass_three`.
* other `d` (and every `s ≤ 0`): the zero measure.  The manuscript has
  `d ∈ {1,2,3}` (`H:homog`) and `s ≥ 0`; the value elsewhere is a convention,
  and the mass statements carry `d = 1 ∨ d = 2 ∨ d = 3`.

Formalized (all proved, nothing supplied):
* mass `G_s(ℝ^d) = s` for `s ≥ 0` and `d ∈ {1,2,3}` (`waveGreen_mass`; at
  `s = 0` the measure is zero);
* `IsFiniteMeasure (waveGreen d s)` for all `d`, `s` (`isFiniteMeasure_waveGreen`);
* support in the closed radius-`s` ball: `G_s((closedBall 0 s)ᶜ) = 0` for all
  `d`, `s` (`waveGreen_compl_closedBall`);
* scaling `G_s(sA) = s G_1(A)` for `s > 0` and every MEASURABLE `A`
  (`waveGreen_scaling`; in `d = 1` it holds for every set, `scaling_one`).  The
  TeX does not say which sets `A`; Borel sets are the reading used here;
* `waveGreen_greenMass`: `GreenMass (waveGreen d)` for `d ∈ {1,2,3}`, which
  discharges the one supplied input of `DampedNormsHomog`;
* `damped_homogeneous_norms_wave`: the conclusions of
  `DampedNormsHomog.damped_homogeneous_norms_paper` with `G := waveGreen d` and
  the only hypothesis `H:homog` (`HomogCovariance`), the dimension condition
  coming from `h.dim`; and `N0_waveGreen`;
* the Fourier identity in `d = 1`: `∫ e^{iξ·x} G_s(dx) = Ĝ_s(ξ)` for `s > 0`
  (`WaveKernel.waveHat`, lines 777-778), with integrability
  (`waveGreen_fourier_one`).

Not formalized: the Fourier identities in `d = 2, 3` (`d = 3` deferred by Le's
decision 4).  They are not needed for `damped_homogeneous_norms_wave`: the
norms `N₁`, `N₂` of `DampedNorms` are defined through `waveHat` directly, and
only `N₀` involves the measures.

Proof route (no TeX proof to follow; the TeX quotes the masses and scaling
from the source):
* `d = 1`: `EuclideanSpace.volume_ball` with `Γ(3/2) = √π/2`;
* `d = 2`: polar coordinates (`integral_fun_norm_addHaar`) and the
  antiderivative `-√(s²-r²)/(2π)` of `r (2π√(s²-r²))⁻¹` (auxiliary lemmas);
  scaling by the linear change of variables `x = s y`
  (`Measure.map_addHaar_smul`);
* `d = 3`: `Measure.toSphere_apply_univ` and `EuclideanSpace.volume_ball_fin_three`;
  scaling from the preimage identity `{ω : sω ∈ sA} = {ω : ω ∈ A}`;
* Fourier identity in `d = 1`: transport to `ℝ` by the coordinate map and
  `∫_{-s}^{s} e^{iat} dt = (e^{ias} - e^{-ias})/(ia)` (`integral_exp_mul_complex`).
Lemmas marked "Auxiliary to the Lean proof route" have no manuscript label.
-/

public import Mathlib
public import StratonovichHAMSecondMoment.HomogHypothesis
public import StratonovichHAMSecondMoment.TimeFractional
public import StratonovichHAMSecondMoment.SpectralHomog
public import StratonovichHAMSecondMoment.WaveKernel
public import StratonovichHAMSecondMoment.DampedNorms
public import StratonovichHAMSecondMoment.DampedNormsHomog

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Real Metric Filter
open scoped ENNReal NNReal Pointwise Topology

namespace StratonovichHAMSecondMoment.WaveGreen

open HomogHypothesis TimeFractional SpectralHomog WaveKernel DampedNorms DampedNormsHomog

/-! ### Definition -/

/-- The wave Green measure `G_s` on `ℝ^d` (main TeX lines 746, 5182-5186;
Chen (2.5)): `d = 1`: `½ 1_{|x|<s} dx`; `d = 2`:
`1_{|x|<s} dx / (2π√(s²-|x|²))`; `d = 3`: `σ_s/(4πs)`, written as
`(s/(4π)) · map (ω ↦ sω) volume.toSphere`, which takes Mathlib's
`Measure.toSphere` as the surface measure of the unit sphere (a definitional
choice, Le's decision 4; see the module doc); other `d`: `0`. -/
def waveGreen : (d : ℕ) → ℝ → Measure (Rd d)
  | 1, s => ENNReal.ofReal (1 / 2) • volume.restrict (ball 0 s)
  | 2, s => volume.withDensity ((ball (0 : Rd 2) s).indicator
      fun x => ENNReal.ofReal ((2 * π * Real.sqrt (s ^ 2 - ‖x‖ ^ 2))⁻¹))
  | 3, s => ENNReal.ofReal (s / (4 * π)) •
      (volume.toSphere.map fun ω : sphere (0 : Rd 3) 1 => s • (ω : Rd 3))
  | _, _ => 0

/-- Outside `d ∈ {1,2,3}` the definition is the zero measure (a convention;
the manuscript has `d ∈ {1,2,3}`). -/
theorem waveGreen_other (d : ℕ) (h1 : d ≠ 1) (h2 : d ≠ 2) (h3 : d ≠ 3) (s : ℝ) :
    waveGreen d s = 0 := by
  unfold waveGreen; split <;> simp_all

/-- For `s ≤ 0` the wave Green measure is zero (in `d = 1, 2` the ball is
empty, in `d = 3` the factor `s/(4π)` is `≤ 0`). -/
theorem waveGreen_of_nonpos (d : ℕ) (s : ℝ) (hs : s ≤ 0) : waveGreen d s = 0 := by
  by_cases h1 : d = 1
  · subst h1; simp [waveGreen, ball_eq_empty.2 hs]
  by_cases h2 : d = 2
  · subst h2; simp [waveGreen, ball_eq_empty.2 hs]
  by_cases h3 : d = 3
  · subst h3
    have : s / (4 * π) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hs (by positivity)
    simp [waveGreen, ENNReal.ofReal_eq_zero.2 this]
  exact waveGreen_other d h1 h2 h3 s

/-! ### Mass -/

/-- `Γ(3/2) = √π/2`.  Auxiliary to the Lean proof route. -/
theorem gamma_three_halves : Real.Gamma (1 / 2 + 1) = √π / 2 := by
  rw [Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]; ring

/-- Mass in `d = 1`: `G_s(ℝ) = s` for `s > 0`. -/
theorem mass_one (s : ℝ) (hs : 0 < s) : waveGreen 1 s univ = ENNReal.ofReal s := by
  simp only [waveGreen, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, EuclideanSpace.volume_ball, smul_eq_mul]
  simp only [Fintype.card_fin, pow_one, Nat.cast_one]
  rw [gamma_three_halves, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have : (0 : ℝ) < √π := Real.sqrt_pos.2 Real.pi_pos
  field_simp

/-- The radial density in `d = 2`, `h(r) = (2π√(s²-r²))⁻¹` (it is `(2π·0)⁻¹ = 0`
for `r ≥ s` by the conventions of `Real.sqrt` and `⁻¹`; only its values on
`r < s` enter `waveGreen 2`).  Auxiliary to the Lean proof route. -/
def radial2 (s r : ℝ) : ℝ := (2 * π * Real.sqrt (s ^ 2 - r ^ 2))⁻¹

/-- Auxiliary to the Lean proof route. -/
theorem radial2_nonneg (s r : ℝ) : 0 ≤ radial2 s r := by unfold radial2; positivity

/-- Auxiliary to the Lean proof route. -/
theorem radial2_eq_zero (s r : ℝ) (hs : 0 ≤ s) (hr : s ≤ r) : radial2 s r = 0 := by
  unfold radial2
  rw [Real.sqrt_eq_zero'.2 (by nlinarith)]; simp

/-- `r ↦ -√(s²-r²)/(2π)` is an antiderivative of `r · h(r)` on `(0,s)`.
Auxiliary to the Lean proof route. -/
theorem hasDerivAt_radial2 (s y : ℝ) (hy : y ∈ Ioo 0 s) :
    HasDerivAt (fun r => -Real.sqrt (s ^ 2 - r ^ 2) / (2 * π)) (y * radial2 s y) y := by
  have hpos : 0 < s ^ 2 - y ^ 2 := by nlinarith [hy.1, hy.2]
  have h1 : HasDerivAt (fun r => s ^ 2 - r ^ 2) (-(2 * y)) y := by
    simpa using ((hasDerivAt_pow 2 y).const_sub (s ^ 2))
  have h2' := (h1.sqrt hpos.ne').neg.div_const (2 * π)
  convert h2' using 1
  unfold radial2
  have := Real.sqrt_pos.2 hpos
  field_simp

/-- `∫_0^s r h(r) dr = s/(2π)`, with integrability.  Auxiliary to the Lean
proof route. -/
theorem integral_radial2 (s : ℝ) (hs : 0 < s) :
    IntegrableOn (fun y => y * radial2 s y) (Ioc 0 s) ∧
      ∫ y in Ioc 0 s, y * radial2 s y = s / (2 * π) := by
  have hc : ContinuousOn (fun r => -Real.sqrt (s ^ 2 - r ^ 2) / (2 * π)) (Icc 0 s) := by
    fun_prop
  have hI := intervalIntegral.integrableOn_deriv_of_nonneg hc
    (fun y hy => hasDerivAt_radial2 s y hy) (fun y hy => mul_nonneg hy.1.le (radial2_nonneg s y))
  refine ⟨hI, ?_⟩
  rw [← intervalIntegral.integral_of_le hs.le,
    intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hs.le hc
      (fun y hy => (hasDerivAt_radial2 s y hy).hasDerivWithinAt)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hs.le).2 hI)]
  simp [Real.sqrt_sq hs.le]
  field_simp

/-- Mass in `d = 2`: `G_s(ℝ²) = s` for `s > 0`. -/
theorem mass_two (s : ℝ) (hs : 0 < s) : waveGreen 2 s univ = ENNReal.ofReal s := by
  have hind : ((ball (0 : Rd 2) s).indicator
      fun x => ENNReal.ofReal ((2 * π * Real.sqrt (s ^ 2 - ‖x‖ ^ 2))⁻¹)) =
      fun x => ENNReal.ofReal (radial2 s ‖x‖) := by
    funext x
    by_cases hx : x ∈ ball (0 : Rd 2) s
    · simp [hx, radial2]
    · rw [indicator_of_notMem hx, radial2_eq_zero s _ hs.le (by simpa using hx)]; simp
  have hint : IntegrableOn (fun y : ℝ => y ^ (Module.finrank ℝ (Rd 2) - 1) • radial2 s y)
      (Ioi 0) := by
    simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
    have := (integral_radial2 s hs).1
    rw [show Ioi (0 : ℝ) = Ioc 0 s ∪ Ioi s from (Ioc_union_Ioi_eq_Ioi hs.le).symm]
    refine this.congr_fun (fun y _ => by simp) measurableSet_Ioc |>.union ?_
    refine integrableOn_zero.congr_fun (fun y hy => ?_) measurableSet_Ioi
    simp [radial2_eq_zero s y hs.le (le_of_lt hy)]
  have hI : Integrable (fun x : Rd 2 => radial2 s ‖x‖) :=
    (integrable_fun_norm_addHaar volume).2 hint
  show volume.withDensity _ univ = _
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hind,
    ← ofReal_integral_eq_lintegral_ofReal hI
      (Filter.Eventually.of_forall fun x => radial2_nonneg s _),
    integral_fun_norm_addHaar volume (fun r => radial2 s r)]
  congr 1
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  rw [show Ioi (0 : ℝ) = Ioc 0 s ∪ Ioi s from (Ioc_union_Ioi_eq_Ioi hs.le).symm,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi]
  · have hz : ∫ y in Ioi s, y ^ 1 * radial2 s y = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero (fun y hy => by
        simp [radial2_eq_zero s y hs.le (le_of_lt hy)])
    rw [hz]
    rw [Measure.real, EuclideanSpace.volume_ball_fin_two]
    have e : ∫ x in Ioc 0 s, x ^ (2 - 1) * radial2 s x = s / (2 * π) := by
      simpa using (integral_radial2 s hs).2
    simp only [add_zero]
    rw [e]
    simp [ENNReal.toReal_ofReal Real.pi_pos.le]
    field_simp
  · simpa using (integral_radial2 s hs).1
  · refine integrableOn_zero.congr_fun (fun y hy => ?_) measurableSet_Ioi
    simp [radial2_eq_zero s y hs.le (le_of_lt hy)]

/-- Mass in `d = 3`: `G_s(ℝ³) = s` for `s > 0` (the total mass of
`volume.toSphere` in `ℝ³` is `3 · (4π/3) = 4π`). -/
theorem mass_three (s : ℝ) (hs : 0 < s) : waveGreen 3 s univ = ENNReal.ofReal s := by
  simp only [waveGreen, Measure.smul_apply, smul_eq_mul]
  rw [Measure.map_apply (by fun_prop) MeasurableSet.univ, preimage_univ,
    Measure.toSphere_apply_univ, EuclideanSpace.volume_ball_fin_three]
  simp only [finrank_euclideanSpace, Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
  rw [show ((3 : ℕ) : ENNReal) = ENNReal.ofReal 3 by simp, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

/-- The mass identity `G_s(ℝ^d) = s` (lines 881, 5186-5187; notation list line 102)
for `d ∈ {1,2,3}` and every `s ≥ 0`. -/
theorem waveGreen_mass (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) (s : ℝ) (hs : 0 ≤ s) :
    waveGreen d s univ = ENNReal.ofReal s := by
  rcases hs.eq_or_lt with rfl | hs
  · simp [waveGreen_of_nonpos d 0 le_rfl]
  rcases hd with rfl | rfl | rfl
  · exact mass_one s hs
  · exact mass_two s hs
  · exact mass_three s hs

/-- Every `waveGreen d s` is a finite measure (all `d`, `s`). -/
theorem isFiniteMeasure_waveGreen (d : ℕ) (s : ℝ) : IsFiniteMeasure (waveGreen d s) := by
  rcases le_or_gt s 0 with hs | hs
  · rw [waveGreen_of_nonpos d s hs]; infer_instance
  by_cases hd : d = 1 ∨ d = 2 ∨ d = 3
  · exact ⟨by rw [waveGreen_mass d hd s hs.le]; exact ENNReal.ofReal_lt_top⟩
  · push Not at hd
    rw [waveGreen_other d hd.1 hd.2.1 hd.2.2 s]; infer_instance

/-- The finiteness of `waveGreen d s` as an instance. -/
instance instIsFiniteMeasureWaveGreen (d : ℕ) (s : ℝ) : IsFiniteMeasure (waveGreen d s) :=
  isFiniteMeasure_waveGreen d s

/-- `GreenMass (waveGreen d)` for `d ∈ {1,2,3}`: the supplied input of
`DampedNormsHomog` (line 881) is discharged. -/
theorem waveGreen_greenMass (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) :
    GreenMass (waveGreen d) :=
  ⟨fun s hs => waveGreen_mass d hd s hs.le⟩

/-! ### Support -/

/-- Support in the closed radius-`s` ball (notation list line 102):
`G_s((closedBall 0 s)ᶜ) = 0`, for all `d` and `s`. -/
theorem waveGreen_compl_closedBall (d : ℕ) (s : ℝ) :
    waveGreen d s (closedBall (0 : Rd d) s)ᶜ = 0 := by
  rcases le_or_gt s 0 with hs | hs
  · rw [waveGreen_of_nonpos d s hs]; rfl
  by_cases h1 : d = 1
  · subst h1
    simp only [waveGreen, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply' measurableSet_ball]
    rw [show (closedBall (0 : Rd 1) s)ᶜ ∩ ball 0 s = ∅ from
      disjoint_iff_inter_eq_empty.1 (disjoint_compl_left_iff_subset.2 ball_subset_closedBall),
      measure_empty, mul_zero]
  by_cases h2 : d = 2
  · subst h2
    show volume.withDensity _ _ = 0
    rw [withDensity_apply _ measurableSet_closedBall.compl]
    refine (setLIntegral_congr_fun measurableSet_closedBall.compl
      (fun x hx => indicator_of_notMem
        (fun hb => hx (ball_subset_closedBall hb)) _)).trans lintegral_zero
  by_cases h3 : d = 3
  · subst h3
    simp only [waveGreen, Measure.smul_apply, smul_eq_mul]
    rw [Measure.map_apply (by fun_prop) measurableSet_closedBall.compl]
    have : ((fun ω : sphere (0 : Rd 3) 1 => s • (ω : Rd 3)) ⁻¹' (closedBall 0 s)ᶜ) = ∅ := by
      ext ω
      simp [norm_smul, abs_of_pos hs]
    rw [this, measure_empty, mul_zero]
  rw [waveGreen_other d h1 h2 h3 s]; rfl

/-! ### Scaling -/

/-- Scaling in `d = 1` (every set `A`): `G_s(sA) = s G_1(A)`, `s > 0`. -/
theorem scaling_one (s : ℝ) (hs : 0 < s) (A : Set (Rd 1)) :
    waveGreen 1 s (s • A) = ENNReal.ofReal s * waveGreen 1 1 A := by
  simp only [waveGreen, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply' measurableSet_ball]
  rw [← smul_unitBall_of_pos hs, ← smul_set_inter₀ hs.ne', Measure.addHaar_smul]
  simp only [finrank_euclideanSpace, Fintype.card_fin, pow_one, abs_of_pos hs]
  ring

/-- Scaling in `d = 2`: `G_s(sA) = s G_1(A)` for `s > 0` and measurable `A`
(change of variables `x = s y`). -/
theorem scaling_two (s : ℝ) (hs : 0 < s) (A : Set (Rd 2)) (hA : MeasurableSet A) :
    waveGreen 2 s (s • A) = ENNReal.ofReal s * waveGreen 2 1 A := by
  set F : ℝ → Rd 2 → ℝ≥0∞ := fun t => (ball (0 : Rd 2) t).indicator
      fun x => ENNReal.ofReal ((2 * π * Real.sqrt (t ^ 2 - ‖x‖ ^ 2))⁻¹) with hF
  have hW : ∀ t, waveGreen 2 t = volume.withDensity (F t) := fun t => rfl
  rw [hW, hW, withDensity_apply _ (hA.const_smul₀ s), withDensity_apply _ hA,
    ← lintegral_indicator (hA.const_smul₀ s), ← lintegral_indicator hA]
  set e : Rd 2 ≃ᵐ Rd 2 := (Homeomorph.smulOfNeZero s hs.ne').toMeasurableEquiv
  have hmap : Measure.map e (volume : Measure (Rd 2)) =
      ENNReal.ofReal (s ^ 2)⁻¹ • volume := by
    have he : (⇑e : Rd 2 → Rd 2) = fun x => s • x := rfl
    have := Measure.map_addHaar_smul (volume : Measure (Rd 2)) hs.ne'
    rw [he]
    simpa [finrank_euclideanSpace] using this
  have hcv : ∀ g : Rd 2 → ℝ≥0∞, ∫⁻ x, g x = ENNReal.ofReal (s ^ 2) * ∫⁻ y, g (s • y) := by
    intro g
    have h1 := lintegral_map_equiv g e (μ := (volume : Measure (Rd 2)))
    rw [hmap, lintegral_smul_measure, smul_eq_mul] at h1
    have h2 : ∫⁻ y, g (s • y) = ∫⁻ y, g (e y) := rfl
    rw [h2, ← h1, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
      mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]
  rw [hcv]
  have hpt : ∀ y : Rd 2, (s • A).indicator (F s) (s • y) =
      ENNReal.ofReal s⁻¹ * A.indicator (F 1) y := by
    intro y
    by_cases hy : y ∈ A
    · rw [indicator_of_mem ((smul_mem_smul_set_iff₀ hs.ne' A y).2 hy), indicator_of_mem hy]
      simp only [hF]
      by_cases hb : ‖y‖ < 1
      · have hb' : s • y ∈ ball (0 : Rd 2) s := by
          simp [norm_smul, abs_of_pos hs]; nlinarith [norm_nonneg y]
        rw [indicator_of_mem hb', indicator_of_mem (by simpa using hb),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have h1 : 0 < 1 - ‖y‖ ^ 2 := by nlinarith [norm_nonneg y]
        have h2 : s ^ 2 - ‖s • y‖ ^ 2 = s ^ 2 * (1 ^ 2 - ‖y‖ ^ 2) := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]; ring
        rw [h2, Real.sqrt_mul (by positivity), Real.sqrt_sq hs.le]
        field_simp
      · have hb' : s • y ∉ ball (0 : Rd 2) s := by
          simp [norm_smul, abs_of_pos hs]; push Not at hb; nlinarith
        rw [indicator_of_notMem hb', indicator_of_notMem (by simpa using hb), mul_zero]
    · rw [indicator_of_notMem (by rwa [smul_mem_smul_set_iff₀ hs.ne']), indicator_of_notMem hy,
        mul_zero]
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  field_simp

/-- Scaling in `d = 3`: `G_s(sA) = s G_1(A)` for `s > 0` and measurable `A`. -/
theorem scaling_three (s : ℝ) (hs : 0 < s) (A : Set (Rd 3)) (hA : MeasurableSet A) :
    waveGreen 3 s (s • A) = ENNReal.ofReal s * waveGreen 3 1 A := by
  simp only [waveGreen, Measure.smul_apply, smul_eq_mul]
  rw [Measure.map_apply (by fun_prop) (hA.const_smul₀ s),
    Measure.map_apply (by fun_prop) hA]
  have hpre : ((fun ω : sphere (0 : Rd 3) 1 => s • (ω : Rd 3)) ⁻¹' (s • A)) =
      ((fun ω : sphere (0 : Rd 3) 1 => (1 : ℝ) • (ω : Rd 3)) ⁻¹' A) := by
    ext ω; simp [smul_mem_smul_set_iff₀ hs.ne']
  rw [hpre, ← mul_assoc, ← ENNReal.ofReal_mul hs.le]
  congr 2
  ring

/-- The scaling `G_s(sA) = s G_1(A)` (lines 5186-5187) for `d ∈ {1,2,3}`,
`s > 0` and measurable `A`. -/
theorem waveGreen_scaling (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) (s : ℝ) (hs : 0 < s)
    (A : Set (Rd d)) (hA : MeasurableSet A) :
    waveGreen d s (s • A) = ENNReal.ofReal s * waveGreen d 1 A := by
  rcases hd with rfl | rfl | rfl
  · exact scaling_one s hs A
  · exact scaling_two s hs A hA
  · exact scaling_three s hs A hA

/-- The four properties of the wave Green measures in one statement, for
`d ∈ {1,2,3}` (lines 5186-5187 and notation list line 102): mass `s` for
`s ≥ 0`, finiteness, support in the closed radius-`s` ball, and the scaling
`G_s(sA) = s G_1(A)` for `s > 0` and measurable `A`. -/
theorem waveGreen_paper (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) :
    (∀ s : ℝ, 0 ≤ s → waveGreen d s univ = ENNReal.ofReal s) ∧
      (∀ s : ℝ, IsFiniteMeasure (waveGreen d s)) ∧
      (∀ s : ℝ, waveGreen d s (closedBall (0 : Rd d) s)ᶜ = 0) ∧
      (∀ s : ℝ, 0 < s → ∀ A : Set (Rd d), MeasurableSet A →
        waveGreen d s (s • A) = ENNReal.ofReal s * waveGreen d 1 A) :=
  ⟨waveGreen_mass d hd, isFiniteMeasure_waveGreen d, waveGreen_compl_closedBall d,
    waveGreen_scaling d hd⟩

/-! ### `L:damped-homogeneous-norms` with nothing supplied -/

/-- `N₀(θ) = θ^{-2}` (lines 809-810) for the wave Green measures, `θ > 0`,
`d ∈ {1,2,3}`, with the integrand integrable on `(0,∞)`. -/
theorem N0_waveGreen (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) (θ : ℝ) (hθ : 0 < θ) :
    IntegrableOn (fun s => Real.exp (-(θ * s)) * (waveGreen d s univ).toReal) (Ioi 0) ∧
      N0 (waveGreen d) θ = θ ^ (-(2 : ℝ)) :=
  N0_eq (waveGreen d) (waveGreen_greenMass d hd) θ hθ

/-- `L:damped-homogeneous-norms` (lines 803-848, proof 849-919) under `H:homog`
alone, with `N₀` built from the wave Green measures `waveGreen d`: the
conclusions of `DampedNormsHomog.damped_homogeneous_norms_paper`, whose one
supplied input `GreenMass G` is discharged by `waveGreen_greenMass` (the
dimension condition is `h.dim`).  The scope of each conclusion (the upper
bounds of `E:damped-multiplier-comparison` for a multiplier `g ∈ [0,1]` on the
spectral measure, tails over `(M,∞) ∩ (0,∞)`) is
as documented in `DampedNormsHomog`; the `d = 3` Green measure is the
definitional choice documented in this module. -/
theorem damped_homogeneous_norms_wave {d : ℕ} {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (h : HomogCovariance d alpha alpha0 Γ μ) :
    (∀ θ : ℝ, 0 < θ →
      (Integrable (N2integrand (d := d) alpha0 θ) (P2.prod μ) ∧
        Integrable (fun p : ℝ × ℝ => Real.exp (-(θ * (p.1 + p.2))) * |p.1 - p.2| ^ (-alpha0) *
          ∫ ξ, waveHat p.1 ξ * waveHat p.2 ξ ∂μ) P2 ∧
        Integrable (fun l : ℝ => l ^ (alpha0 - 1) * resolvent μ (θ + l))
          L0) ∧
      0 ≤ N2sq alpha0 θ μ ∧
      IntegrableOn (fun s => Real.exp (-(θ * s)) * (waveGreen d s univ).toReal) (Ioi 0) ∧
      N0 (waveGreen d) θ = θ ^ (-(2 : ℝ)) ∧
      N1 alpha0 θ μ = θ ^ (alpha + alpha0 - 2) * N1 alpha0 1 μ ∧
      N2sq alpha0 θ μ = θ ^ (-(4 - alpha - alpha0)) * N2sq alpha0 1 μ) ∧
    (∀ M : ℝ, Integrable (N2onIntegrand (d := d) alpha0 1 (Ioi M)) (P2.prod μ) ∧
      Integrable (N2onOuter alpha0 1 (Ioi M) μ) P2 ∧ 0 ≤ N2tailSq alpha0 M μ) ∧
    Tendsto (fun M => N1tail alpha0 M μ) atTop (𝓝 0) ∧
    Tendsto (fun M => N2tailSq alpha0 M μ) atTop (𝓝 0) ∧
    Tendsto (fun M => N2tail alpha0 M μ) atTop (𝓝 0) ∧
    (∀ θ : ℝ, 0 < θ → ∀ g : Rd d → ℝ≥0, Measurable g → (∀ ξ, g ξ ≤ 1) →
      ∀ S S' : Set ℝ, MeasurableSet S → MeasurableSet S' → S ⊆ S' →
        Integrable (fun l : ℝ => l ^ (alpha0 - 1) * resolvent (smoothed μ g) (θ + l))
          L0 ∧
        N1on alpha0 θ S (smoothed μ g) ≤ N1on alpha0 θ S' μ ∧
        Integrable (N2onOuter alpha0 θ S (smoothed μ g)) P2 ∧
        Integrable (N2onOuter alpha0 θ S' μ) P2 ∧
        N2onSq alpha0 θ S (smoothed μ g) ≤ N2onSq alpha0 θ S' μ) :=
  damped_homogeneous_norms_paper h (waveGreen d) (waveGreen_greenMass d h.dim)

/-! ### The Fourier transform in `d = 1` -/

/-- The coordinate `ℝ¹ → ℝ`, `x ↦ x 0`, as a measurable equivalence.  Auxiliary to
the Lean proof route. -/
def coordOne : Rd 1 ≃ᵐ ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm.trans (MeasurableEquiv.funUnique (Fin 1) ℝ)

/-- Auxiliary to the Lean proof route. -/
theorem coordOne_apply (x : Rd 1) : coordOne x = x 0 := rfl

/-- The coordinate map preserves Lebesgue measure.  Auxiliary to the Lean proof
route. -/
theorem coordOne_mp : MeasurePreserving coordOne (volume : Measure (Rd 1)) volume :=
  (volume_preserving_funUnique (Fin 1) ℝ).comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 1))

/-- Auxiliary to the Lean proof route. -/
theorem norm_coord_one (x : Rd 1) : ‖x‖ = |x 0| := by
  rw [EuclideanSpace.norm_eq]; simp [Real.sqrt_sq_eq_abs]

/-- Auxiliary to the Lean proof route. -/
theorem inner_coord_one (ξ x : Rd 1) : inner ℝ ξ x = ξ 0 * x 0 := by
  simp [PiLp.inner_apply, mul_comm]

/-- Auxiliary to the Lean proof route. -/
theorem ball_eq_preimage_coordOne (s : ℝ) : ball (0 : Rd 1) s = coordOne ⁻¹' Ioo (-s) s := by
  ext x; simp [coordOne_apply, norm_coord_one, abs_lt]

/-- `∫_{(-s,s)} e^{iat} dt = 2 Ĝ_s(a)` (with `Ĝ_s` evaluated at the point `a` of
`ℝ¹`), `s > 0`.  Auxiliary to the Lean proof route. -/
theorem integral_exp_Ioo (a s : ℝ) (hs : 0 < s) :
    ∫ t in Ioo (-s) s, Complex.exp (Complex.I * ((a * t : ℝ) : ℂ)) =
      ((2 * waveHat s (EuclideanSpace.single (0 : Fin 1) a) : ℝ) : ℂ) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith)]
  have hn : ‖EuclideanSpace.single (0 : Fin 1) a‖ = |a| := by simp
  by_cases ha : a = 0
  · subst ha; simp [waveHat]; ring
  · have hc : Complex.I * (a : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast ha)
    have := integral_exp_mul_complex (a := -s) (b := s) hc
    simp only [Complex.ofReal_mul]
    simp_rw [← mul_assoc]
    rw [this, waveHat, hn, Real.sinc_of_ne_zero (mul_ne_zero hs.ne' (abs_ne_zero.2 ha))]
    have hsin : Real.sin (s * |a|) / (s * |a|) * s = Real.sin (a * s) / a := by
      rcases abs_choice a with h | h <;> rw [h]
      · field_simp
      · rw [show s * -a = -(a * s) by ring, Real.sin_neg]; field_simp
    rw [mul_comm s, hsin]
    push_cast
    rw [show (Complex.I * a * (s : ℂ)) = ((a * s : ℝ) : ℂ) * Complex.I by push_cast; ring,
      show (Complex.I * a * -(s : ℂ)) = ((-(a * s) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg, show (a : ℂ) * (s : ℂ) = ((a * s : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_sin]
    have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
    field_simp
    push_cast
    ring_nf

/-- Auxiliary to the Lean proof route. -/
theorem single_coord_one (ξ : Rd 1) : ξ = EuclideanSpace.single (0 : Fin 1) (ξ 0) := by
  ext i; fin_cases i; simp

/-- The Fourier transform of the `d = 1` wave Green measure:
`∫ e^{iξ·x} G_s(dx) = Ĝ_s(ξ) = sin(s|ξ|)/|ξ|` (`WaveKernel.waveHat`, lines
777-778) for `s > 0`, with integrability.  This identifies `waveHat` with the
Fourier transform of `waveGreen 1 s`.  (The `d = 2, 3` identities are not
formalized.) -/
theorem waveGreen_fourier_one (s : ℝ) (hs : 0 < s) (ξ : Rd 1) :
    Integrable (fun x : Rd 1 => Complex.exp (Complex.I * ((inner ℝ ξ x : ℝ) : ℂ)))
        (waveGreen 1 s) ∧
      ∫ x, Complex.exp (Complex.I * ((inner ℝ ξ x : ℝ) : ℂ)) ∂(waveGreen 1 s) =
        (waveHat s ξ : ℂ) := by
  refine ⟨Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
    (Filter.Eventually.of_forall fun x => ?_), ?_⟩
  · rw [Complex.norm_exp]; simp
  show ∫ x, _ ∂(ENNReal.ofReal (1 / 2) • volume.restrict (ball 0 s)) = _
  have hin : ∀ x : Rd 1, inner ℝ ξ x = ξ 0 * coordOne x := fun x => inner_coord_one ξ x
  simp_rw [hin]
  rw [integral_smul_measure, ball_eq_preimage_coordOne,
    coordOne_mp.setIntegral_preimage_emb coordOne.measurableEmbedding
      (fun t => Complex.exp (Complex.I * ((ξ 0 * t : ℝ) : ℂ)))]
  · rw [integral_exp_Ioo (ξ 0) s hs, ← single_coord_one, ENNReal.toReal_ofReal (by norm_num)]
    push_cast
    simp only [Complex.real_smul]; push_cast; ring

end StratonovichHAMSecondMoment.WaveGreen
