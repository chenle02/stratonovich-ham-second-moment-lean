module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L18, item L18-E, part 3: `E:joint-temporal-tail` (main TeX lines 1892-1927, display
1915-1920, "uniformly in all spatial widths" 1921, at revision edf7085f (book 1.1.3)).

* the tail norms of the damped kernels for the marked edge, `A_e = (M,∞)`:
  `N_{1,e} ≤ N_1^{(M)}(1)` and `N_{2,e}² ≤ N_2^{(M)}(1)²` (`E:damped-tail-norms`,
  `E:damped-multiplier-comparison`), uniformly in the spatial width of the edge;
* the difference-of-products inequality with one marked tail kernel `K_{1/η}`;
* the envelope bound with one marked edge (it appears once in `Q_1` or twice in `Q_2`);
* `joint_temporal_tail_of_le_two` for `d = 1, 2` (Green densities `green1`, `green2`) and
  `joint_temporal_tail` with the d = 3 Green-width removal (decision 8, see that docstring).
-/
public import Mathlib
public import StratonovichHAMSecondMoment.JointFixedOrder
public import StratonovichHAMSecondMoment.EnvelopeD3Wave
public import StratonovichHAMSecondMoment.HomogeneousEnvelope
public import StratonovichHAMSecondMoment.PairingEnvelope

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal Real Pointwise Nat

namespace StratonovichHAMSecondMoment.JointTail

open HomogHypothesis (Rd HomogCovariance)
open LowAlphaConvolution (gaussFactor gammaEps smoothedGreen)
open DiagramModel (Pi2 predVal incr openers covEps covWeight pos spatial diagram freq timeWeight
  twoSimplex)
open WaveGreen (waveGreen)
open WaveKernel (waveHat)
open PairingInterface
open PairingBridge
open PairingDampedNorms (GreenDensity)
open WickInterface

variable {d : ℕ}

/-! ### The tail norms of the damped kernels (`E:damped-tail-norms`) -/

/-- The capped Gamma mixture with Laplace domain `(M,∞)` is the restricted kernel `K_{(M,L]}`. -/
theorem kappaCap_nuE_tail {a : ℝ} (ha : 0 < a) {M : ℝ} (hM : 0 ≤ M) (L t : ℝ) :
    kappaCap (nuE a (Ioi M)) L t = ENNReal.ofReal (DampedNormsHomog.KS a (Ioc M L) t) := by
  have hG : 0 < (Real.Gamma a)⁻¹ := inv_pos.2 (Real.Gamma_pos_of_pos ha)
  have hset : Ioc 0 L ∩ Ioi M = Ioc M L := by
    ext x; simp only [mem_inter_iff, mem_Ioc, mem_Ioi]; constructor
    · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨lt_of_le_of_lt hM h1, h2⟩, h1⟩
  unfold kappaCap nuE DampedNormsHomog.KS
  rw [restrict_withDensity measurableSet_Ioc, lintegral_withDensity_eq_lintegral_mul _
    (by fun_prop) (by fun_prop), Measure.restrict_restrict measurableSet_Ioc, hset]
  have hcongr : ∀ l ∈ Ioc M L, ((fun l => ENNReal.ofReal ((Real.Gamma a)⁻¹ * l ^ (a - 1))) *
      fun l => ENNReal.ofReal (Real.exp (-(l * |t|)))) l =
      ENNReal.ofReal ((Real.Gamma a)⁻¹ * TimeFractional.subKernel a |t| l) := by
    intro l hl
    have hl0 : 0 < l := lt_of_le_of_lt hM hl.1
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (mul_nonneg hG.le (Real.rpow_nonneg hl0.le _)),
      TimeFractional.subKernel, mul_comm l |t|]
    ring_nf
  have hInt : IntegrableOn (fun l => TimeFractional.subKernel a |t| l) (Ioc M L) := by
    have hr : IntegrableOn (fun l : ℝ => l ^ (a - 1)) (Ioc M L) :=
      (JointFixedOrder.integrableOn_rpow_Ioc ha L).mono_set (Ioc_subset_Ioc_left hM)
    refine hr.mono' ((by unfold TimeFractional.subKernel; fun_prop : Measurable fun l : ℝ =>
      TimeFractional.subKernel a |t| l).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with l hl
    exact JointFixedOrder.subKernel_le t (lt_of_le_of_lt hM hl.1)
  have hInt' : Integrable (fun l => TimeFractional.subKernel a |t| l)
      (TimeFractional.L0.restrict (Ioc M L)) := by
    rw [TimeFractional.L0, Measure.restrict_restrict measurableSet_Ioc,
      Set.inter_eq_left.2 ((Ioc_subset_Ioc_left hM).trans Set.Ioc_subset_Ioi_self)]
    exact hInt
  rw [setLIntegral_congr_fun measurableSet_Ioc hcongr, ← ofReal_integral_eq_lintegral_ofReal
    (hInt.const_mul _), integral_const_mul]
  · congr 2
    rw [TimeFractional.L0, Measure.restrict_restrict measurableSet_Ioc,
      Set.inter_eq_left.2 ((Ioc_subset_Ioc_left hM).trans Set.Ioc_subset_Ioi_self)]
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with l hl
    exact mul_nonneg hG.le (TimeFractional.subKernel_nonneg a |t| l
      (lt_of_le_of_lt hM hl.1).le)

section Tail

variable {g : Kernel d} (hgd : GreenDensity d g)
  {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)} (hH : HomogCovariance d alpha α₀ Γ μ)
  {ε : ℝ} (hε : 0 < ε)
include hgd hH hε

/-- **The capped covariance quadratic form with the tail Laplace domain `(M,∞)`**: the analogue
of `PairingDampedNorms.QL_damp_eq` with `K_{(M,L]}` in place of `K_{(0,L]}`. -/
theorem QL_damp_tail_eq {θ : ℝ} (hθ : 0 < θ) {M : ℝ} (hM : 0 ≤ M) (L : ℝ) :
    QL (nuE α₀ (Ioi M)) (smoothSpec μ ε) L (zeroExt (damp θ g)) (zeroExt (damp θ g)) =
      ENNReal.ofReal (DampedNormsHomog.N2onSq α₀ θ (Ioc M L) (smoothSpec μ ε)) := by
  have := hH.μ_radon
  obtain ⟨hR, hμ0⟩ := DampedNormsHomog.homog_spectral_facts hH
  obtain ⟨hI, -, -⟩ := DampedNormsHomog.N2onSq_smoothed_mono μ hR hμ0 α₀ θ hH.alpha0_pos
    hH.alpha0_lt_one hθ (PairingDampedNorms.gaussMultNN ε) (PairingDampedNorms.measurable_gaussMultNN ε) (PairingDampedNorms.gaussMultNN_le_one hε.le)
    (Ioc M L) univ measurableSet_Ioc MeasurableSet.univ (subset_univ _)
  rw [PairingDampedNorms.smoothed_gaussMultNN] at hI
  obtain ⟨hc, -⟩ := PairingDampedNorms.gammaEps_props hH hε
  have hγ : ∀ z, gammaOf (smoothSpec μ ε) z = ENNReal.ofReal (gammaEps Γ ε z) := fun z => by
    rw [gammaOf_smoothSpec hH hε, LowAlphaUpper.covEps_eq_ofReal hε.le
      (LowAlphaConvolution.integrable_heatDens hH.Γ_tempered hε)]
  have hzm : Measurable fun p : ℝ × Rd d => zeroExt (damp θ g) p.1 p.2 := by
    have e : (fun p : ℝ × Rd d => zeroExt (damp θ g) p.1 p.2) =
        {p : ℝ × Rd d | 0 < p.1}.indicator (Function.uncurry (damp θ g)) := by
      funext p
      by_cases hp : 0 < p.1
      · rw [Set.indicator_of_mem (show p ∈ {p : ℝ × Rd d | 0 < p.1} from hp)]
        exact Set.indicator_of_mem (show p.1 ∈ Ioi (0 : ℝ) from hp) _
      · rw [Set.indicator_of_notMem (show p ∉ {p : ℝ × Rd d | 0 < p.1} from hp)]
        exact Set.indicator_of_notMem (show p.1 ∉ Ioi (0 : ℝ) from hp) _
    rw [e]
    exact (hgd.measurable_damp θ).indicator (measurableSet_lt measurable_const measurable_fst)
  have hΦ : Measurable fun w : (ℝ × Rd d) × (ℝ × Rd d) =>
      zeroExt (damp θ g) w.1.1 w.1.2 * zeroExt (damp θ g) w.2.1 w.2.2 *
        kappaCap (nuE α₀ (Ioi M)) L (w.1.1 - w.2.1) * gammaOf (smoothSpec μ ε) (w.1.2 - w.2.2) := by
    have hνs : SFinite (nuE α₀ (Ioi M)) := by unfold nuE; infer_instance
    have hγm : Measurable fun w : (ℝ × Rd d) × (ℝ × Rd d) =>
        gammaOf (smoothSpec μ ε) (w.1.2 - w.2.2) := by
      simp_rw [hγ]
      exact ENNReal.measurable_ofReal.comp (hc.measurable.comp
        ((measurable_snd.comp measurable_fst).sub (measurable_snd.comp measurable_snd)))
    exact (((hzm.comp measurable_fst).mul (hzm.comp measurable_snd)).mul
      ((PairingDampedNorms.measurable_kappaCap _ L).comp ((measurable_fst.comp measurable_fst).sub
        (measurable_fst.comp measurable_snd)))).mul hγm
  unfold QL
  rw [PairingDampedNorms.lintegral_four (fun s x r y => zeroExt (damp θ g) s x * zeroExt (damp θ g) r y *
    kappaCap (nuE α₀ (Ioi M)) L (s - r) * gammaOf (smoothSpec μ ε) (x - y)) hΦ]
  have hpt : ∀ s r : ℝ, ∫⁻ x, ∫⁻ y, zeroExt (damp θ g) s x * zeroExt (damp θ g) r y *
      kappaCap (nuE α₀ (Ioi M)) L (s - r) * gammaOf (smoothSpec μ ε) (x - y) =
      (Ioi (0 : ℝ)).indicator (fun s => (Ioi (0 : ℝ)).indicator (fun r =>
        ENNReal.ofReal (DampedNormsHomog.N2onOuter α₀ θ (Ioc M L) (smoothSpec μ ε) (s, r))) r) s := by
    intro s r
    by_cases hs : s ∈ Ioi (0 : ℝ)
    · by_cases hr : r ∈ Ioi (0 : ℝ)
      · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hr]
        have hs0 : 0 < s := hs
        have hr0 : 0 < r := hr
        have hzs : ∀ x, zeroExt (damp θ g) s x = ENNReal.ofReal (Real.exp (-(θ * s))) * g s x :=
          fun x => Set.indicator_of_mem hs _
        have hzr : ∀ y, zeroExt (damp θ g) r y = ENNReal.ofReal (Real.exp (-(θ * r))) * g r y :=
          fun y => Set.indicator_of_mem hr _
        set c := ENNReal.ofReal (Real.exp (-(θ * s))) * ENNReal.ofReal (Real.exp (-(θ * r))) *
          kappaCap (nuE α₀ (Ioi M)) L (s - r) with hcdef
        have hct : c ≠ ∞ := by
          rw [hcdef, kappaCap_nuE_tail hH.alpha0_pos hM]
          exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
        have hre : ∀ x y, zeroExt (damp θ g) s x * zeroExt (damp θ g) r y *
            kappaCap (nuE α₀ (Ioi M)) L (s - r) * gammaOf (smoothSpec μ ε) (x - y) =
            c * (g s x * g r y * gammaOf (smoothSpec μ ε) (x - y)) := by
          intro x y
          rw [hzs, hzr, hcdef]
          ring
        simp_rw [hre, lintegral_const_mul' _ _ hct]
        rw [(PairingDampedNorms.lintegral_double_spatial hgd hH hε hs0 hr0).1, hcdef, kappaCap_nuE_tail hH.alpha0_pos hM,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (mul_nonneg (by positivity)
            (DampedNormsHomog.KS_nonneg _ _ _ hH.alpha0_pos))]
        unfold DampedNormsHomog.N2onOuter
        congr 1
        rw [show -(θ * (s + r)) = -(θ * s) + -(θ * r) by ring, Real.exp_add]
      · rw [Set.indicator_of_mem hs, Set.indicator_of_notMem hr]
        have hzr : ∀ y, zeroExt (damp θ g) r y = 0 := fun y => Set.indicator_of_notMem hr _
        simp [hzr]
    · rw [Set.indicator_of_notMem hs]
      have hzs : ∀ x, zeroExt (damp θ g) s x = 0 := fun x => Set.indicator_of_notMem hs _
      simp [hzs]
  simp_rw [hpt]
  have hnn : 0 ≤ᵐ[TimeFractional.P2] DampedNormsHomog.N2onOuter α₀ θ (Ioc M L) (smoothSpec μ ε) := by
    filter_upwards [DampedNorms.ae_P2] with p hp
    unfold DampedNormsHomog.N2onOuter
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le
      (DampedNormsHomog.KS_nonneg _ _ _ hH.alpha0_pos))
      (PairingDampedNorms.lintegral_double_spatial hgd hH hε hp.1 hp.2.1).2
  rw [DampedNormsHomog.N2onSq, ofReal_integral_eq_lintegral_ofReal hI hnn,
    TimeFractional.P2, lintegral_prod _ hI.aestronglyMeasurable.aemeasurable.ennreal_ofReal]
  rw [← lintegral_indicator measurableSet_Ioi]
  refine lintegral_congr fun s => ?_
  by_cases hs : s ∈ Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem hs]
    simp only [Set.indicator_of_mem hs]
    rw [lintegral_indicator measurableSet_Ioi]
  · rw [Set.indicator_of_notMem hs]
    simp [Set.indicator_of_notMem hs]

/-- **The second tail norm** (`E:damped-tail-norms`): an edge with Laplace domain `(M,∞)`,
`M ≥ 0`, and spectral measure `e^{-ε|ξ|²/2} μ` has `N_{2,e}(e^{-s}G)² ≤ N_2^{(M)}(1)²`. -/
theorem N2_damp_tail_sq_le {M : ℝ} (hM : 0 ≤ M) (E : EdgeData d) (hA : E.A = Ioi M)
    (hμ : E.μ = smoothSpec μ ε) :
    N2 α₀ E (damp 1 g) ^ 2 ≤ ENNReal.ofReal (DampedNormsHomog.N2tailSq α₀ M μ) := by
  have := hH.μ_radon
  obtain ⟨hR, hμ0⟩ := DampedNormsHomog.homog_spectral_facts hH
  unfold N2
  rw [hA, hμ, NC_sq]
  refine iSup_le fun L => ?_
  change QL (nuE α₀ (Ioi M)) (smoothSpec μ ε) (L : ℝ) (zeroExt (damp 1 g))
    (zeroExt (damp 1 g)) ≤ _
  rw [QL_damp_tail_eq hgd hH hε one_pos hM]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := (DampedNormsHomog.N2onSq_smoothed_mono μ hR hμ0 α₀ 1 hH.alpha0_pos
    hH.alpha0_lt_one one_pos (PairingDampedNorms.gaussMultNN ε)
    (PairingDampedNorms.measurable_gaussMultNN ε) (PairingDampedNorms.gaussMultNN_le_one hε.le)
    (Ioc M (L : ℝ)) (Ioi M) measurableSet_Ioc measurableSet_Ioi Ioc_subset_Ioi_self).2.2
  rwa [PairingDampedNorms.smoothed_gaussMultNN] at h

/-- **The first tail norm** (`E:damped-tail-norms`): an edge with Laplace domain `(M,∞)`,
`M ≥ 0`, and spectral measure `e^{-ε|ξ|²/2} μ` has `N_{1,e}(e^{-s}G) ≤ N_1^{(M)}(1)`. -/
theorem N1_damp_tail_le {M : ℝ} (hM : 0 ≤ M) (E : EdgeData d) (hA : E.A = Ioi M)
    (hμ : E.μ = smoothSpec μ ε) :
    N1 α₀ E (damp 1 g) ≤ ENNReal.ofReal (DampedNormsHomog.N1tail α₀ M μ) := by
  have := hH.μ_radon
  obtain ⟨hR, -⟩ := DampedNormsHomog.homog_spectral_facts hH
  have hG : 0 < (Real.Gamma α₀)⁻¹ := inv_pos.2 (Real.Gamma_pos_of_pos hH.alpha0_pos)
  set B : ℝ → ℝ≥0∞ := fun l => ∫⁻ ξ, ENNReal.ofReal (1 / ((1 + l) ^ 2 + ‖ξ‖ ^ 2)) ∂μ with hB
  have hBm : Measurable B :=
    Measurable.lintegral_prod_right' (f := fun p : ℝ × Rd d =>
      ENNReal.ofReal (1 / ((1 + p.1) ^ 2 + ‖p.2‖ ^ 2))) (ENNReal.measurable_ofReal.comp
        (by fun_prop))
  have hae : ∀ᵐ l ∂nuE α₀ (Ioi M), 0 < l := by
    refine (withDensity_absolutelyContinuous _ _).ae_le ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with l hl
    exact lt_of_le_of_lt hM hl
  unfold N1
  rw [hA, hμ]
  calc ∫⁻ l, ∫⁻ ξ, ‖lapFour (damp 1 g) l ξ‖ₑ ∂(smoothSpec μ ε) ∂nuE α₀ (Ioi M)
      ≤ ∫⁻ l, B l ∂nuE α₀ (Ioi M) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae] with l hl
        simp_rw [PairingDampedNorms.enorm_lapFour_damp hgd zero_le_one hl]
        unfold smoothSpec
        have hm : Measurable fun ξ : Rd d => ENNReal.ofReal (1 / ((1 + l) ^ 2 + ‖ξ‖ ^ 2)) :=
          ENNReal.measurable_ofReal.comp (by fun_prop)
        have hgm : Measurable fun ξ : Rd d => ENNReal.ofReal (gaussFactor ε ξ) :=
          ENNReal.measurable_ofReal.comp (by unfold gaussFactor; fun_prop)
        rw [lintegral_withDensity_eq_lintegral_mul _ hgm hm]
        refine lintegral_mono fun ξ => ?_
        simp only [Pi.mul_apply]
        calc ENNReal.ofReal (gaussFactor ε ξ) * ENNReal.ofReal (1 / ((1 + l) ^ 2 + ‖ξ‖ ^ 2))
            ≤ 1 * ENNReal.ofReal (1 / ((1 + l) ^ 2 + ‖ξ‖ ^ 2)) := by
              gcongr
              exact ENNReal.ofReal_le_one.2 (LowAlphaConvolution.gaussFactor_le_one hε.le ξ)
          _ = _ := one_mul _
    _ = ∫⁻ l in Ioi M, ENNReal.ofReal ((Real.Gamma α₀)⁻¹ *
          (l ^ (α₀ - 1) * SpectralHomog.resolvent μ (1 + l))) := by
        unfold nuE
        rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hBm]
        refine setLIntegral_congr_fun measurableSet_Ioi fun l hl => ?_
        have hl0 : (0 : ℝ) < l := lt_of_le_of_lt hM hl
        simp only [Pi.mul_apply, hB]
        rw [← ofReal_integral_eq_lintegral_ofReal
          (SpectralHomog.resolvent_integrable hR (1 + l) (by linarith))
          (Filter.Eventually.of_forall fun ξ => by positivity),
          ← ENNReal.ofReal_mul (mul_nonneg hG.le (Real.rpow_nonneg hl0.le _)), mul_assoc]
        rfl
    _ = ENNReal.ofReal (DampedNormsHomog.N1tail α₀ M μ) := by
        have hI := (ClockCopyHomog.damped_norms_finite_paper hH 1 one_pos).2.2
        rw [← ofReal_integral_eq_lintegral_ofReal, integral_const_mul]
        · unfold DampedNormsHomog.N1tail DampedNormsHomog.N1on
          congr 2
          rw [TimeFractional.L0, Measure.restrict_restrict measurableSet_Ioi,
            Set.inter_eq_left.2 (Ioi_subset_Ioi hM)]
        · exact IntegrableOn.mono_set (t := Ioi 0) (hI.const_mul _) (Ioi_subset_Ioi hM)
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with l hl
          exact mul_nonneg hG.le (mul_nonneg (Real.rpow_nonneg (lt_of_le_of_lt hM hl).le _)
            (ClockCopy.resolvent_nonneg μ _))

end Tail

/-! ### The tail norms for the Green-smoothed kernels (`d = 3`, uniformly in `η`) -/

/-- **The first tail norm from a Laplace-Fourier bound**: if `|𝓛(e^{-s}G)(λ,ξ)| ≤ ((1+λ)²+|ξ|²)⁻¹`
for `λ > 0`, an edge with domain `(M,∞)` and spectral measure `e^{-ε|ξ|²/2} μ` has
`N_{1,e} ≤ N_1^{(M)}(1)`. -/
theorem N1_tail_of_lap {g : Kernel d} {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha α₀ Γ μ) {ε : ℝ} (hε : 0 < ε)
    (hlap : ∀ l : ℝ, 0 < l → ∀ ξ : Rd d,
      ‖lapFour (damp 1 g) l ξ‖ₑ ≤ ENNReal.ofReal (1 / ((1 + l) ^ 2 + ‖ξ‖ ^ 2)))
    {M : ℝ} (hM : 0 ≤ M) (E : EdgeData d) (hA : E.A = Ioi M) (hμ : E.μ = smoothSpec μ ε) :
    N1 α₀ E (damp 1 g) ≤ ENNReal.ofReal (DampedNormsHomog.N1tail α₀ M μ) := by
  have := hH.μ_radon
  obtain ⟨hR, -⟩ := DampedNormsHomog.homog_spectral_facts hH
  have hG : 0 < (Real.Gamma α₀)⁻¹ := inv_pos.2 (Real.Gamma_pos_of_pos hH.alpha0_pos)
  set B : ℝ → ℝ≥0∞ := fun l => ∫⁻ ξ, ENNReal.ofReal (1 / ((1 + l) ^ 2 + ‖ξ‖ ^ 2)) ∂μ with hB
  have hBm : Measurable B :=
    Measurable.lintegral_prod_right' (f := fun p : ℝ × Rd d =>
      ENNReal.ofReal (1 / ((1 + p.1) ^ 2 + ‖p.2‖ ^ 2))) (ENNReal.measurable_ofReal.comp
        (by fun_prop))
  have hae : ∀ᵐ l ∂nuE α₀ (Ioi M), 0 < l := by
    refine (withDensity_absolutelyContinuous _ _).ae_le ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with l hl
    exact lt_of_le_of_lt hM hl
  unfold N1
  rw [hA, hμ]
  calc ∫⁻ l, ∫⁻ ξ, ‖lapFour (damp 1 g) l ξ‖ₑ ∂(smoothSpec μ ε) ∂nuE α₀ (Ioi M)
      ≤ ∫⁻ l, B l ∂nuE α₀ (Ioi M) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae] with l hl
        refine (lintegral_mono (hlap l hl)).trans ?_
        unfold smoothSpec
        have hm : Measurable fun ξ : Rd d => ENNReal.ofReal (1 / ((1 + l) ^ 2 + ‖ξ‖ ^ 2)) :=
          ENNReal.measurable_ofReal.comp (by fun_prop)
        have hgm : Measurable fun ξ : Rd d => ENNReal.ofReal (gaussFactor ε ξ) :=
          ENNReal.measurable_ofReal.comp (by unfold gaussFactor; fun_prop)
        rw [lintegral_withDensity_eq_lintegral_mul _ hgm hm]
        refine lintegral_mono fun ξ => ?_
        simp only [Pi.mul_apply]
        calc ENNReal.ofReal (gaussFactor ε ξ) * ENNReal.ofReal (1 / ((1 + l) ^ 2 + ‖ξ‖ ^ 2))
            ≤ 1 * ENNReal.ofReal (1 / ((1 + l) ^ 2 + ‖ξ‖ ^ 2)) := by
              gcongr
              exact ENNReal.ofReal_le_one.2 (LowAlphaConvolution.gaussFactor_le_one hε.le ξ)
          _ = _ := one_mul _
    _ = ∫⁻ l in Ioi M, ENNReal.ofReal ((Real.Gamma α₀)⁻¹ *
          (l ^ (α₀ - 1) * SpectralHomog.resolvent μ (1 + l))) := by
        unfold nuE
        rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hBm]
        refine setLIntegral_congr_fun measurableSet_Ioi fun l hl => ?_
        have hl0 : (0 : ℝ) < l := lt_of_le_of_lt hM hl
        simp only [Pi.mul_apply, hB]
        rw [← ofReal_integral_eq_lintegral_ofReal
          (SpectralHomog.resolvent_integrable hR (1 + l) (by linarith))
          (Filter.Eventually.of_forall fun ξ => by positivity),
          ← ENNReal.ofReal_mul (mul_nonneg hG.le (Real.rpow_nonneg hl0.le _)), mul_assoc]
        rfl
    _ = ENNReal.ofReal (DampedNormsHomog.N1tail α₀ M μ) := by
        have hI := (ClockCopyHomog.damped_norms_finite_paper hH 1 one_pos).2.2
        rw [← ofReal_integral_eq_lintegral_ofReal, integral_const_mul]
        · unfold DampedNormsHomog.N1tail DampedNormsHomog.N1on
          congr 2
          rw [TimeFractional.L0, Measure.restrict_restrict measurableSet_Ioi,
            Set.inter_eq_left.2 (Ioi_subset_Ioi hM)]
        · exact IntegrableOn.mono_set (t := Ioi 0) (hI.const_mul _) (Ioi_subset_Ioi hM)
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with l hl
          exact mul_nonneg hG.le (mul_nonneg (Real.rpow_nonneg (lt_of_le_of_lt hM hl).le _)
            (ClockCopy.resolvent_nonneg μ _))

section TailSmooth

variable {G : ℝ → Measure (Rd d)} {η : ℝ} {g : Kernel d}
  (hgd : PairingSmoothedNorms.SmoothDensity d G η g)
  {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)} (hH : HomogCovariance d alpha α₀ Γ μ)
  {ε : ℝ} (hε : 0 < ε)
include hgd hH hε

/-- The capped quadratic form with the tail domain `(M,∞)` for a smoothed Green density (the
analogue of `PairingSmoothedNorms.QL_damp_eq`). -/
theorem QL_damp_tail_eq_smooth {θ : ℝ} (hθ : 0 < θ) {M : ℝ} (hM : 0 ≤ M) (L : ℝ) :
    QL (nuE α₀ (Ioi M)) (smoothSpec μ ε) L (zeroExt (damp θ g)) (zeroExt (damp θ g)) =
      ENNReal.ofReal (DampedNormsHomog.N2onSq α₀ θ (Ioc M L)
        (DampedNormsHomog.smoothed μ (PairingSmoothedNorms.multNN ε η))) := by
  have := hH.μ_radon
  obtain ⟨hR, hμ0⟩ := DampedNormsHomog.homog_spectral_facts hH
  obtain ⟨hI, -, -⟩ := DampedNormsHomog.N2onSq_smoothed_mono μ hR hμ0 α₀ θ hH.alpha0_pos
    hH.alpha0_lt_one hθ (PairingSmoothedNorms.multNN ε η) (PairingSmoothedNorms.measurable_multNN ε η)
    (PairingSmoothedNorms.multNN_le_one hε.le hgd.nonneg)
    (Ioc M L) univ measurableSet_Ioc MeasurableSet.univ (subset_univ _)
  obtain ⟨hc, -⟩ := PairingDampedNorms.gammaEps_props hH hε
  have hγ : ∀ z, gammaOf (smoothSpec μ ε) z = ENNReal.ofReal (gammaEps Γ ε z) := fun z => by
    rw [gammaOf_smoothSpec hH hε, LowAlphaUpper.covEps_eq_ofReal hε.le
      (LowAlphaConvolution.integrable_heatDens hH.Γ_tempered hε)]
  have hzm : Measurable fun p : ℝ × Rd d => zeroExt (damp θ g) p.1 p.2 := by
    have e : (fun p : ℝ × Rd d => zeroExt (damp θ g) p.1 p.2) =
        {p : ℝ × Rd d | 0 < p.1}.indicator (Function.uncurry (damp θ g)) := by
      funext p
      by_cases hp : 0 < p.1
      · rw [Set.indicator_of_mem (show p ∈ {p : ℝ × Rd d | 0 < p.1} from hp)]
        exact Set.indicator_of_mem (show p.1 ∈ Ioi (0 : ℝ) from hp) _
      · rw [Set.indicator_of_notMem (show p ∉ {p : ℝ × Rd d | 0 < p.1} from hp)]
        exact Set.indicator_of_notMem (show p.1 ∉ Ioi (0 : ℝ) from hp) _
    rw [e]
    exact (hgd.measurable_damp θ).indicator (measurableSet_lt measurable_const measurable_fst)
  have hΦ : Measurable fun w : (ℝ × Rd d) × (ℝ × Rd d) =>
      zeroExt (damp θ g) w.1.1 w.1.2 * zeroExt (damp θ g) w.2.1 w.2.2 *
        kappaCap (nuE α₀ (Ioi M)) L (w.1.1 - w.2.1) * gammaOf (smoothSpec μ ε) (w.1.2 - w.2.2) := by
    have hνs : SFinite (nuE α₀ (Ioi M)) := by unfold nuE; infer_instance
    have hγm : Measurable fun w : (ℝ × Rd d) × (ℝ × Rd d) =>
        gammaOf (smoothSpec μ ε) (w.1.2 - w.2.2) := by
      simp_rw [hγ]
      exact ENNReal.measurable_ofReal.comp (hc.measurable.comp
        ((measurable_snd.comp measurable_fst).sub (measurable_snd.comp measurable_snd)))
    exact (((hzm.comp measurable_fst).mul (hzm.comp measurable_snd)).mul
      ((PairingDampedNorms.measurable_kappaCap _ L).comp ((measurable_fst.comp measurable_fst).sub
        (measurable_fst.comp measurable_snd)))).mul hγm
  unfold QL
  rw [PairingDampedNorms.lintegral_four (fun s x r y => zeroExt (damp θ g) s x * zeroExt (damp θ g) r y *
    kappaCap (nuE α₀ (Ioi M)) L (s - r) * gammaOf (smoothSpec μ ε) (x - y)) hΦ]
  have hpt : ∀ s r : ℝ, ∫⁻ x, ∫⁻ y, zeroExt (damp θ g) s x * zeroExt (damp θ g) r y *
      kappaCap (nuE α₀ (Ioi M)) L (s - r) * gammaOf (smoothSpec μ ε) (x - y) =
      (Ioi (0 : ℝ)).indicator (fun s => (Ioi (0 : ℝ)).indicator (fun r =>
        ENNReal.ofReal (DampedNormsHomog.N2onOuter α₀ θ (Ioc M L)
          (DampedNormsHomog.smoothed μ (PairingSmoothedNorms.multNN ε η)) (s, r))) r) s := by
    intro s r
    by_cases hs : s ∈ Ioi (0 : ℝ)
    · by_cases hr : r ∈ Ioi (0 : ℝ)
      · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hr]
        have hs0 : 0 < s := hs
        have hr0 : 0 < r := hr
        have hzs : ∀ x, zeroExt (damp θ g) s x = ENNReal.ofReal (Real.exp (-(θ * s))) * g s x :=
          fun x => Set.indicator_of_mem hs _
        have hzr : ∀ y, zeroExt (damp θ g) r y = ENNReal.ofReal (Real.exp (-(θ * r))) * g r y :=
          fun y => Set.indicator_of_mem hr _
        set c := ENNReal.ofReal (Real.exp (-(θ * s))) * ENNReal.ofReal (Real.exp (-(θ * r))) *
          kappaCap (nuE α₀ (Ioi M)) L (s - r) with hcdef
        have hct : c ≠ ∞ := by
          rw [hcdef, kappaCap_nuE_tail hH.alpha0_pos hM]
          exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
        have hre : ∀ x y, zeroExt (damp θ g) s x * zeroExt (damp θ g) r y *
            kappaCap (nuE α₀ (Ioi M)) L (s - r) * gammaOf (smoothSpec μ ε) (x - y) =
            c * (g s x * g r y * gammaOf (smoothSpec μ ε) (x - y)) := by
          intro x y
          rw [hzs, hzr, hcdef]
          ring
        simp_rw [hre, lintegral_const_mul' _ _ hct]
        rw [(PairingSmoothedNorms.lintegral_double_spatial hgd hH hε hs0 hr0).1, PairingSmoothedNorms.integral_wh_smoothSpec, hcdef,
          kappaCap_nuE_tail hH.alpha0_pos hM,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (mul_nonneg (by positivity)
            (DampedNormsHomog.KS_nonneg _ _ _ hH.alpha0_pos))]
        unfold DampedNormsHomog.N2onOuter
        congr 1
        rw [show -(θ * (s + r)) = -(θ * s) + -(θ * r) by ring, Real.exp_add]
      · rw [Set.indicator_of_mem hs, Set.indicator_of_notMem hr]
        have hzr : ∀ y, zeroExt (damp θ g) r y = 0 := fun y => Set.indicator_of_notMem hr _
        simp [hzr]
    · rw [Set.indicator_of_notMem hs]
      have hzs : ∀ x, zeroExt (damp θ g) s x = 0 := fun x => Set.indicator_of_notMem hs _
      simp [hzs]
  simp_rw [hpt]
  have hnn : 0 ≤ᵐ[TimeFractional.P2] DampedNormsHomog.N2onOuter α₀ θ (Ioc M L)
      (DampedNormsHomog.smoothed μ (PairingSmoothedNorms.multNN ε η)) := by
    filter_upwards [DampedNorms.ae_P2] with p hp
    unfold DampedNormsHomog.N2onOuter
    rw [← PairingSmoothedNorms.integral_wh_smoothSpec]
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le
      (DampedNormsHomog.KS_nonneg _ _ _ hH.alpha0_pos))
      (PairingSmoothedNorms.lintegral_double_spatial hgd hH hε hp.1 hp.2.1).2
  rw [DampedNormsHomog.N2onSq, ofReal_integral_eq_lintegral_ofReal hI hnn,
    TimeFractional.P2, lintegral_prod _ hI.aestronglyMeasurable.aemeasurable.ennreal_ofReal]
  rw [← lintegral_indicator measurableSet_Ioi]
  refine lintegral_congr fun s => ?_
  by_cases hs : s ∈ Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem hs]
    simp only [Set.indicator_of_mem hs]
    rw [lintegral_indicator measurableSet_Ioi]
  · rw [Set.indicator_of_notMem hs]
    simp [Set.indicator_of_notMem hs]

/-- **The second tail norm for a smoothed Green density**, uniformly in the Green width. -/
theorem N2_damp_tail_sq_le_smooth {M : ℝ} (hM : 0 ≤ M) (E : EdgeData d) (hA : E.A = Ioi M)
    (hμ : E.μ = smoothSpec μ ε) :
    N2 α₀ E (damp 1 g) ^ 2 ≤ ENNReal.ofReal (DampedNormsHomog.N2tailSq α₀ M μ) := by
  have := hH.μ_radon
  obtain ⟨hR, hμ0⟩ := DampedNormsHomog.homog_spectral_facts hH
  unfold N2
  rw [hA, hμ, NC_sq]
  refine iSup_le fun L => ?_
  change QL (nuE α₀ (Ioi M)) (smoothSpec μ ε) (L : ℝ) (zeroExt (damp 1 g))
    (zeroExt (damp 1 g)) ≤ _
  rw [QL_damp_tail_eq_smooth hgd hH hε one_pos hM]
  refine ENNReal.ofReal_le_ofReal ?_
  exact (DampedNormsHomog.N2onSq_smoothed_mono μ hR hμ0 α₀ 1 hH.alpha0_pos
    hH.alpha0_lt_one one_pos (PairingSmoothedNorms.multNN ε η)
    (PairingSmoothedNorms.measurable_multNN ε η)
    (PairingSmoothedNorms.multNN_le_one hε.le hgd.nonneg)
    (Ioc M (L : ℝ)) (Ioi M) measurableSet_Ioc measurableSet_Ioi Ioc_subset_Ioi_self).2.2

/-- **The first tail norm for a smoothed Green density**, uniformly in the Green width. -/
theorem N1_damp_tail_le_smooth {M : ℝ} (hM : 0 ≤ M) (E : EdgeData d) (hA : E.A = Ioi M)
    (hμ : E.μ = smoothSpec μ ε) :
    N1 α₀ E (damp 1 g) ≤ ENNReal.ofReal (DampedNormsHomog.N1tail α₀ M μ) :=
  N1_tail_of_lap hH hε (fun l hl ξ => by
    rw [PairingSmoothedNorms.enorm_lapFour_damp hgd zero_le_one hl]
    exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left (by positivity)
      (LowAlphaConvolution.gaussFactor_le_one hgd.nonneg ξ))) hM E hA hμ

end TailSmooth

/-! ### The difference of products (TeX 1900-1903) -/

/-- **The elementary difference-of-products inequality**:
`∏ (g_i + h_i) ≤ ∏ g_i + Σ_i h_i ∏_{j ≠ i} (g_j + h_j)` (one marked factor per term). -/
theorem prod_add_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (g h : ι → ℝ≥0∞) :
    ∏ i ∈ s, (g i + h i) ≤ ∏ i ∈ s, g i + ∑ i ∈ s, h i * ∏ j ∈ s.erase i, (g j + h j) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj, Finset.erase_insert hj,
      add_mul]
    have hrest : ∀ i ∈ s, g j * (h i * ∏ l ∈ s.erase i, (g l + h l)) ≤
        h i * ∏ l ∈ (insert j s).erase i, (g l + h l) := by
      intro i hi
      have hne : j ≠ i := fun h' => hj (h' ▸ hi)
      rw [Finset.erase_insert_of_ne hne,
        Finset.prod_insert fun h' => hj (Finset.mem_of_mem_erase h')]
      calc g j * (h i * ∏ l ∈ s.erase i, (g l + h l))
          = h i * (g j * ∏ l ∈ s.erase i, (g l + h l)) := by ring
        _ ≤ h i * ((g j + h j) * ∏ l ∈ s.erase i, (g l + h l)) := by
            gcongr; exact le_self_add
    calc g j * ∏ i ∈ s, (g i + h i) + h j * ∏ i ∈ s, (g i + h i)
        ≤ g j * (∏ i ∈ s, g i + ∑ i ∈ s, h i * ∏ l ∈ s.erase i, (g l + h l)) +
            h j * ∏ i ∈ s, (g i + h i) := by gcongr
      _ = g j * ∏ i ∈ s, g i + ∑ i ∈ s, g j * (h i * ∏ l ∈ s.erase i, (g l + h l)) +
            h j * ∏ i ∈ s, (g i + h i) := by rw [mul_add, Finset.mul_sum]
      _ ≤ g j * ∏ i ∈ s, g i + ∑ i ∈ s, h i * ∏ l ∈ (insert j s).erase i, (g l + h l) +
            h j * ∏ i ∈ s, (g i + h i) :=
          add_le_add (add_le_add le_rfl (Finset.sum_le_sum fun i hi => hrest i hi)) le_rfl
      _ = _ := by ring

/-- `|r|^{-α₀} = γ^0_η(r) + K_{1/η}(r)`: the full Gamma mixture splits at the cap `η⁻¹`
(TeX 1883-1885). -/
theorem kerA_Ioi_split (a : ℝ) {η : ℝ} (hη : 0 < η) (u : ℝ) :
    kerA a (Ioi 0) u = kerA a (capSet η) u + kerA a (Ioi η⁻¹) u := by
  have hU : Ioi (0 : ℝ) = capSet η ∪ Ioi η⁻¹ := by
    rw [capSet_of_pos hη]; exact (Ioc_union_Ioi_eq_Ioi (inv_pos.2 hη).le).symm
  have hdisj : Disjoint (capSet η) (Ioi η⁻¹) := by
    rw [capSet_of_pos hη]
    exact Set.disjoint_left.2 fun x hx hx' => (not_lt.2 hx.2) hx'
  unfold kerA nuE
  rw [hU, Measure.restrict_union hdisj measurableSet_Ioi, withDensity_add_measure,
    lintegral_add_measure]

/-- The Laplace domains with one marked edge `e₀` carrying the tail `(M,∞)`. -/
def markA {N : ℕ} (e0 : Sym2 (Fin N)) (M : ℝ) : Sym2 (Fin N) → Set ℝ :=
  fun e => if e = e0 then Ioi M else Ioi 0

theorem measurableSet_markA {N : ℕ} (e0 : Sym2 (Fin N)) (M : ℝ) (e : Sym2 (Fin N)) :
    MeasurableSet (markA e0 M e) := by
  unfold markA; split_ifs <;> exact measurableSet_Ioi

theorem markA_subset {N : ℕ} (e0 : Sym2 (Fin N)) {M : ℝ} (hM : 0 ≤ M) (e : Sym2 (Fin N)) :
    markA e0 M e ⊆ Ioi 0 := by
  unfold markA; split_ifs
  · exact Ioi_subset_Ioi hM
  · exact subset_rfl

/-- Distinct openers give distinct pairs. -/
theorem edge_ne_of_openers {N : ℕ} {D : Fin N → Fin N} {i j : Fin N} (hi : i ∈ openers D)
    (hj : j ∈ openers D) (hne : i ≠ j) : s(i, D i) ≠ s(j, D j) := by
  intro h
  have hi' : i < D i := (Finset.mem_filter.1 hi).2
  have hj' : j < D j := (Finset.mem_filter.1 hj).2
  rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact hne h1
  · rw [h2] at hi'
    rw [← h1] at hj'
    exact absurd (hi'.trans hj') (lt_irrefl _)

/-- **The difference of products for the pair product**:
`∏ |s_j-s_h|^{-α₀} ≤ ∏ γ^0_η(s_j-s_h) + Σ_{marked pair} K_{1/η} ∏_{others} |·|^{-α₀}`
(TeX 1900-1903). -/
theorem pairTime_zero_le {a η : ℝ} (hη : 0 < η) {N : ℕ} (m : ℕ) (D : Fin N → Fin N)
    (r : Fin N → ℝ) :
    pairTime a (capDom (0 : Fin N → ℝ)) m D r ≤ pairTime a (capDom fun _ : Fin N => η) m D r +
      ∑ i0 ∈ openers D, pairTime a (markA s(i0, D i0) η⁻¹) m D r := by
  set u : Fin N → ℝ := fun i => gapTime m r i - gapTime m r (D i) with hu
  have h0 : pairTime a (capDom (0 : Fin N → ℝ)) m D r =
      ∏ i ∈ openers D, (kerA a (capSet η) (u i) + kerA a (Ioi η⁻¹) (u i)) := by
    unfold pairTime
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [capDom_zero, kerA_Ioi_split a hη]
  have hc : pairTime a (capDom fun _ : Fin N => η) m D r = ∏ i ∈ openers D, kerA a (capSet η) (u i) := by
    unfold pairTime
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [capDom_const]
  have hm : ∀ i0 ∈ openers D, pairTime a (markA s(i0, D i0) η⁻¹) m D r =
      kerA a (Ioi η⁻¹) (u i0) *
        ∏ j ∈ (openers D).erase i0, (kerA a (capSet η) (u j) + kerA a (Ioi η⁻¹) (u j)) := by
    intro i0 hi0
    unfold pairTime
    rw [← Finset.mul_prod_erase _ _ hi0]
    congr 1
    · simp only [markA, ↓reduceIte, hu]
    · refine Finset.prod_congr rfl fun j hj => ?_
      have hne := edge_ne_of_openers (Finset.mem_of_mem_erase hj) hi0 (Finset.ne_of_mem_erase hj)
      simp only [markA, hne, ↓reduceIte]
      rw [kerA_Ioi_split a hη]
  rw [h0, hc, Finset.sum_congr rfl hm]
  exact prod_add_le _ _ _

/-! ### The envelope with one marked edge -/

/-- **An admissible product with one marked edge** (TeX 1912-1914: "The marked edge appears once
in the first-norm product or twice in the second-norm product in every admissible assignment"):
if `N_0 ≤ 1`, every unmarked edge has `2N_1 ≤ Z`, `N_2 ≤ Z` (`Z ≥ 1`) and the marked edge has
`2N_1 ≤ τ_1`, `N_2² ≤ τ_2`, the product is at most `(τ_1 + τ_2) Z^{2|L|}`. -/
theorem prodP_marked_le {α : Type*} [DecidableEq α] (a : ℝ) {L : Finset α}
    {Ds : Finset (Sym2 α)} (ed : Sym2 α → EdgeData d) (G : Kernel d) (A : Adm L Ds)
    {Z τ1 τ2 : ℝ≥0∞} (hZ : 1 ≤ Z) (hN0 : N0 G ≤ 1) {e0 : Sym2 α} (he0 : e0 ∈ Ds)
    (h1 : ∀ e ∈ Ds, e ≠ e0 → 2 * N1 a (ed e) G ≤ Z) (h2 : ∀ e ∈ Ds, e ≠ e0 → N2 a (ed e) G ≤ Z)
    (t1 : 2 * N1 a (ed e0) G ≤ τ1) (t2 : N2 a (ed e0) G ^ 2 ≤ τ2) :
    prodP a ed (fun _ => G) A ≤ (τ1 + τ2) * Z ^ (2 * L.card) := by
  have hQ1L : A.Q1 ⊆ L := fun l hl => A.cover ▸
    Finset.mem_union_left _ (Finset.mem_union_right _ hl)
  have hQ2L : A.Q2 ⊆ L := fun l hl => A.cover ▸ Finset.mem_union_right _ hl
  have hrest1 : ∏ l ∈ A.Q1.filter (fun l => ¬ A.iota l = e0), 2 * N1 a (ed (A.iota l)) G ≤
      Z ^ L.card := by
    calc _ ≤ ∏ _l ∈ A.Q1.filter (fun l => ¬ A.iota l = e0), Z :=
          Finset.prod_le_prod fun l hl => by
            rw [Finset.mem_filter] at hl
            exact h1 _ (A.mapsTo l (Finset.mem_union_left _ hl.1)) hl.2
      _ = Z ^ (A.Q1.filter fun l => ¬ A.iota l = e0).card := Finset.prod_const _
      _ ≤ Z ^ L.card := pow_le_pow_right₀ hZ
          (Finset.card_le_card ((Finset.filter_subset _ _).trans hQ1L))
  have hrest2 : ∏ l ∈ A.Q2.filter (fun l => ¬ A.iota l = e0), N2 a (ed (A.iota l)) G ≤
      Z ^ L.card := by
    calc _ ≤ ∏ _l ∈ A.Q2.filter (fun l => ¬ A.iota l = e0), Z :=
          Finset.prod_le_prod fun l hl => by
            rw [Finset.mem_filter] at hl
            exact h2 _ (A.mapsTo l (Finset.mem_union_right _ hl.1)) hl.2
      _ = Z ^ (A.Q2.filter fun l => ¬ A.iota l = e0).card := Finset.prod_const _
      _ ≤ Z ^ L.card := pow_le_pow_right₀ hZ
          (Finset.card_le_card ((Finset.filter_subset _ _).trans hQ2L))
  have h0 : ∏ _l ∈ A.Q0, N0 G ≤ 1 := by
    calc ∏ _l ∈ A.Q0, N0 G ≤ ∏ _l ∈ A.Q0, (1 : ℝ≥0∞) := Finset.prod_le_prod fun _ _ => hN0
      _ = 1 := Finset.prod_const_one
  have hpow : Z ^ (2 * L.card) = Z ^ L.card * Z ^ L.card := by rw [two_mul, pow_add]
  unfold prodP
  rw [← Finset.prod_filter_mul_prod_filter_not A.Q1 (fun l => A.iota l = e0),
    ← Finset.prod_filter_mul_prod_filter_not A.Q2 (fun l => A.iota l = e0)]
  rcases A.edge e0 he0 with ⟨c1, c2⟩ | ⟨c1, c2⟩
  · obtain ⟨l0, hl0⟩ := Finset.card_eq_one.1 c1
    have hι : A.iota l0 = e0 := by
      have := Finset.mem_singleton_self l0
      rw [← hl0] at this
      exact (Finset.mem_filter.1 this).2
    rw [Finset.card_eq_zero.1 c2, hl0, Finset.prod_singleton, Finset.prod_empty, hι]
    calc (∏ _l ∈ A.Q0, N0 G) * (2 * N1 a (ed e0) G *
          ∏ l ∈ A.Q1.filter (fun l => ¬ A.iota l = e0), 2 * N1 a (ed (A.iota l)) G) *
          (1 * ∏ l ∈ A.Q2.filter (fun l => ¬ A.iota l = e0), N2 a (ed (A.iota l)) G)
        ≤ 1 * (τ1 * Z ^ L.card) * (1 * Z ^ L.card) := by gcongr
      _ = τ1 * (Z ^ L.card * Z ^ L.card) := by ring
      _ ≤ (τ1 + τ2) * Z ^ (2 * L.card) := by rw [hpow]; gcongr; exact le_self_add
  · obtain ⟨x, y, hxy, hxy'⟩ := Finset.card_eq_two.1 c2
    have hx : A.iota x = e0 := by
      have : x ∈ A.Q2.filter (fun l => A.iota l = e0) := by rw [hxy']; simp
      exact (Finset.mem_filter.1 this).2
    have hy : A.iota y = e0 := by
      have : y ∈ A.Q2.filter (fun l => A.iota l = e0) := by rw [hxy']; simp
      exact (Finset.mem_filter.1 this).2
    rw [Finset.card_eq_zero.1 c1, hxy', Finset.prod_pair hxy, Finset.prod_empty, hx, hy]
    calc (∏ _l ∈ A.Q0, N0 G) * (1 *
          ∏ l ∈ A.Q1.filter (fun l => ¬ A.iota l = e0), 2 * N1 a (ed (A.iota l)) G) *
          (N2 a (ed e0) G * N2 a (ed e0) G *
            ∏ l ∈ A.Q2.filter (fun l => ¬ A.iota l = e0), N2 a (ed (A.iota l)) G)
        ≤ 1 * (1 * Z ^ L.card) * (τ2 * Z ^ L.card) := by
          rw [← sq]; gcongr
      _ = τ2 * (Z ^ L.card * Z ^ L.card) := by ring
      _ ≤ (τ1 + τ2) * Z ^ (2 * L.card) := by rw [hpow]; gcongr; exact le_add_self

/-! ### The assembly for a Green family with a finite density (d = 1, 2) -/

theorem le_of_sq_le {x K : ℝ≥0∞} (hK : 1 ≤ K) (h : x ^ 2 ≤ K) : x ≤ K := by
  rcases le_total x 1 with hx | hx
  · exact hx.trans hK
  · calc x = x * 1 := (mul_one x).symm
      _ ≤ x * x := by gcongr
      _ = x ^ 2 := (sq x).symm
      _ ≤ K := h

theorem N1tail_nonneg {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)} (hH : HomogCovariance d alpha α₀ Γ μ)
    (M : ℝ) : 0 ≤ DampedNormsHomog.N1tail α₀ M μ := by
  unfold DampedNormsHomog.N1tail DampedNormsHomog.N1on
  refine mul_nonneg (inv_nonneg.2 (Real.Gamma_pos_of_pos hH.alpha0_pos).le)
    (integral_nonneg_of_ae ?_)
  filter_upwards [ae_restrict_of_ae (ae_restrict_mem (μ := volume) measurableSet_Ioi)] with l hl
  exact mul_nonneg (Real.rpow_nonneg (le_of_lt hl) _) (ClockCopy.resolvent_nonneg μ _)

section Assembly

variable {g : Kernel d} (hgd : GreenDensity d g)
  {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)} (hH : HomogCovariance d alpha α₀ Γ μ)
include hgd hH

/-- The unmarked edges: `2N_1 ≤ K` and `N_2 ≤ K` with `K = Khom` (`L:damped-homogeneous-norms`,
uniformly in the spatial width of the edge). -/
theorem unmarked_le {b : ℝ} (hb : 0 < b) (E : EdgeData d) (hA : E.A = Ioi 0)
    (hμ : E.μ = smoothSpec μ b) :
    2 * N1 α₀ E (damp 1 g) ≤ ENNReal.ofReal (HomogeneousEnvelope.Khom α₀ μ) ∧
      N2 α₀ E (damp 1 g) ≤ ENNReal.ofReal (HomogeneousEnvelope.Khom α₀ μ) := by
  have e1 : N1 α₀ E (damp 1 g) = N1 α₀ (smoothEdge hH hb) (damp 1 g) := by
    unfold N1; rw [hA, hμ]; rfl
  have e2 : N2 α₀ E (damp 1 g) = N2 α₀ (smoothEdge hH hb) (damp 1 g) := by
    unfold N2; rw [hA, hμ]; rfl
  have hK1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (HomogeneousEnvelope.Khom α₀ μ) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (HomogeneousEnvelope.one_le_Khom α₀ μ)
  constructor
  · rw [e1]
    calc 2 * N1 α₀ (smoothEdge hH hb) (damp 1 g)
        ≤ 2 * ENNReal.ofReal (DampedNorms.N1 α₀ 1 μ) := by
          gcongr; exact PairingDampedNorms.N1_damp_le hgd hH hb one_pos
      _ = ENNReal.ofReal (2 * DampedNorms.N1 α₀ 1 μ) := by
          rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]
      _ ≤ _ := ENNReal.ofReal_le_ofReal ((le_max_left _ _).trans (le_max_left _ _))
  · rw [e2]
    refine le_of_sq_le hK1 ((PairingDampedNorms.N2_damp_sq_le hgd hH hb one_pos).trans ?_)
    exact ENNReal.ofReal_le_ofReal ((le_max_right _ _).trans (le_max_left _ _))

/-- The marked edge: `2N_1 ≤ τ` and `N_2² ≤ τ` with `τ = 2(N_1^{(M)}(1) + N_2^{(M)}(1)²)`. -/
theorem marked_le {b : ℝ} (hb : 0 < b) {M : ℝ} (hM : 0 ≤ M) (E : EdgeData d) (hA : E.A = Ioi M)
    (hμ : E.μ = smoothSpec μ b) :
    2 * N1 α₀ E (damp 1 g) ≤ ENNReal.ofReal (2 * (DampedNormsHomog.N1tail α₀ M μ +
        DampedNormsHomog.N2tailSq α₀ M μ)) ∧
      N2 α₀ E (damp 1 g) ^ 2 ≤ ENNReal.ofReal (2 * (DampedNormsHomog.N1tail α₀ M μ +
        DampedNormsHomog.N2tailSq α₀ M μ)) := by
  have h1 := N1tail_nonneg hH M
  have h2 := (DampedNormsHomog.N2tail_props hH M).2.2.2
  constructor
  · calc 2 * N1 α₀ E (damp 1 g) ≤ 2 * ENNReal.ofReal (DampedNormsHomog.N1tail α₀ M μ) := by
          gcongr; exact N1_damp_tail_le hgd hH hb hM E hA hμ
      _ = ENNReal.ofReal (2 * DampedNormsHomog.N1tail α₀ M μ) := by
          rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)
  · exact (N2_damp_tail_sq_le hgd hH hb hM E hA hμ).trans (ENNReal.ofReal_le_ofReal (by linarith))

omit hH in
/-- The damped kernels satisfy the envelope's kernel hypotheses once the edge norms are finite. -/
theorem kernelHyp_wick {α : Type*} [DecidableEq α] (dg : TwoChain α) (ed : Sym2 α → EdgeData d)
    (h : ∀ e ∈ dg.D, N1 α₀ (ed e) (damp 1 g) < ⊤ ∧ N2 α₀ (ed e) (damp 1 g) < ⊤) :
    KernelHyp α₀ dg ed (fun _ => damp 1 g) :=
  ⟨fun _ _ => hgd.measurable_damp 1,
    fun _ _ => by rw [PairingDampedNorms.N0_damp hgd one_pos]; exact ENNReal.ofReal_lt_top,
    fun _ _ e he => (h e he).1, fun _ _ e he => (h e he).2⟩

/-- **The horizon loss and the bridge to M7** (TeX 1905-1912): on `ℓ_1 < T_1, ℓ_2 < T_2`,
`∫ ∏ κ_{A_e} dρ_{ε,D} ≤ e^{T_1+T_2} I_D(e^{-s} G)` with the per-edge data `wickEdge`. -/
theorem horizon_le_pairingIntegral (hBr : M8M7BridgeTarget d) {m n : ℕ}
    {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n) {ε : Fin (m + n) → ℝ} (hε : ∀ i, 0 < ε i)
    (A : Sym2 (Fin (m + n)) → Set ℝ) (hAm : ∀ e, MeasurableSet (A e)) (hA0 : ∀ e, A e ⊆ Ioi 0)
    (T1 T2 : ℝ) :
    ∫⁻ r in horizon m T1 T2, pairTime α₀ A m D r ∂wickRho (waveGreen d) Γ ε m D ≤
      ENNReal.ofReal (Real.exp (T1 + T2)) *
        pairingIntegral α₀ (m4Chain m n D) (wickEdge hH hε A hAm hA0) (fun _ => damp 1 g) := by
  have hHm := JointFixedOrder.measurableSet_horizon m (N := m + n) T1 T2
  calc ∫⁻ r in horizon m T1 T2, pairTime α₀ A m D r ∂wickRho (waveGreen d) Γ ε m D
      ≤ ∫⁻ r in horizon m T1 T2, ENNReal.ofReal (Real.exp (T1 + T2)) *
          (ENNReal.ofReal (Real.exp (-(1 * ∑ i, r i))) * pairTime α₀ A m D r)
          ∂wickRho (waveGreen d) Γ ε m D := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem hHm] with r hr
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        have h1 : 1 ≤ Real.exp (T1 + T2 + -(1 * ∑ i, r i)) := Real.one_le_exp (by
          linarith [JointFixedOrder.sum_lt_of_mem_horizon hr])
        calc pairTime α₀ A m D r = 1 * pairTime α₀ A m D r := (one_mul _).symm
          _ ≤ _ := by
              gcongr
              rw [← ENNReal.ofReal_one]
              exact ENNReal.ofReal_le_ofReal h1
    _ ≤ ∫⁻ r, ENNReal.ofReal (Real.exp (T1 + T2)) *
          (ENNReal.ofReal (Real.exp (-(1 * ∑ i, r i))) * pairTime α₀ A m D r)
          ∂wickRho (waveGreen d) Γ ε m D := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (Real.exp (T1 + T2)) * ∫⁻ r, ENNReal.ofReal (Real.exp (-(1 * ∑ i, r i))) *
          pairTime α₀ A m D r ∂wickRho (waveGreen d) Γ ε m D :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
        gcongr
        exact hBr hH (waveGreen d) g hgd.meas hgd.fin hgd.eq m n D hD ε hε A hAm hA0 1 zero_le_one

/-- **`E:joint-temporal-tail` for a Green family with a finite density** (TeX lines 1892-1921 at
revision edf7085f (book 1.1.3); d = 1, 2 by `green1`, `green2`), with the per-edge bridge
`M8M7BridgeTarget` (item C) as a hypothesis: the difference of products
(`pairTime_zero_le`), the horizon loss `e^{T_1+T_2}` and the bridge
(`horizon_le_pairingIntegral`), `L:pairing-product-envelope`
(`PairingEnvelope.pairing_product_envelope`), the unmarked norms by
`L:damped-homogeneous-norms` (`unmarked_le`) and the marked tail norms (`marked_le`), all
independent of the spatial widths; the marked edge is used once in `Q_1` or twice in `Q_2`
(`prodP_marked_le`).  The constant is `C = (m+n) e^{T_1+T_2} K^{2(m+n)} · 4`. -/
theorem joint_temporal_tail_of_density (hBr : M8M7BridgeTarget d) {m n k : ℕ}
    (hmn : m + n = 2 * k) (hk : 1 ≤ k) {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n)
    {T1 T2 : ℝ} : ∃ C : ℝ, ∀ ε : Fin (m + n) → ℝ, (∀ i, 0 < ε i) →
    ∀ η : ℝ, 0 < η →
      wickF (waveGreen d) Γ α₀ (capDom fun _ : Fin (m + n) => η) ε m D T1 T2 ≤
          wickF (waveGreen d) Γ α₀ (capDom (0 : Fin (m + n) → ℝ)) ε m D T1 T2 ∧
        wickF (waveGreen d) Γ α₀ (capDom (0 : Fin (m + n) → ℝ)) ε m D T1 T2 ≠ ⊤ ∧
        wickF (waveGreen d) Γ α₀ (capDom (0 : Fin (m + n) → ℝ)) ε m D T1 T2 ≤
          wickF (waveGreen d) Γ α₀ (capDom fun _ : Fin (m + n) => η) ε m D T1 T2 +
            ENNReal.ofReal (C * (DampedNormsHomog.N1tail α₀ η⁻¹ μ +
              DampedNormsHomog.N2tailSq α₀ η⁻¹ μ)) := by
  set Lc := (m4Chain m n D).labels.card with hLc
  set Zr := HomogeneousEnvelope.Khom α₀ μ with hZr
  set Ex := Real.exp (T1 + T2) with hEx
  refine ⟨((m + n : ℕ) : ℝ) * Ex * Zr ^ (2 * Lc) * 4, fun ε hε η hη => ?_⟩
  have hZr0 : 0 ≤ Zr := (HomogeneousEnvelope.Khom_pos α₀ μ).le
  have hZ : (1 : ℝ≥0∞) ≤ ENNReal.ofReal Zr := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (HomogeneousEnvelope.one_le_Khom α₀ μ)
  have hN0 : N0 (damp 1 g) ≤ 1 := by rw [PairingDampedNorms.N0_damp hgd one_pos]; simp
  have hPE := PairingEnvelope.pairing_product_envelope d (Fin (m + n)) α₀ hH.alpha0_pos
    hH.alpha0_lt_one (m4Chain m n D)
  have hwf := m4Chain_wf hD
  have hcard : (openers D).card = k := DiagramModel.card_openers hD hmn
  obtain ⟨i1, hi1⟩ : (openers D).Nonempty := by
    rw [← Finset.card_pos, hcard]; omega
  have he1 : s(i1, D i1) ∈ (m4Chain m n D).D := by
    rw [D_m4Chain_eq_image hD]; exact Finset.mem_image_of_mem _ hi1
  have hHm := JointFixedOrder.measurableSet_horizon m (N := m + n) T1 T2
  -- the full kernels: the envelope is finite
  have hAm0 : ∀ e, MeasurableSet (capDom (0 : Fin (m + n) → ℝ) e) := fun e => by
    rw [capDom_zero]; exact measurableSet_Ioi
  have hA00 : ∀ e, capDom (0 : Fin (m + n) → ℝ) e ⊆ Ioi 0 := fun e => by rw [capDom_zero]
  have hu0 : ∀ e, 2 * N1 α₀ (wickEdge hH hε _ hAm0 hA00 e) (damp 1 g) ≤ ENNReal.ofReal Zr ∧
      N2 α₀ (wickEdge hH hε _ hAm0 hA00 e) (damp 1 g) ≤ ENNReal.ofReal Zr := fun e =>
    unmarked_le hgd hH (edgeWidth_pos hε e) _ (by rw [wickEdge_A, capDom_zero]) (wickEdge_μ _ _ _ _ _ _)
  have hfull : wickF (waveGreen d) Γ α₀ (capDom (0 : Fin (m + n) → ℝ)) ε m D T1 T2 ≤
      ENNReal.ofReal Ex * ((ENNReal.ofReal Zr + ENNReal.ofReal Zr ^ 2) *
        ENNReal.ofReal Zr ^ (2 * Lc)) := by
    refine (horizon_le_pairingIntegral hgd hH hBr hD hε _ hAm0 hA00 T1 T2).trans ?_
    gcongr
    refine (hPE _ _ hwf (kernelHyp_wick hgd _ _ fun e _ => ⟨?_, ?_⟩)).trans ?_
    · have := (hu0 e).1
      refine lt_of_le_of_lt (le_trans (le_mul_of_one_le_left zero_le (by norm_num)) this)
        ENNReal.ofReal_lt_top
    · exact lt_of_le_of_lt (hu0 e).2 ENNReal.ofReal_lt_top
    · refine iSup_le fun A => prodP_marked_le α₀ _ _ A hZ hN0 he1
        (fun e _ _ => (hu0 e).1) (fun e _ _ => (hu0 e).2) (hu0 _).1 ?_
      exact pow_le_pow_left₀ zero_le (hu0 _).2 2
  refine ⟨JointFixedOrder.wickF_le_zero _ _ _ _ ε m D T1 T2, ne_top_of_le_ne_top ?_ hfull, ?_⟩
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top
      (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.pow_ne_top ENNReal.ofReal_ne_top⟩)
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))
  -- the marked terms
  have hM : (0 : ℝ) ≤ η⁻¹ := (inv_pos.2 hη).le
  set t := DampedNormsHomog.N1tail α₀ η⁻¹ μ + DampedNormsHomog.N2tailSq α₀ η⁻¹ μ with ht
  have ht0 : 0 ≤ t := add_nonneg (N1tail_nonneg hH _) (DampedNormsHomog.N2tail_props hH _).2.2.2
  set τ := ENNReal.ofReal (2 * t) with hτ
  have hmark : ∀ i0 ∈ openers D, ∫⁻ r in horizon m T1 T2, pairTime α₀ (markA s(i0, D i0) η⁻¹) m D r
      ∂wickRho (waveGreen d) Γ ε m D ≤
        ENNReal.ofReal Ex * ((τ + τ) * ENNReal.ofReal Zr ^ (2 * Lc)) := by
    intro i0 hi0
    have he0 : s(i0, D i0) ∈ (m4Chain m n D).D := by
      rw [D_m4Chain_eq_image hD]; exact Finset.mem_image_of_mem _ hi0
    have hAm := measurableSet_markA s(i0, D i0) η⁻¹
    have hA0 := markA_subset s(i0, D i0) hM
    have hun : ∀ e, e ≠ s(i0, D i0) →
        2 * N1 α₀ (wickEdge hH hε _ hAm hA0 e) (damp 1 g) ≤ ENNReal.ofReal Zr ∧
        N2 α₀ (wickEdge hH hε _ hAm hA0 e) (damp 1 g) ≤ ENNReal.ofReal Zr := fun e he =>
      unmarked_le hgd hH (edgeWidth_pos hε e) _ (by rw [wickEdge_A]; simp [markA, he])
        (wickEdge_μ _ _ _ _ _ _)
    have hmk := marked_le hgd hH (edgeWidth_pos hε s(i0, D i0)) hM
      (wickEdge hH hε _ hAm hA0 s(i0, D i0)) (by rw [wickEdge_A]; simp [markA])
      (wickEdge_μ _ _ _ _ _ _)
    refine (horizon_le_pairingIntegral hgd hH hBr hD hε _ hAm hA0 T1 T2).trans ?_
    gcongr
    refine (hPE _ _ hwf (kernelHyp_wick hgd _ _ fun e _ => ?_)).trans ?_
    · by_cases he : e = s(i0, D i0)
      · subst he
        refine ⟨lt_of_le_of_lt (le_trans (le_mul_of_one_le_left zero_le (by norm_num)) hmk.1)
          ENNReal.ofReal_lt_top, ?_⟩
        refine lt_top_iff_ne_top.2 fun htop => ?_
        have := hmk.2
        rw [htop, ENNReal.top_pow two_ne_zero] at this
        exact absurd this (not_le.2 ENNReal.ofReal_lt_top)
      · exact ⟨lt_of_le_of_lt (le_trans (le_mul_of_one_le_left zero_le (by norm_num))
          (hun e he).1) ENNReal.ofReal_lt_top, lt_of_le_of_lt (hun e he).2 ENNReal.ofReal_lt_top⟩
    · exact iSup_le fun A => prodP_marked_le α₀ _ _ A hZ hN0 he0
        (fun e _ he => (hun e he).1) (fun e _ he => (hun e he).2) hmk.1 hmk.2
  -- assembly
  calc wickF (waveGreen d) Γ α₀ (capDom (0 : Fin (m + n) → ℝ)) ε m D T1 T2
      ≤ ∫⁻ r in horizon m T1 T2, (pairTime α₀ (capDom fun _ : Fin (m + n) => η) m D r +
          ∑ i0 ∈ openers D, pairTime α₀ (markA s(i0, D i0) η⁻¹) m D r)
          ∂wickRho (waveGreen d) Γ ε m D :=
        lintegral_mono fun r => pairTime_zero_le hη m D r
    _ = wickF (waveGreen d) Γ α₀ (capDom fun _ : Fin (m + n) => η) ε m D T1 T2 +
          ∑ i0 ∈ openers D, ∫⁻ r in horizon m T1 T2, pairTime α₀ (markA s(i0, D i0) η⁻¹) m D r
            ∂wickRho (waveGreen d) Γ ε m D := by
        rw [lintegral_add_left (JointFixedOrder.measurable_pairTime _ _ m D),
          lintegral_finsetSum _ fun i _ => JointFixedOrder.measurable_pairTime _ _ m D]
        rfl
    _ ≤ wickF (waveGreen d) Γ α₀ (capDom fun _ : Fin (m + n) => η) ε m D T1 T2 +
          ∑ _i0 ∈ openers D, ENNReal.ofReal Ex * ((τ + τ) * ENNReal.ofReal Zr ^ (2 * Lc)) := by
        gcongr with i0 hi0; exact hmark i0 hi0
    _ ≤ wickF (waveGreen d) Γ α₀ (capDom fun _ : Fin (m + n) => η) ε m D T1 T2 +
          ENNReal.ofReal (((m + n : ℕ) : ℝ) * Ex * Zr ^ (2 * Lc) * 4 * t) := by
        gcongr
        rw [Finset.sum_const, nsmul_eq_mul]
        have hc : ((openers D).card : ℝ≥0∞) ≤ ((m + n : ℕ) : ℝ≥0∞) := by
          exact_mod_cast (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)
        calc ((openers D).card : ℝ≥0∞) * (ENNReal.ofReal Ex * ((τ + τ) * ENNReal.ofReal Zr ^ (2 * Lc)))
            ≤ ((m + n : ℕ) : ℝ≥0∞) *
                (ENNReal.ofReal Ex * ((τ + τ) * ENNReal.ofReal Zr ^ (2 * Lc))) := by gcongr
          _ = _ := by
              rw [hτ, ← ENNReal.ofReal_add (by positivity) (by positivity),
                ← ENNReal.ofReal_pow hZr0, ← ENNReal.ofReal_mul (by positivity),
                ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_natCast,
                ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
              congr 1
              ring

end Assembly

section Abstract

variable {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)} (hH : HomogCovariance d alpha α₀ Γ μ)

/-- The horizon loss for any measure family: on `ℓ_1 < T_1, ℓ_2 < T_2`,
`∫ f dρ ≤ e^{T_1+T_2} ∫ e^{-Σ r} f dρ`. -/
theorem horizon_le_of_bridge {N : ℕ} {m : ℕ} {T1 T2 : ℝ}
    (hHm : MeasurableSet (horizon m (N := N) T1 T2)) {ρ : Measure (Fin N → ℝ)}
    (f : (Fin N → ℝ) → ℝ≥0∞) {X : ℝ≥0∞}
    (hbr : ∫⁻ r, ENNReal.ofReal (Real.exp (-(1 * ∑ i, r i))) * f r ∂ρ ≤ X) :
    ∫⁻ r in horizon m T1 T2, f r ∂ρ ≤ ENNReal.ofReal (Real.exp (T1 + T2)) * X := by
  calc ∫⁻ r in horizon m T1 T2, f r ∂ρ
      ≤ ∫⁻ r in horizon m T1 T2, ENNReal.ofReal (Real.exp (T1 + T2)) *
          (ENNReal.ofReal (Real.exp (-(1 * ∑ i, r i))) * f r) ∂ρ := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem hHm] with r hr
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        have h1 : 1 ≤ Real.exp (T1 + T2 + -(1 * ∑ i, r i)) := Real.one_le_exp (by
          linarith [JointFixedOrder.sum_lt_of_mem_horizon hr])
        calc f r = 1 * f r := (one_mul _).symm
          _ ≤ _ := by
              gcongr
              rw [← ENNReal.ofReal_one]
              exact ENNReal.ofReal_le_ofReal h1
    _ ≤ ∫⁻ r, ENNReal.ofReal (Real.exp (T1 + T2)) *
          (ENNReal.ofReal (Real.exp (-(1 * ∑ i, r i))) * f r) ∂ρ := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (Real.exp (T1 + T2)) *
          ∫⁻ r, ENNReal.ofReal (Real.exp (-(1 * ∑ i, r i))) * f r ∂ρ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by gcongr

/-- The envelope's kernel hypotheses for a measurable damped kernel with finite edge norms. -/
theorem kernelHyp_of {g : Kernel d} (hmeas : Measurable (Function.uncurry (damp 1 g)))
    (hN0 : N0 (damp 1 g) ≤ 1) {α : Type*} [DecidableEq α] (dg : TwoChain α)
    (ed : Sym2 α → EdgeData d)
    (h : ∀ e ∈ dg.D, N1 α₀ (ed e) (damp 1 g) < ⊤ ∧ N2 α₀ (ed e) (damp 1 g) < ⊤) :
    KernelHyp α₀ dg ed (fun _ => damp 1 g) :=
  ⟨fun _ _ => hmeas, fun _ _ => lt_of_le_of_lt hN0 ENNReal.one_lt_top,
    fun _ _ e he => (h e he).1, fun _ _ e he => (h e he).2⟩

include hH in
/-- **The tail estimate of Step 2 for any Green family** with a bridge to M7 and uniform norm
bounds (the abstract form of `joint_temporal_tail_of_density`): the full-kernel bound and
`F_{ε,0} ≤ F_{ε,η} + (m+n) e^{T_1+T_2} K^{2(m+n)} 4 t` when every unmarked edge has
`2N_1, N_2 ≤ K` and the marked edge `2N_1, N_2² ≤ 2t`. -/
theorem tail_abstract {G : ℝ → Measure (Rd d)} {g : Kernel d}
    (hmeas : Measurable (Function.uncurry (damp 1 g))) (hN0 : N0 (damp 1 g) ≤ 1) {Zr t : ℝ}
    (hZr1 : 1 ≤ Zr) (ht0 : 0 ≤ t) {m n k : ℕ} (hmn : m + n = 2 * k) (hk : 1 ≤ k)
    {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n) (T1 T2 : ℝ) {ε : Fin (m + n) → ℝ}
    (hε : ∀ i, 0 < ε i) {η : ℝ} (hη : 0 < η)
    (hbr : ∀ (A : Sym2 (Fin (m + n)) → Set ℝ) (hAm : ∀ e, MeasurableSet (A e))
      (hA0 : ∀ e, A e ⊆ Ioi 0),
      ∫⁻ r, ENNReal.ofReal (Real.exp (-(1 * ∑ i, r i))) * pairTime α₀ A m D r
          ∂wickRho G Γ ε m D ≤
        pairingIntegral α₀ (m4Chain m n D) (wickEdge hH hε A hAm hA0) (fun _ => damp 1 g))
    (hun : ∀ (E : EdgeData d) (b : ℝ), 0 < b → E.A = Ioi 0 → E.μ = smoothSpec μ b →
      2 * N1 α₀ E (damp 1 g) ≤ ENNReal.ofReal Zr ∧ N2 α₀ E (damp 1 g) ≤ ENNReal.ofReal Zr)
    (hmk : ∀ (E : EdgeData d) (b : ℝ), 0 < b → E.A = Ioi η⁻¹ → E.μ = smoothSpec μ b →
      2 * N1 α₀ E (damp 1 g) ≤ ENNReal.ofReal (2 * t) ∧
        N2 α₀ E (damp 1 g) ^ 2 ≤ ENNReal.ofReal (2 * t)) :
    wickF G Γ α₀ (capDom (0 : Fin (m + n) → ℝ)) ε m D T1 T2 ≤
        ENNReal.ofReal (Real.exp (T1 + T2)) * ((ENNReal.ofReal Zr + ENNReal.ofReal Zr ^ 2) *
          ENNReal.ofReal Zr ^ (2 * (m4Chain m n D).labels.card)) ∧
      wickF G Γ α₀ (capDom (0 : Fin (m + n) → ℝ)) ε m D T1 T2 ≤
        wickF G Γ α₀ (capDom fun _ : Fin (m + n) => η) ε m D T1 T2 +
          ENNReal.ofReal (((m + n : ℕ) : ℝ) * Real.exp (T1 + T2) *
            Zr ^ (2 * (m4Chain m n D).labels.card) * 4 * t) := by
  set Lc := (m4Chain m n D).labels.card with hLc
  set Ex := Real.exp (T1 + T2) with hEx
  have hZr0 : 0 ≤ Zr := zero_le_one.trans hZr1
  have hZ : (1 : ℝ≥0∞) ≤ ENNReal.ofReal Zr := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hZr1
  have hPE := PairingEnvelope.pairing_product_envelope d (Fin (m + n)) α₀ hH.alpha0_pos
    hH.alpha0_lt_one (m4Chain m n D)
  have hwf := m4Chain_wf hD
  have hcard : (openers D).card = k := DiagramModel.card_openers hD hmn
  obtain ⟨i1, hi1⟩ : (openers D).Nonempty := by
    rw [← Finset.card_pos, hcard]; omega
  have he1 : s(i1, D i1) ∈ (m4Chain m n D).D := by
    rw [D_m4Chain_eq_image hD]; exact Finset.mem_image_of_mem _ hi1
  have hHm := JointFixedOrder.measurableSet_horizon m (N := m + n) T1 T2
  -- the full kernels: the envelope is finite
  have hAm0 : ∀ e, MeasurableSet (capDom (0 : Fin (m + n) → ℝ) e) := fun e => by
    rw [capDom_zero]; exact measurableSet_Ioi
  have hA00 : ∀ e, capDom (0 : Fin (m + n) → ℝ) e ⊆ Ioi 0 := fun e => by rw [capDom_zero]
  have hu0 : ∀ e, 2 * N1 α₀ (wickEdge hH hε _ hAm0 hA00 e) (damp 1 g) ≤ ENNReal.ofReal Zr ∧
      N2 α₀ (wickEdge hH hε _ hAm0 hA00 e) (damp 1 g) ≤ ENNReal.ofReal Zr := fun e =>
    hun _ _ (edgeWidth_pos hε e) (by rw [wickEdge_A, capDom_zero]) (wickEdge_μ _ _ _ _ _ _)
  have hfull : wickF (G) Γ α₀ (capDom (0 : Fin (m + n) → ℝ)) ε m D T1 T2 ≤
      ENNReal.ofReal Ex * ((ENNReal.ofReal Zr + ENNReal.ofReal Zr ^ 2) *
        ENNReal.ofReal Zr ^ (2 * Lc)) := by
    refine (horizon_le_of_bridge hHm _ (hbr _ hAm0 hA00)).trans ?_
    gcongr
    refine (hPE _ _ hwf (kernelHyp_of hmeas hN0 _ _ fun e _ => ⟨?_, ?_⟩)).trans ?_
    · have := (hu0 e).1
      refine lt_of_le_of_lt (le_trans (le_mul_of_one_le_left zero_le (by norm_num)) this)
        ENNReal.ofReal_lt_top
    · exact lt_of_le_of_lt (hu0 e).2 ENNReal.ofReal_lt_top
    · refine iSup_le fun A => prodP_marked_le α₀ _ _ A hZ hN0 he1
        (fun e _ _ => (hu0 e).1) (fun e _ _ => (hu0 e).2) (hu0 _).1 ?_
      exact pow_le_pow_left₀ zero_le (hu0 _).2 2
  refine ⟨hfull, ?_⟩
  -- the marked terms
  have hM : (0 : ℝ) ≤ η⁻¹ := (inv_pos.2 hη).le
  set τ := ENNReal.ofReal (2 * t) with hτ
  have hmark : ∀ i0 ∈ openers D, ∫⁻ r in horizon m T1 T2, pairTime α₀ (markA s(i0, D i0) η⁻¹) m D r
      ∂wickRho (G) Γ ε m D ≤
        ENNReal.ofReal Ex * ((τ + τ) * ENNReal.ofReal Zr ^ (2 * Lc)) := by
    intro i0 hi0
    have he0 : s(i0, D i0) ∈ (m4Chain m n D).D := by
      rw [D_m4Chain_eq_image hD]; exact Finset.mem_image_of_mem _ hi0
    have hAm := measurableSet_markA s(i0, D i0) η⁻¹
    have hA0 := markA_subset s(i0, D i0) hM
    have hun : ∀ e, e ≠ s(i0, D i0) →
        2 * N1 α₀ (wickEdge hH hε _ hAm hA0 e) (damp 1 g) ≤ ENNReal.ofReal Zr ∧
        N2 α₀ (wickEdge hH hε _ hAm hA0 e) (damp 1 g) ≤ ENNReal.ofReal Zr := fun e he =>
      hun _ _ (edgeWidth_pos hε e) (by rw [wickEdge_A]; simp [markA, he])
        (wickEdge_μ _ _ _ _ _ _)
    have hmk := hmk (wickEdge hH hε _ hAm hA0 s(i0, D i0)) _ (edgeWidth_pos hε s(i0, D i0))
      (by rw [wickEdge_A]; simp [markA]) (wickEdge_μ _ _ _ _ _ _)
    refine (horizon_le_of_bridge hHm _ (hbr _ hAm hA0)).trans ?_
    gcongr
    refine (hPE _ _ hwf (kernelHyp_of hmeas hN0 _ _ fun e _ => ?_)).trans ?_
    · by_cases he : e = s(i0, D i0)
      · subst he
        refine ⟨lt_of_le_of_lt (le_trans (le_mul_of_one_le_left zero_le (by norm_num)) hmk.1)
          ENNReal.ofReal_lt_top, ?_⟩
        refine lt_top_iff_ne_top.2 fun htop => ?_
        have := hmk.2
        rw [htop, ENNReal.top_pow two_ne_zero] at this
        exact absurd this (not_le.2 ENNReal.ofReal_lt_top)
      · exact ⟨lt_of_le_of_lt (le_trans (le_mul_of_one_le_left zero_le (by norm_num))
          (hun e he).1) ENNReal.ofReal_lt_top, lt_of_le_of_lt (hun e he).2 ENNReal.ofReal_lt_top⟩
    · exact iSup_le fun A => prodP_marked_le α₀ _ _ A hZ hN0 he0
        (fun e _ he => (hun e he).1) (fun e _ he => (hun e he).2) hmk.1 hmk.2
  -- assembly
  calc wickF (G) Γ α₀ (capDom (0 : Fin (m + n) → ℝ)) ε m D T1 T2
      ≤ ∫⁻ r in horizon m T1 T2, (pairTime α₀ (capDom fun _ : Fin (m + n) => η) m D r +
          ∑ i0 ∈ openers D, pairTime α₀ (markA s(i0, D i0) η⁻¹) m D r)
          ∂wickRho (G) Γ ε m D :=
        lintegral_mono fun r => pairTime_zero_le hη m D r
    _ = wickF (G) Γ α₀ (capDom fun _ : Fin (m + n) => η) ε m D T1 T2 +
          ∑ i0 ∈ openers D, ∫⁻ r in horizon m T1 T2, pairTime α₀ (markA s(i0, D i0) η⁻¹) m D r
            ∂wickRho (G) Γ ε m D := by
        rw [lintegral_add_left (JointFixedOrder.measurable_pairTime _ _ m D),
          lintegral_finsetSum _ fun i _ => JointFixedOrder.measurable_pairTime _ _ m D]
        rfl
    _ ≤ wickF (G) Γ α₀ (capDom fun _ : Fin (m + n) => η) ε m D T1 T2 +
          ∑ _i0 ∈ openers D, ENNReal.ofReal Ex * ((τ + τ) * ENNReal.ofReal Zr ^ (2 * Lc)) := by
        gcongr with i0 hi0; exact hmark i0 hi0
    _ ≤ wickF (G) Γ α₀ (capDom fun _ : Fin (m + n) => η) ε m D T1 T2 +
          ENNReal.ofReal (((m + n : ℕ) : ℝ) * Ex * Zr ^ (2 * Lc) * 4 * t) := by
        gcongr
        rw [Finset.sum_const, nsmul_eq_mul]
        have hc : ((openers D).card : ℝ≥0∞) ≤ ((m + n : ℕ) : ℝ≥0∞) := by
          exact_mod_cast (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)
        calc ((openers D).card : ℝ≥0∞) * (ENNReal.ofReal Ex * ((τ + τ) * ENNReal.ofReal Zr ^ (2 * Lc)))
            ≤ ((m + n : ℕ) : ℝ≥0∞) *
                (ENNReal.ofReal Ex * ((τ + τ) * ENNReal.ofReal Zr ^ (2 * Lc))) := by gcongr
          _ = _ := by
              rw [hτ, ← ENNReal.ofReal_add (by positivity) (by positivity),
                ← ENNReal.ofReal_pow hZr0, ← ENNReal.ofReal_mul (by positivity),
                ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_natCast,
                ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
              congr 1
              ring


end Abstract

/-- **`E:joint-temporal-tail` in `d = 1, 2`** (`JointTemporalTailTarget d`; TeX lines 1892-1921 at
revision edf7085f (book 1.1.3)), with the per-edge bridge `M8M7BridgeTarget d` (item C) as a
hypothesis; the Green densities are `green1`, `green2` (no Green smoothing is needed). -/
theorem joint_temporal_tail_of_le_two {d : ℕ} (hd : d = 1 ∨ d = 2) (hBr : M8M7BridgeTarget d) :
    JointTemporalTailTarget d := by
  rcases hd with rfl | rfl
  · intro alpha α₀ Γ μ hH m n k hmn hk D hD T1 T2 _ _
    exact joint_temporal_tail_of_density PairingDampedNorms.greenDensity_one hH hBr hmn hk hD
  · intro alpha α₀ Γ μ hH m n k hmn hk D hD T1 T2 _ _
    exact joint_temporal_tail_of_density PairingDampedNorms.greenDensity_two hH hBr hmn hk hD

/-! ### `d = 3`: Green-width removal at fixed noise widths (decision 8) -/

section D3

variable {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)} (hH : HomogCovariance d alpha α₀ Γ μ)
include hH

/-- `J_{ε,D}` of a Green family with a finite measurable density is measurable. -/
theorem measurable_wickJ_density {G : ℝ → Measure (Rd d)} {g : Kernel d}
    (hg : Measurable (Function.uncurry g)) (hfin : ∀ s x, g s x ≠ ∞)
    (hG : ∀ s, G s = volume.withDensity (g s)) {N : ℕ} {ε : Fin N → ℝ} (hε : ∀ i, 0 < ε i)
    (m : ℕ) (D : Fin N → Fin N) : Measurable (wickJ G Γ ε m D) := by
  have hgs : ∀ s, Measurable (g s) := fun s => hg.comp (measurable_const.prodMk measurable_id)
  have hcov := JointFixedOrder.measurable_covW_pos hH hε m D
  have e : wickJ G Γ ε m D = fun r =>
      ∫⁻ w, (∏ i, g (r i) (w i)) * covW Γ ε D (pos m w) ∂(Measure.pi fun _ : Fin N => volume) := by
    funext r
    unfold wickJ
    simp_rw [hG]
    rw [pi_withDensity volume (fun i => g (r i)) (fun i => hgs (r i)) (fun i x => hfin (r i) x)]
    have hm : Measurable fun w : Fin N → Rd d => ∏ i, g (r i) (w i) :=
      Finset.measurable_prod _ fun i _ => (hgs (r i)).comp (measurable_pi_apply i)
    rw [lintegral_withDensity_eq_lintegral_mul _ hm hcov]
    rfl
  rw [e]
  have hf : Measurable fun p : (Fin N → ℝ) × (Fin N → Rd d) =>
      (∏ i, g (p.1 i) (p.2 i)) * covW Γ ε D (pos m p.2) := by
    refine (Finset.measurable_prod _ fun i _ => ?_).mul (hcov.comp measurable_snd)
    have h2 : Measurable fun p : (Fin N → ℝ) × (Fin N → Rd d) => (p.1 i, p.2 i) :=
      ((measurable_pi_apply i).comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp measurable_snd)
    exact hg.comp h2
  exact hf.lintegral_prod_right'

omit hH in
/-- `F_{ε,A,D}` as a Lebesgue integral on the orthant, for an a.e.-measurable density. -/
theorem wickF_eq_lintegral' {G : ℝ → Measure (Rd d)} {N : ℕ} {ε : Fin N → ℝ} {m : ℕ}
    {D : Fin N → Fin N} (hJ : AEMeasurable (wickJ G Γ ε m D) (volume.restrict (posOrthant N)))
    (a : ℝ) (A : Sym2 (Fin N) → Set ℝ) (T1 T2 : ℝ) :
    wickF G Γ a A ε m D T1 T2 =
      ∫⁻ r in posOrthant N ∩ horizon m T1 T2, pairTime a A m D r * wickJ G Γ ε m D r := by
  have hHm := JointFixedOrder.measurableSet_horizon m (N := N) T1 T2
  unfold wickF wickRho
  rw [restrict_withDensity hHm, lintegral_withDensity_eq_lintegral_mul₀
    (hJ.mono_measure Measure.restrict_le_self)
    (JointFixedOrder.measurable_pairTime a A m D).aemeasurable, Measure.restrict_restrict hHm,
    inter_comm]
  refine lintegral_congr fun r => ?_
  simp only [Pi.mul_apply]
  rw [mul_comm]

omit hH in
/-- The spectral form is bounded by `(∫ ∏_e e^{-(ε_j+ε_h)|ξ_e|²/2} dμ^{⊗k}) ∏_l |r_l|`, uniformly
in the Green width `η ≥ 0`. -/
theorem spatialSpecW_le (hH : HomogCovariance d alpha α₀ Γ μ) {N : ℕ} {ε : Fin N → ℝ}
    (hε : ∀ i, 0 < ε i) (m : ℕ) (D : Fin N → Fin N) (r : Fin N → ℝ) {η : ℝ} (hη : 0 ≤ η) :
    spatialSpecW μ η ε m D r ≤
      (∫ ξ, ∏ e : openers D, gaussFactor (ε (e : Fin N) + ε (D e)) (ξ e)
        ∂Measure.pi fun _ : openers D => μ) * ∏ l, |r l| := by
  have := hH.μ_radon
  have hint : Integrable (fun ξ : openers D → Rd d =>
      ∏ e : openers D, gaussFactor (ε (e : Fin N) + ε (D e)) (ξ e))
      (Measure.pi fun _ : openers D => μ) :=
    Integrable.fintype_prod (f := fun e : openers D => gaussFactor (ε (e : Fin N) + ε (D e)))
      fun e => LowAlphaConvolution.integrable_gaussFactor hH.μ_tempered (add_pos (hε _) (hε _))
  rw [← integral_mul_const]
  refine (le_abs_self _).trans ?_
  rw [← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (hint.mul_const _) (ae_of_all _ fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_mul, Finset.abs_prod, Finset.abs_prod]
  refine mul_le_mul ?_ ?_ (Finset.prod_nonneg fun _ _ => abs_nonneg _)
    (Finset.prod_nonneg fun e _ => (Real.exp_pos _).le)
  · exact le_of_eq (Finset.prod_congr rfl fun e _ => abs_of_pos (Real.exp_pos _))
  · exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun l _ =>
      PairingSmoothedNorms.abs_wh_le hη (r l) _

end D3

section Three

variable {alpha α₀ : ℝ} {Γ μ : Measure (Rd 3)} (hH : HomogCovariance 3 alpha α₀ Γ μ)
  (hB : SpectralSpatialWTarget 3)
include hH hB

/-- **Fatou in the Green width** (`d = 3`, decision 8): `F_{ε,A,D} ≤ liminf_{η'↓0} F^{(η')}_{ε,A,D}`
for the Green-smoothed kernels `p_{η'} * G_s`, any Laplace domains. -/
theorem wickF_three_le_liminf {m n k : ℕ} (hmn : m + n = 2 * k) (hk : 1 ≤ k)
    {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n) {ε : Fin (m + n) → ℝ}
    (hε : ∀ i, 0 < ε i) (A : Sym2 (Fin (m + n)) → Set ℝ) (T1 T2 : ℝ) :
    wickF (waveGreen 3) Γ α₀ A ε m D T1 T2 ≤
      liminf (fun η' => wickF (greenS 3 η') Γ α₀ A ε m D T1 T2) (𝓝[>] 0) := by
  have hS := (JointFixedOrder.measurableSet_posOrthant (m + n)).inter
    (JointFixedOrder.measurableSet_horizon m (N := m + n) T1 T2)
  have hmeasJ : ∀ η' : ℝ, 0 < η' → Measurable (wickJ (greenS 3 η') Γ ε m D) := fun η' hη' =>
    measurable_wickJ_density hH (GreenSmoothed3.measurable_green3s η')
      (GreenSmoothed3.green3s_ne_top hη') (fun s => GreenSmoothed3.smoothedGreen_three_eq hη' s) hε m D
  set f : ℝ → (Fin (m + n) → ℝ) → ℝ≥0∞ := fun η' r =>
    if 0 < η' then pairTime α₀ A m D r * wickJ (greenS 3 η') Γ ε m D r else 0 with hf
  rw [JointFixedOrder.wickF_eq_lintegral hH hε]
  calc ∫⁻ r in posOrthant (m + n) ∩ horizon m T1 T2,
        pairTime α₀ A m D r * wickJ (waveGreen 3) Γ ε m D r
      ≤ ∫⁻ r in posOrthant (m + n) ∩ horizon m T1 T2, liminf (fun η' => f η' r) (𝓝[>] 0) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem hS] with r hr
        have hr0 : ∀ i, 0 ≤ r i := fun i => (hr.1 i (mem_univ i)).le
        have hJ := EnvelopeD3Wave.tendsto_wickJ_greenS hB hH hmn hk hD hε hr0
        by_cases hb0 : wickJ (waveGreen 3) Γ ε m D r = 0
        · rw [hb0, mul_zero]; exact zero_le
        · have ht : Tendsto (fun η' => f η' r) (𝓝[>] 0)
              (𝓝 (pairTime α₀ A m D r * wickJ (waveGreen 3) Γ ε m D r)) := by
            refine (ENNReal.Tendsto.const_mul hJ (Or.inl hb0)).congr' ?_
            filter_upwards [self_mem_nhdsWithin] with η' hη'
            simp only [hf, show (0 : ℝ) < η' from hη', ↓reduceIte]
          exact ht.liminf_eq.ge
    _ ≤ liminf (fun η' => ∫⁻ r in posOrthant (m + n) ∩ horizon m T1 T2, f η' r) (𝓝[>] 0) := by
        refine lintegral_liminf_le' fun η' => ?_
        by_cases hη' : 0 < η'
        · simp only [hf, hη', ↓reduceIte]
          exact ((JointFixedOrder.measurable_pairTime _ _ m D).mul (hmeasJ η' hη')).aemeasurable
        · simp only [hf, hη', ↓reduceIte]
          exact aemeasurable_const
    _ = liminf (fun η' => wickF (greenS 3 η') Γ α₀ A ε m D T1 T2) (𝓝[>] 0) := by
        refine Filter.liminf_congr ?_
        filter_upwards [self_mem_nhdsWithin] with η' hη'
        have hη'0 : (0 : ℝ) < η' := hη'
        simp only [hf, hη'0, ↓reduceIte]
        exact (wickF_eq_lintegral' (hmeasJ η' hη'0).aemeasurable α₀ A T1 T2).symm

/-- **Dominated convergence in the Green width** (`d = 3`, decision 8): at a common temporal
width `η > 0` (bounded multiplier) and fixed positive noise widths,
`F^{(η')}_{ε,η,D} → F_{ε,η,D}` as `η' ↓ 0` (the majorant is a constant on the bounded region
`(0,∞)^N ∩ {ℓ_1 < T_1, ℓ_2 < T_2}`; the TeX's route is weak convergence of Green measures,
1923-1926). -/
theorem tendsto_wickF_three {m n k : ℕ} (hmn : m + n = 2 * k) (hk : 1 ≤ k)
    {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n) {ε : Fin (m + n) → ℝ}
    (hε : ∀ i, 0 < ε i) {η : ℝ} (hη : 0 < η) (T1 T2 : ℝ) :
    Tendsto (fun η' => wickF (greenS 3 η') Γ α₀ (capDom fun _ : Fin (m + n) => η) ε m D T1 T2)
      (𝓝[>] 0) (𝓝 (wickF (waveGreen 3) Γ α₀ (capDom fun _ : Fin (m + n) => η) ε m D T1 T2)) := by
  have hS := (JointFixedOrder.measurableSet_posOrthant (m + n)).inter
    (JointFixedOrder.measurableSet_horizon m (N := m + n) T1 T2)
  have hmeasJ : ∀ η' : ℝ, 0 < η' → Measurable (wickJ (greenS 3 η') Γ ε m D) := fun η' hη' =>
    measurable_wickJ_density hH (GreenSmoothed3.measurable_green3s η')
      (GreenSmoothed3.green3s_ne_top hη') (fun s => GreenSmoothed3.smoothedGreen_three_eq hη' s) hε m D
  set Pb := ∏ _i ∈ openers D, kerA α₀ (capSet η) 0 with hPb
  have hPb : Pb ≠ ⊤ := ENNReal.prod_ne_top fun _ _ =>
    JointFixedOrder.kerA_capSet_zero_ne_top hH.alpha0_pos hη
  set Ksp := ∫ ξ, ∏ e : openers D, gaussFactor (ε (e : Fin (m + n)) + ε (D e)) (ξ e)
    ∂Measure.pi fun _ : openers D => μ with hKsp
  set T := T1 + T2
  set bnd : ℝ≥0∞ := Pb * ENNReal.ofReal (Ksp * T ^ (m + n)) with hbnd
  -- the region is bounded
  have hbox : posOrthant (m + n) ∩ horizon m T1 T2 ⊆ Set.pi univ fun _ => Icc (0 : ℝ) T := by
    intro r hr i _
    have h0 : ∀ j, 0 ≤ r j := fun j => (hr.1 j (mem_univ j)).le
    refine ⟨h0 i, ?_⟩
    have := JointFixedOrder.sum_lt_of_mem_horizon hr.2
    exact (Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)).trans this.le
  have hvol : volume (posOrthant (m + n) ∩ horizon m T1 T2) ≠ ⊤ :=
    ne_top_of_le_ne_top ((isCompact_univ_pi fun _ => isCompact_Icc).measure_lt_top.ne)
      (measure_mono hbox)
  have hJb : ∀ η' : ℝ, 0 ≤ η' → ∀ r ∈ posOrthant (m + n) ∩ horizon m T1 T2,
      wickJ (greenS 3 η') Γ ε m D r ≤ ENNReal.ofReal (Ksp * T ^ (m + n)) := by
    intro η' hη' r hr
    have h0 : ∀ j, 0 ≤ r j := fun j => (hr.1 j (mem_univ j)).le
    rw [hB hH η' hη' m n k hmn hk D hD ε hε r h0]
    refine ENNReal.ofReal_le_ofReal ((spatialSpecW_le hH hε m D r hη').trans ?_)
    have hK0 : 0 ≤ Ksp := integral_nonneg fun ξ => Finset.prod_nonneg fun e _ => (Real.exp_pos _).le
    refine mul_le_mul_of_nonneg_left ?_ hK0
    calc ∏ l, |r l| ≤ ∏ _l : Fin (m + n), T :=
          Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun l _ => by
            rw [abs_of_nonneg (h0 l)]; exact (hbox hr l (mem_univ l)).2
      _ = T ^ (m + n) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hlim := tendsto_lintegral_filter_of_dominated_convergence'
    (l := 𝓝[>] (0 : ℝ)) (μ := volume.restrict (posOrthant (m + n) ∩ horizon m T1 T2))
    (F := fun η' r => pairTime α₀ (capDom fun _ : Fin (m + n) => η) m D r *
      wickJ (greenS 3 η') Γ ε m D r)
    (f := fun r => pairTime α₀ (capDom fun _ : Fin (m + n) => η) m D r *
      wickJ (waveGreen 3) Γ ε m D r) (fun _ => bnd)
    (by
      filter_upwards [self_mem_nhdsWithin] with η' hη'
      exact ((JointFixedOrder.measurable_pairTime _ _ m D).mul (hmeasJ η' hη')).aemeasurable)
    (by
      filter_upwards [self_mem_nhdsWithin] with η' hη'
      filter_upwards [ae_restrict_mem hS] with r hr
      exact mul_le_mul' (JointFixedOrder.pairTime_const_le m D r)
        (hJb η' (le_of_lt hη') r hr))
    (by
      rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter]
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hPb ENNReal.ofReal_ne_top) hvol)
    (by
      filter_upwards [ae_restrict_mem hS] with r hr
      have hr0 : ∀ i, 0 ≤ r i := fun i => (hr.1 i (mem_univ i)).le
      exact ENNReal.Tendsto.const_mul (EnvelopeD3Wave.tendsto_wickJ_greenS hB hH hmn hk hD hε hr0)
        (Or.inr (ne_top_of_le_ne_top hPb (JointFixedOrder.pairTime_const_le m D r))))
  rw [JointFixedOrder.wickF_eq_lintegral hH hε]
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with η' hη'
  exact (wickF_eq_lintegral' (hmeasJ η' hη').aemeasurable α₀ _ T1 T2).symm

end Three

/-! ### `E:joint-temporal-tail` in `d = 1, 2, 3` -/

section SmoothBounds

variable {G : ℝ → Measure (Rd d)} {η : ℝ} {g : Kernel d}
  (hgd : PairingSmoothedNorms.SmoothDensity d G η g)
  {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)} (hH : HomogCovariance d alpha α₀ Γ μ)
include hgd hH

/-- The unmarked edges for a smoothed Green density (uniformly in the Green width). -/
theorem unmarked_le_smooth {b : ℝ} (hb : 0 < b) (E : EdgeData d) (hA : E.A = Ioi 0)
    (hμ : E.μ = smoothSpec μ b) :
    2 * N1 α₀ E (damp 1 g) ≤ ENNReal.ofReal (HomogeneousEnvelope.Khom α₀ μ) ∧
      N2 α₀ E (damp 1 g) ≤ ENNReal.ofReal (HomogeneousEnvelope.Khom α₀ μ) := by
  have e1 : N1 α₀ E (damp 1 g) = N1 α₀ (smoothEdge hH hb) (damp 1 g) := by
    unfold N1; rw [hA, hμ]; rfl
  have e2 : N2 α₀ E (damp 1 g) = N2 α₀ (smoothEdge hH hb) (damp 1 g) := by
    unfold N2; rw [hA, hμ]; rfl
  have hK1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (HomogeneousEnvelope.Khom α₀ μ) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (HomogeneousEnvelope.one_le_Khom α₀ μ)
  constructor
  · rw [e1]
    calc 2 * N1 α₀ (smoothEdge hH hb) (damp 1 g)
        ≤ 2 * ENNReal.ofReal (DampedNorms.N1 α₀ 1 μ) := by
          gcongr; exact PairingSmoothedNorms.N1_damp_le hgd hH hb one_pos
      _ = ENNReal.ofReal (2 * DampedNorms.N1 α₀ 1 μ) := by
          rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]
      _ ≤ _ := ENNReal.ofReal_le_ofReal ((le_max_left _ _).trans (le_max_left _ _))
  · rw [e2]
    refine le_of_sq_le hK1 ((PairingSmoothedNorms.N2_damp_sq_le hgd hH hb one_pos).trans ?_)
    exact ENNReal.ofReal_le_ofReal ((le_max_right _ _).trans (le_max_left _ _))

/-- The marked edge for a smoothed Green density (uniformly in the Green width). -/
theorem marked_le_smooth {b : ℝ} (hb : 0 < b) {M : ℝ} (hM : 0 ≤ M) (E : EdgeData d)
    (hA : E.A = Ioi M) (hμ : E.μ = smoothSpec μ b) :
    2 * N1 α₀ E (damp 1 g) ≤ ENNReal.ofReal (2 * (DampedNormsHomog.N1tail α₀ M μ +
        DampedNormsHomog.N2tailSq α₀ M μ)) ∧
      N2 α₀ E (damp 1 g) ^ 2 ≤ ENNReal.ofReal (2 * (DampedNormsHomog.N1tail α₀ M μ +
        DampedNormsHomog.N2tailSq α₀ M μ)) := by
  have h1 := N1tail_nonneg hH M
  have h2 := (DampedNormsHomog.N2tail_props hH M).2.2.2
  constructor
  · calc 2 * N1 α₀ E (damp 1 g) ≤ 2 * ENNReal.ofReal (DampedNormsHomog.N1tail α₀ M μ) := by
          gcongr; exact N1_damp_tail_le_smooth hgd hH hb hM E hA hμ
      _ = ENNReal.ofReal (2 * DampedNormsHomog.N1tail α₀ M μ) := by
          rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)
  · exact (N2_damp_tail_sq_le_smooth hgd hH hb hM E hA hμ).trans
      (ENNReal.ofReal_le_ofReal (by linarith))

end SmoothBounds

/-- **`E:joint-temporal-tail` in `d = 3`** (TeX lines 1892-1927 at revision edf7085f (book
1.1.3)), with the per-edge bridge `M8M7BridgeTarget 3` (item C) and the spectral identity
`SpectralSpatialWTarget 3` (item B) as hypotheses.  At each Green width `η' > 0` the estimate holds
for the smoothed kernels `p_{η'} * G_s` with constants independent of `η'` (`tail_abstract` with
the smoothed norm bounds); the Green smoothing is then removed at fixed noise widths, as in the
TeX (1923-1926), but by a different route (decision 8, disclosed): Fatou in the Green width for
`F_{ε,0,D}` (`wickF_three_le_liminf`) and dominated convergence for the capped `F_{ε,η,D}`
(`tendsto_wickF_three`), both through the pointwise spectral limit
`EnvelopeD3Wave.tendsto_wickJ_greenS` instead of the weak convergence of Green measures. -/
theorem joint_temporal_tail_three (hBr : M8M7BridgeTarget 3) (hB : SpectralSpatialWTarget 3) :
    JointTemporalTailTarget 3 := by
  intro alpha α₀ Γ μ hH m n k hmn hk D hD T1 T2 _ _
  set Zr := HomogeneousEnvelope.Khom α₀ μ with hZr
  set Lc := (m4Chain m n D).labels.card with hLc
  refine ⟨((m + n : ℕ) : ℝ) * Real.exp (T1 + T2) * Zr ^ (2 * Lc) * 4, fun ε hε η hη => ?_⟩
  have hM : (0 : ℝ) ≤ η⁻¹ := (inv_pos.2 hη).le
  set t := DampedNormsHomog.N1tail α₀ η⁻¹ μ + DampedNormsHomog.N2tailSq α₀ η⁻¹ μ with ht
  have ht0 : 0 ≤ t := add_nonneg (N1tail_nonneg hH _) (DampedNormsHomog.N2tail_props hH _).2.2.2
  have key := fun (η' : ℝ) (hη' : 0 < η') =>
    tail_abstract hH (G := greenS 3 η') (g := GreenSmoothed3.green3s η')
      ((EnvelopeD3.smoothDensity_three hη').measurable_damp 1)
      (by rw [PairingSmoothedNorms.N0_damp (EnvelopeD3.smoothDensity_three hη') one_pos]; simp)
      (HomogeneousEnvelope.one_le_Khom α₀ μ) ht0 hmn hk hD T1 T2 hε hη
      (fun A hAm hA0 => hBr hH (greenS 3 η') (GreenSmoothed3.green3s η')
        (GreenSmoothed3.measurable_green3s η') (GreenSmoothed3.green3s_ne_top hη')
        (fun s => GreenSmoothed3.smoothedGreen_three_eq hη' s) m n D hD ε hε A hAm hA0 1
        zero_le_one)
      (fun E b hb hA hμ => unmarked_le_smooth (EnvelopeD3.smoothDensity_three hη') hH hb E hA hμ)
      (fun E b hb hA hμ => marked_le_smooth (EnvelopeD3.smoothDensity_three hη') hH hb hM E hA hμ)
  have hfat0 := wickF_three_le_liminf hH hB hmn hk hD hε (capDom (0 : Fin (m + n) → ℝ)) T1 T2
  have hlimη := tendsto_wickF_three hH hB hmn hk hD hε hη T1 T2
  refine ⟨JointFixedOrder.wickF_le_zero _ _ _ _ ε m D T1 T2, ?_, ?_⟩
  · refine ne_top_of_le_ne_top (b := ENNReal.ofReal (Real.exp (T1 + T2)) *
      ((ENNReal.ofReal Zr + ENNReal.ofReal Zr ^ 2) * ENNReal.ofReal Zr ^ (2 * Lc))) ?_
      (hfat0.trans (liminf_le_of_frequently_le' (Eventually.frequently ?_)))
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top
        (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.pow_ne_top ENNReal.ofReal_ne_top⟩)
        (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))
    · filter_upwards [self_mem_nhdsWithin] with η' hη' using (key η' hη').1
  · calc wickF (waveGreen 3) Γ α₀ (capDom (0 : Fin (m + n) → ℝ)) ε m D T1 T2
        ≤ liminf (fun η' => wickF (greenS 3 η') Γ α₀ (capDom (0 : Fin (m + n) → ℝ)) ε m D T1 T2)
            (𝓝[>] 0) := hfat0
      _ ≤ liminf (fun η' => wickF (greenS 3 η') Γ α₀ (capDom fun _ : Fin (m + n) => η) ε m D T1 T2 +
            ENNReal.ofReal (((m + n : ℕ) : ℝ) * Real.exp (T1 + T2) * Zr ^ (2 * Lc) * 4 * t))
            (𝓝[>] 0) := by
          refine Filter.liminf_le_liminf ?_
          filter_upwards [self_mem_nhdsWithin] with η' hη' using (key η' hη').2
      _ = _ := (hlimη.add tendsto_const_nhds).liminf_eq

/-- **`E:joint-temporal-tail`** (`JointTemporalTailTarget d`; TeX lines 1892-1921 at revision
edf7085f (book 1.1.3)) for every `H:homog` covariance, `d = 1, 2, 3`, with the per-edge bridge
`M8M7BridgeTarget d` (item C) and the spectral identity `SpectralSpatialWTarget d` (item B, used
only in `d = 3`) as hypotheses. -/
theorem joint_temporal_tail (d : ℕ) (hBr : M8M7BridgeTarget d) (hB : SpectralSpatialWTarget d) :
    JointTemporalTailTarget d := by
  intro alpha α₀ Γ μ hH
  rcases hH.dim with rfl | rfl | rfl
  · exact joint_temporal_tail_of_le_two (Or.inl rfl) hBr hH
  · exact joint_temporal_tail_of_le_two (Or.inr rfl) hBr hH
  · exact joint_temporal_tail_three hBr hB hH

end StratonovichHAMSecondMoment.JointTail
