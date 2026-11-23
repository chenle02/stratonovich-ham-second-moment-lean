module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L18, item L18-E, part 2: the d = 3 Green-width removal at fixed noise widths by the
spectral route (decision 8) and the unsmoothed d = 3 successors of L17's E3 bounds
(decision 13; main TeX lines 1652-1655, 1923-1926, the displays `E:crude-corrected` 1980-1984
and `E:theta-envelope` 2003-2006 with proof Steps 1-2 of `L:crude-corrected` 1993-2053, and
2352-2394, at revision edf7085f (book 1.1.3)).

Route difference (disclosed, decision 8): the TeX removes the Green smoothing `p_η * G_s` by weak
convergence of the Green measures against the bounded continuous covariance products
(1652-1655, 1923-1926).  Here the removal goes through the spectral identity of item B
(`SpectralSpatialWTarget`, a hypothesis with its frozen signature): at fixed positive noise
widths, `J^{(η)}_{ε,D}(r) = ∫ ∏_e e^{-(ε_j+ε_h)|ξ_e|²/2} ∏_l e^{-η|η_l|²/2} Ĝ_{r_l}(η_l) μ^{⊗k}(dξ)`
converges as `η ↓ 0` to the unsmoothed value by dominated convergence in `ξ`
(`tendsto_wickJ_greenS`).  The d = 3 diagram bounds then pass from L17's uniform-in-`η` versions
(`EnvelopeD3Final.*_l17`) to `waveGreen 3` by Fatou's lemma in time (`diagram_three_le`): only
an upper bound is needed.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.JointFixedOrder
public import StratonovichHAMSecondMoment.EnvelopeD3Final
public import StratonovichHAMSecondMoment.WhiteCollapse

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal Real Pointwise Nat

namespace StratonovichHAMSecondMoment.EnvelopeD3Wave

open HomogHypothesis (Rd HomogCovariance)
open LowAlphaConvolution (gaussFactor smoothedGreen)
open DiagramModel (Pi2 predVal incr openers covEps covWeight pos spatial diagram freq timeWeight
  twoSimplex)
open WaveGreen (waveGreen)
open WaveKernel (waveHat)
open PairingInterface
open WickInterface

variable {d : ℕ} {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}

/-! ### The spectral form is continuous in the Green width at `0` -/

theorem continuous_freq (m : ℕ) {N : ℕ} (D : Fin N → Fin N) (l : Fin N) :
    Continuous fun ξ : openers D → Rd d => freq m D ξ l := by
  unfold freq
  fun_prop

/-- **Green-width removal in the spectral form**: `η ↦ J^{(η)}` (spectral side) is right
continuous at `0`, at positive noise widths (dominated convergence with the
majorant `∏_e e^{-(ε_j+ε_h)|ξ_e|²/2} ∏_l |r_l|`, integrable since `μ` is tempered). -/
theorem tendsto_spatialSpecW (hH : HomogCovariance d alpha α₀ Γ μ) {N : ℕ} {ε : Fin N → ℝ}
    (hε : ∀ i, 0 < ε i) (m : ℕ) (D : Fin N → Fin N) (r : Fin N → ℝ) :
    Tendsto (fun η => spatialSpecW μ η ε m D r) (𝓝[>] 0) (𝓝 (spatialSpecW μ 0 ε m D r)) := by
  have := hH.μ_radon
  have hgc : ∀ b : ℝ, Continuous fun x : Rd d => gaussFactor b x := fun b => by
    unfold gaussFactor; fun_prop
  have hcont : ∀ η : ℝ, Continuous fun ξ : openers D → Rd d =>
      (∏ e : openers D, gaussFactor (ε (e : Fin N) + ε (D e)) (ξ e)) *
        ∏ l, gaussFactor η (freq m D ξ l) * waveHat (r l) (freq m D ξ l) := fun η =>
    (continuous_finsetProd _ fun e _ => (hgc _).comp (continuous_apply e)).mul
      (continuous_finsetProd _ fun l _ => ((hgc η).comp (continuous_freq m D l)).mul
        (WaveKernel.waveHat_continuous.comp (continuous_const.prodMk (continuous_freq m D l))))
  unfold spatialSpecW
  refine tendsto_integral_filter_of_dominated_convergence
    (fun ξ => (∏ e : openers D, gaussFactor (ε (e : Fin N) + ε (D e)) (ξ e)) * ∏ l, |r l|)
    (Eventually.of_forall fun η => (hcont η).aestronglyMeasurable) ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with η hη
    refine ae_of_all _ fun ξ => ?_
    have hη0 : (0 : ℝ) ≤ η := le_of_lt hη
    rw [Real.norm_eq_abs, abs_mul, Finset.abs_prod, Finset.abs_prod]
    refine mul_le_mul ?_ ?_ (Finset.prod_nonneg fun _ _ => abs_nonneg _)
      (Finset.prod_nonneg fun e _ => (Real.exp_pos _).le)
    · exact le_of_eq (Finset.prod_congr rfl fun e _ => abs_of_pos (Real.exp_pos _))
    · exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun l _ =>
        PairingSmoothedNorms.abs_wh_le hη0 (r l) _
  · exact (Integrable.fintype_prod (f := fun e : openers D => gaussFactor (ε (e : Fin N) + ε (D e)))
      fun e => LowAlphaConvolution.integrable_gaussFactor hH.μ_tempered
        (add_pos (hε _) (hε _))).mul_const _
  · refine ae_of_all _ fun ξ => tendsto_nhdsWithin_of_tendsto_nhds ?_
    have : Continuous fun η : ℝ => (∏ e : openers D, gaussFactor (ε (e : Fin N) + ε (D e)) (ξ e)) *
        ∏ l, gaussFactor η (freq m D ξ l) * waveHat (r l) (freq m D ξ l) := by
      unfold gaussFactor; fun_prop
    exact this.tendsto 0

/-- **The d = 3 (any d) Green-width removal at fixed noise widths** (decision 8; TeX 1652-1655,
1923-1926 by the spectral route): `J^{(η)}_{ε,D}(r) → J_{ε,D}(r)` as `η ↓ 0`, from the spectral
identity `hB` (item B) at `η > 0` and at `η = 0` (`greenS_zero`). -/
theorem tendsto_wickJ_greenS (hB : SpectralSpatialWTarget d) (hH : HomogCovariance d alpha α₀ Γ μ)
    {m n k : ℕ} (hmn : m + n = 2 * k) (hk : 1 ≤ k) {D : Fin (m + n) → Fin (m + n)}
    (hD : D ∈ Pi2 m n) {ε : Fin (m + n) → ℝ} (hε : ∀ i, 0 < ε i) {r : Fin (m + n) → ℝ}
    (hr : ∀ i, 0 ≤ r i) :
    Tendsto (fun η => wickJ (greenS d η) Γ ε m D r) (𝓝[>] 0)
      (𝓝 (wickJ (waveGreen d) Γ ε m D r)) := by
  rw [← wickJ_greenS_zero, hB hH 0 le_rfl m n k hmn hk D hD ε hε r hr]
  refine (ENNReal.tendsto_ofReal (tendsto_spatialSpecW hH hε m D r)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with η hη
  exact (hB hH η (le_of_lt hη) m n k hmn hk D hD ε hε r hr).symm

/-! ### Fatou in time: the unsmoothed d = 3 diagrams -/

/-- The spatial part of a Green family with a finite measurable density is measurable in the
increments. -/
theorem measurable_spatial_of_density (hH : HomogCovariance d alpha α₀ Γ μ) {ε : ℝ} (hε : 0 < ε)
    (G : ℝ → Measure (Rd d)) (g : Kernel d) (hg : Measurable (Function.uncurry g))
    (hfin : ∀ s x, g s x ≠ ∞) (hG : ∀ s, G s = volume.withDensity (g s)) (m : ℕ) {N : ℕ}
    (D : Fin N → Fin N) : Measurable (spatial G (covEps Γ ε) m D) := by
  have hγ : Measurable (covEps Γ ε) := LowAlphaUpper.measurable_covEps hH hε
  have e : spatial G (covEps Γ ε) m D = fun h =>
      ∫⁻ y, (∏ i, g (h i) (DiagramBridge.incrOfPos m y i)) * covWeight (covEps Γ ε) D y :=
    funext fun h => PairingBridge.spatial_eq_of_density G g hg hfin hG hγ m D h
  rw [e]
  have hcov : Measurable fun y : Fin N → Rd d => covWeight (covEps Γ ε) D y :=
    Finset.measurable_prod _ fun i _ =>
      hγ.comp ((measurable_pi_apply i).sub (measurable_pi_apply (D i)))
  have hf : Measurable fun p : (Fin N → ℝ) × (Fin N → Rd d) =>
      (∏ i, g (p.1 i) (DiagramBridge.incrOfPos m p.2 i)) * covWeight (covEps Γ ε) D p.2 := by
    refine (Finset.measurable_prod _ fun i _ => ?_).mul (hcov.comp measurable_snd)
    have h2 : Measurable fun p : (Fin N → ℝ) × (Fin N → Rd d) =>
        (p.1 i, DiagramBridge.incrOfPos m p.2 i) :=
      ((measurable_pi_apply i).comp measurable_fst).prodMk
        (((measurable_pi_apply i).comp (DiagramBridge.measurable_incrOfPos m (d := d) (N := N))).comp
          measurable_snd)
    exact hg.comp h2
  exact hf.lintegral_prod_right'

/-- **The unsmoothed d = 3 diagram sums are bounded by any bound uniform in the Green width**
(Fatou in time, with the pointwise Green-width removal `tendsto_wickJ_greenS`). -/
theorem diagram_three_le (hB : SpectralSpatialWTarget 3) {Γ μ : Measure (Rd 3)}
    (hH : HomogCovariance 3 alpha α₀ Γ μ) {ε : ℝ} (hε : 0 < ε) {m n k : ℕ}
    (hmn : m + n = 2 * k) {t : ℝ} (B : ℝ≥0∞)
    (hbound : ∀ η : ℝ, 0 < η → ∑ D ∈ Pi2 m n,
      diagram (fun s => smoothedGreen (waveGreen 3) s η) (covEps Γ ε) α₀ m n D t ≤ B) :
    ∑ D ∈ Pi2 m n, diagram (waveGreen 3) (covEps Γ ε) α₀ m n D t ≤ B := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · obtain ⟨rfl, rfl⟩ : m = 0 ∧ n = 0 := by omega
    have h1 := hbound 1 one_pos
    simp_rw [DiagramModel.diagram_zero_zero] at h1 ⊢
    exact h1
  have hS := DiagramModel.measurableSet_twoSimplex m n t
  have hε2 : ∀ _ : Fin (m + n), (0 : ℝ) < ε / 2 := fun _ => half_pos hε
  -- the integrands
  set F : ℝ → (Fin (m + n) → ℝ) → ℝ≥0∞ := fun η s => if 0 < η then ∑ D ∈ Pi2 m n,
    timeWeight α₀ D s * spatial (greenS 3 η) (covEps Γ ε) m D (incr m s) else 0 with hF
  set F0 : (Fin (m + n) → ℝ) → ℝ≥0∞ := fun s => ∑ D ∈ Pi2 m n,
    timeWeight α₀ D s * spatial (waveGreen 3) (covEps Γ ε) m D (incr m s) with hF0
  have hmeasη : ∀ η, 0 < η → ∀ D : Fin (m + n) → Fin (m + n),
      Measurable fun s => timeWeight α₀ D s * spatial (greenS 3 η) (covEps Γ ε) m D (incr m s) :=
    fun η hη D => (DiagramModel.measurable_timeWeight α₀ D).mul
      ((measurable_spatial_of_density hH hε _ (GreenSmoothed3.green3s η)
        (GreenSmoothed3.measurable_green3s η) (GreenSmoothed3.green3s_ne_top hη)
        (GreenSmoothed3.smoothedGreen_three_eq hη) m D).comp (DiagramModel.measurable_incr m))
  have hincr : ∀ s ∈ twoSimplex m n t, ∀ i, 0 < incr m s i := fun s hs i => by
    rw [DiagramModel.incr]; linarith [(hs i).1]
  have hmeas0 : ∀ D : Fin (m + n) → Fin (m + n), AEMeasurable
      (fun s => timeWeight α₀ D s * spatial (waveGreen 3) (covEps Γ ε) m D (incr m s))
      (volume.restrict (twoSimplex m n t)) := by
    intro D
    refine ((DiagramModel.measurable_timeWeight α₀ D).mul
      ((JointFixedOrder.measurable_wickJm hH hε2 m D).comp
        (DiagramModel.measurable_incr m))).aemeasurable.congr ?_
    filter_upwards [ae_restrict_mem hS] with s hs
    show timeWeight α₀ D s * JointFixedOrder.wickJm Γ (fun _ => ε / 2) m D (incr m s) = _
    rw [← wickJ_half, JointFixedOrder.wickJ_eq_wickJm hH hε2 m D (hincr s hs)]
  have hsum0 : ∑ D ∈ Pi2 m n, diagram (waveGreen 3) (covEps Γ ε) α₀ m n D t =
      ∫⁻ s in twoSimplex m n t, F0 s := by
    rw [hF0, lintegral_finsetSum' _ fun D _ => hmeas0 D]
    rfl
  have hsumη : ∀ η, 0 < η → ∑ D ∈ Pi2 m n,
      diagram (fun s => smoothedGreen (waveGreen 3) s η) (covEps Γ ε) α₀ m n D t =
      ∫⁻ s in twoSimplex m n t, F η s := fun η hη => by
    simp only [hF, hη, ite_true]
    rw [lintegral_finsetSum' _ fun D _ => (hmeasη η hη D).aemeasurable]
    rfl
  have hpt : ∀ s ∈ twoSimplex m n t, (∀ D ∈ Pi2 m n, timeWeight α₀ D s ≠ ⊤) →
      Tendsto (fun η => F η s) (𝓝[>] 0) (𝓝 (F0 s)) := by
    intro s hs htw
    refine Tendsto.congr' (f₁ := fun η => ∑ D ∈ Pi2 m n,
      timeWeight α₀ D s * spatial (greenS 3 η) (covEps Γ ε) m D (incr m s)) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with η hη
      simp only [hF, show (0 : ℝ) < η from hη, ite_true]
    refine tendsto_finsetSum _ fun D hD => ?_
    have hJ := tendsto_wickJ_greenS hB hH hmn hk hD hε2 (r := incr m s)
      fun i => (hincr s hs i).le
    simp_rw [wickJ_half] at hJ
    exact ENNReal.Tendsto.const_mul hJ (Or.inr (htw D hD))
  rw [hsum0]
  calc ∫⁻ s in twoSimplex m n t, F0 s
      = ∫⁻ s in twoSimplex m n t, liminf (fun η => F η s) (𝓝[>] 0) :=
        lintegral_congr_ae (by
          filter_upwards [ae_restrict_mem hS, ae_restrict_of_ae ((Filter.eventually_all_finset
            (Pi2 m n)).2 fun D hD =>
              WhiteCollapse.ae_timeWeight_ne_top α₀ (DiagramModel.mem_Pi2.1 hD))] with s hs htw
          exact ((hpt s hs htw).liminf_eq).symm)
    _ ≤ liminf (fun η => ∫⁻ s in twoSimplex m n t, F η s) (𝓝[>] 0) := by
        refine (lintegral_liminf_le' (u := 𝓝[>] (0 : ℝ)) (f := F)
          (μ := volume.restrict (twoSimplex m n t)) fun η => ?_)
        by_cases hη : 0 < η
        · simp only [hF, hη, ite_true]
          exact (Finset.measurable_sum _ fun D _ => hmeasη η hη D).aemeasurable
        · simp only [hF, hη, ite_false]
          exact aemeasurable_const
    _ ≤ B := by
        refine liminf_le_of_frequently_le' (Eventually.frequently ?_)
        filter_upwards [self_mem_nhdsWithin] with η hη
        rw [← hsumη η hη]
        exact hbound η hη

/-! ### Decision 13: the unsmoothed d = 3 successors of L17's E3 bounds -/

/-- **`E:homogeneous-envelope` in `d = 3` for `waveGreen 3`** (`HomogEnvelopeThreeTarget`; TeX
lines 2352-2394 at revision edf7085f (book 1.1.3)), with B's spectral identity
`SpectralSpatialWTarget 3` as a hypothesis: L17's bound for the Green-smoothed kernels, uniform in
`η > 0`, passes to `η = 0` by `diagram_three_le` (route difference disclosed in the module doc). -/
theorem homogeneous_envelope_diagrams_three' (hB : SpectralSpatialWTarget 3) :
    HomogEnvelopeThreeTarget := by
  intro alpha α₀ Γ μ hH
  obtain ⟨K, hK, h⟩ := EnvelopeD3Final.homogeneous_envelope_diagrams_three_l17 hH
  exact ⟨K, hK, fun ε hε m n k hmn hk t θ ht hθ =>
    diagram_three_le hB hH hε hmn _ fun η hη => h η hη ε hε m n k hmn hk t θ ht hθ⟩

/-- **`E:theta-envelope` in `d = 3` for `waveGreen 3`** (`ThetaEnvelopeThreeTarget`; TeX: the
display 2003-2006, in Step 1 1993-2031, at revision edf7085f (book 1.1.3)), with
`SpectralSpatialWTarget 3` as a hypothesis. -/
theorem theta_envelope_diagrams_three' (hB : SpectralSpatialWTarget 3) :
    ThetaEnvelopeThreeTarget := by
  intro alpha α₀ Γ μ hH
  obtain ⟨C, θ₀, hC, hθ₀, h⟩ := EnvelopeD3Final.theta_envelope_diagrams_three_l17 hH
  exact ⟨C, θ₀, hC, hθ₀, fun ε hε n t θ ht hθ =>
    diagram_three_le hB hH hε (k := n) (by ring) _ fun η hη => h η hη ε hε n t θ ht hθ⟩

/-- **The first inequality of `E:crude-corrected` for the diagram sums, in `d = 3` for
`waveGreen 3`** (`CrudeCorrectedThreeTarget`; TeX: the display 1980-1984; its first inequality
derived in Step 2, 2036-2041; at revision edf7085f (book 1.1.3)), with
`SpectralSpatialWTarget 3` as a hypothesis. -/
theorem crude_corrected_diagrams_three' (hB : SpectralSpatialWTarget 3) :
    CrudeCorrectedThreeTarget := by
  intro alpha α₀ Γ μ hH
  obtain ⟨C, θ₀, hC, hθ₀, h⟩ := EnvelopeD3Final.crude_corrected_diagrams_three_l17 hH
  exact ⟨C, θ₀, hC, hθ₀, fun ε hε n t hn ht =>
    diagram_three_le hB hH hε (k := n) (by ring) _ fun η hη => h η hη ε hε n t hn ht⟩

end StratonovichHAMSecondMoment.EnvelopeD3Wave
