module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L18, item L18-C, part 2: the uniform mass bound of `L:spatial-wick-measures`, the frozen
target `WickInterface.WickMassBoundTarget` (display TeX lines 1795-1798, content 1796-1797, at
revision edf7085f (book 1.1.3); Steps 2-3 of the proof, TeX 1726-1798, are REPLACED).

Route difference (decision 4 of wave L18, disclosed): the TeX proves `sup_ε L_{ε,D}(0) < ∞` by
Brownian occupation moments (Steps 2-3, with the explicit constant `2^{-2k-2}(∫ e^{-a/2} M_k(a)
da)²`); Mathlib at the pin has no Brownian motion, so this module proves the finiteness by the
envelope route (b), with results of the book applied in a different order:
* the Gamma mixture on the Laplace interval `(0, δ]`, `δ = 1/(2k)`, is bounded below,
  `κ_{(0,δ]}(u) ≥ Γ(α₀)⁻¹ δ^{α₀} e^{-δ|u|}` (`kerA_Ioc_ge`);
* `|s_j - s_h| ≤ Σ_l r_l` for every pair, so `Σ_{pairs} δ|s_j - s_h| ≤ ½ Σ r` and
  `e^{-Σr} ≤ κ₀^{-k} e^{-Σr/2} ∏_{pairs} κ_{(0,δ]}(s_j - s_h)` (`pairTime_ge`);
* the per-edge bridge (`WickBridge.m8_m7_bridge`) at damping `θ = 1/2`, then
  `L:pairing-product-envelope` (`PairingEnvelope.pairing_product_envelope`) and
  `L:damped-homogeneous-norms` (L17's `HomogeneousEnvelope.norms_le_homog`, d = 1, 2;
  `EnvelopeD3.norms_le_homog`, d = 3 Green-smoothed, uniformly in the smoothing width) after
  `nuE_mono`/`NC_mono_measure` for `(0, δ] ⊆ (0,∞)`; the edge norms are uniform in the vertex
  widths (`prodP_le_of_edges`);
* d = 3: the wave Green measure has no density; the bound holds for `greenS 3 η`, `η > 0`,
  uniformly in `η`, and `η ↓ 0` is taken by Fatou in the spectral form of B's
  `SmoothedLaplaceTarget` (the hypothesis `hB`; decision 8, a route difference from the TeX's weak
  convergence of Green measures, 1652-1655).
The approved proposal's variant (cap `(0,1]`, the bridge at damping `θ = 1` with the mass weight
`e^{-(k+1)Σr}`, then the scaling of `ρ_ε` with `c = k+1`: `k+1` is the mass-weight exponent and
the rescaling factor, not a bridge damping) is replaced by the cap `(0, 1/(2k)]` with the bridge
at damping `θ = 1/2` and no rescaling, which needs no scaling of the Green-smoothed kernels in
d = 3; the scaling identity itself is `WickScaling.rho_scaling`.
The TeX's explicit constant is not stated (INTERFACE §4.6).
-/
public import Mathlib
public import StratonovichHAMSecondMoment.WickBridge
public import StratonovichHAMSecondMoment.PairingEnvelope
public import StratonovichHAMSecondMoment.HomogeneousEnvelope
public import StratonovichHAMSecondMoment.EnvelopeD3

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal Real

namespace StratonovichHAMSecondMoment.WickMass

open HomogHypothesis (Rd HomogCovariance)
open LowAlphaConvolution (gaussFactor)
open DiagramModel (Pi2 openers freq)
open WaveGreen (waveGreen)
open PairingInterface
open PairingBridge
open WickInterface
open WickBridge

variable {d : ℕ}

/-! ### The kernel lower bound on a Laplace interval -/

/-- **The Gamma mixture on `(0, δ]` is bounded below**:
`κ_{(0,δ]}(u) = Γ(a)⁻¹ ∫_0^δ e^{-λ|u|} λ^{a-1} dλ ≥ Γ(a)⁻¹ δ^a e^{-δ|u|}` for `0 < a ≤ 1`. -/
theorem kerA_Ioc_ge {a δ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hδ : 0 < δ) (u : ℝ) :
    ENNReal.ofReal ((Real.Gamma a)⁻¹ * δ ^ a * Real.exp (-(δ * |u|))) ≤ kerA a (Ioc 0 δ) u := by
  have hG : 0 < (Real.Gamma a)⁻¹ := inv_pos.2 (Real.Gamma_pos_of_pos ha)
  unfold kerA nuE
  rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  have hlow : ∀ᵐ l ∂(volume.restrict (Ioc (0 : ℝ) δ)),
      ENNReal.ofReal ((Real.Gamma a)⁻¹ * δ ^ (a - 1) * Real.exp (-(δ * |u|))) ≤
        ((fun l => ENNReal.ofReal ((Real.Gamma a)⁻¹ * l ^ (a - 1))) *
          fun l => ENNReal.ofReal (Real.exp (-(l * |u|)))) l := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with l hl
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (mul_nonneg hG.le (Real.rpow_nonneg hl.1.le _))]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : δ ^ (a - 1) ≤ l ^ (a - 1) := Real.rpow_le_rpow_of_nonpos hl.1 hl.2 (by linarith)
    have h2 : Real.exp (-(δ * |u|)) ≤ Real.exp (-(l * |u|)) :=
      Real.exp_le_exp.2 (by nlinarith [abs_nonneg u, hl.2])
    have h3 : 0 ≤ (Real.Gamma a)⁻¹ * δ ^ (a - 1) := mul_nonneg hG.le (Real.rpow_nonneg hδ.le _)
    calc (Real.Gamma a)⁻¹ * δ ^ (a - 1) * Real.exp (-(δ * |u|))
        ≤ (Real.Gamma a)⁻¹ * l ^ (a - 1) * Real.exp (-(δ * |u|)) := by gcongr
      _ ≤ (Real.Gamma a)⁻¹ * l ^ (a - 1) * Real.exp (-(l * |u|)) := by
          gcongr; exact mul_nonneg hG.le (Real.rpow_nonneg hl.1.le _)
  refine le_trans (le_of_eq ?_) (lintegral_mono_ae hlow)
  rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioc,
    sub_zero, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have : δ ^ a = δ ^ (a - 1) * δ := by
    rw [← Real.rpow_add_one hδ.ne']; ring_nf
  rw [this]; ring

/-! ### The pair product lower bound -/

/-- The cumulative times of nonnegative gaps lie in `[0, Σ r]`. -/
theorem gapTime_mem (m : ℕ) {N : ℕ} {r : Fin N → ℝ} (hr : ∀ i, 0 ≤ r i) (i : Fin N) :
    0 ≤ gapTime m r i ∧ gapTime m r i ≤ ∑ j, r j :=
  ⟨Finset.sum_nonneg fun j _ => hr j,
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => hr j⟩

/-- `|s_j - s_h| ≤ Σ_l r_l` for nonnegative gaps. -/
theorem abs_gapTime_sub_le (m : ℕ) {N : ℕ} {r : Fin N → ℝ} (hr : ∀ i, 0 ≤ r i) (i j : Fin N) :
    |gapTime m r i - gapTime m r j| ≤ ∑ l, r l := by
  obtain ⟨h1, h2⟩ := gapTime_mem m hr i
  obtain ⟨h3, h4⟩ := gapTime_mem m hr j
  rw [abs_sub_le_iff]; constructor <;> linarith

/-- The constant `κ₀ = Γ(α₀)⁻¹ δ^{α₀}`, `δ = 1/(2k)`. -/
def kappa0 (a : ℝ) (k : ℕ) : ℝ := (Real.Gamma a)⁻¹ * (1 / (2 * (k : ℝ))) ^ a

theorem kappa0_pos {a : ℝ} (ha : 0 < a) {k : ℕ} (hk : 1 ≤ k) : 0 < kappa0 a k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  unfold kappa0
  exact mul_pos (inv_pos.2 (Real.Gamma_pos_of_pos ha)) (Real.rpow_pos_of_pos (by positivity) _)

/-- **The pair product on `(0, 1/(2k)]` is bounded below**: for nonnegative gaps,
`∏_{pairs} κ_{(0,δ]}(s_j - s_h) ≥ κ₀^k e^{-Σr/2}`. -/
theorem pairTime_ge {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {m n k : ℕ} (hmn : m + n = 2 * k)
    (hk : 1 ≤ k) {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n) {r : Fin (m + n) → ℝ}
    (hr : ∀ i, 0 ≤ r i) :
    ENNReal.ofReal (kappa0 a k ^ k * Real.exp (-(1 / 2 * ∑ i, r i))) ≤
      pairTime a (fun _ => Ioc 0 (1 / (2 * (k : ℝ)))) m D r := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  set δ : ℝ := 1 / (2 * (k : ℝ)) with hδ
  have hδp : 0 < δ := by positivity
  have hcard : (openers D).card = k := DiagramModel.card_openers hD hmn
  set S := ∑ i, r i
  unfold pairTime
  calc ENNReal.ofReal (kappa0 a k ^ k * Real.exp (-(1 / 2 * S)))
      ≤ ENNReal.ofReal (∏ i ∈ openers D, (Real.Gamma a)⁻¹ * δ ^ a *
          Real.exp (-(δ * |gapTime m r i - gapTime m r (D i)|))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Finset.prod_mul_distrib, Finset.prod_const, hcard, ← Real.exp_sum]
        have hsum : ∑ i ∈ openers D, -(δ * |gapTime m r i - gapTime m r (D i)|) ≥
            -(1 / 2 * S) := by
          have : ∑ i ∈ openers D, δ * |gapTime m r i - gapTime m r (D i)| ≤
              ∑ _i ∈ openers D, δ * S :=
            Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_left (abs_gapTime_sub_le m hr i (D i)) hδp.le
          rw [Finset.sum_const, hcard, nsmul_eq_mul] at this
          have hδk : (k : ℝ) * (δ * S) = 1 / 2 * S := by
            rw [hδ]; field_simp
          rw [Finset.sum_neg_distrib]
          linarith
        have hk0 : 0 ≤ kappa0 a k ^ k := pow_nonneg (kappa0_pos ha hk).le _
        unfold kappa0
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hsum) hk0
    _ = ∏ i ∈ openers D, ENNReal.ofReal ((Real.Gamma a)⁻¹ * δ ^ a *
          Real.exp (-(δ * |gapTime m r i - gapTime m r (D i)|))) := by
        refine ENNReal.ofReal_prod_of_nonneg fun i _ => ?_
        have := (kappa0_pos ha hk).le
        unfold kappa0 at this
        exact mul_nonneg this (Real.exp_pos _).le
    _ ≤ _ := Finset.prod_le_prod fun i _ => kerA_Ioc_ge ha ha1 hδp _

/-! ### The envelope with per-edge data -/

/-- **An admissible product with per-edge data**: if `N_0 · 2N_{1,e} ≤ Z` and `N_{2,e}² ≤ Z` for
every edge, the product is at most `Z^{|D|}` (as `HomogeneousEnvelope.prodP_const_le`, with the
edge datum depending on the edge). -/
theorem prodP_le_of_edges {α : Type*} [DecidableEq α] (a : ℝ) {L : Finset α}
    {D : Finset (Sym2 α)} (ed : Sym2 α → EdgeData d) (G : Kernel d) (A : Adm L D) {Z : ℝ≥0∞}
    (h : ∀ e ∈ D, N0 G * (2 * N1 a (ed e) G) ≤ Z ∧ N2 a (ed e) G ^ 2 ≤ Z) :
    prodP a ed (fun _ => G) A ≤ Z ^ D.card := by
  have hc := HomogeneousEnvelope.two_card_Q1_add_card_Q2 A
  have hle : A.Q1.card ≤ D.card := by omega
  have h1 : (∏ l ∈ A.Q0, N0 G) * ∏ l ∈ A.Q1, 2 * N1 a (ed (A.iota l)) G ≤ Z ^ A.Q1.card := by
    rw [Finset.prod_const, A.card01, ← Finset.prod_const, ← Finset.prod_mul_distrib,
      ← Finset.prod_const]
    exact Finset.prod_le_prod fun l hl =>
      (h _ (A.mapsTo l (Finset.mem_union_left _ hl))).1
  have h2 : (∏ l ∈ A.Q2, N2 a (ed (A.iota l)) G) ^ 2 ≤ Z ^ A.Q2.card := by
    rw [← Finset.prod_pow, ← Finset.prod_const]
    exact Finset.prod_le_prod fun l hl =>
      (h _ (A.mapsTo l (Finset.mem_union_right _ hl))).2
  have hsq : prodP a ed (fun _ => G) A ^ 2 ≤ (Z ^ D.card) ^ 2 := by
    unfold prodP
    rw [mul_pow]
    calc ((∏ l ∈ A.Q0, N0 G) * ∏ l ∈ A.Q1, 2 * N1 a (ed (A.iota l)) G) ^ 2 *
          (∏ l ∈ A.Q2, N2 a (ed (A.iota l)) G) ^ 2
        ≤ (Z ^ A.Q1.card) ^ 2 * Z ^ A.Q2.card := by gcongr
      _ = (Z ^ D.card) ^ 2 := by
        rw [← pow_mul, ← pow_mul, ← pow_add]
        congr 1
        omega
  have := ENNReal.rpow_le_rpow hsq (z := ((2 : ℕ) : ℝ)⁻¹) (by positivity)
  rwa [ENNReal.pow_rpow_inv_natCast two_ne_zero, ENNReal.pow_rpow_inv_natCast two_ne_zero] at this

section Homog

variable {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}

/-- **The damped M7 integral with the M8 edge data is bounded uniformly in the widths**:
`L:pairing-product-envelope` with the edge norms bounded through the full-domain edge datum
(`nuE_mono`, `NC_mono_measure` for `A_e ⊆ (0,∞)`), which `L:damped-homogeneous-norms` bounds
uniformly in the pair width. -/
theorem pairingIntegral_wickEdge_le (hH : HomogCovariance d alpha α₀ Γ μ) {m n k : ℕ}
    (hmn : m + n = 2 * k) {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n)
    {ε : Fin (m + n) → ℝ} (hε : ∀ i, 0 < ε i) (A : Sym2 (Fin (m + n)) → Set ℝ)
    (hAm : ∀ e, MeasurableSet (A e)) (hA0 : ∀ e, A e ⊆ Ioi 0) (K : Kernel d)
    (hK : Measurable (Function.uncurry K)) (hN0 : N0 K ≠ 0) (hN0t : N0 K ≠ ⊤) {Z : ℝ≥0∞}
    (hZ : Z ≠ ⊤)
    (hb : ∀ b : ℝ, ∀ hb : 0 < b, N0 K * (2 * N1 α₀ (smoothEdge hH hb) K) ≤ Z ∧
      N2 α₀ (smoothEdge hH hb) K ^ 2 ≤ Z) :
    pairingIntegral α₀ (m4Chain m n D) (wickEdge hH hε A hAm hA0) (fun _ => K) ≤ Z ^ k := by
  have hN1 : ∀ e, N1 α₀ (wickEdge hH hε A hAm hA0 e) K ≤
      N1 α₀ (smoothEdge hH (edgeWidth_pos hε e)) K := fun e =>
    lintegral_mono' (PairingCapRemoval.nuE_mono α₀ (hA0 e)) le_rfl
  have hN2 : ∀ e, N2 α₀ (wickEdge hH hε A hAm hA0 e) K ≤
      N2 α₀ (smoothEdge hH (edgeWidth_pos hε e)) K := fun e =>
    PairingCapRemoval.NC_mono_measure (PairingCapRemoval.nuE_mono α₀ (hA0 e)) _ _
  have hedge : ∀ e, N0 K * (2 * N1 α₀ (wickEdge hH hε A hAm hA0 e) K) ≤ Z ∧
      N2 α₀ (wickEdge hH hε A hAm hA0 e) K ^ 2 ≤ Z := fun e =>
    ⟨le_trans (by gcongr; exact hN1 e) (hb _ (edgeWidth_pos hε e)).1,
      le_trans (by gcongr; exact hN2 e) (hb _ (edgeWidth_pos hε e)).2⟩
  have hKH : KernelHyp α₀ (m4Chain m n D) (wickEdge hH hε A hAm hA0) (fun _ => K) := by
    refine ⟨fun _ _ => hK, fun _ _ => lt_top_iff_ne_top.2 hN0t, fun _ _ e _ => ?_,
      fun _ _ e _ => ?_⟩
    · refine lt_top_iff_ne_top.2 fun htop => hZ ?_
      have := (hedge e).1
      rw [htop, ENNReal.mul_top two_ne_zero, ENNReal.mul_top hN0] at this
      exact top_le_iff.1 this
    · refine lt_top_iff_ne_top.2 fun htop => hZ ?_
      have := (hedge e).2
      rw [htop, ENNReal.top_pow two_ne_zero] at this
      exact top_le_iff.1 this
  refine (PairingEnvelope.pairing_product_envelope d _ α₀ hH.alpha0_pos hH.alpha0_lt_one _ _ _
    (m4Chain_wf hD) hKH).trans (iSup_le fun B => ?_)
  have := prodP_le_of_edges α₀ (wickEdge hH hε A hAm hA0) K B fun e _ => hedge e
  rwa [card_D_m4Chain hD hmn] at this

/-- The damped kernel of a measurable `g` is measurable. -/
theorem measurable_damp {g : Kernel d} (hg : Measurable (Function.uncurry g)) (θ : ℝ) :
    Measurable (Function.uncurry (damp θ g)) := by
  have : Function.uncurry (damp θ g) = fun p : ℝ × Rd d =>
      ENNReal.ofReal (Real.exp (-(θ * p.1))) * Function.uncurry g p := rfl
  rw [this]
  exact (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    ((measurable_const.mul measurable_fst).neg))).mul hg

/-- The Laplace interval `(0, 1/(2k)]` as per-edge data. -/
theorem measurableSet_Ioc_edge (k : ℕ) {α : Type*} :
    ∀ _e : Sym2 α, MeasurableSet (Ioc (0 : ℝ) (1 / (2 * (k : ℝ)))) := fun _ => measurableSet_Ioc

theorem Ioc_edge_subset (k : ℕ) {α : Type*} :
    ∀ _e : Sym2 α, Ioc (0 : ℝ) (1 / (2 * (k : ℝ))) ⊆ Ioi 0 := fun _ => Ioc_subset_Ioi_self

/-- **The mass bound for a Green family with a density** (route (b)): with the uniform norm
bound `Z` of the damped kernel `e^{-s/2} g`,
`L_{ε,D}(0) ≤ κ₀^{-k} Z^k` for every positive vertexwise width. -/
theorem wickL_zero_le_of_density (hH : HomogCovariance d alpha α₀ Γ μ) {m n k : ℕ}
    (hmn : m + n = 2 * k) (hk : 1 ≤ k) {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n)
    (G : ℝ → Measure (Rd d)) (g : Kernel d) (hg : Measurable (Function.uncurry g))
    (hfin : ∀ s x, g s x ≠ ⊤) (hG : ∀ s, G s = volume.withDensity (g s))
    (hN0 : N0 (damp (1 / 2) g) ≠ 0) (hN0t : N0 (damp (1 / 2) g) ≠ ⊤) {Z : ℝ≥0∞} (hZ : Z ≠ ⊤)
    (hb : ∀ b : ℝ, ∀ hb : 0 < b, N0 (damp (1 / 2) g) *
        (2 * N1 α₀ (smoothEdge hH hb) (damp (1 / 2) g)) ≤ Z ∧
      N2 α₀ (smoothEdge hH hb) (damp (1 / 2) g) ^ 2 ≤ Z)
    {ε : Fin (m + n) → ℝ} (hε : ∀ i, 0 < ε i) :
    wickL G Γ ε m D 0 ≤ ENNReal.ofReal ((kappa0 α₀ k ^ k)⁻¹) * Z ^ k := by
  have hκ := pow_pos (kappa0_pos hH.alpha0_pos hk) k
  rw [wickL_zero, wickNu, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hae : ∀ᵐ r ∂wickRho G Γ ε m D, r ∈ posOrthant (m + n) :=
    (withDensity_absolutelyContinuous _ _).ae_le
      (ae_restrict_mem (measurableSet_posOrthant (m + n)))
  have hpt : ∀ᵐ r ∂wickRho G Γ ε m D, ENNReal.ofReal (Real.exp (-∑ i, r i)) ≤
      ENNReal.ofReal ((kappa0 α₀ k ^ k)⁻¹) *
        (ENNReal.ofReal (Real.exp (-(1 / 2 * ∑ i, r i))) *
          pairTime α₀ (fun _ => Ioc 0 (1 / (2 * (k : ℝ)))) m D r) := by
    filter_upwards [hae] with r hr
    have hr0 : ∀ i, 0 ≤ r i := fun i => (hr i (mem_univ i)).le
    have hP := pairTime_ge hH.alpha0_pos hH.alpha0_lt_one.le hmn hk hD hr0
    calc ENNReal.ofReal (Real.exp (-∑ i, r i))
        = ENNReal.ofReal ((kappa0 α₀ k ^ k)⁻¹) *
            (ENNReal.ofReal (Real.exp (-(1 / 2 * ∑ i, r i))) *
              ENNReal.ofReal (kappa0 α₀ k ^ k * Real.exp (-(1 / 2 * ∑ i, r i)))) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
            ← ENNReal.ofReal_mul (inv_pos.2 hκ).le]
          congr 1
          rw [mul_left_comm (Real.exp _), inv_mul_cancel_left₀ hκ.ne', ← Real.exp_add]
          congr 1; ring
      _ ≤ _ := by gcongr
  refine (lintegral_mono_ae hpt).trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  gcongr
  refine (m8_m7_bridge d hH G g hg hfin hG m n D hD ε hε _ (measurableSet_Ioc_edge k)
    (Ioc_edge_subset k) (1 / 2) (by norm_num)).trans ?_
  exact pairingIntegral_wickEdge_le hH hmn hD hε _ _ _ _ (measurable_damp hg _) hN0 hN0t hZ hb

/-- The norm constant of `L:damped-homogeneous-norms` at damping `1/2`. -/
def Zhalf (alpha α₀ : ℝ) (μ : Measure (Rd d)) : ℝ≥0∞ :=
  ENNReal.ofReal (HomogeneousEnvelope.Khom α₀ μ * (1 / 2 : ℝ) ^ (-(4 - alpha - α₀)))

end Homog

/-! ### The mass bound -/

section Mass

variable {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}

/-- The mass bound for the wave Green measures with a Green density (d = 1, 2). -/
theorem wickL_zero_le_green (hH : HomogCovariance d alpha α₀ Γ μ) {g : Kernel d}
    (hgd : PairingDampedNorms.GreenDensity d g) {m n k : ℕ} (hmn : m + n = 2 * k) (hk : 1 ≤ k)
    {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n) {ε : Fin (m + n) → ℝ}
    (hε : ∀ i, 0 < ε i) :
    wickL (waveGreen d) Γ ε m D 0 ≤
      ENNReal.ofReal ((kappa0 α₀ k ^ k)⁻¹) * Zhalf alpha α₀ μ ^ k := by
  have hθ : (0 : ℝ) < 1 / 2 := by norm_num
  have h0 := PairingDampedNorms.N0_damp hgd hθ
  refine wickL_zero_le_of_density hH hmn hk hD (waveGreen d) g hgd.meas hgd.fin hgd.eq ?_ ?_
    ENNReal.ofReal_ne_top (fun b hb => HomogeneousEnvelope.norms_le_homog hgd hH hb hθ) hε
  · rw [h0]; exact ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hθ _) |>.ne'
  · rw [h0]; exact ENNReal.ofReal_ne_top

/-- The mass bound for the Green-smoothed `d = 3` kernels, uniformly in the smoothing width. -/
theorem wickL_zero_le_three {Γ μ : Measure (Rd 3)} (hH : HomogCovariance 3 alpha α₀ Γ μ)
    {η : ℝ} (hη : 0 < η) {m n k : ℕ} (hmn : m + n = 2 * k) (hk : 1 ≤ k)
    {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n) {ε : Fin (m + n) → ℝ}
    (hε : ∀ i, 0 < ε i) :
    wickL (greenS 3 η) Γ ε m D 0 ≤
      ENNReal.ofReal ((kappa0 α₀ k ^ k)⁻¹) * Zhalf alpha α₀ μ ^ k := by
  have hθ : (0 : ℝ) < 1 / 2 := by norm_num
  have hgd := EnvelopeD3.smoothDensity_three hη
  have h0 := PairingSmoothedNorms.N0_damp hgd hθ
  refine wickL_zero_le_of_density hH hmn hk hD (greenS 3 η) _ hgd.meas hgd.fin hgd.eq ?_ ?_
    ENNReal.ofReal_ne_top (fun b hb => EnvelopeD3.norms_le_homog hgd hH hb hθ) hε
  · rw [h0]; exact ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hθ _) |>.ne'
  · rw [h0]; exact ENNReal.ofReal_ne_top

/-- The integrand of `laplaceRHS μ η ε m D 0` is continuous in the frequencies. -/
theorem continuous_laplaceIntegrand {N : ℕ} (η : ℝ) (ε : Fin N → ℝ) (m : ℕ)
    (D : Fin N → Fin N) :
    Continuous fun ξ : openers D → Rd d =>
      (∏ e : openers D, gaussFactor (ε (e : Fin N) + ε (D e)) (ξ e)) *
        ∏ l, gaussFactor η (freq m D ξ l) /
          ((1 + (0 : Fin N → ℝ) l) ^ 2 + ‖freq m D ξ l‖ ^ 2) := by
  have hfr : ∀ l, Continuous fun ξ : openers D → Rd d => freq m D ξ l := fun l => by
    unfold freq; fun_prop
  refine (continuous_finsetProd _ fun e _ => ?_).mul (continuous_finsetProd _ fun l _ => ?_)
  · unfold gaussFactor; fun_prop
  · refine Continuous.div ?_ ?_ fun ξ => by simp only [Pi.zero_apply]; positivity
    · unfold gaussFactor; exact Real.continuous_exp.comp (by fun_prop)
    · exact continuous_const.add ((hfr l).norm.pow 2)

/-- **The Green-width removal in d = 3** (Fatou in the spectral form of `SmoothedLaplaceTarget`,
decision 8): a bound for `L^{(η)}_{ε,D}(0)` uniform in `η > 0` bounds `L_{ε,D}(0)`. -/
theorem wickL_zero_le_of_smoothed {Γ μ : Measure (Rd 3)} (hH : HomogCovariance 3 alpha α₀ Γ μ)
    (hB : SmoothedLaplaceTarget 3) {m n k : ℕ} (hmn : m + n = 2 * k) (hk : 1 ≤ k)
    {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n) {ε : Fin (m + n) → ℝ}
    (hε : ∀ i, 0 < ε i) {C : ℝ≥0∞} (hC : ∀ η : ℝ, 0 < η → wickL (greenS 3 η) Γ ε m D 0 ≤ C) :
    wickL (waveGreen 3) Γ ε m D 0 ≤ C := by
  have hL : ∀ η : ℝ, 0 ≤ η → wickL (greenS 3 η) Γ ε m D 0 = laplaceRHS μ η ε m D 0 :=
    fun η hη => hB hH η hη m n k hmn hk D hD ε hε 0 fun _ => le_rfl
  have h0 := hL 0 le_rfl
  rw [greenS_zero] at h0
  rw [h0]
  set f : ℝ → (openers D → Rd 3) → ℝ≥0∞ := fun η ξ => ENNReal.ofReal
    ((∏ e : openers D, gaussFactor (ε (e : Fin (m + n)) + ε (D e)) (ξ e)) *
      ∏ l, gaussFactor η (freq m D ξ l) /
        ((1 + (0 : Fin (m + n) → ℝ) l) ^ 2 + ‖freq m D ξ l‖ ^ 2)) with hf
  have hlap : ∀ η, laplaceRHS μ η ε m D 0 = ∫⁻ ξ, f η ξ ∂(Measure.pi fun _ : openers D => μ) :=
    fun η => rfl
  have hu : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hpos : ∀ j : ℕ, 0 < 1 / ((j : ℝ) + 1) := fun j => by positivity
  have hlim : ∀ ξ, Tendsto (fun j : ℕ => f (1 / ((j : ℝ) + 1)) ξ) atTop (𝓝 (f 0 ξ)) := by
    intro ξ
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    have hc : Continuous fun η : ℝ =>
        (∏ e : openers D, gaussFactor (ε (e : Fin (m + n)) + ε (D e)) (ξ e)) *
          ∏ l, gaussFactor η (freq m D ξ l) /
            ((1 + (0 : Fin (m + n) → ℝ) l) ^ 2 + ‖freq m D ξ l‖ ^ 2) := by
      refine continuous_const.mul (continuous_finsetProd _ fun l _ => ?_)
      unfold gaussFactor; fun_prop
    exact (hc.tendsto 0).comp hu
  have hmeas : ∀ j : ℕ, AEMeasurable (f (1 / ((j : ℝ) + 1)))
      (Measure.pi fun _ : openers D => μ) := fun j =>
    (ENNReal.measurable_ofReal.comp
      (continuous_laplaceIntegrand (1 / ((j : ℝ) + 1)) ε m D).measurable).aemeasurable
  rw [hlap]
  calc ∫⁻ ξ, f 0 ξ ∂(Measure.pi fun _ : openers D => μ)
      = ∫⁻ ξ, liminf (fun j : ℕ => f (1 / ((j : ℝ) + 1)) ξ) atTop
          ∂(Measure.pi fun _ : openers D => μ) :=
        lintegral_congr fun ξ => ((hlim ξ).liminf_eq).symm
    _ ≤ liminf (fun j : ℕ => ∫⁻ ξ, f (1 / ((j : ℝ) + 1)) ξ ∂(Measure.pi fun _ : openers D => μ))
          atTop := lintegral_liminf_le' hmeas
    _ ≤ C := by
        refine Filter.liminf_le_of_frequently_le' (Frequently.of_forall fun j => ?_)
        rw [← hlap, ← hL _ (hpos j).le]
        exact hC _ (hpos j)

/-- **The uniform mass bound `sup_ε L_{ε,D}(0) < ∞`** (`WickMassBoundTarget`; display TeX lines
1795-1798, content 1796-1797, at revision edf7085f (book 1.1.3)), by route (b) (decision 4, a
disclosed route difference: the envelope, the damped norms and the kernel lower bound on
`(0, 1/(2k)]` in place of the Brownian occupation moments of Steps 2-3, TeX 1726-1798; the
explicit constant is not stated).  B's `SmoothedLaplaceTarget` is used only for `d = 3` (the
Green-width removal by Fatou in the spectral form, decision 8). -/
theorem wick_mass_bound (d : ℕ) (hB : SmoothedLaplaceTarget d) : WickMassBoundTarget d := by
  intro alpha α₀ Γ μ hH m n k hmn hk D hD
  refine ⟨ENNReal.ofReal ((kappa0 α₀ k ^ k)⁻¹) * Zhalf alpha α₀ μ ^ k,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.pow_lt_top ENNReal.ofReal_lt_top), fun ε hε => ?_⟩
  rcases hH.dim with rfl | rfl | rfl
  · exact wickL_zero_le_green hH PairingDampedNorms.greenDensity_one hmn hk hD hε
  · exact wickL_zero_le_green hH PairingDampedNorms.greenDensity_two hmn hk hD hε
  · exact wickL_zero_le_of_smoothed hH hB hmn hk hD hε fun η hη =>
      wickL_zero_le_three hH hη hmn hk hD hε

/-- **The uniform mass bound in d = 1, 2 with no hypothesis** (the green densities `green1`,
`green2`; a corollary, not a fallback: `wick_mass_bound` covers d = 3 with `hB`). -/
theorem wick_mass_bound_of_le_two {d : ℕ} (hd : d = 1 ∨ d = 2) : WickMassBoundTarget d := by
  intro alpha α₀ Γ μ hH m n k hmn hk D hD
  refine ⟨ENNReal.ofReal ((kappa0 α₀ k ^ k)⁻¹) * Zhalf alpha α₀ μ ^ k,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.pow_lt_top ENNReal.ofReal_lt_top), fun ε hε => ?_⟩
  rcases hd with rfl | rfl
  · exact wickL_zero_le_green hH PairingDampedNorms.greenDensity_one hmn hk hD hε
  · exact wickL_zero_le_green hH PairingDampedNorms.greenDensity_two hmn hk hD hε

end Mass

end StratonovichHAMSecondMoment.WickMass
