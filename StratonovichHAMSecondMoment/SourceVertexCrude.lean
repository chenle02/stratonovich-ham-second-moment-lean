module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L19, item L19-G: `L:vertex-crude` (Uniform vertexwise regularization bound), main TeX file
`notes/notes_stratonovich_ham_second_moment.tex`, statement lines 2062-2074 (`E:vertex-crude`
2065-2068, `E:vertex-summability` 2071-2073), proof lines 2076-2145, at revision edf7085f
(book 1.1.3).

Formalized:
* `vertex_diagram : VertexDiagramTarget d` (deterministic half, no supplied input): for every
  `H:homog` covariance there are `C > 0`, `θ₀ > 0` (chosen first) with
  `Σ_{D ∈ Π_n} F_{ε,δ,D}(t,t) ≤ q_n(t)²` for all `n ≥ 1`, `t > 0` and all positive vertexwise
  widths `ε, δ` on the `2n` vertices (the M8 diagrams `wickF (waveGreen d) Γ α₀ (capDom δ) ε n D t t`
  of `WickInterface`), `d = 1, 2, 3`;
* `vertex_crude : VertexCrudeTarget d` with C's `TerminalMixedMomentTarget d` and D's
  `FixedOrderL2Target d` as hypotheses (decision 9; discharged at integration): the bounds
  `‖Y_n^a(t,x)‖₂ ≤ q_n(t)` (`n ≥ 1`), `‖X_n(t,x)‖₂ ≤ q_n(t)` (`n ≥ 0`, `q_0 = e^{θ₀t}`) and
  `Σ_n √(n+1) q_n(T) < ∞` for every real `T`.

Route (TeX Steps 1-2, 2083-2145).  Step 1: per pairing, the horizon `ℓ_1, ℓ_2 < t` gives the
loss `e^{2θt}` against the damping `e^{-θΣr}` (`horizon_le_damped`; per pairing
`wickF_le_of_density`); the per-edge bridge M8 → M7 `WickBridge.m8_m7_bridge` with the per-edge data `WickInterface.wickEdge` (Laplace domain
`A_e = capSet (δ_j ∨ δ_h)`, spectral measure `e^{-(ε_j+ε_h)|ξ|²/2} μ`); the envelope
`PairingEnvelope.pairing_product_envelope` (`L:pairing-product-envelope`, which permits a
separate edge datum on each edge, TeX 2097-2098); the edge norms are uniform in all widths
because `A_e ⊆ (0,∞)` only lowers the norms (`PairingCapRemoval.nuE_mono`, `NC_mono_measure`:
`N1_le_smoothEdge`, `N2_le_smoothEdge`) and the norms of the uncapped edge with any Gaussian
weight obey `E:homogeneous-norms` (`HomogeneousEnvelope.norms_le_homog`, d = 1, 2;
`EnvelopeD3.norms_le_homog` for the Green-smoothed kernels, d = 3), whence
`F ≤ e^{2θt} (K θ^{-β})^n`, `β = 4 - α - α₀ > 2` (`prodP_le_of_edges`: an admissible product with
per-edge data).  In d = 3 the Green smoothing is removed at the fixed positive noise widths by
Fatou in the Green width (`JointTail.wickF_three_le_liminf`, any Laplace domains; the TeX says
"first with Green smoothing if d = 3", 2096-2097, and "Let the Green width tend to zero at these
fixed positive noise widths", 2133).  Step 2: `θ ≥ θ₀ = 1`, `θ^{-β} ≤ θ^{-2}`,
`θ = θ₀ + n/t`, `P_n n^{-2n} ≤ 2^n/n!` (`CrudeCorrected.card_Pi2_le`), `C = 2e²K`.  The
random-variable half: `‖Y_n^a‖² = E[Y_n^a Y_n^a] = Σ_D F(...)` (C's target at `b = a`, the
copied widths of TeX 2087-2088, reversed at 2093-2094, are positive), the joint-limit bound by continuity of
the norm along D's common-width limit (`stratInt`), `X_0 = 1` a.s. (`Ya_zero`).

Route differences (disclosed): the TeX bounds the square of `Y_n^a` through Wick's formula for
the source's fields; here that identity is C's frozen `TerminalMixedMomentTarget` (taken as a
hypothesis).  `E:vertex-summability` is proved by comparison with
`((1/2)^n + (4CT²)^n/n!)/2` (arithmetic-geometric mean) instead of the ratio test of TeX
2138-2143; it is stated for every real `T` (interface observation 4).  The TeX's closed Laplace
domain `[0, (δ_j∨δ_l)^{-1}]` and `γ^0_{δ_j∨δ_l}` (2090, 2101) are the half-open `capSet` of the
interface (a null difference, interface observation 3).
-/
public import Mathlib
public import StratonovichHAMSecondMoment.SourceInterface
public import StratonovichHAMSecondMoment.WickBridge
public import StratonovichHAMSecondMoment.WickSpectral
public import StratonovichHAMSecondMoment.JointTail
public import StratonovichHAMSecondMoment.EnvelopeD3
public import StratonovichHAMSecondMoment.CrudeCorrected
public import StratonovichHAMSecondMoment.PairingEnvelope

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal Real Nat

namespace StratonovichHAMSecondMoment.SourceVertexCrude

open HomogHypothesis (Rd HomogCovariance)
open WaveGreen (waveGreen)
open DiagramModel (Pi2 rev)
open TerminalWick (Pt prodL2)
open PairingInterface
open PairingBridge (smoothEdge)
open WickInterface
open SourceInterface
open HomogeneousEnvelope (Khom Khom_pos one_le_Khom)

universe u

variable {d : ℕ}

/-! ### Step 1: uniform edge norms and the per-pairing envelope -/

section Edges

variable {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)} (hH : HomogCovariance d alpha α₀ Γ μ)
include hH

/-- Restricting the Laplace domain to `A_e ⊆ (0,∞)` only lowers `N_{1,e}` (TeX 2108-2110: "the
spatial Gaussian multiplier and temporal truncation can only decrease its nonnegative spectral
integral"; only the truncation is removed here). -/
theorem N1_le_smoothEdge (E : EdgeData d) {b : ℝ} (hb : 0 < b) (hμ : E.μ = smoothSpec μ b)
    (G : Kernel d) : N1 α₀ E G ≤ N1 α₀ (smoothEdge hH hb) G := by
  unfold N1
  rw [hμ]
  exact lintegral_mono' (PairingCapRemoval.nuE_mono α₀ E.A_subset) le_rfl

/-- Restricting the Laplace domain to `A_e ⊆ (0,∞)` only lowers `N_{2,e}` (TeX 2110-2112). -/
theorem N2_le_smoothEdge (E : EdgeData d) {b : ℝ} (hb : 0 < b) (hμ : E.μ = smoothSpec μ b)
    (G : Kernel d) : N2 α₀ E G ≤ N2 α₀ (smoothEdge hH hb) G := by
  unfold N2
  rw [hμ]
  exact PairingCapRemoval.NC_mono_measure (PairingCapRemoval.nuE_mono α₀ E.A_subset) _ G

end Edges

/-- **An admissible product with per-edge data** (TeX 2097-2098 and 2125-2131): if every edge of
`D` has `N_0 · 2N_{1,e} ≤ Z` and `N_{2,e}² ≤ Z`, then `𝒫_{Q,ι} ≤ Z^{|D|}` (`q_0 = q_1`,
`q_0 + q_2/2 = |D|`). -/
theorem prodP_le_of_edges {α : Type*} [DecidableEq α] (a : ℝ) {L : Finset α}
    {D : Finset (Sym2 α)} (ed : Sym2 α → EdgeData d) (G : Kernel d) (A : Adm L D) {Z : ℝ≥0∞}
    (h1 : ∀ e ∈ D, N0 G * (2 * N1 a (ed e) G) ≤ Z) (h2 : ∀ e ∈ D, N2 a (ed e) G ^ 2 ≤ Z) :
    prodP a ed (fun _ => G) A ≤ Z ^ D.card := by
  have hc := HomogeneousEnvelope.two_card_Q1_add_card_Q2 A
  have hle : A.Q1.card ≤ D.card := by omega
  have hq : A.Q2.card = 2 * (D.card - A.Q1.card) := by omega
  have hP1 : (∏ _l ∈ A.Q0, N0 G) * ∏ l ∈ A.Q1, 2 * N1 a (ed (A.iota l)) G ≤ Z ^ A.Q1.card := by
    rw [Finset.prod_const, A.card01, ← Finset.prod_const (s := A.Q1) (N0 G),
      ← Finset.prod_mul_distrib]
    calc ∏ l ∈ A.Q1, N0 G * (2 * N1 a (ed (A.iota l)) G) ≤ ∏ _l ∈ A.Q1, Z :=
          Finset.prod_le_prod fun l hl => h1 _ (A.mapsTo l (Finset.mem_union_left _ hl))
      _ = Z ^ A.Q1.card := Finset.prod_const _
  have hsq : (∏ l ∈ A.Q2, N2 a (ed (A.iota l)) G) ^ 2 ≤ (Z ^ (D.card - A.Q1.card)) ^ 2 := by
    rw [← Finset.prod_pow, ← pow_mul, mul_comm, ← hq]
    calc ∏ l ∈ A.Q2, N2 a (ed (A.iota l)) G ^ 2 ≤ ∏ _l ∈ A.Q2, Z :=
          Finset.prod_le_prod fun l hl => h2 _ (A.mapsTo l (Finset.mem_union_right _ hl))
      _ = Z ^ A.Q2.card := Finset.prod_const _
  have hP2 : ∏ l ∈ A.Q2, N2 a (ed (A.iota l)) G ≤ Z ^ (D.card - A.Q1.card) := by
    by_contra hcon
    exact absurd hsq (not_le.2 (ENNReal.pow_lt_pow_left two_ne_zero (not_le.1 hcon)))
  unfold prodP
  calc (∏ _l ∈ A.Q0, N0 G) * (∏ l ∈ A.Q1, 2 * N1 a (ed (A.iota l)) G) *
        ∏ l ∈ A.Q2, N2 a (ed (A.iota l)) G
      ≤ Z ^ A.Q1.card * Z ^ (D.card - A.Q1.card) := mul_le_mul' hP1 hP2
    _ = Z ^ D.card := by rw [← pow_add, Nat.add_sub_cancel' hle]

/-- The horizon loss with damping `θ ≥ 0`: on `ℓ_1, ℓ_2 < t`,
`∫ f dρ ≤ e^{2θt} ∫ e^{-θΣr} f dρ` (TeX 2125-2131 with `E:theta-envelope` 2003-2006; the horizon loss as at
1996-1997). -/
theorem horizon_le_damped {N m : ℕ} {t θ : ℝ} (hθ : 0 ≤ θ) {ρ : Measure (Fin N → ℝ)}
    (f : (Fin N → ℝ) → ℝ≥0∞) :
    ∫⁻ r in horizon m t t, f r ∂ρ ≤ ENNReal.ofReal (Real.exp (2 * θ * t)) *
      ∫⁻ r, ENNReal.ofReal (Real.exp (-(θ * ∑ i, r i))) * f r ∂ρ := by
  have hHm := JointFixedOrder.measurableSet_horizon m (N := N) t t
  calc ∫⁻ r in horizon m t t, f r ∂ρ
      ≤ ∫⁻ r in horizon m t t, ENNReal.ofReal (Real.exp (2 * θ * t)) *
          (ENNReal.ofReal (Real.exp (-(θ * ∑ i, r i))) * f r) ∂ρ := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem hHm] with r hr
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        have hs := JointFixedOrder.sum_lt_of_mem_horizon hr
        have h1 : 1 ≤ Real.exp (2 * θ * t + -(θ * ∑ i, r i)) := Real.one_le_exp (by nlinarith)
        calc f r = 1 * f r := (one_mul _).symm
          _ ≤ _ := by
              gcongr
              rw [← ENNReal.ofReal_one]
              exact ENNReal.ofReal_le_ofReal h1
    _ ≤ ∫⁻ r, ENNReal.ofReal (Real.exp (2 * θ * t)) *
          (ENNReal.ofReal (Real.exp (-(θ * ∑ i, r i))) * f r) ∂ρ := setLIntegral_le_lintegral _ _
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

section Abstract

variable {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)} (hH : HomogCovariance d alpha α₀ Γ μ)
include hH

/-- **Step 1 for one pairing, any Green family with a finite density** (TeX 2083-2132): for the
M8 diagram with per-edge Laplace domains `A_e ⊆ (0,∞)` and positive vertexwise spatial widths,
`F_{ε,A,D}(t,t) ≤ e^{2θt} (K θ^{-β})^n` for `θ > 0`, provided the uncapped Gaussian-weighted
edge norms of the damped kernels obey `E:homogeneous-norms` with the constant `K = Khom`,
uniformly in the Gaussian width. -/
theorem wickF_le_of_density {G : ℝ → Measure (Rd d)} {g : Kernel d}
    (hg : Measurable (Function.uncurry g)) (hfin : ∀ s x, g s x ≠ ⊤)
    (hG : ∀ s, G s = volume.withDensity (g s))
    (hmeas : ∀ θ, Measurable (Function.uncurry (damp θ g)))
    (hN0 : ∀ θ : ℝ, 0 < θ → N0 (damp θ g) < ⊤)
    (hfin12 : ∀ θ : ℝ, 0 < θ → ∀ (b : ℝ) (hb : 0 < b),
      N1 α₀ (smoothEdge hH hb) (damp θ g) < ⊤ ∧ N2 α₀ (smoothEdge hH hb) (damp θ g) < ⊤)
    (hnorm : ∀ θ : ℝ, 0 < θ → ∀ (b : ℝ) (hb : 0 < b),
      N0 (damp θ g) * (2 * N1 α₀ (smoothEdge hH hb) (damp θ g)) ≤
          ENNReal.ofReal (Khom α₀ μ * θ ^ (-(4 - alpha - α₀))) ∧
        N2 α₀ (smoothEdge hH hb) (damp θ g) ^ 2 ≤
          ENNReal.ofReal (Khom α₀ μ * θ ^ (-(4 - alpha - α₀))))
    {n : ℕ} {D : Fin (n + n) → Fin (n + n)} (hD : D ∈ Pi2 n n) {ε : Fin (n + n) → ℝ}
    (hε : ∀ i, 0 < ε i) (A : Sym2 (Fin (n + n)) → Set ℝ) (hAm : ∀ e, MeasurableSet (A e))
    (hA0 : ∀ e, A e ⊆ Ioi 0) {t θ : ℝ} (hθ : 0 < θ) :
    wickF G Γ α₀ A ε n D t t ≤
      ENNReal.ofReal (Real.exp (2 * θ * t) * (Khom α₀ μ * θ ^ (-(4 - alpha - α₀))) ^ n) := by
  set Z := Khom α₀ μ * θ ^ (-(4 - alpha - α₀)) with hZ
  have hZ0 : 0 ≤ Z := by positivity [Khom_pos α₀ μ]
  set ed := wickEdge hH hε A hAm hA0 with hed
  have hb : ∀ e, 0 < edgeWidth ε e := edgeWidth_pos hε
  have hμe : ∀ e, (ed e).μ = smoothSpec μ (edgeWidth ε e) := fun e => wickEdge_μ _ _ _ _ _ _
  have h1 : ∀ e, N1 α₀ (ed e) (damp θ g) ≤ N1 α₀ (smoothEdge hH (hb e)) (damp θ g) := fun e =>
    N1_le_smoothEdge hH (ed e) (hb e) (hμe e) _
  have h2 : ∀ e, N2 α₀ (ed e) (damp θ g) ≤ N2 α₀ (smoothEdge hH (hb e)) (damp θ g) := fun e =>
    N2_le_smoothEdge hH (ed e) (hb e) (hμe e) _
  have hKH : KernelHyp α₀ (m4Chain n n D) ed (fun _ => damp θ g) :=
    ⟨fun _ _ => hmeas θ, fun _ _ => hN0 θ hθ,
      fun _ _ e _ => lt_of_le_of_lt (h1 e) (hfin12 θ hθ _ (hb e)).1,
      fun _ _ e _ => lt_of_le_of_lt (h2 e) (hfin12 θ hθ _ (hb e)).2⟩
  have henv : env α₀ (m4Chain n n D) ed (fun _ => damp θ g) ≤ ENNReal.ofReal Z ^ n := by
    refine iSup_le fun Aa => ?_
    have := prodP_le_of_edges α₀ ed (damp θ g) Aa (Z := ENNReal.ofReal Z)
      (fun e _ => (mul_le_mul' le_rfl (mul_le_mul' le_rfl (h1 e))).trans (hnorm θ hθ _ (hb e)).1)
      (fun e _ => (pow_le_pow_left₀ zero_le (h2 e) 2).trans (hnorm θ hθ _ (hb e)).2)
    rwa [PairingBridge.card_D_m4Chain hD (two_mul n).symm] at this
  calc wickF G Γ α₀ A ε n D t t
      ≤ ENNReal.ofReal (Real.exp (2 * θ * t)) *
          ∫⁻ r, ENNReal.ofReal (Real.exp (-(θ * ∑ i, r i))) * pairTime α₀ A n D r
            ∂wickRho G Γ ε n D := horizon_le_damped hθ.le _
    _ ≤ ENNReal.ofReal (Real.exp (2 * θ * t)) *
          pairingIntegral α₀ (m4Chain n n D) ed (fun _ => damp θ g) := by
        gcongr
        exact WickBridge.m8_m7_bridge d hH G g hg hfin hG n n D hD ε hε A hAm hA0 θ hθ.le
    _ ≤ ENNReal.ofReal (Real.exp (2 * θ * t)) * env α₀ (m4Chain n n D) ed (fun _ => damp θ g) := by
        gcongr
        exact PairingEnvelope.pairing_product_envelope d (Fin (n + n)) α₀ hH.alpha0_pos
          hH.alpha0_lt_one _ _ _ (m4Chain_wf hD) hKH
    _ ≤ ENNReal.ofReal (Real.exp (2 * θ * t)) * ENNReal.ofReal Z ^ n := by gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_pow hZ0, ← ENNReal.ofReal_mul (Real.exp_pos _).le]

end Abstract

/-- **Step 1 for one pairing, `d = 1, 2, 3`, for the wave Green measures** (TeX 2083-2132, the
Green-width removal of d = 3 at 2133): under `H:homog`,
`F_{ε,A,D}(t,t) ≤ e^{2θt} (K θ^{-β})^n` for every pairing `D ∈ Π_n`, `n ≥ 1`, every per-edge
Laplace domains `A_e ⊆ (0,∞)` (in particular `capDom δ`), all positive vertexwise spatial widths,
`θ > 0`; `K = Khom` depends only on `α₀` and `μ`. -/
theorem wickF_le_homog {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha α₀ Γ μ) {n : ℕ} (hn : 1 ≤ n) {D : Fin (n + n) → Fin (n + n)}
    (hD : D ∈ Pi2 n n) {ε : Fin (n + n) → ℝ} (hε : ∀ i, 0 < ε i) (A : Sym2 (Fin (n + n)) → Set ℝ)
    (hAm : ∀ e, MeasurableSet (A e)) (hA0 : ∀ e, A e ⊆ Ioi 0) {t θ : ℝ} (hθ : 0 < θ) :
    wickF (waveGreen d) Γ α₀ A ε n D t t ≤
      ENNReal.ofReal (Real.exp (2 * θ * t) * (Khom α₀ μ * θ ^ (-(4 - alpha - α₀))) ^ n) := by
  have hden : ∀ {g : Kernel d}, PairingDampedNorms.GreenDensity d g →
      wickF (waveGreen d) Γ α₀ A ε n D t t ≤
        ENNReal.ofReal (Real.exp (2 * θ * t) * (Khom α₀ μ * θ ^ (-(4 - alpha - α₀))) ^ n) := by
    intro g hgd
    refine wickF_le_of_density hH hgd.meas hgd.fin hgd.eq hgd.measurable_damp
      (fun θ hθ => by rw [PairingDampedNorms.N0_damp hgd hθ]; exact ENNReal.ofReal_lt_top)
      (fun θ hθ b hb => ⟨?_, ?_⟩) (fun θ hθ b hb =>
          HomogeneousEnvelope.norms_le_homog hgd hH hb hθ) hD hε A hAm hA0 hθ
    · exact lt_of_le_of_lt (PairingDampedNorms.N1_damp_le hgd hH hb hθ) ENNReal.ofReal_lt_top
    · have h := lt_of_le_of_lt (PairingDampedNorms.N2_damp_sq_le hgd hH hb hθ)
        ENNReal.ofReal_lt_top
      refine lt_top_iff_ne_top.2 fun htop => ?_
      rw [htop] at h
      simp at h
  rcases hH.dim with rfl | rfl | rfl
  · exact hden PairingDampedNorms.greenDensity_one
  · exact hden PairingDampedNorms.greenDensity_two
  · -- d = 3: the Green-smoothed kernels, uniformly in the Green width, then Fatou
    have hsm : ∀ η' : ℝ, 0 < η' → wickF (greenS 3 η') Γ α₀ A ε n D t t ≤
        ENNReal.ofReal (Real.exp (2 * θ * t) * (Khom α₀ μ * θ ^ (-(4 - alpha - α₀))) ^ n) := by
      intro η' hη'
      have hgd := EnvelopeD3.smoothDensity_three hη'
      refine wickF_le_of_density hH hgd.meas hgd.fin hgd.eq hgd.measurable_damp
        (fun θ hθ => by rw [PairingSmoothedNorms.N0_damp hgd hθ]; exact ENNReal.ofReal_lt_top)
        (fun θ hθ b hb => ⟨?_, ?_⟩) (fun θ hθ b hb => EnvelopeD3.norms_le_homog hgd hH hb hθ)
        hD hε A hAm hA0 hθ
      · exact lt_of_le_of_lt (PairingSmoothedNorms.N1_damp_le hgd hH hb hθ) ENNReal.ofReal_lt_top
      · have h := lt_of_le_of_lt (PairingSmoothedNorms.N2_damp_sq_le hgd hH hb hθ)
          ENNReal.ofReal_lt_top
        refine lt_top_iff_ne_top.2 fun htop => ?_
        rw [htop] at h
        simp at h
    refine (JointTail.wickF_three_le_liminf hH (WickSpectral.spectral_spatial_w 3)
      (k := n) (two_mul n).symm hn hD hε A t t).trans ?_
    refine Filter.liminf_le_of_frequently_le' (Eventually.frequently ?_)
    filter_upwards [self_mem_nhdsWithin] with η' hη' using hsm η' hη'

/-! ### Step 2: the factorial bound -/

/-- `q_n(t)² = e^{2θ₀t} C^n t^{2n} / n!` (TeX 2067). -/
theorem qn_sq {C : ℝ} (hC : 0 ≤ C) (θ₀ : ℝ) (n : ℕ) (t : ℝ) :
    qn C θ₀ n t ^ 2 = Real.exp (2 * θ₀ * t) * C ^ n * t ^ (2 * n) / (n ! : ℝ) := by
  unfold qn
  rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), ← pow_mul, mul_comm n 2,
    pow_mul, Real.sq_sqrt hC, ← pow_mul, ← Real.exp_nat_mul]
  push_cast
  ring_nf

/-- **Step 2 arithmetic** (TeX 2125-2135): `P_n e^{2θt} (K θ^{-β})^n ≤ e^{2t} (2e²K)^n t^{2n}/n!`
at `θ = 1 + n/t`, for `β ≥ 2`, `K > 0`, `n ≥ 1`, `t > 0`. -/
theorem step2_le {K β : ℝ} (hK : 0 < K) (hβ : 2 ≤ β) {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 0 < t) :
    ((Pi2 n n).card : ℝ) * (Real.exp (2 * (1 + n / t) * t) * (K * (1 + n / t) ^ (-β)) ^ n) ≤
      Real.exp (2 * 1 * t) * (2 * Real.exp 2 * K) ^ n * t ^ (2 * n) / (n ! : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnt : 0 < (n : ℝ) / t := by positivity
  set θ := 1 + n / t with hθdef
  have hθ1 : 1 ≤ θ := by linarith
  have hθ0 : 0 < θ := by linarith
  have hexp : Real.exp (2 * θ * t) = Real.exp (2 * 1 * t) * Real.exp 2 ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, hθdef]
    congr 1
    field_simp
  have hθpow : θ ^ (-β) ≤ t ^ 2 / (n : ℝ) ^ 2 := by
    calc θ ^ (-β) ≤ θ ^ (-(2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hθ1 (by linarith)
      _ ≤ ((n : ℝ) / t) ^ (-(2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hnt (by linarith) (by norm_num)
      _ = t ^ 2 / (n : ℝ) ^ 2 := by
          rw [Real.rpow_neg hnt.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
            div_pow, inv_div]
  have hKθ : (K * θ ^ (-β)) ^ n ≤ K ^ n * t ^ (2 * n) / (n : ℝ) ^ (2 * n) := by
    calc (K * θ ^ (-β)) ^ n ≤ (K * (t ^ 2 / (n : ℝ) ^ 2)) ^ n :=
          pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hθpow hK.le) n
      _ = K ^ n * t ^ (2 * n) / (n : ℝ) ^ (2 * n) := by rw [mul_pow, div_pow, ← pow_mul,
            ← pow_mul, mul_div_assoc]
  have hcard := CrudeCorrected.card_Pi2_le n
  have hf : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  have hnn : (0 : ℝ) < (n : ℝ) ^ (2 * n) := by positivity
  rw [hexp]
  calc ((Pi2 n n).card : ℝ) * (Real.exp (2 * 1 * t) * Real.exp 2 ^ n * (K * θ ^ (-β)) ^ n)
      ≤ (2 ^ n * (n : ℝ) ^ (2 * n) / n !) * (Real.exp (2 * 1 * t) * Real.exp 2 ^ n *
          (K ^ n * t ^ (2 * n) / (n : ℝ) ^ (2 * n))) := by gcongr
    _ = Real.exp (2 * 1 * t) * (2 * Real.exp 2 * K) ^ n * t ^ (2 * n) / (n ! : ℝ) := by
        field_simp
        ring

/-- **`L:vertex-crude`, deterministic half** (`VertexDiagramTarget d`; TeX lines 2062-2068 and
proof Steps 1-2, 2083-2135, at revision edf7085f (book 1.1.3)), with no supplied input: under
`H:homog` there are `C, θ₀ > 0`, chosen before `n`, `t` and the widths, such that
`Σ_{D ∈ Π_n} F_{ε,δ,D}(t,t) ≤ q_n(t)²` for all `n ≥ 1`, `t > 0` and all positive vertexwise
widths `ε, δ` on the `2n` vertices (interface observation 6: arbitrary widths, not only copied
ones; the bound holds for any Laplace domains `A_e ⊆ (0,∞)`).  `θ₀ = 1`, `C = 2e²K`,
`K = Khom α₀ μ`. -/
theorem vertex_diagram (d : ℕ) : VertexDiagramTarget d := by
  intro alpha α₀ Γ μ hH
  set K := Khom α₀ μ with hKdef
  have hK := Khom_pos α₀ μ
  have hβ : 2 ≤ 4 - alpha - α₀ := by linarith [hH.threshold]
  refine ⟨2 * Real.exp 2 * K, 1, by positivity, one_pos, fun n hn t ht ε δ hε _ => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set θ := 1 + n / t with hθdef
  have hθ0 : 0 < θ := by positivity
  have hAm : ∀ e, MeasurableSet (capDom δ e) := fun e => measurableSet_capSet _
  have hA0 : ∀ e, capDom δ e ⊆ Ioi 0 := fun e => capSet_subset_Ioi _
  rw [qn_sq (by positivity)]
  calc ∑ D ∈ Pi2 n n, wickF (waveGreen d) Γ α₀ (capDom δ) ε n D t t
      ≤ ∑ _D ∈ Pi2 n n, ENNReal.ofReal (Real.exp (2 * θ * t) *
          (K * θ ^ (-(4 - alpha - α₀))) ^ n) :=
        Finset.sum_le_sum fun D hD => wickF_le_homog hH hn hD hε _ hAm hA0 hθ0
    _ = ENNReal.ofReal ((Pi2 n n).card * (Real.exp (2 * θ * t) *
          (K * θ ^ (-(4 - alpha - α₀))) ^ n)) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (step2_le hK hβ hn ht)

/-! ### The random-variable half -/

section RV

/-- `‖f‖² = E[f f]` in `L²(P)`. -/
theorem norm_sq_eq_integral {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (f : Lp ℝ 2 P) :
    ‖f‖ ^ 2 = ∫ ω, (f : Ω → ℝ) ω * (f : Ω → ℝ) ω ∂P := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  simp [sq]

/-- **`E:vertex-summability`** (TeX 2071-2073 and 2138-2143): `Σ_n √(n+1) q_n(T) < ∞` for every
real `T`; by `√(n+1) ≤ √2^n` and the arithmetic-geometric mean
`√((4CT²)^n/n! · 2^{-n}) ≤ ((1/2)^n + (4CT²)^n/n!)/2` (route difference: comparison instead of the
ratio test). -/
theorem summable_sqrt_qn {C : ℝ} (hC : 0 ≤ C) (θ₀ T : ℝ) :
    Summable fun n : ℕ => Real.sqrt ((n : ℝ) + 1) * qn C θ₀ n T := by
  set z := 4 * C * T ^ 2 with hz
  have hz0 : 0 ≤ z := by positivity
  refine Summable.of_norm_bounded ((((summable_geometric_two).add
    (Real.summable_pow_div_factorial z)).div_const 2).mul_left (Real.exp (θ₀ * T))) fun n => ?_
  have hf : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  have hs : 0 ≤ Real.sqrt (n ! : ℝ) := Real.sqrt_nonneg _
  -- `√(n+1) ≤ √2^n`
  have h2n : Real.sqrt ((n : ℝ) + 1) ≤ Real.sqrt 2 ^ n := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]
    have : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
    exact_mod_cast this
  -- the AM-GM step
  have hamgm : Real.sqrt 2 ^ n * Real.sqrt C ^ n * |T| ^ n / Real.sqrt (n ! : ℝ) ≤
      ((1 / 2 : ℝ) ^ n + z ^ n / (n ! : ℝ)) / 2 := by
    set X := Real.sqrt 2 ^ n * Real.sqrt C ^ n * |T| ^ n / Real.sqrt (n ! : ℝ) with hX
    set a := (1 / 2 : ℝ) ^ n with ha
    set b := z ^ n / (n ! : ℝ) with hb
    have hX0 : 0 ≤ X := by positivity
    have ha0 : 0 ≤ a := by positivity
    have hb0 : 0 ≤ b := by positivity
    have hc : (Real.sqrt 2 * Real.sqrt C * |T|) ^ 2 = 1 / 2 * z := by
      rw [hz, mul_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hC, sq_abs]; ring
    have hX2 : X ^ 2 = a * b := by
      rw [hX, ha, hb, ← mul_pow, ← mul_pow, div_pow, Real.sq_sqrt hf.le, ← pow_mul,
        mul_comm n 2, pow_mul, hc, mul_div_assoc', ← mul_pow]
    have h4 : (2 * X) ^ 2 ≤ (a + b) ^ 2 := by nlinarith [sq_nonneg (a - b)]
    have h5 := (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 h4
    linarith
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  unfold qn
  rw [abs_div, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_pow, abs_pow,
    abs_of_nonneg (Real.sqrt_nonneg C), abs_of_nonneg hs]
  calc Real.sqrt ((n : ℝ) + 1) * (Real.exp (θ₀ * T) * Real.sqrt C ^ n * |T| ^ n /
        Real.sqrt (n ! : ℝ))
      ≤ Real.sqrt 2 ^ n * (Real.exp (θ₀ * T) * Real.sqrt C ^ n * |T| ^ n /
          Real.sqrt (n ! : ℝ)) := by gcongr
    _ = Real.exp (θ₀ * T) * (Real.sqrt 2 ^ n * Real.sqrt C ^ n * |T| ^ n /
          Real.sqrt (n ! : ℝ)) := by ring
    _ ≤ Real.exp (θ₀ * T) * (((1 / 2 : ℝ) ^ n + z ^ n / (n ! : ℝ)) / 2) := by gcongr

/-- **`L:vertex-crude`** (`VertexCrudeTarget d`; TeX lines 2062-2074, proof 2076-2145, at
revision edf7085f (book 1.1.3)), with C's `TerminalMixedMomentTarget d` and D's
`FixedOrderL2Target d` as hypotheses (decision 9; discharged at integration): under `H:homog`
there are `C, θ₀ > 0` such that, for every source field, `‖Y_n^a(t,x)‖₂ ≤ q_n(t)` for `n ≥ 1`
and all positive vertexwise widths `a` (`‖Y_n^a‖² = Σ_D F(...)` at the reversed copied widths,
C's target with `b = a`, and `vertex_diagram`), `‖X_n(t,x)‖₂ ≤ q_n(t)` for every `n`
(`X_0 = 1` a.s., `q_0 = e^{θ₀t} ≥ 1`; for `n ≥ 1` by continuity of the norm along D's
common-width limit), and `Σ_n √(n+1) q_n(T) < ∞` for every `T` (`summable_sqrt_qn`). -/
theorem vertex_crude (d : ℕ) (hM : TerminalMixedMomentTarget.{u} d)
    (hX : FixedOrderL2Target.{u} d) : VertexCrudeTarget.{u} d := by
  intro alpha α₀ Γ μ hH
  obtain ⟨C, θ₀, hC, hθ₀, hdiag⟩ := vertex_diagram d hH
  have hYa : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (W : SrcPt d → Ω → ℝ) (hW : SourceField α₀ Γ P W) (t : ℝ) (ht : 0 < t) (x : Rd d)
      (n : ℕ), 1 ≤ n → ∀ a : Fin n → PosW, ‖Ya hW t ht.le x a‖ ≤ qn C θ₀ n t := by
    intro Ω _ P _ W hW t ht x n hn a
    obtain ⟨-, hEq⟩ := hM hH P W hW t ht x n n a a
    have hε : ∀ i, 0 < epsV a a (rev n n i) := fun i => PosW.eps_pos _
    have hδ : ∀ i, 0 < delV a a (rev n n i) := fun i => PosW.del_pos _
    have hS := hdiag n hn t ht (fun i => epsV a a (rev n n i)) (fun i => delV a a (rev n n i))
      hε hδ
    have hfin : ∀ D ∈ Pi2 n n, wickF (waveGreen d) Γ α₀ (capDom fun i => delV a a (rev n n i))
        (fun i => epsV a a (rev n n i)) n D t t ≠ ⊤ := fun D hD =>
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        ((Finset.single_le_sum (fun _ _ => zero_le) hD).trans hS)
    have hsq : ‖Ya hW t ht.le x a‖ ^ 2 ≤ qn C θ₀ n t ^ 2 := by
      rw [norm_sq_eq_integral, hEq, ← ENNReal.toReal_sum hfin]
      exact ENNReal.toReal_le_of_le_ofReal (sq_nonneg _) hS
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (qn_nonneg ht.le n) two_ne_zero).1 hsq
  refine ⟨C, θ₀, hC, hθ₀, hYa, ?_, fun T => summable_sqrt_qn hC.le θ₀ T⟩
  intro Ω _ P _ W hW t ht x n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `X_0 = 1` almost surely
    rw [XL2_zero, qn_zero]
    have h1 : ‖Ya hW t ht.le x (Fin.elim0 : Fin 0 → PosW)‖ = 1 := by
      rw [Lp.norm_def, eLpNorm_congr_ae (Ya_zero hH.dim hW t ht.le x _),
        eLpNorm_const _ (by norm_num) (IsProbabilityMeasure.ne_zero P)]
      simp
    rw [h1]
    exact Real.one_le_exp (by positivity)
  · -- `X_n` is the common-width limit of `Y_n^{(ε,δ)}`
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [XL2_succ]
    have hlim := (hX hH P W hW t ht x (k + 1) hn).2
    refine le_of_tendsto hlim.norm (Eventually.of_forall fun p => ?_)
    exact hYa P W hW t ht x (k + 1) hn _

end RV

end StratonovichHAMSecondMoment.SourceVertexCrude
