module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L18, item L18-C, part 1: the per-edge bridge from the Wick-measure model M8
(`WickInterface`) to the label-set pairing integral `I_D` of M7 (`PairingInterface`), the frozen
target `WickInterface.M8M7BridgeTarget` (TeX lines 1905-1911 at revision edf7085f (book 1.1.3):
the envelope applied to the damped kernels `e^{-θs} G_s`, each spatial edge measure
Gaussian-weighted, each temporal domain a Laplace interval or its restriction).

Formalized (all proved, nothing supplied):
* `wickJ_eq_of_density`: for Green measures with a finite measurable density `g`, `J_{ε,D}(r)` in
  position variables, `∫ ∏_l g(r_l, y_l - y_{p(l)}) ∏_{{j,h}} γ_{ε_j+ε_h}(y_j - y_h) dy`
  (main TeX lines 1666-1669 with 5338-5341), with vertexwise widths; `measurable_wickJ'`;
* `incrEquiv`, `measurePreserving_incr`: the time change of variables `s ↦ (s_l - s_{p(l)})_l`
  (inverse `gapTime`) preserves Lebesgue measure;
* `m8_m7_bridge` (`M8M7BridgeTarget d`): `∫ e^{-θΣr} ∏ κ_{A_e}(s_j - s_h) dρ_{ε,D} ≤
  I_D(e^{-θ·} g)` with the per-edge data `wickEdge` (it is an identity; only `≤` is proved, by
  the substitution `r = incr s` and Tonelli in the direction that needs no measurability).

This extends L17's `PairingBridge.diagram_le_pairingIntegral` (constant edge datum, `A = (0,∞)`)
to per-edge widths and Laplace domains; it reuses L17's `pi_withDensity`,
`measurePreserving_incrOfPos_d`, `m4Chain_predTime`, `m4Chain_predPos`, `prod_edges_m4Chain`,
`labels_m4Chain`, `pairingIntegral_m4Chain_eq` and the interface's `gapTime_incr`.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.WickInterface
public import StratonovichHAMSecondMoment.LowAlphaUpper
public import StratonovichHAMSecondMoment.PairingCapRemoval

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal Real

namespace StratonovichHAMSecondMoment.WickBridge

open HomogHypothesis (Rd HomogCovariance)
open DiagramModel (Pi2 pred predVal incr openers covEps pos)
open DiagramBridge (incrOfPos pos_incrOfPos)
open PairingInterface
open PairingBridge
open WickInterface

variable {d : ℕ}

/-! ### The spatial part with a Green density -/

section Density

variable {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}

/-- The vertexwise covariance product is measurable (positive widths). -/
theorem measurable_covW (hH : HomogCovariance d alpha α₀ Γ μ) {N : ℕ} {ε : Fin N → ℝ}
    (hε : ∀ i, 0 < ε i) (D : Fin N → Fin N) : Measurable (covW Γ ε D) := by
  unfold covW
  exact Finset.measurable_prod _ fun i _ =>
    (LowAlphaUpper.measurable_covEps hH (add_pos (hε i) (hε (D i)))).comp
      ((measurable_pi_apply i).sub (measurable_pi_apply (D i)))

/-- The position form of `J_{ε,D}(r)` for a Green density (the integrand of the bridge). -/
def wickJ' (g : Kernel d) (Γ : Measure (Rd d)) {N : ℕ} (ε : Fin N → ℝ) (m : ℕ)
    (D : Fin N → Fin N) (r : Fin N → ℝ) : ℝ≥0∞ :=
  ∫⁻ y, (∏ i, g (r i) (incrOfPos m y i)) * covW Γ ε D y

/-- **`J_{ε,D}` with a Green density in position variables** (TeX 1666-1669 with main TeX lines
5338-5341): for Green measures `G_s = g(s,·) dy` with a finite measurable density,
`J_{ε,D}(r) = ∫ ∏_l g(r_l, y_l - y_{p(l)}) ∏_{{j,h}} γ_{ε_j+ε_h}(y_j - y_h) dy`. -/
theorem wickJ_eq_of_density (hH : HomogCovariance d alpha α₀ Γ μ) (G : ℝ → Measure (Rd d))
    (g : Kernel d) (hg : Measurable (Function.uncurry g)) (hfin : ∀ s x, g s x ≠ ∞)
    (hG : ∀ s, G s = volume.withDensity (g s)) {N : ℕ} {ε : Fin N → ℝ} (hε : ∀ i, 0 < ε i)
    (m : ℕ) (D : Fin N → Fin N) (r : Fin N → ℝ) :
    wickJ G Γ ε m D r = wickJ' g Γ ε m D r := by
  have hgs : ∀ s, Measurable (g s) := fun s => hg.comp (measurable_const.prodMk measurable_id)
  unfold wickJ wickJ'
  simp_rw [hG]
  rw [pi_withDensity volume (fun i => g (r i)) (fun i => hgs (r i)) (fun i x => hfin (r i) x)]
  have hmeas : Measurable fun w : Fin N → Rd d => ∏ i, g (r i) (w i) :=
    Finset.measurable_prod _ fun i _ => (hgs (r i)).comp (measurable_pi_apply i)
  have hcp : Measurable fun w : Fin N → Rd d => covW Γ ε D (pos m w) :=
    (measurable_covW hH hε D).comp (DiagramBridge.posEquiv m d N).measurable
  rw [lintegral_withDensity_eq_lintegral_mul _ hmeas hcp]
  change ∫⁻ a, ((fun w : Fin N → Rd d => ∏ i, g (r i) (w i)) *
    fun w : Fin N → Rd d => covW Γ ε D (pos m w)) a ∂(volume : Measure (Fin N → Rd d)) = _
  conv_lhs => rw [← (measurePreserving_incrOfPos_d m N d).lintegral_comp_emb
    (DiagramBridge.posEquiv m d N).symm.measurableEmbedding]
  refine lintegral_congr fun y => ?_
  simp only [Pi.mul_apply]
  rw [pos_incrOfPos]

/-- The position form of `J` is measurable in the gaps. -/
theorem measurable_wickJ' (hH : HomogCovariance d alpha α₀ Γ μ) (g : Kernel d)
    (hg : Measurable (Function.uncurry g)) {N : ℕ} {ε : Fin N → ℝ} (hε : ∀ i, 0 < ε i)
    (m : ℕ) (D : Fin N → Fin N) : Measurable (wickJ' g Γ ε m D) := by
  have hgi : ∀ i : Fin N, Measurable fun p : (Fin N → ℝ) × (Fin N → Rd d) =>
      g (p.1 i) (incrOfPos m p.2 i) := by
    intro i
    have hpair : Measurable fun p : (Fin N → ℝ) × (Fin N → Rd d) => (p.1 i, incrOfPos m p.2 i) :=
      ((measurable_pi_apply i).comp measurable_fst).prodMk
        (((measurable_pi_apply i).comp (DiagramBridge.measurable_incrOfPos m)).comp measurable_snd)
    exact hg.comp hpair
  have h : Measurable fun p : (Fin N → ℝ) × (Fin N → Rd d) =>
      (∏ i, g (p.1 i) (incrOfPos m p.2 i)) * covW Γ ε D p.2 :=
    (Finset.measurable_prod _ fun i _ => hgi i).mul ((measurable_covW hH hε D).comp measurable_snd)
  exact h.lintegral_prod_right'

end Density

/-! ### The time change of variables -/

/-- The open orthant is measurable. -/
theorem measurableSet_posOrthant (N : ℕ) : MeasurableSet (posOrthant N) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioi

/-- The cumulative times are measurable in the gaps. -/
theorem measurable_gapTime (m : ℕ) {N : ℕ} : Measurable (gapTime m (N := N)) :=
  measurable_pi_iff.2 fun _ => Finset.measurable_sum _ fun j _ => measurable_pi_apply j

/-- The increments map `s ↦ (s_l - s_{p(l)})_l` as a measurable equivalence (inverse:
`gapTime`). -/
def incrEquiv (m N : ℕ) : (Fin N → ℝ) ≃ᵐ (Fin N → ℝ) where
  toFun := incr m
  invFun := gapTime m
  left_inv := gapTime_incr m
  right_inv := incr_gapTime m
  measurable_toFun := DiagramModel.measurable_incr m
  measurable_invFun := measurable_gapTime m

/-- **The time increments preserve Lebesgue measure** (determinant one). -/
theorem measurePreserving_incr (m N : ℕ) :
    MeasurePreserving (incr m (N := N)) volume volume := by
  have h : incr m (N := N) = ⇑(Matrix.toLin' (DiagramBridge.incrMatrix m N)) := by
    funext s
    rw [Matrix.toLin'_apply, DiagramBridge.incrMatrix_mulVec]
    rfl
  rw [h]
  exact DiagramBridge.measurePreserving_incrMatrix m N

/-! ### The bridge -/

section Bridge

variable {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}

/-- Auxiliary: a product of exponentials of `-θ x_i` is the exponential of `-θ Σ x_i`. -/
theorem prod_ofReal_exp (θ : ℝ) {N : ℕ} (x : Fin N → ℝ) :
    ∏ i, ENNReal.ofReal (Real.exp (-(θ * x i))) = ENNReal.ofReal (Real.exp (-(θ * ∑ i, x i))) := by
  rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => (Real.exp_pos _).le, ← Real.exp_sum]
  congr 2
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]

/-- The pointwise comparison at `r = incr s`: the M8 integrand is the M7 integrand. -/
theorem integrand_eq (hH : HomogCovariance d alpha α₀ Γ μ) (g : Kernel d) {m n : ℕ}
    {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n) {ε : Fin (m + n) → ℝ}
    (hε : ∀ i, 0 < ε i) (A : Sym2 (Fin (m + n)) → Set ℝ) (hAm : ∀ e, MeasurableSet (A e))
    (hA0 : ∀ e, A e ⊆ Ioi 0) (θ : ℝ) (s : Fin (m + n) → ℝ) (y : Fin (m + n) → Rd d) :
    (posOrthant (m + n)).indicator (fun r => ENNReal.ofReal (Real.exp (-(θ * ∑ i, r i))) *
        pairTime α₀ A m D r) (incr m s) *
      ((∏ i, g (incr m s i) (incrOfPos m y i)) * covW Γ ε D y) ≤
    integrand α₀ (m4Chain m n D) (wickEdge hH hε A hAm hA0) (fun _ => damp θ g)
      (fun i => (s i, y i)) := by
  by_cases hs : incr m s ∈ posOrthant (m + n)
  · rw [Set.indicator_of_mem hs]
    have hz : (fun i => (s i, y i)) ∈ (m4Chain m n D).posSimplex := by
      intro l _
      rw [m4Chain_predTime]
      have := hs l (Set.mem_univ l)
      simp only [mem_Ioi, incr] at this
      simp only
      linarith
    unfold integrand
    rw [Set.indicator_of_mem hz, labels_m4Chain, prod_edges_m4Chain hD]
    simp only [m4Chain_predTime, m4Chain_predPos, edgeWeight_mk]
    have hedge : ∏ i ∈ openers D, kappa α₀ (wickEdge hH hε A hAm hA0 s(i, D i)) (s i - s (D i)) *
        gammaOf (wickEdge hH hε A hAm hA0 s(i, D i)).μ (y i - y (D i)) =
        pairTime α₀ A m D (incr m s) * covW Γ ε D y := by
      rw [pairTime, covW, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [kappa_wickEdge, gammaOf_wickEdge, gapTime_incr]
      rfl
    rw [hedge]
    have hdamp : ∏ i, damp θ g (s i - predVal m (fun j => s j) i)
        (y i - predVal m (fun j => y j) i) =
        (∏ i, ENNReal.ofReal (Real.exp (-(θ * incr m s i)))) *
          ∏ i, g (incr m s i) (incrOfPos m y i) := by
      rw [← Finset.prod_mul_distrib]
      rfl
    rw [hdamp, prod_ofReal_exp]
    apply le_of_eq
    ring
  · rw [Set.indicator_of_notMem hs, zero_mul]
    exact zero_le

/-- **The per-edge bridge M8 → M7** (`M8M7BridgeTarget`; TeX lines 1905-1911 at revision edf7085f
(book 1.1.3)): for a Green family with a finite jointly measurable density `g`, every pairing,
positive vertexwise widths, per-edge Laplace domains `A_e ⊆ (0,∞)` and `θ ≥ 0`,
`∫ e^{-θΣr} ∏_{{j,h}} κ_{A_{jh}}(s_j - s_h) dρ_{ε,D} ≤ I_D(e^{-θ·} g)` with the per-edge data
`wickEdge` (`A_e`, `e^{-(ε_j+ε_h)|ξ|²/2} μ`), by the substitution `r = incr s` (determinant one),
the position form of `J` and Tonelli.  (Equality holds; only `≤` is proved and used.) -/
theorem m8_m7_bridge (d : ℕ) : M8M7BridgeTarget d := by
  intro alpha α₀ Γ μ hH G g hg hfin hG m n D hD ε hε A hAm hA0 θ _hθ
  set F : (Fin (m + n) → ℝ) → ℝ≥0∞ := fun r =>
    ENNReal.ofReal (Real.exp (-(θ * ∑ i, r i))) * pairTime α₀ A m D r with hF
  have hJ : wickJ G Γ ε m D = wickJ' g Γ ε m D :=
    funext fun r => wickJ_eq_of_density hH G g hg hfin hG hε m D r
  have hmJ := measurable_wickJ' hH g hg (Γ := Γ) hε m D
  -- the M8 side as a Lebesgue integral over the orthant
  have h1 : ∫⁻ r, F r ∂wickRho G Γ ε m D ≤
      ∫⁻ r, (posOrthant (m + n)).indicator (fun r => wickJ' g Γ ε m D r * F r) r := by
    unfold wickRho
    rw [hJ]
    refine (lintegral_withDensity_le_lintegral_mul _ hmJ F).trans (le_of_eq ?_)
    rw [← lintegral_indicator (measurableSet_posOrthant (m + n))]
    rfl
  -- the substitution `r = incr s`
  have h2 : ∫⁻ r, (posOrthant (m + n)).indicator (fun r => wickJ' g Γ ε m D r * F r) r =
      ∫⁻ s, (posOrthant (m + n)).indicator (fun r => wickJ' g Γ ε m D r * F r) (incr m s) :=
    ((measurePreserving_incr m (m + n)).lintegral_comp_emb
      (incrEquiv m (m + n)).measurableEmbedding _).symm
  -- the M7 side
  have h3 : pairingIntegral α₀ (m4Chain m n D) (wickEdge hH hε A hAm hA0) (fun _ => damp θ g) ≥
      ∫⁻ s : Fin (m + n) → ℝ, ∫⁻ y : Fin (m + n) → Rd d,
        integrand α₀ (m4Chain m n D) (wickEdge hH hε A hAm hA0) (fun _ => damp θ g)
          (fun i => (s i, y i)) := by
    rw [pairingIntegral_m4Chain_eq, Measure.volume_eq_prod]
    have hdm : Measurable (Function.uncurry (damp θ g)) := by
      have : Function.uncurry (damp θ g) = fun p : ℝ × Rd d =>
          ENNReal.ofReal (Real.exp (-(θ * p.1))) * Function.uncurry g p := rfl
      rw [this]
      exact (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        ((measurable_const.mul measurable_fst).neg))).mul hg
    have hmi := PairingCapRemoval.measurable_integrand α₀ (m4Chain m n D)
      (wickEdge hH hε A hAm hA0) (fun _ => damp θ g) (fun _ _ => hdm)
    have hcomp : Measurable fun p : (Fin (m + n) → ℝ) × (Fin (m + n) → Rd d) =>
        (fun i => (p.1 i, p.2 i) : Fin (m + n) → ℝ × Rd d) :=
      measurable_pi_iff.2 fun i =>
        ((measurable_pi_apply i).comp measurable_fst).prodMk
          ((measurable_pi_apply i).comp measurable_snd)
    exact (lintegral_prod _ (hmi.comp hcomp).aemeasurable).ge
  refine h1.trans (h2.le.trans (le_trans ?_ h3))
  refine lintegral_mono fun s => ?_
  have hpt : (posOrthant (m + n)).indicator (fun r => wickJ' g Γ ε m D r * F r) (incr m s) =
      (posOrthant (m + n)).indicator F (incr m s) * wickJ' g Γ ε m D (incr m s) := by
    by_cases hs : incr m s ∈ posOrthant (m + n)
    · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs, mul_comm]
    · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, zero_mul]
  rw [hpt, wickJ']
  refine (lintegral_const_mul_le _ _).trans (lintegral_mono fun y => ?_)
  exact integrand_eq hH g hD hε A hAm hA0 θ s y

end Bridge

end StratonovichHAMSecondMoment.WickBridge
