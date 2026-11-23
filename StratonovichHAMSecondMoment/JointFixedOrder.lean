module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L18, item L18-E, part 1: the identity M8 = M4, the joint diagram limit of
`L:joint-fixed-order` (Steps 1 and 3) and its M4 corollary `DiagramLimits` (main TeX lines
814-832 with 1657-1677 and 1853-1945 at revision edf7085f (book 1.1.3)).  Narrower: the
deterministic half of `L:joint-fixed-order`; Step 4 (the `L²` construction of `X_n`, 1949-1965)
is not formalized.  `joint_diagram_limit` and `diagramLimits_homog` take the spatial Wick-measure
lemma (`SpatialWickMeasuresTarget`, item D) and `E:joint-temporal-tail`
(`JointTemporalTailTarget`, proved in `JointTail` from items B and C) as hypotheses with their
frozen signatures.

* `m8_m4_identity` (`M8M4IdentityTarget`): M4's diagram at noise width `ε` is
  `F_{ε/2,0,D}(t,t)`, by the change of variables `r = incr m s` (determinant one) from the two
  ordered time simplices to the gap vectors on `ℓ_1, ℓ_2 < t`;
* the density `J_{ε,D}` of `ρ_{ε,D}` is a.e.-measurable on the orthant (`aemeasurable_wickJ`),
  from the scaling `G_s = s · (v ↦ s v)_* G_1` of the wave Green measures (`WaveGreen.waveGreen_scaling`);
* monotonicity of `F_{ε,A,D}` in the Laplace domains (`wickF_mono`), and the finiteness of
  `ρ_{ε,D}` on the horizon from the finiteness of `ν_{ε,D}` (`wickRho_horizon_le`);
* Step 1: the bounded continuous multiplier `capMult` at a common temporal width;
* Step 3: the squeeze `squeeze_limit`, `joint_limit_aux`, `joint_diagram_limit`
  (`JointDiagramLimitTarget`) and `diagramLimits_homog` (`DiagramLimitsHomogTarget`).
-/
public import Mathlib
public import StratonovichHAMSecondMoment.WickInterface
public import StratonovichHAMSecondMoment.PairingCapRemoval
public import StratonovichHAMSecondMoment.PairingDampedNorms

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal Real Pointwise BoundedContinuousFunction Nat

namespace StratonovichHAMSecondMoment.JointFixedOrder

open HomogHypothesis (Rd HomogCovariance)
open DiagramModel (Pi2 SameChain pred predVal incr openers covEps covWeight pos spatial diagram
  diagramLim timeCov timeWeight twoSimplex)
open WaveGreen (waveGreen)
open PairingInterface
open WickInterface

variable {d : ℕ}

/-! ### The wave Green measures as scaled pushforwards -/

/-- `G_s = s · (v ↦ s v)_* G_1` for `s > 0` (`WaveGreen.waveGreen_scaling`). -/
theorem waveGreen_eq_smul_map (hd : d = 1 ∨ d = 2 ∨ d = 3) {s : ℝ} (hs : 0 < s) :
    waveGreen d s = ENNReal.ofReal s • (waveGreen d 1).map (fun v : Rd d => s • v) := by
  ext A hA
  rw [Measure.smul_apply, Measure.map_apply (measurable_const_smul s) hA, smul_eq_mul,
    Set.preimage_smul₀ hs.ne', ← WaveGreen.waveGreen_scaling d hd s hs _ (hA.const_smul₀ _),
    smul_inv_smul₀ hs.ne']

/-- The product of the wave Green measures at positive gaps is the scaled pushforward of the
product of the unit-time Green measures. -/
theorem pi_waveGreen_eq (hd : d = 1 ∨ d = 2 ∨ d = 3) {N : ℕ} {r : Fin N → ℝ}
    (hr : ∀ i, 0 < r i) :
    Measure.pi (fun i => waveGreen d (r i)) =
      (∏ i, ENNReal.ofReal (r i)) • (Measure.pi fun _ : Fin N => waveGreen d 1).map
        (fun v i => r i • v i) := by
  have : ∀ s, IsFiniteMeasure (waveGreen d s) := WaveGreen.isFiniteMeasure_waveGreen d
  refine Measure.pi_eq (μ := fun i => waveGreen d (r i)) fun s hs => ?_
  have hT : Measurable fun v : Fin N → Rd d => fun i => r i • v i := by fun_prop
  rw [Measure.smul_apply, Measure.map_apply hT (MeasurableSet.univ_pi hs), smul_eq_mul]
  have hpre : (fun v : Fin N → Rd d => fun i => r i • v i) ⁻¹' Set.pi univ s =
      Set.pi univ fun i => (r i)⁻¹ • s i := by
    ext v
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    exact forall_congr' fun i => (Set.mem_inv_smul_set_iff₀ (hr i).ne' _ _).symm
  rw [hpre, Measure.pi_pi, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [waveGreen_eq_smul_map hd (hr i), Measure.smul_apply,
    Measure.map_apply (measurable_const_smul _) (hs i), smul_eq_mul, Set.preimage_smul₀ (hr i).ne']

/-! ### Measurability of the density `J_{ε,D}` on the orthant -/

section Meas

variable {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}

/-- The spatial pair product at the positions of the increments is measurable. -/
theorem measurable_covW_pos (hH : HomogCovariance d alpha α₀ Γ μ) {N : ℕ} {ε : Fin N → ℝ}
    (hε : ∀ i, 0 < ε i) (m : ℕ) (D : Fin N → Fin N) :
    Measurable fun w : Fin N → Rd d => covW Γ ε D (pos m w) := by
  unfold covW
  refine Finset.measurable_prod _ fun i _ => ?_
  exact (LowAlphaUpper.measurable_covEps hH (add_pos (hε i) (hε (D i)))).comp
    ((DiagramModel.measurable_pos m i).sub (DiagramModel.measurable_pos m (D i)))

/-- The positive measurable version of `J_{ε,D}` on the orthant. -/
def wickJm (Γ : Measure (Rd d)) {N : ℕ} (ε : Fin N → ℝ) (m : ℕ) (D : Fin N → Fin N)
    (r : Fin N → ℝ) : ℝ≥0∞ :=
  (∏ i, ENNReal.ofReal (r i)) *
    ∫⁻ v, covW Γ ε D (pos m fun i => r i • v i) ∂Measure.pi fun _ : Fin N => waveGreen d 1

theorem measurable_wickJm (hH : HomogCovariance d alpha α₀ Γ μ) {N : ℕ} {ε : Fin N → ℝ}
    (hε : ∀ i, 0 < ε i) (m : ℕ) (D : Fin N → Fin N) : Measurable (wickJm Γ ε m D) := by
  have : ∀ s, IsFiniteMeasure (waveGreen d s) := WaveGreen.isFiniteMeasure_waveGreen d
  unfold wickJm
  refine (Finset.measurable_prod _ fun i _ =>
    ENNReal.measurable_ofReal.comp (measurable_pi_apply i)).mul ?_
  have hT : Measurable fun p : (Fin N → ℝ) × (Fin N → Rd d) => fun i => p.1 i • p.2 i := by
    fun_prop
  exact ((measurable_covW_pos hH hε m D).comp hT).lintegral_prod_right'

theorem wickJ_eq_wickJm (hH : HomogCovariance d alpha α₀ Γ μ) {N : ℕ} {ε : Fin N → ℝ}
    (hε : ∀ i, 0 < ε i) (m : ℕ) (D : Fin N → Fin N) {r : Fin N → ℝ} (hr : ∀ i, 0 < r i) :
    wickJ (waveGreen d) Γ ε m D r = wickJm Γ ε m D r := by
  unfold wickJ wickJm
  rw [pi_waveGreen_eq hH.dim hr, lintegral_smul_measure,
    lintegral_map (measurable_covW_pos hH hε m D) (by fun_prop), smul_eq_mul]

theorem measurableSet_posOrthant (N : ℕ) : MeasurableSet (posOrthant N) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioi

/-- **`J_{ε,D}` is a.e.-measurable on the orthant** (positive spatial widths). -/
theorem aemeasurable_wickJ (hH : HomogCovariance d alpha α₀ Γ μ) {N : ℕ} {ε : Fin N → ℝ}
    (hε : ∀ i, 0 < ε i) (m : ℕ) (D : Fin N → Fin N) :
    AEMeasurable (wickJ (waveGreen d) Γ ε m D) (volume.restrict (posOrthant N)) := by
  refine (measurable_wickJm hH hε m D).aemeasurable.congr ?_
  filter_upwards [ae_restrict_mem (measurableSet_posOrthant N)] with r hr
  exact (wickJ_eq_wickJm hH hε m D fun i => hr i (mem_univ i)).symm

end Meas

/-! ### The temporal kernels -/

theorem measurable_kerA (a : ℝ) (S : Set ℝ) : Measurable (kerA a S) := by
  unfold kerA
  have : Measurable fun x : ℝ × ℝ => ENNReal.ofReal (Real.exp (-(x.2 * |x.1|))) :=
    (Real.continuous_exp.comp (by fun_prop : Continuous fun x : ℝ × ℝ => -(x.2 * |x.1|)))
      |>.measurable.ennreal_ofReal
  have hs : SFinite (nuE a S) := by unfold nuE; infer_instance
  exact this.lintegral_prod_right'

theorem measurable_gapTime (m : ℕ) {N : ℕ} (i : Fin N) :
    Measurable fun r : Fin N → ℝ => gapTime m r i := by
  unfold gapTime
  exact Finset.measurable_sum _ fun j _ => measurable_pi_apply j

theorem measurable_pairTime (a : ℝ) {N : ℕ} (A : Sym2 (Fin N) → Set ℝ) (m : ℕ)
    (D : Fin N → Fin N) : Measurable (pairTime a A m D) := by
  unfold pairTime
  exact Finset.measurable_prod _ fun i _ =>
    (measurable_kerA a _).comp ((measurable_gapTime m i).sub (measurable_gapTime m (D i)))

/-- `κ_S` is monotone in the Laplace domain. -/
theorem kerA_mono (a : ℝ) {S S' : Set ℝ} (h : S ⊆ S') (u : ℝ) : kerA a S u ≤ kerA a S' u :=
  lintegral_mono' (PairingCapRemoval.nuE_mono a h) le_rfl

theorem pairTime_mono (a : ℝ) {N : ℕ} {A A' : Sym2 (Fin N) → Set ℝ} (h : ∀ e, A e ⊆ A' e)
    (m : ℕ) (D : Fin N → Fin N) (r : Fin N → ℝ) : pairTime a A m D r ≤ pairTime a A' m D r :=
  Finset.prod_le_prod fun _ _ => kerA_mono a (h _) _

/-- `F_{ε,A,D}` is monotone in the Laplace domains. -/
theorem wickF_mono (G : ℝ → Measure (Rd d)) (Γ : Measure (Rd d)) (a : ℝ) {N : ℕ}
    {A A' : Sym2 (Fin N) → Set ℝ} (h : ∀ e, A e ⊆ A' e) (ε : Fin N → ℝ) (m : ℕ)
    (D : Fin N → Fin N) (T1 T2 : ℝ) : wickF G Γ a A ε m D T1 T2 ≤ wickF G Γ a A' ε m D T1 T2 :=
  lintegral_mono fun r => pairTime_mono a h m D r

/-- Every vertexwise temporal cutoff is below the full kernel: `F_{ε,δ,D} ≤ F_{ε,0,D}`. -/
theorem wickF_le_zero (G : ℝ → Measure (Rd d)) (Γ : Measure (Rd d)) (a : ℝ) {N : ℕ}
    (δ : Fin N → ℝ) (ε : Fin N → ℝ) (m : ℕ) (D : Fin N → Fin N) (T1 T2 : ℝ) :
    wickF G Γ a (capDom δ) ε m D T1 T2 ≤ wickF G Γ a (capDom (0 : Fin N → ℝ)) ε m D T1 T2 :=
  wickF_mono G Γ a (fun e => by rw [capDom_zero]; exact capSet_subset_Ioi _) ε m D T1 T2

/-- A common temporal width `η` is below every vertexwise width `δ < η`:
`F_{ε,η,D} ≤ F_{ε,δ,D}` (TeX 1937-1940). -/
theorem wickF_const_le (G : ℝ → Measure (Rd d)) (Γ : Measure (Rd d)) (a : ℝ) {N : ℕ}
    {δ : Fin N → ℝ} {η : ℝ} (hδ : ∀ i, δ i ≤ η) (ε : Fin N → ℝ) (m : ℕ) (D : Fin N → Fin N)
    (T1 T2 : ℝ) :
    wickF G Γ a (capDom fun _ : Fin N => η) ε m D T1 T2 ≤ wickF G Γ a (capDom δ) ε m D T1 T2 := by
  refine wickF_mono G Γ a (fun e => ?_) ε m D T1 T2
  rw [capDom_const]
  induction e using Sym2.ind with
  | h j h =>
    rw [capDom_mk]
    intro l hl
    exact ⟨hl.1, le_trans (mul_le_mul_of_nonneg_right (max_le (hδ j) (hδ h)) hl.1.le) hl.2⟩

/-! ### The horizon -/

theorem measurableSet_horizon (m : ℕ) {N : ℕ} (T1 T2 : ℝ) :
    MeasurableSet (horizon m (N := N) T1 T2) := by
  have h1 : Measurable fun r : Fin N → ℝ => ell1 m r :=
    Finset.measurable_sum _ fun j _ => measurable_pi_apply j
  have h2 : Measurable fun r : Fin N → ℝ => ell2 m r :=
    Finset.measurable_sum _ fun j _ => measurable_pi_apply j
  exact (measurableSet_lt h1 measurable_const).inter (measurableSet_lt h2 measurable_const)

/-- On the orthant and the horizon, `Σ_l r_l = ℓ_1 + ℓ_2 < T_1 + T_2`. -/
theorem sum_lt_of_mem_horizon {m : ℕ} {N : ℕ} {T1 T2 : ℝ} {r : Fin N → ℝ}
    (hr : r ∈ horizon m T1 T2) : ∑ i, r i < T1 + T2 := by
  have hsplit : ∑ i, r i = ell1 m r + ell2 m r := by
    unfold ell1 ell2
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin N => (i : ℕ) < m)]
    congr 1
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext i
    simp
  rw [hsplit]
  exact add_lt_add hr.1 hr.2

/-- `ρ_{ε,D}` on the horizon is at most `e^{T_1+T_2}` times the mass of `ν_{ε,D}` there. -/
theorem wickRho_horizon_le (G : ℝ → Measure (Rd d)) (Γ : Measure (Rd d)) {N : ℕ}
    (ε : Fin N → ℝ) (m : ℕ) (D : Fin N → Fin N) (T1 T2 : ℝ) :
    wickRho G Γ ε m D (horizon m T1 T2) ≤
      ENNReal.ofReal (Real.exp (T1 + T2)) * wickNu G Γ ε m D (horizon m T1 T2) := by
  have hm : Measurable fun r : Fin N → ℝ => ENNReal.ofReal (Real.exp (-∑ i, r i)) := by fun_prop
  rw [wickNu, withDensity_apply _ (measurableSet_horizon m T1 T2), ← lintegral_const_mul _ hm,
    ← setLIntegral_one]
  refine setLIntegral_mono (measurable_const.mul hm) fun r hr => ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal (Real.one_le_exp ?_)
  linarith [sum_lt_of_mem_horizon hr]

/-! ### The change of variables `r = incr m s` -/

/-- M4's increment map as a measurable equivalence (inverse `gapTime`). -/
def incrEquiv (m N : ℕ) : (Fin N → ℝ) ≃ᵐ (Fin N → ℝ) where
  toFun := incr m
  invFun := gapTime m
  left_inv s := gapTime_incr m s
  right_inv r := incr_gapTime m r
  measurable_toFun := DiagramModel.measurable_incr m
  measurable_invFun := Measurable.of_eval fun i => measurable_gapTime m i

/-- The increment map preserves Lebesgue measure (determinant one). -/
theorem measurePreserving_incr (m N : ℕ) :
    MeasurePreserving (incr m (N := N)) volume volume := by
  have h := DiagramBridge.measurePreserving_incrMatrix m N
  have e : (Matrix.toLin' (DiagramBridge.incrMatrix m N) : (Fin N → ℝ) → (Fin N → ℝ)) =
      incr m := by
    funext v
    rw [Matrix.toLin'_apply, DiagramBridge.incrMatrix_mulVec]
    rfl
  rwa [e] at h

/-- Within a chain the cumulative time is at most the chain length (nonnegative gaps). -/
theorem gapTime_le_ell1 {m : ℕ} {N : ℕ} {r : Fin N → ℝ} (hr : ∀ i, 0 ≤ r i) {i : Fin N}
    (hi : (i : ℕ) < m) : gapTime m r i ≤ ell1 m r := by
  unfold gapTime ell1
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) fun j _ _ => hr j
  rw [Finset.mem_filter] at hj ⊢
  exact ⟨Finset.mem_univ _, hj.2.1.2 hi⟩

theorem gapTime_le_ell2 {m : ℕ} {N : ℕ} {r : Fin N → ℝ} (hr : ∀ i, 0 ≤ r i) {i : Fin N}
    (hi : m ≤ (i : ℕ)) : gapTime m r i ≤ ell2 m r := by
  unfold gapTime ell2
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) fun j _ _ => hr j
  rw [Finset.mem_filter] at hj ⊢
  refine ⟨Finset.mem_univ _, ?_⟩
  by_contra hjm
  exact absurd (hj.2.1.1 (by omega)) (by omega)

/-- The chain lengths are the last cumulative times. -/
theorem ell1_eq_gapTime {m n : ℕ} (r : Fin (m + n) → ℝ) (hm : 0 < m) :
    ell1 m r = gapTime m r ⟨m - 1, by omega⟩ := by
  unfold gapTime ell1
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, SameChain, Fin.le_def]
  omega

theorem ell2_eq_gapTime {m n : ℕ} (r : Fin (m + n) → ℝ) (hn : 0 < n) :
    ell2 m r = gapTime m r ⟨m + n - 1, by omega⟩ := by
  unfold gapTime ell2
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, SameChain, Fin.le_def]
  have := j.isLt
  omega

theorem ell1_nonneg {m : ℕ} {N : ℕ} {r : Fin N → ℝ} (hr : ∀ i, 0 ≤ r i) : 0 ≤ ell1 m r :=
  Finset.sum_nonneg fun i _ => hr i

theorem ell2_nonneg {m : ℕ} {N : ℕ} {r : Fin N → ℝ} (hr : ∀ i, 0 ≤ r i) : 0 ≤ ell2 m r :=
  Finset.sum_nonneg fun i _ => hr i

/-- The two ordered time simplices are the preimage of `(0,∞)^N ∩ {ℓ_1, ℓ_2 < t}` under the
increment map (`t > 0`). -/
theorem incr_preimage {m n : ℕ} {t : ℝ} (ht : 0 < t) :
    incr m ⁻¹' (posOrthant (m + n) ∩ horizon m t t) = twoSimplex m n t := by
  ext s
  simp only [Set.mem_preimage, Set.mem_inter_iff, posOrthant, Set.mem_pi, Set.mem_univ,
    true_implies, Set.mem_Ioi, DiagramModel.twoSimplex, Set.mem_ofPred_eq]
  set r := incr m s with hrdef
  have hs : s = gapTime m r := (gapTime_incr m s).symm
  constructor
  · rintro ⟨hpos, hh⟩
    intro i
    refine ⟨by have := hpos i; rw [hrdef, incr] at this; linarith, ?_⟩
    rw [hs]
    by_cases hi : (i : ℕ) < m
    · exact (gapTime_le_ell1 (fun j => (hpos j).le) hi).trans_lt hh.1
    · exact (gapTime_le_ell2 (fun j => (hpos j).le) (by omega)).trans_lt hh.2
  · intro h
    have hpos : ∀ i, 0 < r i := fun i => by rw [hrdef, incr]; linarith [(h i).1]
    refine ⟨hpos, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos m with hm | hm
      · unfold ell1
        rw [Finset.sum_eq_zero fun i hi => by simp [hm] at hi]
        exact ht
      · rw [ell1_eq_gapTime r hm, ← hs]
        exact (h _).2
    · rcases Nat.eq_zero_or_pos n with hn | hn
      · unfold ell2
        rw [Finset.sum_eq_zero fun i hi => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          have := i.isLt; omega]
        exact ht
      · rw [ell2_eq_gapTime r hn, ← hs]
        exact (h _).2

/-! ### The identity M8 = M4 -/

section Identity

variable {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}

/-- `F_{ε,A,D}(T_1,T_2)` as a Lebesgue integral over `(0,∞)^N ∩ {ℓ_1 < T_1, ℓ_2 < T_2}`. -/
theorem wickF_eq_lintegral (hH : HomogCovariance d alpha α₀ Γ μ) {N : ℕ} {ε : Fin N → ℝ}
    (hε : ∀ i, 0 < ε i) (a : ℝ) (A : Sym2 (Fin N) → Set ℝ) (m : ℕ) (D : Fin N → Fin N)
    (T1 T2 : ℝ) :
    wickF (waveGreen d) Γ a A ε m D T1 T2 =
      ∫⁻ r in posOrthant N ∩ horizon m T1 T2,
        pairTime a A m D r * wickJ (waveGreen d) Γ ε m D r := by
  have hHm := measurableSet_horizon m (N := N) T1 T2
  unfold wickF wickRho
  rw [restrict_withDensity hHm, lintegral_withDensity_eq_lintegral_mul₀
    ((aemeasurable_wickJ hH hε m D).mono_measure Measure.restrict_le_self)
    (measurable_pairTime a A m D).aemeasurable, Measure.restrict_restrict hHm, inter_comm]
  refine lintegral_congr fun r => ?_
  simp only [Pi.mul_apply]
  rw [mul_comm]

/-- **The identity M8 = M4** (`M8M4IdentityTarget`; TeX lines 814-832 with 1873-1881 and
1895-1896 at revision edf7085f (book 1.1.3)): M4's diagram at the common noise width `ε` is the
M8 integral `F_{ε/2,0,D}(t,t)` (vertex widths `ε/2`, full temporal kernels, horizon `t` in both
chains), by the change of variables `r = incr m s` (`incr_preimage`, determinant one); the
integrands agree by `pairTime_capDom_zero_incr` and `wickJ_half`. -/
theorem m8_m4_identity (d : ℕ) : M8M4IdentityTarget d := by
  intro alpha α₀ Γ μ hH ε hε m n D _ t ht
  rw [wickF_eq_lintegral hH (fun _ => half_pos hε) α₀ _ m D t t, diagram,
    ← incr_preimage (n := n) ht]
  have hmp := (measurePreserving_incr m (m + n)).setLIntegral_comp_preimage_emb
    (incrEquiv m (m + n)).measurableEmbedding
    (fun r => pairTime α₀ (capDom (0 : Fin (m + n) → ℝ)) m D r *
      wickJ (waveGreen d) Γ (fun _ => ε / 2) m D r) (posOrthant (m + n) ∩ horizon m t t)
  rw [← hmp]
  refine setLIntegral_congr_fun (DiagramModel.measurable_incr m
    ((measurableSet_posOrthant _).inter (measurableSet_horizon m t t))) fun s _ => ?_
  rw [pairTime_capDom_zero_incr hH.alpha0_pos, wickJ_half]

end Identity

/-! ### The capped temporal kernel is bounded and continuous (TeX 1883-1888) -/

/-- `∫_{(0,L]} λ^{a-1} dλ < ∞` for `a > 0`. -/
theorem integrableOn_rpow_Ioc {a : ℝ} (ha : 0 < a) (L : ℝ) :
    IntegrableOn (fun l : ℝ => l ^ (a - 1)) (Ioc 0 L) := by
  rcases le_or_gt L 0 with hL | hL
  · rw [Set.Ioc_eq_empty (not_lt.2 hL)]; exact integrableOn_empty
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hL.le).1
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))

/-- The capped kernel `κ_{(0,L]}` is the restricted kernel `K_{(0,L]}` of `DampedNormsHomog`. -/
theorem kerA_Ioc_eq {a : ℝ} (ha : 0 < a) (L u : ℝ) :
    kerA a (Ioc 0 L) u = ENNReal.ofReal (DampedNormsHomog.KS a (Ioc 0 L) u) := by
  rw [← PairingDampedNorms.kappaCap_nuE ha L u]
  unfold kerA kappaCap
  rw [← PairingCapRemoval.nuE_inter, Set.inter_eq_right.2 Set.Ioc_subset_Ioi_self]

theorem subKernel_le {a : ℝ} (u : ℝ) {l : ℝ} (hl : 0 < l) :
    ‖TimeFractional.subKernel a |u| l‖ ≤ l ^ (a - 1) := by
  rw [Real.norm_eq_abs, abs_of_nonneg (TimeFractional.subKernel_nonneg a |u| l hl.le),
    TimeFractional.subKernel]
  calc l ^ (a - 1) * Real.exp (-(|u| * l)) ≤ l ^ (a - 1) * 1 :=
        mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.2 (by nlinarith [abs_nonneg u]))
          (Real.rpow_nonneg hl.le _)
    _ = l ^ (a - 1) := mul_one _

/-- `u ↦ K_{(0,L]}(u)` is continuous. -/
theorem continuous_KS_Ioc {a : ℝ} (ha : 0 < a) (L : ℝ) :
    Continuous fun u => DampedNormsHomog.KS a (Ioc 0 L) u := by
  unfold DampedNormsHomog.KS
  refine continuous_const.mul ?_
  have hI : Integrable (fun l : ℝ => l ^ (a - 1)) (TimeFractional.L0.restrict (Ioc 0 L)) := by
    rw [TimeFractional.L0, Measure.restrict_restrict measurableSet_Ioc,
      Set.inter_eq_left.2 Set.Ioc_subset_Ioi_self]
    exact integrableOn_rpow_Ioc ha L
  refine continuous_of_dominated (bound := fun l => l ^ (a - 1)) (fun u => ?_) (fun u => ?_)
    hI (ae_of_all _ fun l => ?_)
  · exact (by unfold TimeFractional.subKernel; fun_prop :
      Measurable fun l => TimeFractional.subKernel a |u| l).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with l hl
    exact subKernel_le u hl.1
  · unfold TimeFractional.subKernel; fun_prop

/-- `κ_S(u) ≤ κ_S(0)` for `S ⊆ (0,∞)` measurable. -/
theorem kerA_le_zero (a : ℝ) {S : Set ℝ} (hS : MeasurableSet S) (hS0 : S ⊆ Ioi 0) (u : ℝ) :
    kerA a S u ≤ kerA a S 0 := by
  refine lintegral_mono_ae ?_
  filter_upwards [PairingConvolution.ae_nuE_mem a hS] with l hl
  have hl0 : 0 < l := hS0 hl
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  simp only [abs_zero, mul_zero, neg_zero, Left.neg_nonpos_iff]
  positivity

/-- The pair product at a common temporal width `η > 0`, in real form. -/
theorem pairTime_const_eq {a η : ℝ} (ha : 0 < a) (hη : 0 < η) {N : ℕ} (m : ℕ)
    (D : Fin N → Fin N) (r : Fin N → ℝ) :
    pairTime a (capDom fun _ : Fin N => η) m D r =
      ENNReal.ofReal (∏ i ∈ openers D,
        DampedNormsHomog.KS a (Ioc 0 η⁻¹) (gapTime m r i - gapTime m r (D i))) := by
  unfold pairTime
  simp_rw [capDom_const, capSet_of_pos hη, kerA_Ioc_eq ha]
  rw [ENNReal.ofReal_prod_of_nonneg fun i _ => DampedNormsHomog.KS_nonneg _ _ _ ha]

/-- The bound `∏ κ_η(0)` of the pair product at a common width `η > 0`. -/
theorem pairTime_const_le {a η : ℝ} {N : ℕ} (m : ℕ) (D : Fin N → Fin N)
    (r : Fin N → ℝ) :
    pairTime a (capDom fun _ : Fin N => η) m D r ≤
      ∏ _i ∈ openers D, kerA a (capSet η) 0 := by
  unfold pairTime
  refine Finset.prod_le_prod fun i _ => ?_
  rw [capDom_const]
  exact kerA_le_zero a (measurableSet_capSet η) (capSet_subset_Ioi η) _

theorem kerA_capSet_zero_ne_top {a η : ℝ} (ha : 0 < a) (hη : 0 < η) :
    kerA a (capSet η) 0 ≠ ⊤ := by
  rw [capSet_of_pos hη, kerA_Ioc_eq ha]; exact ENNReal.ofReal_ne_top

/-- The continuous gap-coordinate cumulative times. -/
theorem continuous_gapTime (m : ℕ) {N : ℕ} (i : Fin N) :
    Continuous fun r : Fin N → ℝ => gapTime m r i := by
  unfold gapTime
  exact continuous_finsetSum _ fun j _ => continuous_apply j

/-- **The bounded continuous multiplier** `∏_{{j,h}} γ^0_η(s_j - s_h)` at a common temporal
width `η > 0` (TeX 1886-1887: "At a common temporal width `η > 0` the multiplier is bounded and
continuous"). -/
def capMult {a η : ℝ} (ha : 0 < a) (hη : 0 < η) {N : ℕ} (m : ℕ) (D : Fin N → Fin N) :
    (Fin N → ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun r => (pairTime a (capDom fun _ : Fin N => η) m D r).toReal)
    (by
      have e : (fun r => (pairTime a (capDom fun _ : Fin N => η) m D r).toReal) =
          fun r => ∏ i ∈ openers D,
            DampedNormsHomog.KS a (Ioc 0 η⁻¹) (gapTime m r i - gapTime m r (D i)) := by
        funext r
        rw [pairTime_const_eq ha hη, ENNReal.toReal_ofReal
          (Finset.prod_nonneg fun i _ => DampedNormsHomog.KS_nonneg _ _ _ ha)]
      rw [e]
      exact continuous_finsetProd _ fun i _ => (continuous_KS_Ioc ha _).comp
        ((continuous_gapTime m i).sub (continuous_gapTime m (D i))))
    (∏ _i ∈ openers D, kerA a (capSet η) 0).toReal
    (fun r => by
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.toReal_mono (ENNReal.prod_ne_top fun _ _ => kerA_capSet_zero_ne_top ha hη)
        (pairTime_const_le m D r))

theorem capMult_apply {a η : ℝ} (ha : 0 < a) (hη : 0 < η) {N : ℕ} (m : ℕ) (D : Fin N → Fin N)
    (r : Fin N → ℝ) : capMult ha hη m D r = (pairTime a (capDom fun _ : Fin N => η) m D r).toReal :=
  rfl

theorem ofReal_capMult {a η : ℝ} (ha : 0 < a) (hη : 0 < η) {N : ℕ} (m : ℕ) (D : Fin N → Fin N)
    (r : Fin N → ℝ) :
    ENNReal.ofReal (capMult ha hη m D r) = pairTime a (capDom fun _ : Fin N => η) m D r := by
  rw [capMult_apply, ENNReal.ofReal_toReal]
  exact ne_top_of_le_ne_top (ENNReal.prod_ne_top fun _ _ => kerA_capSet_zero_ne_top ha hη)
    (pairTime_const_le m D r)

/-- At positive widths with `ν_{ε,D}` finite, the capped `F_{ε,η,D}(T_1,T_2)` is the real integral
of the bounded continuous multiplier on the horizon. -/
theorem wickF_const_eq_ofReal (G : ℝ → Measure (Rd d)) (Γ : Measure (Rd d)) {a η : ℝ}
    (ha : 0 < a) (hη : 0 < η) {N : ℕ} (ε : Fin N → ℝ) (m : ℕ) (D : Fin N → Fin N) (T1 T2 : ℝ)
    (hfin : IsFiniteMeasure (wickNu G Γ ε m D)) :
    wickF G Γ a (capDom fun _ : Fin N => η) ε m D T1 T2 =
      ENNReal.ofReal (∫ r in horizon m T1 T2, capMult ha hη m D r ∂wickRho G Γ ε m D) := by
  have hρ : wickRho G Γ ε m D (horizon m T1 T2) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
      (wickRho_horizon_le G Γ ε m D T1 T2)
  have : IsFiniteMeasure ((wickRho G Γ ε m D).restrict (horizon m T1 T2)) :=
    isFiniteMeasure_restrict.2 hρ
  rw [ofReal_integral_eq_lintegral_ofReal ((capMult ha hη m D).integrable _)
    (ae_of_all _ fun r => by rw [capMult_apply]; exact ENNReal.toReal_nonneg)]
  unfold wickF
  simp_rw [ofReal_capMult]

/-! ### An abstract squeeze (Step 3, TeX 1931-1945) -/

/-- **The squeeze of Step 3**: lower functions `L_η ≤ F ≤ U ≤ L_η + c_η` (eventually), each `L_η`
converging to a finite `b_η`, and `c_η → 0`: then `F` converges to the finite
`b = sup_η b_η`. -/
theorem squeeze_limit {X : Type*} {l : Filter X} [l.NeBot] {F U : X → ℝ≥0∞}
    {L : ℝ → X → ℝ≥0∞} {b c : ℝ → ℝ≥0∞}
    (hFU : ∀ᶠ x in l, F x ≤ U x)
    (hLF : ∀ η, 0 < η → ∀ᶠ x in l, L η x ≤ F x)
    (hUL : ∀ η, 0 < η → ∀ᶠ x in l, U x ≤ L η x + c η)
    (hL : ∀ η, 0 < η → Tendsto (L η) l (𝓝 (b η)))
    (hb : ∀ η, 0 < η → b η ≠ ⊤)
    (hc : Tendsto c (𝓝[>] 0) (𝓝 0)) :
    Tendsto F l (𝓝 (⨆ η ∈ Ioi (0 : ℝ), b η)) ∧ (⨆ η ∈ Ioi (0 : ℝ), b η) ≠ ⊤ := by
  set B := ⨆ η ∈ Ioi (0 : ℝ), b η with hBdef
  have key : ∀ η, 0 < η → ∀ η', 0 < η' → b η ≤ b η' + c η' := by
    intro η hη η' hη'
    refine le_of_tendsto_of_tendsto (hL η hη) ((hL η' hη').add tendsto_const_nhds) ?_
    filter_upwards [hLF η hη, hFU, hUL η' hη'] with x h1 h2 h3
    exact h1.trans (h2.trans h3)
  have hB : ∀ η', 0 < η' → B ≤ b η' + c η' := fun η' hη' =>
    iSup₂_le fun η hη => key η hη η' hη'
  have hbB : ∀ η, 0 < η → b η ≤ B := fun η hη => le_iSup₂ (f := fun η (_ : η ∈ Ioi (0 : ℝ)) => b η) η hη
  have hBtop : B ≠ ⊤ := by
    obtain ⟨η', hc1, hη'⟩ := ((hc.eventually (gt_mem_nhds zero_lt_one)).and
      self_mem_nhdsWithin).exists
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hb η' hη', ne_top_of_lt hc1⟩) (hB η' hη')
  refine ⟨tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩, hBtop⟩
  · obtain ⟨η, ha'⟩ := lt_iSup_iff.1 ha
    obtain ⟨hη, hab⟩ := lt_iSup_iff.1 ha'
    filter_upwards [(hL η hη).eventually (lt_mem_nhds hab), hLF η hη] with x h1 h2
    exact h1.trans_le h2
  · obtain ⟨e, hBe, hea⟩ := exists_between ha
    have hlim : Tendsto (fun η => B + c η) (𝓝[>] 0) (𝓝 (B + 0)) := tendsto_const_nhds.add hc
    rw [add_zero] at hlim
    obtain ⟨η, h1, hη⟩ := ((hlim.eventually (gt_mem_nhds hBe)).and self_mem_nhdsWithin).exists
    have hη0 : 0 < η := hη
    have hbe : b η + c η < e := (add_le_add (hbB η hη0) le_rfl).trans_lt h1
    filter_upwards [((hL η hη0).add tendsto_const_nhds).eventually (gt_mem_nhds hbe), hFU,
      hUL η hη0] with x h2 h3 h4
    exact (h3.trans h4).trans_lt (h2.trans hea)

/-! ### The joint diagram limit (Steps 1 and 3 of `L:joint-fixed-order`) -/

section Joint

variable {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}

/-- The tail error `C (N_1^{(1/η)}(1) + N_2^{(1/η)}(1)²) → 0` as `η ↓ 0`. -/
theorem tendsto_tailErr (hH : HomogCovariance d alpha α₀ Γ μ) (C : ℝ) :
    Tendsto (fun η : ℝ => ENNReal.ofReal (C * (DampedNormsHomog.N1tail α₀ η⁻¹ μ +
      DampedNormsHomog.N2tailSq α₀ η⁻¹ μ))) (𝓝[>] 0) (𝓝 0) := by
  have h1 := (DampedNormsHomog.N1tail_tendsto hH).comp tendsto_inv_nhdsGT_zero
  have h2 := (DampedNormsHomog.N2tail_tendsto hH).1.comp tendsto_inv_nhdsGT_zero
  have h := ((h1.add h2).const_mul C)
  rw [add_zero, mul_zero] at h
  simpa using ENNReal.tendsto_ofReal h

/-- Widths eventually below `η` along the width filter. -/
theorem eventually_le_of_widthFilter {N : ℕ} {η : ℝ} (hη : 0 < η) :
    ∀ᶠ δ in widthFilter N, ∀ i, δ i ≤ η := by
  refine (nhdsWithin_le_nhds (s := posOrthant N)) ?_
  refine eventually_all.2 fun i => ?_
  exact ((continuous_apply i).tendsto (0 : Fin N → ℝ)).eventually
    (Iic_mem_nhds (by simpa using hη))

theorem eventually_pos_of_widthFilter (N : ℕ) : ∀ᶠ ε in widthFilter N, ∀ i, 0 < ε i := by
  filter_upwards [self_mem_nhdsWithin] with ε hε i using hε i (mem_univ i)

/-- **The two limits of Steps 1-3** at a fixed horizon `(T_1, T_2)`, from the spatial Wick-measure
lemma (`hW`, `E:spatial-wick-limit`) and the uniform temporal tail (`hT`,
`E:joint-temporal-tail`): the vertexwise-cutoff diagrams `F_{ε,δ,D}` converge jointly, and the
full-kernel diagrams `F_{ε,0,D}` converge in the spatial widths, to one finite limit. -/
theorem joint_limit_aux (hH : HomogCovariance d alpha α₀ Γ μ)
    (hW : SpatialWickMeasuresTarget d) (hT : JointTemporalTailTarget d) {m n k : ℕ}
    (hmn : m + n = 2 * k) (hk : 1 ≤ k) {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n)
    {T1 T2 : ℝ} (h1 : 0 < T1) (h2 : 0 < T2) :
    ∃ b : ℝ≥0∞, b ≠ ⊤ ∧
      Tendsto (fun p : (Fin (m + n) → ℝ) × (Fin (m + n) → ℝ) =>
          wickF (waveGreen d) Γ α₀ (capDom p.2) p.1 m D T1 T2)
        (widthFilter (m + n) ×ˢ widthFilter (m + n)) (𝓝 b) ∧
      Tendsto (fun ε => wickF (waveGreen d) Γ α₀ (capDom (0 : Fin (m + n) → ℝ)) ε m D T1 T2)
        (widthFilter (m + n)) (𝓝 b) := by
  obtain ⟨νD, -, hfin, -, -, -, -, -, hlim⟩ := hW hH m n k hmn hk D hD
  obtain ⟨C, hC⟩ := hT hH m n k hmn hk D hD T1 T2 h1 h2
  have ha := hH.alpha0_pos
  set Fc : ℝ → (Fin (m + n) → ℝ) → ℝ≥0∞ := fun η ε =>
    wickF (waveGreen d) Γ α₀ (capDom fun _ : Fin (m + n) => η) ε m D T1 T2 with hFc
  set U : (Fin (m + n) → ℝ) → ℝ≥0∞ := fun ε =>
    wickF (waveGreen d) Γ α₀ (capDom (0 : Fin (m + n) → ℝ)) ε m D T1 T2 with hU
  set b : ℝ → ℝ≥0∞ := fun η => if hη : 0 < η then
    ENNReal.ofReal (∫ r in horizon m T1 T2, capMult ha hη m D r ∂rhoLim νD) else 0 with hbdef
  set c : ℝ → ℝ≥0∞ := fun η => ENNReal.ofReal (C * (DampedNormsHomog.N1tail α₀ η⁻¹ μ +
    DampedNormsHomog.N2tailSq α₀ η⁻¹ μ)) with hcdef
  have hb : ∀ η, 0 < η → b η ≠ ⊤ := fun η hη => by
    simp only [hbdef, hη, ↓reduceDIte]; exact ENNReal.ofReal_ne_top
  have hLc : ∀ η, 0 < η → Tendsto (Fc η) (widthFilter (m + n)) (𝓝 (b η)) := by
    intro η hη
    simp only [hbdef, hη, ↓reduceDIte]
    refine (ENNReal.tendsto_ofReal (hlim (capMult ha hη m D) T1 T2 h1 h2)).congr' ?_
    filter_upwards [eventually_pos_of_widthFilter (m + n)] with ε hε
    exact (wickF_const_eq_ofReal _ _ ha hη ε m D T1 T2 (hfin ε hε)).symm
  have hUL : ∀ η, 0 < η → ∀ᶠ ε in widthFilter (m + n), U ε ≤ Fc η ε + c η := by
    intro η hη
    filter_upwards [eventually_pos_of_widthFilter (m + n)] with ε hε
    exact (hC ε hε η hη).2.2
  have hc := tendsto_tailErr hH C
  have hsU := squeeze_limit (F := U) (U := U) (L := Fc) (b := b) (c := c)
    (Eventually.of_forall fun _ => le_rfl)
    (fun η hη => by
      filter_upwards [eventually_pos_of_widthFilter (m + n)] with ε hε
      exact (hC ε hε η hη).1) hUL hLc hb hc
  have hsF := squeeze_limit (l := widthFilter (m + n) ×ˢ widthFilter (m + n))
    (F := fun p : (Fin (m + n) → ℝ) × (Fin (m + n) → ℝ) =>
      wickF (waveGreen d) Γ α₀ (capDom p.2) p.1 m D T1 T2)
    (U := fun p => U p.1) (L := fun η p => Fc η p.1) (b := b) (c := c)
    (Eventually.of_forall fun p => wickF_le_zero _ _ _ p.2 p.1 m D T1 T2)
    (fun η hη => (tendsto_snd.eventually (eventually_le_of_widthFilter hη)).mono
      fun p hp => wickF_const_le _ _ _ hp p.1 m D T1 T2)
    (fun η hη => tendsto_fst.eventually (hUL η hη))
    (fun η hη => (hLc η hη).comp tendsto_fst) hb hc
  exact ⟨_, hsU.2, hsF.1, hsU.1⟩

/-- **The joint diagram limit of `L:joint-fixed-order`** (`JointDiagramLimitTarget`; TeX lines
1855-1858, proof Steps 1-3 1864-1945 at revision edf7085f (book 1.1.3)), with the spatial
Wick-measure lemma (`SpatialWickMeasuresTarget`, item D) and `E:joint-temporal-tail`
(`JointTemporalTailTarget`) as hypotheses: every two-chain diagram `F_{ε,δ,D}(t,t)` with
`m + n = 2k ≥ 2` (unequal and empty chains included) has a finite limit as all vertexwise spatial
and temporal widths tend to zero at arbitrary relative rates.  Step 1 is `E:spatial-wick-limit`
applied to the bounded continuous multiplier `capMult`; Step 3 is the squeeze
`F_{ε,η} ≤ F_{ε,δ} ≤ F_{ε,0} ≤ F_{ε,η} + C(N_1^{(1/η)}(1) + N_2^{(1/η)}(1)²)`
(`squeeze_limit`), the limit being `sup_η b_D(η)`. -/
theorem joint_diagram_limit (d : ℕ) (hW : SpatialWickMeasuresTarget d)
    (hT : JointTemporalTailTarget d) : JointDiagramLimitTarget d := by
  intro alpha α₀ Γ μ hH m n k hmn hk D hD t ht
  obtain ⟨b, hb, hF, -⟩ := joint_limit_aux hH hW hT hmn hk hD ht ht
  exact ⟨b, hb, hF⟩

/-- The common half-width map `ε ↦ (ε/2, …, ε/2)` sends `𝓝[>] 0` into the width filter. -/
theorem tendsto_half_widthFilter (N : ℕ) :
    Tendsto (fun ε : ℝ => fun _ : Fin N => ε / 2) (𝓝[>] 0) (widthFilter N) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : Tendsto (fun ε : ℝ => fun _ : Fin N => ε / 2) (𝓝 0) (𝓝 fun _ => 0 / 2) :=
      (continuous_pi fun _ => continuous_id.div_const 2).tendsto 0
    have e : (fun _ : Fin N => (0 : ℝ) / 2) = 0 := by funext; simp
    rw [e] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact fun i _ => half_pos (show (0 : ℝ) < ε from hε)

/-- **`DiagramLimits` for every `H:homog` covariance, with finite limits**
(`DiagramLimitsHomogTarget`; the M4 corollary of `L:joint-fixed-order`, TeX lines 1855-1858 with
825-832 at revision edf7085f (book 1.1.3)), from the same hypotheses as `joint_diagram_limit`:
M4's common-width diagram is `F_{ε/2,0,D}(t,t)` (`m8_m4_identity`), and the full-kernel limit of
`joint_limit_aux` gives the limit along `ε ↓ 0`; odd `m + n` has no pairings and `m = n = 0` is
the constant one. -/
theorem diagramLimits_homog (d : ℕ) (hW : SpatialWickMeasuresTarget d)
    (hT : JointTemporalTailTarget d) : DiagramLimitsHomogTarget d := by
  intro alpha α₀ Γ μ hH t ht
  have key : ∀ (m n : ℕ) (D : Fin (m + n) → Fin (m + n)), D ∈ Pi2 m n →
      ∃ b : ℝ≥0∞, b ≠ ⊤ ∧
        Tendsto (fun ε => diagram (waveGreen d) (covEps Γ ε) α₀ m n D t) (𝓝[>] 0) (𝓝 b) := by
    intro m n D hD
    rcases Nat.even_or_odd (m + n) with ⟨k, hk⟩ | hodd
    · rcases Nat.eq_zero_or_pos k with rfl | hk1
      · obtain ⟨rfl, rfl⟩ : m = 0 ∧ n = 0 := by omega
        refine ⟨1, ENNReal.one_ne_top, ?_⟩
        simp_rw [DiagramModel.diagram_zero_zero]
        exact tendsto_const_nhds
      · obtain ⟨b, hb, -, hU⟩ := joint_limit_aux hH hW hT (k := k) (by omega) hk1 hD ht ht
        refine ⟨b, hb, (hU.comp (tendsto_half_widthFilter _)).congr' ?_⟩
        filter_upwards [self_mem_nhdsWithin] with ε hε
        exact (m8_m4_identity d hH ε hε m n D hD t ht).symm
    · rw [DiagramModel.Pi2_odd hodd] at hD
      exact absurd hD (Finset.notMem_empty _)
  refine ⟨fun m n D hD => ?_, fun m n D hD => ?_⟩
  · obtain ⟨b, -, hb⟩ := key m n D hD
    rw [DiagramModel.diagramLim, hb.limUnder_eq]
    exact hb
  · obtain ⟨b, hbt, hb⟩ := key m n D hD
    rw [DiagramModel.diagramLim, hb.limUnder_eq]
    exact hbt

end Joint

end StratonovichHAMSecondMoment.JointFixedOrder
