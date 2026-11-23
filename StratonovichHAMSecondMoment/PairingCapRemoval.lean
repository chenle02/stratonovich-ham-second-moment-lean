module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L17, item L17-B, part 2: Step 5 of `L:pairing-product-envelope`, the removal of the finite
temporal cap (TeX lines 1631-1638, in the proof 1502-1639, at revision edf7085f (book 1.1.3)).

`cap_removal`: if the full bound `I_D(G) ≤ Env_D(G)` holds at the finite cap for every edge count
(`CappedEnvelopeAt`, D's output), then it holds without a cap (`PairingEnvelopeTarget`, the lemma).

Proof (the reading of INTERFACE.md §2, item B).  Cap every edge datum at `L ∈ ℕ`:
`A_e ∩ (0, L]` (`EdgeData.cap`); the capped data are capped (`CappedOn`).
* The norms `N_{1,e}`, `N_{2,e}` are monotone in `A_e` (`ν_e` increases with `A_e`, and `N_{1,e}`
  is an integral against `ν_e`, `N_{2,e}` a cap limit of pairings with `κ_L` increasing in `ν_e`),
  so every admissible product, hence the envelope, at the cap is at most the uncapped one, and the
  kernel hypotheses pass to the cap.
* The temporal kernels `κ_e` at the cap increase to `κ_e` as `L → ∞` (monotone convergence over
  `(0, L] ↑ (0, ∞)`, `ν_e` living on `A_e ⊆ (0, ∞)`), so the diagram integrands increase and the
  diagram integral is at most the supremum of the capped integrals (monotone convergence again).
Hence `I_D(G) ≤ sup_L I_D^{(L)}(G) ≤ sup_L Env_D^{(L)}(G) ≤ Env_D(G)`.  The TeX's "maximum of the
limits" of the finitely many admissible products is not needed in this direction: the capped
envelope is bounded by the uncapped one term by term.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.PairingConvolution

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Function
open scoped ENNReal Real

namespace StratonovichHAMSecondMoment.PairingCapRemoval

open HomogHypothesis (Rd)
open PairingInterface PairingConvolution

variable {d : ℕ}

/-! ### Monotonicity of the norms in `A_e` -/

theorem nuE_mono (a : ℝ) {A B : Set ℝ} (h : A ⊆ B) : nuE a A ≤ nuE a B := by
  refine Measure.le_iff.2 fun s hs => ?_
  simp only [nuE, withDensity_apply _ hs]
  exact lintegral_mono' (Measure.restrict_mono subset_rfl (Measure.restrict_mono h le_rfl)) le_rfl

theorem cap_A (E : EdgeData d) (L : ℝ) : (E.cap L).A = E.A ∩ Ioc 0 L := rfl

theorem cap_μ (E : EdgeData d) (L : ℝ) : (E.cap L).μ = E.μ := rfl

theorem nuE_cap_le (a : ℝ) (E : EdgeData d) (L : ℝ) : nuE a (E.cap L).A ≤ nuE a E.A :=
  nuE_mono a (by rw [cap_A]; exact inter_subset_left)

theorem N1_cap_le (a : ℝ) (E : EdgeData d) (L : ℝ) (G : Kernel d) :
    N1 a (E.cap L) G ≤ N1 a E G := by
  unfold N1
  rw [cap_μ]
  exact lintegral_mono' (nuE_cap_le a E L) le_rfl

theorem kappaCap_mono_measure {ν ν' : Measure ℝ} (h : ν ≤ ν') (L t : ℝ) :
    kappaCap ν L t ≤ kappaCap ν' L t :=
  lintegral_mono' (Measure.restrict_mono subset_rfl h) le_rfl

theorem NC_mono_measure {ν ν' : Measure ℝ} (h : ν ≤ ν') (μ : Measure (Rd d)) (G : Kernel d) :
    NC ν μ G ≤ NC ν' μ G := by
  unfold NC Q QL
  refine ENNReal.rpow_le_rpow (iSup_mono fun L => ?_) (by norm_num)
  exact lintegral_mono fun p => lintegral_mono fun q =>
    mul_le_mul' (mul_le_mul' le_rfl (kappaCap_mono_measure h _ _)) le_rfl

theorem N2_cap_le (a : ℝ) (E : EdgeData d) (L : ℝ) (G : Kernel d) :
    N2 a (E.cap L) G ≤ N2 a E G := by
  unfold N2
  rw [cap_μ]
  exact NC_mono_measure (nuE_cap_le a E L) E.μ G

/-- The capped edge data. -/
def capEd {α : Type*} (ed : Sym2 α → EdgeData d) (L : ℝ) : Sym2 α → EdgeData d :=
  fun e => (ed e).cap L

theorem prodP_cap_le {α : Type*} [DecidableEq α] (a : ℝ) (ed : Sym2 α → EdgeData d)
    (G : α → Kernel d) (L : ℝ) {Ls : Finset α} {D : Finset (Sym2 α)} (A : Adm Ls D) :
    prodP a (capEd ed L) G A ≤ prodP a ed G A := by
  unfold prodP
  refine mul_le_mul' (mul_le_mul' le_rfl (Finset.prod_le_prod fun l _ => ?_))
    (Finset.prod_le_prod fun l _ => ?_)
  · exact mul_le_mul' le_rfl (N1_cap_le a (ed (A.iota l)) L (G l))
  · exact N2_cap_le a (ed (A.iota l)) L (G l)

theorem env_cap_le {α : Type*} [DecidableEq α] (a : ℝ) (dg : TwoChain α)
    (ed : Sym2 α → EdgeData d) (G : α → Kernel d) (L : ℝ) :
    env a dg (capEd ed L) G ≤ env a dg ed G :=
  iSup_mono fun A => prodP_cap_le a ed G L A

theorem kernelHyp_cap {α : Type*} [DecidableEq α] {a : ℝ} {dg : TwoChain α}
    {ed : Sym2 α → EdgeData d} {G : α → Kernel d} (hK : KernelHyp a dg ed G) (L : ℝ) :
    KernelHyp a dg (capEd ed L) G :=
  ⟨hK.meas, hK.N0_lt, fun l hl e he => (N1_cap_le a (ed e) L (G l)).trans_lt (hK.N1_lt l hl e he),
    fun l hl e he => (N2_cap_le a (ed e) L (G l)).trans_lt (hK.N2_lt l hl e he)⟩

theorem cappedOn_capEd {α : Type*} (D : Finset (Sym2 α)) (ed : Sym2 α → EdgeData d) (L : ℝ) :
    CappedOn D (capEd ed L) :=
  ⟨L, fun e _ => by rw [capEd, cap_A]; exact inter_subset_right⟩

/-! ### Monotone convergence of the temporal kernels -/

theorem nuE_inter (a : ℝ) (A : Set ℝ) (L : ℝ) :
    nuE a (A ∩ Ioc 0 L) = (nuE a A).restrict (Ioc 0 L) := by
  rw [nuE, nuE, restrict_withDensity measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    inter_comm]

theorem kappa_cap_mono (a : ℝ) (E : EdgeData d) (t : ℝ) :
    Monotone fun L : ℕ => kappa a (E.cap L) t := fun L L' h =>
  lintegral_mono' (nuE_mono a (by
    rw [cap_A, cap_A]
    exact inter_subset_inter_right _ (Ioc_subset_Ioc_right (Nat.cast_le.2 h)))) le_rfl

theorem kappa_cap_iSup (a : ℝ) (E : EdgeData d) (t : ℝ) :
    ⨆ L : ℕ, kappa a (E.cap L) t = kappa a E t := by
  have hcap : ∀ L : ℕ, kappa a (E.cap L) t =
      ∫⁻ l in Ioc 0 (L : ℝ), ENNReal.ofReal (Real.exp (-(l * |t|))) ∂nuE a E.A := fun L => by
    unfold kappa
    rw [cap_A, nuE_inter]
  simp only [hcap]
  have hd : Directed (· ⊆ ·) fun L : ℕ => Ioc (0 : ℝ) L :=
    Monotone.directed_le fun L L' h => Ioc_subset_Ioc_right (Nat.cast_le.2 h)
  rw [← setLIntegral_iUnion_of_directed _ hd]
  have hU : (⋃ L : ℕ, Ioc (0 : ℝ) L) = Ioi 0 := by
    ext x
    simp only [mem_iUnion, mem_Ioc, mem_Ioi]
    constructor
    · rintro ⟨L, hx, -⟩; exact hx
    · intro hx
      obtain ⟨L, hL⟩ := exists_nat_ge x
      exact ⟨L, hx, hL⟩
  rw [hU, Measure.restrict_eq_self_of_ae_mem]
  · rfl
  · filter_upwards [ae_nuE_mem a E.measurableSet_A] with l hl using E.A_subset hl

theorem measurable_kappa (a : ℝ) (E : EdgeData d) : Measurable (kappa a E) := by
  unfold kappa
  have : Measurable fun x : ℝ × ℝ => ENNReal.ofReal (Real.exp (-(x.2 * |x.1|))) :=
    (Real.continuous_exp.comp (by fun_prop : Continuous fun x : ℝ × ℝ => -(x.2 * |x.1|)))
      |>.measurable.ennreal_ofReal
  exact this.lintegral_prod_right'

/-! ### The edge weights and the integrand -/

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
theorem edgeWeight_cap_iSup (a : ℝ) (E : EdgeData d) (z : α → ℝ × Rd d) (e : Sym2 α) :
    ⨆ L : ℕ, edgeWeight a (E.cap L) z e = edgeWeight a E z e := by
  induction e using Sym2.ind with
  | h j k =>
    simp only [edgeWeight_mk, cap_μ]
    rw [← ENNReal.iSup_mul, kappa_cap_iSup]

omit [DecidableEq α] in
theorem edgeWeight_cap_mono (a : ℝ) (E : EdgeData d) (z : α → ℝ × Rd d) (e : Sym2 α) :
    Monotone fun L : ℕ => edgeWeight a (E.cap L) z e := by
  induction e using Sym2.ind with
  | h j k =>
    intro L L' h
    simp only [edgeWeight_mk, cap_μ]
    exact mul_le_mul' (kappa_cap_mono a E _ h) le_rfl

omit [DecidableEq α] in
theorem measurable_edgeWeight (a : ℝ) (E : EdgeData d) (e : Sym2 α) :
    Measurable fun z : α → ℝ × Rd d => edgeWeight a E z e := by
  induction e using Sym2.ind with
  | h j k =>
    simp only [edgeWeight_mk]
    exact ((measurable_kappa a E).comp ((measurable_pi_apply j).fst.sub
      (measurable_pi_apply k).fst)).mul ((measurable_gammaOf E.μ).comp
        ((measurable_pi_apply j).snd.sub (measurable_pi_apply k).snd))

theorem measurable_predTime (dg : TwoChain α) (l : α) :
    Measurable fun z : α → ℝ × Rd d => dg.predTime z l := by
  unfold TwoChain.predTime
  rcases dg.pred l with _ | p
  · exact measurable_const
  · exact (measurable_pi_apply p).fst

theorem measurable_predPos (dg : TwoChain α) (l : α) :
    Measurable fun z : α → ℝ × Rd d => dg.predPos z l := by
  unfold TwoChain.predPos
  rcases dg.pred l with _ | p
  · exact measurable_const
  · exact (measurable_pi_apply p).snd

theorem measurableSet_posSimplex (dg : TwoChain α) :
    MeasurableSet (dg.posSimplex : Set (α → ℝ × Rd d)) := by
  have h : (dg.posSimplex : Set (α → ℝ × Rd d)) =
      ⋂ l ∈ dg.labels, {z : α → ℝ × Rd d | dg.predTime z l < (z l).1} := by
    ext z; simp [TwoChain.posSimplex]
  rw [h]
  exact Finset.measurableSet_biInter _ fun l _ =>
    measurableSet_lt (measurable_predTime dg l) (measurable_pi_apply l).fst

theorem measurable_integrand (a : ℝ) (dg : TwoChain α) (ed : Sym2 α → EdgeData d)
    (G : α → Kernel d) (hG : ∀ l ∈ dg.labels, Measurable (uncurry (G l))) :
    Measurable (integrand a dg ed G) := by
  unfold integrand
  refine Measurable.indicator ?_ (measurableSet_posSimplex dg)
  refine Measurable.mul (Finset.measurable_prod _ fun l hl => ?_)
    (Finset.measurable_prod _ fun e _ => measurable_edgeWeight a (ed e) e)
  exact (hG l hl).comp (f := fun z : α → ℝ × Rd d =>
    ((z l).1 - dg.predTime z l, (z l).2 - dg.predPos z l))
    (((measurable_pi_apply l).fst.sub (measurable_predTime dg l)).prodMk
      ((measurable_pi_apply l).snd.sub (measurable_predPos dg l)))

/-- `∏ sup ≤ sup ∏` for monotone families (ℕ is directed). -/
theorem prod_iSup_le_iSup_prod {ι : Type*} (s : Finset ι) (w : ι → ℕ → ℝ≥0∞)
    (hw : ∀ i, Monotone (w i)) : ∏ i ∈ s, ⨆ L, w i L ≤ ⨆ L, ∏ i ∈ s, w i L := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih =>
    rw [Finset.prod_insert hb]
    calc (⨆ L, w b L) * ∏ i ∈ s, ⨆ L, w i L ≤ (⨆ L, w b L) * ⨆ L, ∏ i ∈ s, w i L :=
          mul_le_mul' le_rfl ih
      _ = ⨆ L, ⨆ L', w b L * ∏ i ∈ s, w i L' := by
          rw [ENNReal.iSup_mul]
          exact iSup_congr fun L => ENNReal.mul_iSup _ _
      _ ≤ ⨆ M, w b M * ∏ i ∈ s, w i M :=
          iSup₂_le fun L L' => le_iSup_of_le (max L L') (mul_le_mul' (hw b (le_max_left _ _))
            (Finset.prod_le_prod fun i _ => hw i (le_max_right _ _)))
      _ = ⨆ M, ∏ i ∈ insert b s, w i M := by simp only [Finset.prod_insert hb]

theorem integrand_cap_mono (a : ℝ) (dg : TwoChain α) (ed : Sym2 α → EdgeData d)
    (G : α → Kernel d) : Monotone fun L : ℕ => integrand a dg (capEd ed L) G := by
  intro L L' h z
  unfold integrand
  refine Set.indicator_le_indicator (mul_le_mul' le_rfl (Finset.prod_le_prod fun e _ => ?_))
  exact edgeWeight_cap_mono a (ed e) z e h

theorem integrand_le_iSup_cap (a : ℝ) (dg : TwoChain α) (ed : Sym2 α → EdgeData d)
    (G : α → Kernel d) (z : α → ℝ × Rd d) :
    integrand a dg ed G z ≤ ⨆ L : ℕ, integrand a dg (capEd ed L) G z := by
  unfold integrand
  by_cases hz : z ∈ dg.posSimplex
  · simp only [Set.indicator_of_mem hz]
    rw [← ENNReal.mul_iSup]
    refine mul_le_mul' le_rfl ?_
    calc ∏ e ∈ dg.D, edgeWeight a (ed e) z e
        = ∏ e ∈ dg.D, ⨆ L : ℕ, edgeWeight a ((ed e).cap L) z e :=
          Finset.prod_congr rfl fun e _ => (edgeWeight_cap_iSup a (ed e) z e).symm
      _ ≤ ⨆ L : ℕ, ∏ e ∈ dg.D, edgeWeight a ((ed e).cap L) z e :=
          prod_iSup_le_iSup_prod _ (fun e L => edgeWeight a ((ed e).cap L) z e)
            fun e => edgeWeight_cap_mono a (ed e) z e
      _ = ⨆ L : ℕ, ∏ e ∈ dg.D, edgeWeight a (capEd ed L e) z e := rfl
  · simp [Set.indicator_of_notMem hz]

/-- The diagram integral is at most the supremum of the capped diagram integrals. -/
theorem pairingIntegral_le_iSup_cap (a : ℝ) (dg : TwoChain α) (ed : Sym2 α → EdgeData d)
    (G : α → Kernel d) (hG : ∀ l ∈ dg.labels, Measurable (uncurry (G l))) :
    pairingIntegral a dg ed G ≤ ⨆ L : ℕ, pairingIntegral a dg (capEd ed L) G := by
  unfold pairingIntegral lmarginal
  calc ∫⁻ y, integrand a dg ed G (updateFinset 0 dg.labels y) ∂_
      ≤ ∫⁻ y, ⨆ L : ℕ, integrand a dg (capEd ed L) G (updateFinset 0 dg.labels y) ∂_ :=
        lintegral_mono fun y => integrand_le_iSup_cap a dg ed G _
    _ = _ := lintegral_iSup
        (fun L => (measurable_integrand a dg (capEd ed L) G hG).comp measurable_updateFinset)
        (fun L L' h y => integrand_cap_mono a dg ed G h _)

/-! ### Step 5 -/

/-- **Step 5 of `L:pairing-product-envelope`: removal of the finite temporal cap** (TeX lines
1631-1638 at revision edf7085f (book 1.1.3)).  The full bound at the finite cap for every edge
count gives the lemma `E:pairing-product-envelope` (TeX 1492-1495) for arbitrary measurable
`A_e`. -/
theorem cap_removal {α : Type*} [DecidableEq α]
    (hcap : ∀ a : ℝ, 0 < a → a < 1 → ∀ n : ℕ, CappedEnvelopeAt d α a n) :
    PairingEnvelopeTarget d α := by
  intro a ha0 ha1 dg ed G hwf hK
  refine (pairingIntegral_le_iSup_cap a dg ed G hK.meas).trans (iSup_le fun L => ?_)
  exact (hcap a ha0 ha1 dg.D.card dg (capEd ed L) G hwf rfl (cappedOn_capEd dg.D ed L)
    (kernelHyp_cap hK L)).trans (env_cap_le a dg ed G L)

end StratonovichHAMSecondMoment.PairingCapRemoval
