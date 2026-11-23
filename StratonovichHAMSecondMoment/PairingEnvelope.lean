module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L17, item L17-D: Steps 3-4 of `L:pairing-product-envelope` at the finite temporal cap, the
induction on the number of edges, and the assembly of the lemma, against the frozen interface
`PairingInterface` (L17-0).

TeX anchors: main file `notes/notes_stratonovich_ham_second_moment.tex` at revision edf7085f
(book 1.1.3): the section setup lines 1434-1488; `L:pairing-product-envelope` statement lines
1489-1500 (`E:pairing-product-envelope` 1492-1495), proof 1502-1639: Step 3 (same-chain pairs
and the pair of terminal endpoints) lines 1598-1612, Step 4 (two distinct cross pairs) lines
1615-1627, Step 5 (cap removal) lines 1631-1638.

Results:
* `capped_envelope (hA : TranslatedCSTarget d) (hC : ∀ a n, RegionalHalfBoundTarget d α a n)
  a ha0 ha1 : ∀ n, CappedEnvelopeAt d α a n` (Steps 3-4 and the induction on `n`, TeX
  1598-1627, with `envelope_zero` at `n = 0`, TeX 1498-1499);
* `pairing_product_envelope (d) (α) : PairingEnvelopeTarget d α`: the lemma, whole and
  hypothesis-free, assembled from A (`translated_covariance_cs`, `translated_covariance_cs_capped`),
  B (`convolution_norms`, `cap_removal`), C (`regional_half_bound`) and `capped_envelope`;
* `pairing_product_envelope_of`, `pairing_product_envelope_of_capRemoval`: the same assembly
  with the B/C outputs as hypotheses (frozen statements).

The three cases of the induction step (`n + 1` edges), as in the TeX:
1. **an endpoint paired inside its own chain** (TeX 1599-1601): its partner `w` satisfies
   `s_w ≤ s_{p(v)}` on the whole positive simplex (`chain_le_predTime`), so the region
   `{s_w ≤ s_{p(v)}}` carries the whole integral and Step 2 (`hC`) gives `2 I ≤ env`
   (`same_chain_bound`); an empty chain is included;
2. **the two terminal endpoints paired to each other** (TeX 1601-1611): `lmarginal` peels the
   two endpoints (`lmarginal_insert'`); with the predecessors `(A,z)`, `(B,w)` fixed, the
   endpoint integral is `Q_L(T_{A,z} G_u⁰, T_{B,w} G_v⁰)` and `L:translated-covariance-CS`
   (`hA`) bounds it by `N_{2,e}(G_u) N_{2,e}(G_v)`; the rest is the diagram with both
   endpoints and their edge deleted, bounded by the induction hypothesis; `u, v` go into `Q_2`
   (`admPairQ2`, `terminal_pair_bound`);
3. **two distinct cross pairs** (TeX 1615-1627): the regions `{s_a ≤ s_q}` (remove `v`) and
   `{s_q < s_a, s_b ≤ s_p}` (remove `u`) cover the positive simplex (on it `s_b ≤ s_q < s_a ≤
   s_p`), each half-bound is `≤ env / 2`, and `x + y ≤ env` (`cross_pairs_bound`).

Readings (for the fidelity review): the regions of case 3 are the TeX's `{s_a ≤ s_q}` and its
complement intersected with `{s_b ≤ s_p}`, which holds on the whole positive simplex of the
complement (TeX 1621-1622: "the chain orders give `s_p ≥ s_a > s_q ≥ s_b`"); the frozen
`RegionalHalfBoundTarget` needs `s_b ≤ s_p` on all of the region, not only on the simplex.
In case 2 the finite cap `L` of `CappedOn` is used to identify `κ_e` with `κ_{e,⌈L⌉}`
(`kappa_eq_kappaCap`), and `Q_{⌈L⌉} ≤ Q` (the interface's cap supremum).  Everything is in
`ℝ≥0∞`; the finiteness hypotheses are those of `KernelHyp` (`N_{2,e} < ∞` is used for
`L:translated-covariance-CS` and to pull the constant out of the outer marginal).
-/
public import Mathlib
public import StratonovichHAMSecondMoment.PairingInterface
public import StratonovichHAMSecondMoment.PairingTranslatedCS
public import StratonovichHAMSecondMoment.PairingConvolution
public import StratonovichHAMSecondMoment.PairingCapRemoval
public import StratonovichHAMSecondMoment.PairingRegional

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Function Finset
open scoped ENNReal Real

namespace StratonovichHAMSecondMoment.PairingEnvelope

open HomogHypothesis (Rd)
open PairingInterface
open PairingTranslatedCS (measurable_gammaOf measurable_zeroExt)

variable {d : ℕ}

/-! ### Predecessors in a list -/

section ListPred

variable {α : Type*} [DecidableEq α]

theorem listPred_cons' (a : α) (l : List α) (y : α) :
    listPred (a :: l) y = if l.head? = some y then some a else listPred l y := by
  cases l with
  | nil => simp [listPred]
  | cons b r =>
    simp only [listPred, List.head?_cons, Option.some.injEq]
    by_cases h : y = b
    · subst h; simp
    · simp [h, Ne.symm h]

theorem listPred_mem' {l : List α} {x y : α} (h : listPred l y = some x) : x ∈ l ∧ y ∈ l := by
  induction l with
  | nil => simp [listPred] at h
  | cons a r ih =>
    rw [listPred_cons'] at h
    split_ifs at h with hy
    · cases h
      exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ (List.mem_of_mem_head? hy)⟩
    · obtain ⟨h1, h2⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩

theorem listPred_ne_self' {l : List α} (hl : l.Nodup) (y : α) : listPred l y ≠ some y := by
  induction l with
  | nil => simp [listPred]
  | cons a r ih =>
    rw [listPred_cons']
    have ha := (List.nodup_cons.1 hl).1
    split_ifs with hy
    · intro h
      cases h
      exact ha (List.mem_of_mem_head? hy)
    · exact ih (List.nodup_cons.1 hl).2

/-- Appending a last label does not change the other predecessors. -/
theorem listPred_concat (l : List α) {x y : α} (hy : y ≠ x) :
    listPred (l ++ [x]) y = listPred l y := by
  induction l with
  | nil => simp [listPred]
  | cons a r ih =>
    rw [List.cons_append, listPred_cons', listPred_cons', ih]
    cases r with
    | nil => simp [Ne.symm hy, listPred]
    | cons b r' => simp

/-- The predecessor of the appended last label is the old last label. -/
theorem listPred_concat_self {l : List α} (hl : l ≠ []) {x : α} (hx : x ∉ l) :
    listPred (l ++ [x]) x = some (l.getLast hl) := by
  induction l with
  | nil => exact absurd rfl hl
  | cons a r ih =>
    cases r with
    | nil => simp [listPred]
    | cons b r' =>
      have hb : b ≠ x := fun h => hx (h ▸ List.mem_cons_of_mem _ List.mem_cons_self)
      have hx' : x ∉ b :: r' := fun h => hx (List.mem_cons_of_mem _ h)
      show listPred (a :: (b :: r' ++ [x])) x = _
      have hh : ¬ ((b :: r' ++ [x]).head? = some x) := by simp [hb]
      rw [listPred_cons', ite_eq_right hh, ih (List.cons_ne_nil b r') hx']
      simp

/-- A predecessor in `l ++ [x]` lies in `l`. -/
theorem listPred_concat_mem {l : List α} {x y p : α} (h : listPred (l ++ [x]) y = some p) :
    p ∈ l := by
  induction l with
  | nil => simp [listPred] at h
  | cons a r ih =>
    rw [List.cons_append, listPred_cons'] at h
    split_ifs at h
    · cases h; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

/-- Along a chain whose consecutive times increase, every time is at most the last one. -/
theorem chain_le_last {β : Type*} (t : α → β) [LinearOrder β] {l : List α} (hl : l.Nodup)
    (hP : ∀ x y, listPred l y = some x → t x < t y) (hne : l ≠ []) :
    ∀ w ∈ l, t w ≤ t (l.getLast hne) := by
  induction l with
  | nil => exact absurd rfl hne
  | cons a r ih =>
    intro w hw
    cases r with
    | nil =>
      rw [List.mem_singleton] at hw
      subst hw; exact le_rfl
    | cons b r' =>
      have hnd := (List.nodup_cons.1 hl).2
      have hP' : ∀ x y, listPred (b :: r') y = some x → t x < t y := by
        intro x y h
        refine hP x y ?_
        rw [listPred_cons']
        split_ifs with hy
        · exfalso
          rw [List.head?_cons, Option.some.injEq] at hy
          subst hy
          rw [listPred_head hnd] at h
          simp at h
        · exact h
      have ih' := ih hnd hP' (List.cons_ne_nil b r')
      rw [List.getLast_cons (List.cons_ne_nil b r')]
      rcases List.mem_cons.1 hw with rfl | hw'
      · have hab : t w < t b := hP w b (by rw [listPred_cons']; simp)
        exact hab.le.trans (ih' b List.mem_cons_self)
      · exact ih' w hw'

end ListPred

/-! ### Chains, predecessors and the positive simplex -/

section Chains

variable {α : Type*} [DecidableEq α]

theorem mem_labels' {dg : TwoChain α} {l : α} : l ∈ dg.labels ↔ l ∈ dg.c1 ∨ l ∈ dg.c2 := by
  simp [TwoChain.labels]

theorem disj_c12' {dg : TwoChain α} (hwf : dg.WF) {x : α} (h1 : x ∈ dg.c1) (h2 : x ∈ dg.c2) :
    False :=
  (List.nodup_append.1 hwf.nodup).2.2 x h1 x h2 rfl

theorem pred_eq_c1 {dg : TwoChain α} {l : α} (h : l ∈ dg.c1) : dg.pred l = listPred dg.c1 l := by
  simp [TwoChain.pred, h]

theorem pred_eq_c2 {dg : TwoChain α} (hwf : dg.WF) {l : α} (h : l ∈ dg.c2) :
    dg.pred l = listPred dg.c2 l := by
  unfold TwoChain.pred
  rw [ite_eq_right (fun h1 => disj_c12' hwf h1 h)]

theorem pred_ne_self' {dg : TwoChain α} (hwf : dg.WF) (l : α) : dg.pred l ≠ some l := by
  unfold TwoChain.pred
  split_ifs
  · exact listPred_ne_self' hwf.nodup.of_append_left l
  · exact listPred_ne_self' hwf.nodup.of_append_right l

theorem pred_mem_labels {dg : TwoChain α} {l p : α} (h : dg.pred l = some p) :
    p ∈ dg.labels := by
  unfold TwoChain.pred at h
  split_ifs at h
  · exact mem_labels'.2 (Or.inl (listPred_mem' h).1)
  · exact mem_labels'.2 (Or.inr (listPred_mem' h).1)

theorem predTime_eq_of_pred (dg : TwoChain α) (z : α → ℝ × Rd d) {l p : α}
    (h : dg.pred l = some p) : dg.predTime z l = (z p).1 := by
  simp [TwoChain.predTime, h]

/-- Coordinates other than the predecessor do not change `predTime`, `predPos`. -/
theorem predTime_congr (dg : TwoChain α) {z z' : α → ℝ × Rd d} (l : α)
    (h : ∀ p, dg.pred l = some p → z p = z' p) :
    dg.predTime z l = dg.predTime z' l ∧ dg.predPos z l = dg.predPos z' l := by
  unfold TwoChain.predTime TwoChain.predPos
  cases hp : dg.pred l with
  | none => simp
  | some p => simp [h p hp]

theorem measurable_predTime (dg : TwoChain α) (l : α) :
    Measurable fun z : α → ℝ × Rd d => dg.predTime z l := by
  unfold TwoChain.predTime
  cases dg.pred l with
  | none => exact measurable_const
  | some p => exact (measurable_pi_apply p).fst

theorem measurable_predPos (dg : TwoChain α) (l : α) :
    Measurable fun z : α → ℝ × Rd d => dg.predPos z l := by
  unfold TwoChain.predPos
  cases dg.pred l with
  | none => exact measurable_const
  | some p => exact (measurable_pi_apply p).snd

/-- On the positive simplex, times increase along each chain. -/
theorem posSimplex_chain {dg : TwoChain α} (hwf : dg.WF) {z : α → ℝ × Rd d}
    (hz : z ∈ dg.posSimplex) {c : List α} (hc : c = dg.c1 ∨ c = dg.c2) :
    ∀ x y, listPred c y = some x → (z x).1 < (z y).1 := by
  intro x y h
  have hy : y ∈ c := (listPred_mem' h).2
  have hpred : dg.pred y = some x := by
    rcases hc with rfl | rfl
    · rw [pred_eq_c1 hy, h]
    · rw [pred_eq_c2 hwf hy, h]
  have hyL : y ∈ dg.labels := by
    rcases hc with rfl | rfl
    · exact mem_labels'.2 (Or.inl hy)
    · exact mem_labels'.2 (Or.inr hy)
  have := hz y hyL
  rwa [predTime_eq_of_pred dg z hpred] at this

/-- **Chain order** (TeX 1599-1600, 1621-1622): a label before the endpoint `v` of its chain
has time at most `s_{p(v)}` on the positive simplex. -/
theorem chain_le_predTime {dg : TwoChain α} (hwf : dg.WF) {z : α → ℝ × Rd d}
    (hz : z ∈ dg.posSimplex) {c' : List α} {v w : α}
    (hc : dg.c1 = c' ++ [v] ∨ dg.c2 = c' ++ [v]) (hw : w ∈ c') :
    (z w).1 ≤ dg.predTime z v := by
  have hne : c' ≠ [] := List.ne_nil_of_mem hw
  have hnd : (c' ++ [v]).Nodup := by
    rcases hc with h | h
    · rw [← h]; exact hwf.nodup.of_append_left
    · rw [← h]; exact hwf.nodup.of_append_right
  have hv : v ∉ c' := fun h => (List.nodup_append.1 hnd).2.2 v h v List.mem_cons_self rfl
  have hchain : ∀ x y, listPred (c' ++ [v]) y = some x → (z x).1 < (z y).1 := by
    rcases hc with h | h
    · exact posSimplex_chain hwf hz (c := c' ++ [v]) (Or.inl h.symm)
    · exact posSimplex_chain hwf hz (c := c' ++ [v]) (Or.inr h.symm)
  have hchain' : ∀ x y, listPred c' y = some x → (z x).1 < (z y).1 := by
    intro x y h
    have hyv : y ≠ v := fun hyv => hv (hyv ▸ (listPred_mem' h).2)
    exact hchain x y (by rw [listPred_concat c' hyv, h])
  have hpv : dg.pred v = some (c'.getLast hne) := by
    rcases hc with h | h
    · rw [pred_eq_c1 (by rw [h]; simp), h, listPred_concat_self hne hv]
    · rw [pred_eq_c2 hwf (by rw [h]; simp), h, listPred_concat_self hne hv]
  rw [predTime_eq_of_pred dg z hpv]
  exact chain_le_last (fun l => (z l).1) (List.nodup_append.1 hnd).1 hchain' hne w hw

end Chains

/-! ### Measurability of the diagram integrand -/

section Measurability

variable {α : Type*} [DecidableEq α]

theorem measurableSet_posSimplex (dg : TwoChain α) :
    MeasurableSet (dg.posSimplex : Set (α → ℝ × Rd d)) := by
  have e : (dg.posSimplex : Set (α → ℝ × Rd d)) =
      ⋂ l ∈ dg.labels, {z : α → ℝ × Rd d | dg.predTime z l < (z l).1} := by
    ext z; simp [TwoChain.posSimplex]
  rw [e]
  exact Finset.measurableSet_biInter _ fun l _ =>
    measurableSet_lt (measurable_predTime dg l) (measurable_pi_apply l).fst

theorem sFinite_nuE (a : ℝ) (A : Set ℝ) : SFinite (nuE a A) := by
  unfold nuE; infer_instance

theorem measurable_kappa (a : ℝ) (E : EdgeData d) : Measurable (kappa a E) := by
  have := sFinite_nuE a E.A
  unfold kappa
  have : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-(p.2 * |p.1|))) :=
    ENNReal.measurable_ofReal.comp (Continuous.measurable (by fun_prop))
  exact this.lintegral_prod_right'

omit [DecidableEq α] in
theorem measurable_edgeWeight (a : ℝ) (E : EdgeData d) (e : Sym2 α) :
    Measurable fun z : α → ℝ × Rd d => edgeWeight a E z e := by
  induction e using Sym2.ind with
  | h j k =>
    simp only [edgeWeight_mk]
    exact ((measurable_kappa a E).comp
      ((measurable_pi_apply j).fst.sub (measurable_pi_apply k).fst)).mul
      ((measurable_gammaOf E.μ).comp ((measurable_pi_apply j).snd.sub (measurable_pi_apply k).snd))

theorem measurable_integrand {a : ℝ} {dg : TwoChain α} {ed : Sym2 α → EdgeData d}
    {G : α → Kernel d} (hK : KernelHyp a dg ed G) : Measurable (integrand a dg ed G) := by
  unfold integrand
  refine Measurable.indicator (Measurable.mul ?_ ?_) (measurableSet_posSimplex dg)
  · refine Finset.measurable_prod _ fun l hl => ?_
    exact (hK.meas l hl).comp (f := fun z : α → ℝ × Rd d =>
      ((z l).1 - dg.predTime z l, (z l).2 - dg.predPos z l))
      (((measurable_pi_apply l).fst.sub (measurable_predTime dg l)).prodMk
        ((measurable_pi_apply l).snd.sub (measurable_predPos dg l)))
  · exact Finset.measurable_prod _ fun e _ => measurable_edgeWeight a (ed e) e

end Measurability

/-! ### Regions -/

section Regions

variable {α : Type*} [DecidableEq α]

/-- If a region contains the positive simplex, it carries the whole diagram integral. -/
theorem pairingIntegral_le_region (a : ℝ) (dg : TwoChain α) (ed : Sym2 α → EdgeData d)
    (G : α → Kernel d) {R : Set (α → ℝ × Rd d)} (hR : ∀ z ∈ dg.posSimplex, z ∈ R) :
    pairingIntegral a dg ed G ≤ regionIntegral a dg ed G R := by
  unfold pairingIntegral regionIntegral
  refine lmarginal_mono (fun z => ?_) 0
  by_cases hz : z ∈ dg.posSimplex
  · rw [indicator_of_mem (hR z hz)]
  · simp [integrand, indicator_of_notMem hz]

/-- Two regions covering the positive simplex. -/
theorem pairingIntegral_le_add {a : ℝ} {dg : TwoChain α} {ed : Sym2 α → EdgeData d}
    {G : α → Kernel d} (hK : KernelHyp a dg ed G) {R₁ R₂ : Set (α → ℝ × Rd d)}
    (hR₁ : MeasurableSet R₁) (hR : ∀ z ∈ dg.posSimplex, z ∈ R₁ ∨ z ∈ R₂) :
    pairingIntegral a dg ed G ≤ regionIntegral a dg ed G R₁ + regionIntegral a dg ed G R₂ := by
  have hm := measurable_integrand hK
  unfold pairingIntegral regionIntegral lmarginal
  refine le_trans (lintegral_mono fun y => ?_) (lintegral_add_left
    (f := fun y => R₁.indicator (integrand a dg ed G) (updateFinset 0 dg.labels y))
    ((hm.indicator hR₁).comp measurable_updateFinset) _).le
  set z := updateFinset (0 : α → ℝ × Rd d) dg.labels y
  by_cases hz : z ∈ dg.posSimplex
  · rcases hR z hz with h | h
    · rw [indicator_of_mem h]; exact le_self_add
    · rw [indicator_of_mem (s := R₂) h]; exact le_add_self
  · simp [integrand, indicator_of_notMem hz]

theorem add_le_of_halves {x y E : ℝ≥0∞} (hx : 2 * x ≤ E) (hy : 2 * y ≤ E) : x + y ≤ E := by
  have : 2 * (x + y) ≤ 2 * E := by
    calc 2 * (x + y) = 2 * x + 2 * y := by ring
      _ ≤ E + E := add_le_add hx hy
      _ = 2 * E := by ring
  exact (ENNReal.mul_le_mul_iff_right two_ne_zero ENNReal.ofNat_ne_top).1 this

theorem le_two_mul (x : ℝ≥0∞) : x ≤ 2 * x := by
  rw [two_mul]; exact le_self_add

/-- The region `{s_w ≤ s_{p(v)}}`: measurable and independent of `(s_v, x_v)`. -/
theorem region_props {dg : TwoChain α} (hwf : dg.WF) {v w : α} (hwv : w ≠ v) :
    MeasurableSet {z : α → ℝ × Rd d | (z w).1 ≤ dg.predTime z v} ∧
    ∀ z z' : α → ℝ × Rd d, (∀ l, l ≠ v → z l = z' l) →
      ((z w).1 ≤ dg.predTime z v ↔ (z' w).1 ≤ dg.predTime z' v) := by
  refine ⟨measurableSet_le (measurable_pi_apply w).fst (measurable_predTime dg v),
    fun z z' h => ?_⟩
  have h1 : dg.predTime z v = dg.predTime z' v :=
    (predTime_congr dg v fun p hp => h p (fun hpv => pred_ne_self' hwf v (hpv ▸ hp))).1
  rw [h w hwv, h1]

end Regions

/-! ### Step 3, same-chain pairs (TeX 1599-1601) -/

section SameChain

variable {α : Type*} [DecidableEq α]

/-- **Same-chain pair** (TeX 1599-1601): an endpoint `v` paired with `w` before it on its own
chain; the half-bound holds on the whole domain. -/
theorem same_chain_bound {a : ℝ} {n : ℕ} (ha0 : 0 < a) (ha1 : a < 1)
    (hC : RegionalHalfBoundTarget d α a n) (IH : CappedEnvelopeAt d α a n)
    {dg : TwoChain α} {ed : Sym2 α → EdgeData d} {G : α → Kernel d} (hwf : dg.WF)
    (hcard : dg.D.card = n + 1) (hcap : CappedOn dg.D ed) (hK : KernelHyp a dg ed G)
    {c' : List α} {v w : α} (hc : dg.c1 = c' ++ [v] ∨ dg.c2 = c' ++ [v]) (hw : w ∈ c')
    (he : s(v, w) ∈ dg.D) : pairingIntegral a dg ed G ≤ env a dg ed G := by
  have hnd : (c' ++ [v]).Nodup := by
    rcases hc with h | h
    · rw [← h]; exact hwf.nodup.of_append_left
    · rw [← h]; exact hwf.nodup.of_append_right
  have hwv : w ≠ v := fun h =>
    (List.nodup_append.1 hnd).2.2 v (h ▸ hw) v List.mem_cons_self rfl
  have hend : dg.IsEndpoint v := by
    unfold TwoChain.IsEndpoint
    rcases hc with h | h
    · left; rw [h]; simp
    · right; rw [h]; simp
  obtain ⟨hRm, hRind⟩ := region_props (d := d) hwf hwv
  have h2 := hC ha0 ha1 IH dg ed G hwf hcard hcap hK v w
    {z | (z w).1 ≤ dg.predTime z v} hend (by rw [Sym2.eq_swap]; exact he) hRm hRind
    (fun z hz => hz)
  calc pairingIntegral a dg ed G
      ≤ regionIntegral a dg ed G {z | (z w).1 ≤ dg.predTime z v} :=
        pairingIntegral_le_region a dg ed G fun z hz => chain_le_predTime hwf hz hc hw
    _ ≤ 2 * regionIntegral a dg ed G {z | (z w).1 ≤ dg.predTime z v} := le_two_mul _
    _ ≤ _ := h2

end SameChain

/-! ### Step 4, two distinct cross pairs (TeX 1615-1627) -/

section Cross

variable {α : Type*} [DecidableEq α]

/-- **Two distinct cross pairs** (TeX 1615-1627): `v` (end of chain 2) is paired with `w ∈ c1'`
and `u` (end of chain 1) with `b ∈ c2'`; the regions `{s_w ≤ s_{p(v)}}` and
`{s_{p(v)} < s_w, s_b ≤ s_{p(u)}}` cover the positive simplex. -/
theorem cross_pairs_bound {a : ℝ} {n : ℕ} (ha0 : 0 < a) (ha1 : a < 1)
    (hC : RegionalHalfBoundTarget d α a n) (IH : CappedEnvelopeAt d α a n)
    {dg : TwoChain α} {ed : Sym2 α → EdgeData d} {G : α → Kernel d} (hwf : dg.WF)
    (hcard : dg.D.card = n + 1) (hcap : CappedOn dg.D ed) (hK : KernelHyp a dg ed G)
    {c1' c2' : List α} {u v w b : α} (h1 : dg.c1 = c1' ++ [u]) (h2 : dg.c2 = c2' ++ [v])
    (hw : w ∈ c1') (hb : b ∈ c2') (hvw : s(v, w) ∈ dg.D) (hub : s(u, b) ∈ dg.D) :
    pairingIntegral a dg ed G ≤ env a dg ed G := by
  have hu1 : u ∈ dg.c1 := by rw [h1]; simp
  have hv2 : v ∈ dg.c2 := by rw [h2]; simp
  have hw1 : w ∈ dg.c1 := by rw [h1]; exact List.mem_append_left _ hw
  have hb2 : b ∈ dg.c2 := by rw [h2]; exact List.mem_append_left _ hb
  have hwv : w ≠ v := fun h => disj_c12' hwf hw1 (h ▸ hv2)
  have hbu : b ≠ u := fun h => disj_c12' hwf (h ▸ hu1) hb2
  have hnd1 : (c1' ++ [u]).Nodup := by rw [← h1]; exact hwf.nodup.of_append_left
  have hwu : w ≠ u := fun h =>
    (List.nodup_append.1 hnd1).2.2 u (h ▸ hw) u List.mem_cons_self rfl
  have hendv : dg.IsEndpoint v := Or.inr (by rw [h2]; simp)
  have hendu : dg.IsEndpoint u := Or.inl (by rw [h1]; simp)
  -- region 1: remove `v`
  obtain ⟨hR1m, hR1ind⟩ := region_props (d := d) hwf hwv
  have hx := hC ha0 ha1 IH dg ed G hwf hcard hcap hK v w
    {z | (z w).1 ≤ dg.predTime z v} hendv (by rw [Sym2.eq_swap]; exact hvw) hR1m hR1ind
    (fun z hz => hz)
  -- region 2: remove `u`
  set R₂ : Set (α → ℝ × Rd d) :=
    {z | dg.predTime z v < (z w).1 ∧ (z b).1 ≤ dg.predTime z u} with hR₂
  have hpv : ∀ p, dg.pred v = some p → p ≠ u := by
    intro p hp hpu
    rw [pred_eq_c2 hwf hv2] at hp
    exact disj_c12' hwf hu1 (hpu ▸ (listPred_mem' hp).1)
  have hR2m : MeasurableSet R₂ :=
    (measurableSet_lt (measurable_predTime dg v) (measurable_pi_apply w).fst).inter
      (measurableSet_le (measurable_pi_apply b).fst (measurable_predTime dg u))
  have hR2ind : ∀ z z' : α → ℝ × Rd d, (∀ l, l ≠ u → z l = z' l) → (z ∈ R₂ ↔ z' ∈ R₂) := by
    intro z z' h
    have e1 : dg.predTime z v = dg.predTime z' v :=
      (predTime_congr dg v fun p hp => h p (hpv p hp)).1
    have e2 : dg.predTime z u = dg.predTime z' u :=
      (predTime_congr dg u fun p hp => h p (fun hpu => pred_ne_self' hwf u (hpu ▸ hp))).1
    simp only [hR₂, Set.mem_ofPred_eq, e1, e2, h w hwu, h b hbu]
  have hy := hC ha0 ha1 IH dg ed G hwf hcard hcap hK u b R₂ hendu
    (by rw [Sym2.eq_swap]; exact hub) hR2m hR2ind (fun z hz => hz.2)
  refine le_trans (pairingIntegral_le_add hK hR1m fun z hz => ?_) (add_le_of_halves hx hy)
  by_cases h : (z w).1 ≤ dg.predTime z v
  · exact Or.inl h
  · refine Or.inr ⟨lt_of_not_ge h, ?_⟩
    calc (z b).1 ≤ dg.predTime z v := chain_le_predTime hwf hz (Or.inr h2) hb
      _ ≤ (z w).1 := (lt_of_not_ge h).le
      _ ≤ dg.predTime z u := chain_le_predTime hwf hz (Or.inl h1) hw

end Cross

/-! ### Step 3, the pair of terminal endpoints (TeX 1601-1611) -/

section Terminal

variable {α : Type*} [DecidableEq α]

/-- `ν_e((0,L]) < ∞` for `a > 0` (TeX 1512-1513: "its measure is finite since `a > 0`"). -/
theorem nuE_Ioc_lt_top {a : ℝ} (ha : 0 < a) (A : Set ℝ) (L : ℝ) : nuE a A (Ioc 0 L) < ∞ := by
  rcases le_or_gt L 0 with hL | hL
  · rw [Ioc_eq_empty (not_lt.2 hL)]; simp
  unfold nuE
  rw [withDensity_apply _ measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc]
  refine lt_of_le_of_lt (lintegral_mono_set inter_subset_left) ?_
  have hi : IntegrableOn (fun l : ℝ => (Real.Gamma a)⁻¹ * l ^ (a - 1)) (Ioc 0 L) := by
    have := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := L) (r := a - 1)
      (by linarith)
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hL.le).1 this).const_mul _
  exact hi.lintegral_lt_top

/-- On a capped edge, `κ_e = κ_{e,L'}` for every cap `L' ≥ L`. -/
theorem kappa_eq_kappaCap (a : ℝ) (E : EdgeData d) {L L' : ℝ} (hA : E.A ⊆ Ioc 0 L)
    (hL : L ≤ L') (t : ℝ) : kappa a E t = kappaCap (nuE a E.A) L' t := by
  unfold kappa kappaCap
  rw [Measure.restrict_eq_self_of_ae_mem]
  have h : ∀ᵐ l ∂nuE a E.A, l ∈ E.A := by
    unfold nuE
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem E.measurableSet_A)
  filter_upwards [h] with l hl
  exact ⟨(hA hl).1, (hA hl).2.trans hL⟩

/-- The integrand depends only on the label coordinates. -/
theorem integrand_congr {a : ℝ} {dg : TwoChain α} (hwf : dg.WF) (ed : Sym2 α → EdgeData d)
    (G : α → Kernel d) {z z' : α → ℝ × Rd d} (h : ∀ l ∈ dg.labels, z l = z' l) :
    integrand a dg ed G z = integrand a dg ed G z' := by
  have ht : ∀ l, dg.predTime z l = dg.predTime z' l ∧ dg.predPos z l = dg.predPos z' l :=
    fun l => predTime_congr dg l fun p hp => h p (pred_mem_labels hp)
  have hpos : z ∈ dg.posSimplex ↔ z' ∈ dg.posSimplex := by
    show (∀ l ∈ dg.labels, dg.predTime z l < (z l).1) ↔
      (∀ l ∈ dg.labels, dg.predTime z' l < (z' l).1)
    exact forall₂_congr fun l hl => by rw [(ht l).1, h l hl]
  have hG : ∏ l ∈ dg.labels, G l ((z l).1 - dg.predTime z l) ((z l).2 - dg.predPos z l) =
      ∏ l ∈ dg.labels, G l ((z' l).1 - dg.predTime z' l) ((z' l).2 - dg.predPos z' l) :=
    prod_congr rfl fun l hl => by rw [h l hl, (ht l).1, (ht l).2]
  have hE : ∏ e ∈ dg.D, edgeWeight a (ed e) z e = ∏ e ∈ dg.D, edgeWeight a (ed e) z' e := by
    refine prod_congr rfl fun e he => ?_
    induction e using Sym2.ind with
    | h j k =>
      rw [edgeWeight_mk, edgeWeight_mk, h j ((hwf.edge _ he).2 j (Sym2.mem_mk_left j k)),
        h k ((hwf.edge _ he).2 k (Sym2.mem_mk_right j k))]
  unfold integrand
  by_cases hz : z ∈ dg.posSimplex
  · rw [indicator_of_mem hz, indicator_of_mem (hpos.1 hz), hG, hE]
  · rw [indicator_of_notMem hz, indicator_of_notMem (fun h' => hz (hpos.2 h'))]

theorem adm_sub0 {L : Finset α} {D : Finset (Sym2 α)} (A : Adm L D) : A.Q0 ⊆ L := by
  intro x hx; rw [← A.cover]; simp [hx]

theorem adm_sub1 {L : Finset α} {D : Finset (Sym2 α)} (A : Adm L D) : A.Q1 ⊆ L := by
  intro x hx; rw [← A.cover]; simp [hx]

theorem adm_sub2 {L : Finset α} {D : Finset (Sym2 α)} (A : Adm L D) : A.Q2 ⊆ L := by
  intro x hx; rw [← A.cover]; simp [hx]

/-- The iota of `admPairQ2`. -/
def pairIota (iota : α → Sym2 α) (u v : α) (l : α) : Sym2 α :=
  if l = u ∨ l = v then s(u, v) else iota l

/-- **Terminal pair into `Q₂`** (TeX 1610-1611: "adding `u, v` to `Q_2`"): from an admissible
assignment of the reduced labels and matching, put `u, v` into `Q₂` with `ι u = ι v = {u,v}`. -/
def admPairQ2 {L : Finset α} {D : Finset (Sym2 α)} (A : Adm L D) (u v : α) (hu : u ∉ L)
    (hv : v ∉ L) (huv : u ≠ v) (hD : s(u, v) ∉ D) {L₂ : Finset α} {D₂ : Finset (Sym2 α)}
    (hL₂ : L₂ = insert u (insert v L)) (hD₂ : D₂ = insert s(u, v) D) : Adm L₂ D₂ where
  Q0 := A.Q0
  Q1 := A.Q1
  Q2 := insert u (insert v A.Q2)
  iota := pairIota A.iota u v
  cover := by
    rw [hL₂]; ext x
    have h := Finset.ext_iff.1 A.cover x
    simp only [Finset.mem_union, Finset.mem_insert] at h ⊢; tauto
  d01 := A.d01
  d02 := by
    rw [Finset.disjoint_insert_right, Finset.disjoint_insert_right]
    exact ⟨fun h => hu (adm_sub0 A h), fun h => hv (adm_sub0 A h), A.d02⟩
  d12 := by
    rw [Finset.disjoint_insert_right, Finset.disjoint_insert_right]
    exact ⟨fun h => hu (adm_sub1 A h), fun h => hv (adm_sub1 A h), A.d12⟩
  card01 := A.card01
  mapsTo := by
    intro l hl
    rw [hD₂]
    unfold pairIota
    by_cases h : l = u ∨ l = v
    · rw [ite_eq_left h]; exact Finset.mem_insert_self _ _
    · rw [ite_eq_right h]
      refine Finset.mem_insert_of_mem (A.mapsTo l ?_)
      simp only [Finset.mem_union, Finset.mem_insert] at hl ⊢
      tauto
  edge := by
    intro e' he'
    rw [hD₂] at he'
    have hne : ∀ l ∈ L, ¬ (l = u ∨ l = v) := fun l hl h => by
      rcases h with rfl | rfl
      · exact hu hl
      · exact hv hl
    have hf1 : (A.Q1.filter fun l => pairIota A.iota u v l = e') =
        A.Q1.filter fun l => A.iota l = e' :=
      Finset.filter_congr fun l hl => by
        rw [pairIota, ite_eq_right (hne l (adm_sub1 A hl))]
    have hf2 : (A.Q2.filter fun l => pairIota A.iota u v l = e') =
        A.Q2.filter fun l => A.iota l = e' :=
      Finset.filter_congr fun l hl => by
        rw [pairIota, ite_eq_right (hne l (adm_sub2 A hl))]
    have hu' : pairIota A.iota u v u = s(u, v) := by simp [pairIota]
    have hv' : pairIota A.iota u v v = s(u, v) := by simp [pairIota]
    rw [hf1, Finset.filter_insert, Finset.filter_insert, hu', hv', hf2]
    rcases Finset.mem_insert.1 he' with rfl | he'D
    · right
      have h1 : (A.Q1.filter fun l => A.iota l = s(u, v)) = ∅ :=
        Finset.filter_eq_empty_iff.2 fun l hl h => hD (h ▸ A.mapsTo l (Finset.mem_union_left _ hl))
      have h2 : (A.Q2.filter fun l => A.iota l = s(u, v)) = ∅ :=
        Finset.filter_eq_empty_iff.2 fun l hl h => hD (h ▸ A.mapsTo l (Finset.mem_union_right _ hl))
      rw [h1, h2]
      simp [huv]
    · have hne' : s(u, v) ≠ e' := fun h => hD (h ▸ he'D)
      simp only [hne', ite_false]
      exact A.edge e' he'D

theorem prodP_pairQ2 (a : ℝ) (ed : Sym2 α → EdgeData d) (G : α → Kernel d) {L : Finset α}
    {D : Finset (Sym2 α)} (A : Adm L D) (u v : α) (hu : u ∉ L) (hv : v ∉ L) (huv : u ≠ v)
    (hD : s(u, v) ∉ D) {L₂ : Finset α} {D₂ : Finset (Sym2 α)}
    (hL₂ : L₂ = insert u (insert v L)) (hD₂ : D₂ = insert s(u, v) D) :
    prodP a ed G (admPairQ2 A u v hu hv huv hD hL₂ hD₂) =
      prodP a ed G A * (N2 a (ed s(u, v)) (G u) * N2 a (ed s(u, v)) (G v)) := by
  have hne : ∀ l ∈ L, ¬ (l = u ∨ l = v) := fun l hl h => by
    rcases h with rfl | rfl
    · exact hu hl
    · exact hv hl
  have e1 : ∏ l ∈ A.Q1, 2 * N1 a (ed (pairIota A.iota u v l)) (G l) =
      ∏ l ∈ A.Q1, 2 * N1 a (ed (A.iota l)) (G l) :=
    prod_congr rfl fun l hl => by rw [pairIota, ite_eq_right (hne l (adm_sub1 A hl))]
  have e2 : ∏ l ∈ A.Q2, N2 a (ed (pairIota A.iota u v l)) (G l) =
      ∏ l ∈ A.Q2, N2 a (ed (A.iota l)) (G l) :=
    prod_congr rfl fun l hl => by rw [pairIota, ite_eq_right (hne l (adm_sub2 A hl))]
  have hu2 : u ∉ insert v A.Q2 := by
    rw [Finset.mem_insert]; rintro (h | h)
    · exact huv h
    · exact hu (adm_sub2 A h)
  have hv2 : v ∉ A.Q2 := fun h => hv (adm_sub2 A h)
  simp only [prodP, admPairQ2]
  rw [prod_insert hu2, prod_insert hv2, e1, e2]
  simp only [pairIota, true_or, or_true, ite_true]
  ring

/-- **The pair of terminal endpoints** (TeX 1601-1611): if the two terminal endpoints are paired
to each other, `L:translated-covariance-CS` with the separate origins of their predecessors
bounds the endpoint integral by `N_{2,e}(G_u) N_{2,e}(G_v)`, and the induction hypothesis
bounds the rest; `u, v` go into `Q₂`. -/
theorem terminal_pair_bound (hA : TranslatedCSTarget d) {a : ℝ} (ha0 : 0 < a) {n : ℕ}
    (IH : CappedEnvelopeAt d α a n) {dg : TwoChain α} {ed : Sym2 α → EdgeData d}
    {G : α → Kernel d} (hwf : dg.WF) (hcard : dg.D.card = n + 1) (hcap : CappedOn dg.D ed)
    (hK : KernelHyp a dg ed G) {c1' c2' : List α} {u v : α} (h1 : dg.c1 = c1' ++ [u])
    (h2 : dg.c2 = c2' ++ [v]) (he : s(u, v) ∈ dg.D) :
    pairingIntegral a dg ed G ≤ env a dg ed G := by
  set e : Sym2 α := s(u, v) with he_def
  set dg' : TwoChain α := ⟨c1', c2', dg.D.erase e⟩ with hdg'
  -- list facts
  have hu1 : u ∈ dg.c1 := by rw [h1]; simp
  have hv2 : v ∈ dg.c2 := by rw [h2]; simp
  have hnd1 : (c1' ++ [u]).Nodup := by rw [← h1]; exact hwf.nodup.of_append_left
  have hnd2 : (c2' ++ [v]).Nodup := by rw [← h2]; exact hwf.nodup.of_append_right
  have hu1' : u ∉ c1' := fun h => (List.nodup_append.1 hnd1).2.2 u h u List.mem_cons_self rfl
  have hv2' : v ∉ c2' := fun h => (List.nodup_append.1 hnd2).2.2 v h v List.mem_cons_self rfl
  have hu2 : u ∉ dg.c2 := fun h => disj_c12' hwf hu1 h
  have hv1 : v ∉ dg.c1 := fun h => disj_c12' hwf h hv2
  have hu2' : u ∉ c2' := fun h => hu2 (by rw [h2]; exact List.mem_append_left _ h)
  have hv1' : v ∉ c1' := fun h => hv1 (by rw [h1]; exact List.mem_append_left _ h)
  have huv : u ≠ v := fun h => hu2 (h ▸ hv2)
  have hmem1 : ∀ {l}, l ∈ c1' → l ∈ dg.c1 := fun h => by
    rw [h1]; exact List.mem_append_left _ h
  have hmem2 : ∀ {l}, l ∈ c2' → l ∈ dg.c2 := fun h => by
    rw [h2]; exact List.mem_append_left _ h
  have hL' : ∀ l, l ∈ dg'.labels ↔ l ∈ c1' ∨ l ∈ c2' := fun l => mem_labels'
  have huL' : u ∉ dg'.labels := by rw [hL']; tauto
  have hvL' : v ∉ dg'.labels := by rw [hL']; tauto
  have hlabels : dg.labels = insert u (insert v dg'.labels) := by
    ext l
    rw [Finset.mem_insert, Finset.mem_insert, mem_labels', hL', h1, h2]
    simp only [List.mem_append, List.mem_singleton]
    tauto
  have huL : u ∈ dg.labels := by rw [hlabels]; exact Finset.mem_insert_self _ _
  have hvL : v ∈ dg.labels := by rw [hlabels]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hsubL : ∀ l ∈ dg'.labels, l ∈ dg.labels := fun l hl => by
    rw [hlabels]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hl)
  have huv' : u ∉ insert v dg'.labels := by
    rw [Finset.mem_insert]; rintro (h | h)
    · exact huv h
    · exact huL' h
  -- the matching
  have huniq : ∀ e' ∈ dg.D, ∀ x ∈ e', (x = u ∨ x = v) → e' = e := by
    intro e' he' x hx hxuv
    have hxe : x ∈ e := by rcases hxuv with rfl | rfl <;> simp [he_def]
    have hxL : x ∈ dg.labels := (hwf.edge _ he).2 x hxe
    obtain ⟨e0, _, hu⟩ := hwf.cover x hxL
    rw [hu e' ⟨he', hx⟩, hu e ⟨he, hxe⟩]
  have hwf' : dg'.WF := by
    refine ⟨?_, ?_, ?_⟩
    · refine hwf.nodup.sublist ?_
      rw [h1, h2]
      exact (List.sublist_append_left c1' [u]).append (List.sublist_append_left c2' [v])
    · intro e' he'
      obtain ⟨hne, heD⟩ := Finset.mem_erase.1 he'
      refine ⟨(hwf.edge e' heD).1, fun x hx => ?_⟩
      have hxL := (hwf.edge e' heD).2 x hx
      rw [mem_labels', h1, h2] at hxL
      rw [hL']
      have hxu : x ≠ u := fun h => hne (huniq e' heD x hx (Or.inl h))
      have hxv : x ≠ v := fun h => hne (huniq e' heD x hx (Or.inr h))
      simp only [List.mem_append, List.mem_singleton] at hxL
      tauto
    · intro l hl
      obtain ⟨e0, ⟨he0, hle0⟩, huq⟩ := hwf.cover l (hsubL l hl)
      have hlu : l ≠ u := fun h => huL' (h ▸ hl)
      have hlv : l ≠ v := fun h => hvL' (h ▸ hl)
      have hne : e0 ≠ e := by
        intro h
        rw [h, he_def] at hle0
        rcases Sym2.mem_iff.1 hle0 with h' | h'
        · exact hlu h'
        · exact hlv h'
      exact ⟨e0, ⟨Finset.mem_erase.2 ⟨hne, he0⟩, hle0⟩,
        fun y hy => huq y ⟨(Finset.mem_erase.1 hy.1).2, hy.2⟩⟩
  have hcard' : dg'.D.card = n := by
    show (dg.D.erase e).card = n
    rw [card_erase_of_mem he, hcard]; rfl
  have hcap' : CappedOn dg'.D ed := by
    obtain ⟨L, hL⟩ := hcap
    exact ⟨L, fun e' he' => hL e' (Finset.mem_of_mem_erase he')⟩
  have hK' : KernelHyp a dg' ed G :=
    ⟨fun l hl => hK.meas l (hsubL l hl), fun l hl => hK.N0_lt l (hsubL l hl),
      fun l hl e' he' => hK.N1_lt l (hsubL l hl) e' (Finset.mem_of_mem_erase he'),
      fun l hl e' he' => hK.N2_lt l (hsubL l hl) e' (Finset.mem_of_mem_erase he')⟩
  -- predecessors
  have hpred_mem : ∀ l p, dg.pred l = some p → p ∈ dg'.labels := by
    intro l p hp
    rw [hL']
    unfold TwoChain.pred at hp
    split_ifs at hp
    · rw [h1] at hp; exact Or.inl (listPred_concat_mem hp)
    · rw [h2] at hp; exact Or.inr (listPred_concat_mem hp)
  have hpred_eq : ∀ l ∈ dg'.labels, dg'.pred l = dg.pred l := by
    intro l hl
    rw [hL'] at hl
    rcases hl with hl | hl
    · rw [pred_eq_c1 (dg := dg') hl, pred_eq_c1 (hmem1 hl), h1,
        listPred_concat c1' (fun h => hu1' (by rw [← h]; exact hl))]
    · rw [pred_eq_c2 hwf' hl, pred_eq_c2 hwf (hmem2 hl), h2,
        listPred_concat c2' (fun h => hv2' (by rw [← h]; exact hl))]
  have htime : ∀ (z : α → ℝ × Rd d), ∀ l ∈ dg'.labels,
      dg'.predTime z l = dg.predTime z l ∧ dg'.predPos z l = dg.predPos z l := by
    intro z l hl
    unfold TwoChain.predTime TwoChain.predPos
    rw [hpred_eq l hl]
    exact ⟨rfl, rfl⟩
  -- the factorization of the integrand
  set E := ed e with hE
  set K : (α → ℝ × Rd d) → ℝ≥0∞ := fun z =>
    uncurry (zeroExt (G u)) ((z u).1 - dg.predTime z u, (z u).2 - dg.predPos z u) *
      uncurry (zeroExt (G v)) ((z v).1 - dg.predTime z v, (z v).2 - dg.predPos z v) *
      kappa a E ((z u).1 - (z v).1) * gammaOf E.μ ((z u).2 - (z v).2) with hK_def
  have hzero : ∀ (H : Kernel d) (t : ℝ) (x : Rd d),
      uncurry (zeroExt H) (t, x) = if 0 < t then H t x else 0 := by
    intro H t x
    simp only [uncurry, zeroExt, indicator, Set.mem_Ioi]
  have hfac : ∀ z, integrand a dg ed G z = integrand a dg' ed G z * K z := by
    intro z
    have hpos : z ∈ dg.posSimplex ↔ z ∈ dg'.posSimplex ∧
        dg.predTime z u < (z u).1 ∧ dg.predTime z v < (z v).1 := by
      show (∀ l ∈ dg.labels, dg.predTime z l < (z l).1) ↔
        (∀ l ∈ dg'.labels, dg'.predTime z l < (z l).1) ∧ _ ∧ _
      rw [hlabels, Finset.forall_mem_insert, Finset.forall_mem_insert]
      constructor
      · rintro ⟨hu, hv, h⟩
        exact ⟨fun l hl => (htime z l hl).1 ▸ h l hl, hu, hv⟩
      · rintro ⟨h, hu, hv⟩
        exact ⟨hu, hv, fun l hl => (htime z l hl).1 ▸ h l hl⟩
    have hprodG : ∏ l ∈ dg.labels, G l ((z l).1 - dg.predTime z l) ((z l).2 - dg.predPos z l) =
        G u ((z u).1 - dg.predTime z u) ((z u).2 - dg.predPos z u) *
          (G v ((z v).1 - dg.predTime z v) ((z v).2 - dg.predPos z v) *
            ∏ l ∈ dg'.labels, G l ((z l).1 - dg'.predTime z l) ((z l).2 - dg'.predPos z l)) := by
      rw [hlabels, prod_insert huv', prod_insert hvL']
      congr 2
      exact prod_congr rfl fun l hl => by rw [(htime z l hl).1, (htime z l hl).2]
    have hprodE : ∏ e' ∈ dg.D, edgeWeight a (ed e') z e' =
        (kappa a E ((z u).1 - (z v).1) * gammaOf E.μ ((z u).2 - (z v).2)) *
          ∏ e' ∈ dg'.D, edgeWeight a (ed e') z e' := by
      rw [← mul_prod_erase dg.D _ he, he_def, edgeWeight_mk]
    unfold integrand
    simp only [hK_def, hzero, sub_pos]
    by_cases h' : z ∈ dg'.posSimplex
    · by_cases hu' : dg.predTime z u < (z u).1
      · by_cases hv' : dg.predTime z v < (z v).1
        · rw [indicator_of_mem (hpos.2 ⟨h', hu', hv'⟩), indicator_of_mem h', hprodG, hprodE,
            ite_eq_left hu', ite_eq_left hv']
          ring
        · rw [indicator_of_notMem (fun h => hv' (hpos.1 h).2.2), ite_eq_right hv']
          simp
      · rw [indicator_of_notMem (fun h => hu' (hpos.1 h).2.1), ite_eq_right hu']
        simp
    · rw [indicator_of_notMem (fun h => h' (hpos.1 h).1), indicator_of_notMem h']
      simp
  -- measurability
  have hg := measurable_integrand hK
  have hmZ : ∀ {l : α}, l ∈ dg.labels → ∀ (A : ℝ) (zA : Rd d),
      Measurable fun p : ℝ × Rd d => uncurry (zeroExt (G l)) (p.1 - A, p.2 - zA) :=
    fun hl A zA => (measurable_zeroExt (hK.meas _ hl)).comp
      ((measurable_fst.sub measurable_const).prodMk (measurable_snd.sub measurable_const))
  -- the cap
  obtain ⟨Lc, hLc⟩ := hcap
  have hAcap : E.A ⊆ Ioc 0 Lc := hLc e he
  set N : ℕ := ⌈Lc⌉₊
  have hLN : Lc ≤ (N : ℝ) := Nat.le_ceil Lc
  set C := N2 a E (G u) * N2 a E (G v) with hC_def
  have hCtop : C ≠ ∞ :=
    ENNReal.mul_ne_top (hK.N2_lt u huL e he).ne (hK.N2_lt v hvL e he).ne
  -- the endpoint bound by `L:translated-covariance-CS`
  have hendpt : ∀ (A B : ℝ) (zA zB : Rd d),
      ∫⁻ xv : ℝ × Rd d, ∫⁻ xu : ℝ × Rd d,
        uncurry (zeroExt (G u)) (xu.1 - A, xu.2 - zA) *
          uncurry (zeroExt (G v)) (xv.1 - B, xv.2 - zB) *
          kappa a E (xu.1 - xv.1) * gammaOf E.μ (xu.2 - xv.2) ≤ C := by
    intro A B zA zB
    have hX : Measurable fun p : (ℝ × Rd d) × (ℝ × Rd d) =>
        uncurry (zeroExt (G u)) (p.2.1 - A, p.2.2 - zA) *
          uncurry (zeroExt (G v)) (p.1.1 - B, p.1.2 - zB) *
          kappa a E (p.2.1 - p.1.1) * gammaOf E.μ (p.2.2 - p.1.2) :=
      ((((hmZ huL A zA).comp measurable_snd).mul ((hmZ hvL B zB).comp measurable_fst)).mul
        ((measurable_kappa a E).comp (measurable_snd.fst.sub measurable_fst.fst))).mul
        ((measurable_gammaOf E.μ).comp (measurable_snd.snd.sub measurable_fst.snd))
    rw [lintegral_lintegral_swap hX.aemeasurable]
    have hQL : ∫⁻ xu : ℝ × Rd d, ∫⁻ xv : ℝ × Rd d,
        uncurry (zeroExt (G u)) (xu.1 - A, xu.2 - zA) *
          uncurry (zeroExt (G v)) (xv.1 - B, xv.2 - zB) *
          kappa a E (xu.1 - xv.1) * gammaOf E.μ (xu.2 - xv.2) =
        QL (nuE a E.A) E.μ (N : ℝ) (transl A zA (zeroExt (G u))) (transl B zB (zeroExt (G v))) := by
      unfold QL
      simp_rw [kappa_eq_kappaCap a E hAcap hLN]
      rfl
    rw [hQL]
    have hcs := (hA (nuE a E.A) E.μ (fun L _ => nuE_Ioc_lt_top ha0 E.A L) E.isFiniteMeasure_μ
      E.spec_nonneg (G u) (G v) (hK.meas u huL) (hK.meas v hvL) (hK.N0_lt u huL)
      (hK.N0_lt v hvL) (hK.N2_lt u huL e he) (hK.N2_lt v hvL e he) A B zA zB).1
    exact le_trans (le_iSup (fun L : ℕ => QL (nuE a E.A) E.μ (L : ℝ)
      (transl A zA (zeroExt (G u))) (transl B zB (zeroExt (G v)))) N) hcs
  -- peeling the two endpoints
  have hmeas1 : Measurable fun x : α → ℝ × Rd d =>
      ∫⁻ xu : ℝ × Rd d, integrand a dg ed G (update x u xu) :=
    (hg.comp (measurable_update' (a := u))).lintegral_prod_right'
  have hpI : pairingIntegral a dg ed G =
      lmarginal (fun _ => (volume : Measure (ℝ × Rd d))) dg'.labels
        (fun y => ∫⁻ xv : ℝ × Rd d, ∫⁻ xu : ℝ × Rd d,
          integrand a dg ed G (update (update y v xv) u xu)) 0 := by
    unfold pairingIntegral
    rw [hlabels, lmarginal_insert' _ hg huv', lmarginal_insert' _ hmeas1 hvL']
  have hinner : ∀ y : α → ℝ × Rd d,
      ∫⁻ xv : ℝ × Rd d, ∫⁻ xu : ℝ × Rd d, integrand a dg ed G (update (update y v xv) u xu) ≤
        integrand a dg' ed G y * C := by
    intro y
    have hpu : ∀ p, dg.pred u = some p → p ≠ u ∧ p ≠ v := fun p hp =>
      ⟨fun h => huL' (h ▸ hpred_mem u p hp), fun h => hvL' (h ▸ hpred_mem u p hp)⟩
    have hpv : ∀ p, dg.pred v = some p → p ≠ u ∧ p ≠ v := fun p hp =>
      ⟨fun h => huL' (h ▸ hpred_mem v p hp), fun h => hvL' (h ▸ hpred_mem v p hp)⟩
    have hupd : ∀ xv xu : ℝ × Rd d, integrand a dg ed G (update (update y v xv) u xu) =
        integrand a dg' ed G y *
          (uncurry (zeroExt (G u)) (xu.1 - dg.predTime y u, xu.2 - dg.predPos y u) *
            uncurry (zeroExt (G v)) (xv.1 - dg.predTime y v, xv.2 - dg.predPos y v) *
            kappa a E (xu.1 - xv.1) * gammaOf E.μ (xu.2 - xv.2)) := by
      intro xv xu
      set z := update (update y v xv) u xu with hz
      have hzu : z u = xu := by simp [hz]
      have hzv : z v = xv := by simp [hz, Ne.symm huv]
      have hzl : ∀ l, l ≠ u → l ≠ v → z l = y l := fun l h1 h2 => by
        simp [hz, h1, h2]
      have htu := predTime_congr dg (z := z) (z' := y) u fun p hp =>
        hzl p (hpu p hp).1 (hpu p hp).2
      have htv := predTime_congr dg (z := z) (z' := y) v fun p hp =>
        hzl p (hpv p hp).1 (hpv p hp).2
      rw [hfac z, integrand_congr hwf' ed G (z' := y) fun l hl =>
        hzl l (fun h => huL' (h ▸ hl)) (fun h => hvL' (h ▸ hl))]
      simp only [hK_def, hzu, hzv, htu.1, htu.2, htv.1, htv.2]
    simp_rw [hupd]
    have hmx : ∀ xv : ℝ × Rd d, Measurable fun xu : ℝ × Rd d =>
        uncurry (zeroExt (G u)) (xu.1 - dg.predTime y u, xu.2 - dg.predPos y u) *
          uncurry (zeroExt (G v)) (xv.1 - dg.predTime y v, xv.2 - dg.predPos y v) *
          kappa a E (xu.1 - xv.1) * gammaOf E.μ (xu.2 - xv.2) := fun xv =>
      (((hmZ huL _ _).mul measurable_const).mul
        ((measurable_kappa a E).comp (measurable_fst.sub measurable_const))).mul
        ((measurable_gammaOf E.μ).comp (measurable_snd.sub measurable_const))
    have hmy : Measurable fun xv : ℝ × Rd d => ∫⁻ xu : ℝ × Rd d,
        uncurry (zeroExt (G u)) (xu.1 - dg.predTime y u, xu.2 - dg.predPos y u) *
          uncurry (zeroExt (G v)) (xv.1 - dg.predTime y v, xv.2 - dg.predPos y v) *
          kappa a E (xu.1 - xv.1) * gammaOf E.μ (xu.2 - xv.2) := by
      refine Measurable.lintegral_prod_right'
        (f := fun p : (ℝ × Rd d) × (ℝ × Rd d) =>
          uncurry (zeroExt (G u)) (p.2.1 - dg.predTime y u, p.2.2 - dg.predPos y u) *
          uncurry (zeroExt (G v)) (p.1.1 - dg.predTime y v, p.1.2 - dg.predPos y v) *
          kappa a E (p.2.1 - p.1.1) * gammaOf E.μ (p.2.2 - p.1.2)) ?_
      exact ((((hmZ huL _ _).comp measurable_snd).mul ((hmZ hvL _ _).comp measurable_fst)).mul
        ((measurable_kappa a E).comp (measurable_snd.fst.sub measurable_fst.fst))).mul
        ((measurable_gammaOf E.μ).comp (measurable_snd.snd.sub measurable_fst.snd))
    rw [lintegral_congr fun xv => lintegral_const_mul _ (hmx xv), lintegral_const_mul _ hmy]
    exact mul_le_mul' le_rfl (hendpt _ _ _ _)
  -- assembly
  have hD : dg.D = insert e dg'.D := (Finset.insert_erase he).symm
  have he' : e ∉ dg'.D := Finset.notMem_erase e dg.D
  calc pairingIntegral a dg ed G
      ≤ lmarginal (fun _ => (volume : Measure (ℝ × Rd d))) dg'.labels
          (fun y => integrand a dg' ed G y * C) 0 := by
        rw [hpI]; exact lmarginal_mono hinner 0
    _ = pairingIntegral a dg' ed G * C := by
        unfold pairingIntegral lmarginal
        exact lintegral_mul_const' _ _ hCtop
    _ ≤ env a dg' ed G * C := mul_le_mul' (IH dg' ed G hwf' hcard' hcap' hK') le_rfl
    _ ≤ env a dg ed G := by
        unfold env
        rw [ENNReal.iSup_mul]
        refine iSup_le fun A' => ?_
        rw [hC_def, hE, he_def, ← prodP_pairQ2 a ed G A' u v huL' hvL' huv he' hlabels hD]
        exact le_iSup (fun B : Adm dg.labels dg.D => prodP a ed G B) _

end Terminal

/-! ### The induction (Steps 3-4) and the assembly -/

section Assembly

variable {α : Type*} [DecidableEq α]

/-- The partner of a label in a well-formed diagram. -/
theorem exists_partner {dg : TwoChain α} (hwf : dg.WF) {l : α} (hl : l ∈ dg.labels) :
    ∃ w, s(l, w) ∈ dg.D ∧ w ≠ l ∧ w ∈ dg.labels := by
  obtain ⟨e, ⟨he, hle⟩, _⟩ := hwf.cover l hl
  obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 hle
  refine ⟨w, he, fun h => (hwf.edge _ he).1 (Sym2.mk_isDiag_iff.2 h.symm), ?_⟩
  exact (hwf.edge _ he).2 w (Sym2.mem_mk_right l w)

/-- The edge through a label is unique. -/
theorem partner_unique {dg : TwoChain α} (hwf : dg.WF) {l w w' : α} (h : s(l, w) ∈ dg.D)
    (h' : s(l, w') ∈ dg.D) : w = w' := by
  have hl : l ∈ dg.labels := (hwf.edge _ h).2 l (Sym2.mem_mk_left l w)
  obtain ⟨e, _, hu⟩ := hwf.cover l hl
  have h1 := hu _ ⟨h, Sym2.mem_mk_left l w⟩
  have h2 := hu _ ⟨h', Sym2.mem_mk_left l w'⟩
  exact Sym2.congr_right.1 (h1.trans h2.symm)

/-- **The induction step** (Steps 3-4, TeX 1598-1627) at the finite cap. -/
theorem capped_step (hA : TranslatedCSTarget d) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {n : ℕ}
    (hC : RegionalHalfBoundTarget d α a n) (IH : CappedEnvelopeAt d α a n) :
    CappedEnvelopeAt d α a (n + 1) := by
  intro dg ed G hwf hcard hcap hK
  have hlab : ∃ l, l ∈ dg.labels := by
    obtain ⟨e, he⟩ := Finset.card_pos.1 (by rw [hcard]; exact Nat.succ_pos n)
    induction e using Sym2.ind with
    | h x y => exact ⟨x, (hwf.edge _ he).2 x (Sym2.mem_mk_left x y)⟩
  rcases List.eq_nil_or_concat dg.c1 with h1 | ⟨c1', u, h1⟩ <;>
    rcases List.eq_nil_or_concat dg.c2 with h2 | ⟨c2', v, h2⟩ <;>
    try simp only [List.concat_eq_append] at h1 h2
  · -- both chains empty
    obtain ⟨l, hl⟩ := hlab
    rw [mem_labels', h1, h2] at hl
    simp at hl
  · -- only chain 2: the partner of `v` is in `c2'`
    have hvL : v ∈ dg.labels := mem_labels'.2 (Or.inr (by rw [h2]; simp))
    obtain ⟨w, hvw, hwv, hwL⟩ := exists_partner hwf hvL
    rw [mem_labels', h1, h2] at hwL
    simp only [List.not_mem_nil, false_or, List.mem_append, List.mem_singleton] at hwL
    have hw : w ∈ c2' := hwL.resolve_right hwv
    exact same_chain_bound ha0 ha1 hC IH hwf hcard hcap hK (Or.inr h2) hw hvw
  · -- only chain 1
    have huL : u ∈ dg.labels := mem_labels'.2 (Or.inl (by rw [h1]; simp))
    obtain ⟨w, huw, hwu, hwL⟩ := exists_partner hwf huL
    rw [mem_labels', h1, h2] at hwL
    simp only [List.not_mem_nil, or_false, List.mem_append, List.mem_singleton] at hwL
    have hw : w ∈ c1' := hwL.resolve_right hwu
    exact same_chain_bound ha0 ha1 hC IH hwf hcard hcap hK (Or.inl h1) hw huw
  · -- both chains nonempty
    have huL : u ∈ dg.labels := mem_labels'.2 (Or.inl (by rw [h1]; simp))
    have hvL : v ∈ dg.labels := mem_labels'.2 (Or.inr (by rw [h2]; simp))
    obtain ⟨wu, huw, hwu, hwuL⟩ := exists_partner hwf huL
    obtain ⟨wv, hvw, hwv, hwvL⟩ := exists_partner hwf hvL
    by_cases hc1 : wu ∈ c1'
    · exact same_chain_bound ha0 ha1 hC IH hwf hcard hcap hK (Or.inl h1) hc1 huw
    by_cases hc2 : wv ∈ c2'
    · exact same_chain_bound ha0 ha1 hC IH hwf hcard hcap hK (Or.inr h2) hc2 hvw
    rw [mem_labels', h1, h2] at hwuL hwvL
    simp only [List.mem_append, List.mem_singleton] at hwuL hwvL
    have hwu2 : wu ∈ c2' ∨ wu = v := by tauto
    have hwv1 : wv ∈ c1' ∨ wv = u := by tauto
    rcases hwu2 with hb | rfl
    · -- `u` is paired with `b = wu ∈ c2'`; then `v` is not paired with `u`
      rcases hwv1 with hw | hwv'
      · exact cross_pairs_bound ha0 ha1 hC IH hwf hcard hcap hK h1 h2 hw hb hvw huw
      · exfalso
        rw [hwv'] at hvw
        have hvu : s(u, v) ∈ dg.D := by rw [Sym2.eq_swap]; exact hvw
        have hvwu : v = wu := partner_unique hwf hvu huw
        have hnd : (c2' ++ [v]).Nodup := by rw [← h2]; exact hwf.nodup.of_append_right
        exact (List.nodup_append.1 hnd).2.2 v (hvwu ▸ hb) v List.mem_cons_self rfl
    · exact terminal_pair_bound hA ha0 IH hwf hcard hcap hK h1 h2 huw

/-- **Steps 1-4 at the finite cap** (`CappedEnvelopeAt`, TeX 1502-1627): induction on the number of
edges; `n = 0` is `envelope_zero` (TeX 1498-1499); the step uses the regional half-bound of
Step 2 (`hC`, item C) and `L:translated-covariance-CS` (`hA`, item A). -/
theorem capped_envelope {α : Type*} [DecidableEq α] (hA : TranslatedCSTarget d)
    (hC : ∀ (a : ℝ) (n : ℕ), RegionalHalfBoundTarget d α a n) (a : ℝ) (ha0 : 0 < a)
    (ha1 : a < 1) : ∀ n : ℕ, CappedEnvelopeAt d α a n := by
  intro n
  induction n with
  | zero =>
    intro dg ed G hwf hcard _ _
    obtain ⟨h1, h2⟩ := envelope_zero a hwf (Finset.card_eq_zero.1 hcard) ed G
    rw [h1, h2]
  | succ n ih => exact capped_step hA ha0 ha1 (hC a n) ih

/-- **`L:pairing-product-envelope`** (TeX 1489-1500) from the outputs of items A, B and C, taken
as hypotheses with their frozen statements: `hB` is item B's `cap_removal` (Step 5, TeX
1631-1638), `hC` item C's `regional_half_bound` (Step 2, TeX 1539-1595) and `hA` item A's
`translated_covariance_cs`.  At integration, `pairing_product_envelope d α` is this theorem with
the three outputs substituted. -/
theorem pairing_product_envelope_of {α : Type*} [DecidableEq α] (hA : TranslatedCSTarget d)
    (hC : ∀ (a : ℝ) (n : ℕ), RegionalHalfBoundTarget d α a n)
    (hB : (∀ a : ℝ, 0 < a → a < 1 → ∀ n : ℕ, CappedEnvelopeAt d α a n) →
      PairingEnvelopeTarget d α) :
    PairingEnvelopeTarget d α :=
  hB fun a ha0 ha1 => capped_envelope hA hC a ha0 ha1

/-- `L:pairing-product-envelope` with item A's output substituted (A is proved,
`PairingTranslatedCS.translated_covariance_cs`); B's Step 5 and C's Step 2 remain hypotheses
until integration. -/
theorem pairing_product_envelope_of_capRemoval {α : Type*} [DecidableEq α]
    (hC : ∀ (a : ℝ) (n : ℕ), RegionalHalfBoundTarget d α a n)
    (hB : (∀ a : ℝ, 0 < a → a < 1 → ∀ n : ℕ, CappedEnvelopeAt d α a n) →
      PairingEnvelopeTarget d α) :
    PairingEnvelopeTarget d α :=
  pairing_product_envelope_of (PairingTranslatedCS.translated_covariance_cs d) hC hB

/-- **`L:pairing-product-envelope`** (`E:pairing-product-envelope`, TeX 1489-1500; proof
1502-1639), whole and hypothesis-free: Step 5 (item B, `PairingCapRemoval.cap_removal`) applied to
Steps 1-4 at the finite cap (`capped_envelope`), with Step 2 from item C
(`PairingRegional.regional_half_bound`), Step 1 from item B (`PairingConvolution.convolution_norms`,
which takes item A's capped form) and `L:translated-covariance-CS` from item A. -/
theorem pairing_product_envelope (d : ℕ) (α : Type*) [DecidableEq α] :
    PairingEnvelopeTarget d α :=
  PairingCapRemoval.cap_removal fun a ha0 ha1 =>
    capped_envelope (PairingTranslatedCS.translated_covariance_cs d)
      (fun a n => PairingRegional.regional_half_bound
        (PairingConvolution.convolution_norms (PairingTranslatedCS.translated_covariance_cs_capped d))
        a n) a ha0 ha1

end Assembly

end StratonovichHAMSecondMoment.PairingEnvelope
