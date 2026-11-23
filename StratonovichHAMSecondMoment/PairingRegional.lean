module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L17, item L17-C: Step 2 of `L:pairing-product-envelope`, the regional half-bound by
induction (TeX lines 1539-1595 at revision edf7085f (book 1.1.3), main file
`notes/notes_stratonovich_ham_second_moment.tex`; setup 1434-1488).

Main result: `regional_half_bound (hB : ConvolutionNormsTarget d) a n :
RegionalHalfBoundTarget d α a n`.  The only hypothesis is item B's frozen output
`ConvolutionNormsTarget d` (`E:pairing-convolution-norms`, TeX 1522-1535), used for the fused
kernel `G_w * G_b`.  The induction hypothesis is the frozen `CappedEnvelopeAt d α a n`.

Proof structure (TeX's partner `a` is `w` here, as in the frozen target):
* list and diagram combinatorics: the predecessor after deleting a label
  (`listPred_erase`), the reduced diagram `del2` (both endpoints of `e₀ = {w, v}` deleted, `e₀`
  removed), its well-formedness, edge count and predecessors (`pred_del2`);
* admissible assignments (ported from the Step-2 probe): the uniform extension
  `Q₀ ∪ {w}`, `Q₁ ∪ {v}`, `ι[v := e₀]` (`admExtend`) and the one-factor-grows lemma
  (`prodP_update_le`), which together are all three rows of the slot table (TeX 1569-1592);
* analysis: the endpoint integration (TeX 1549-1557; `κ` is antitone in `|t|`, the complex
  Laplace-Fourier Fubini at fixed `λ` gives `N_{1,e₀}(G_v)`, `endpoint_le_N1`), integrating the
  unpaired terminal partner to `N_0` (`lintegral_shift_N0`, TeX 1558-1562) or the partner with a
  successor `b` to the fused kernel `conv (G w) (G b)` at `b` (`lintegral_shift_conv`, TeX
  1563-1566, also when `w` is a first vertex: the predecessor of `b` becomes that of `w`).

Route notes.  The endpoint integration keeps `ν_{e₀}` as an outer lower integral (Tonelli) and
uses the complex Fubini only in `(t,x) × ξ` at fixed `λ > 0`, so neither the cap nor
`0 < a < 1` is used there; the cap and `0 < a < 1` enter only through `hB` for the fused kernel.
The finite maximum of the TeX is the frozen supremum `env`; only `P ≤ env` and
`c * ⨆ = ⨆ (c * ·)` are used.

No `sorry`, no axiom, no instance.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.PairingInterface

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal Real

namespace StratonovichHAMSecondMoment.PairingRegional

open HomogHypothesis (Rd)
open PairingInterface
open PairingInterface.TwoChain

variable {d : ℕ}

/-! ### Predecessors in a list -/

section ListPred

variable {α : Type*} [DecidableEq α]

/-- One-step unfolding of `listPred` through the head. -/
theorem listPred_cons (a : α) (l : List α) (y : α) :
    listPred (a :: l) y = if l.head? = some y then some a else listPred l y := by
  cases l with
  | nil => simp [listPred]
  | cons b r =>
    simp only [listPred, List.head?_cons, Option.some.injEq]
    by_cases h : y = b
    · subst h; simp
    · simp [h, Ne.symm h]

theorem listPred_mem {l : List α} {x y : α} (h : listPred l y = some x) : x ∈ l ∧ y ∈ l := by
  induction l with
  | nil => simp [listPred] at h
  | cons a r ih =>
    rw [listPred_cons] at h
    split_ifs at h with hy
    · cases h
      exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ (List.mem_of_mem_head? hy)⟩
    · obtain ⟨h1, h2⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩

theorem listPred_eq_none_of_notMem {l : List α} {y : α} (h : y ∉ l) : listPred l y = none := by
  cases hp : listPred l y with
  | none => rfl
  | some x => exact absurd (listPred_mem hp).2 h

theorem listPred_ne_self {l : List α} (hl : l.Nodup) (y : α) : listPred l y ≠ some y := by
  induction l with
  | nil => simp [listPred]
  | cons a r ih =>
    rw [listPred_cons]
    have ha := (List.nodup_cons.1 hl).1
    split_ifs with hy
    · intro h
      cases h
      exact ha (List.mem_of_mem_head? hy)
    · exact ih (List.nodup_cons.1 hl).2

/-- The last element of a list without repetitions is nobody's predecessor. -/
theorem listPred_ne_last {l : List α} (hl : l.Nodup) {x : α} (hx : l.getLast? = some x)
    (y : α) : listPred l y ≠ some x := by
  induction l with
  | nil => simp at hx
  | cons a r ih =>
    rw [listPred_cons]
    have ha := (List.nodup_cons.1 hl).1
    cases r with
    | nil => simp [listPred]
    | cons b r' =>
      have hx' : (b :: r').getLast? = some x := by
        rw [List.getLast?_cons_cons] at hx; exact hx
      split_ifs with hy
      · intro h
        cases h
        exact ha (List.mem_of_getLast? hx')
      · exact ih (List.nodup_cons.1 hl).2 hx'

/-- The successor is unique: two labels with the same predecessor coincide. -/
theorem listPred_inj {l : List α} (hl : l.Nodup) {x y w : α} (hx : listPred l x = some w)
    (hy : listPred l y = some w) : x = y := by
  induction l with
  | nil => simp [listPred] at hx
  | cons a r ih =>
    rw [listPred_cons] at hx hy
    have ha := (List.nodup_cons.1 hl).1
    split_ifs at hx hy with h1 h2 h2
    · rw [h1] at h2; exact Option.some_injective _ h2
    · cases hx; exact absurd (listPred_mem hy).1 ha
    · cases hy; exact absurd (listPred_mem hx).1 ha
    · exact ih (List.nodup_cons.1 hl).2 hx hy

/-- **The predecessor after deleting a label**: the successor of the deleted label inherits its
predecessor; every other predecessor is unchanged. -/
theorem listPred_erase {l : List α} (hl : l.Nodup) {x y : α} (hyx : y ≠ x) :
    listPred (l.erase x) y = if listPred l y = some x then listPred l x else listPred l y := by
  induction l with
  | nil => simp [listPred]
  | cons a r ih =>
    have ha := (List.nodup_cons.1 hl).1
    have hr := (List.nodup_cons.1 hl).2
    by_cases hax : a = x
    · subst hax
      rw [List.erase_cons_head]
      have hxr : listPred r y ≠ some a := fun h => ha (listPred_mem h).1
      rw [listPred_cons a r y]
      by_cases hy : r.head? = some y
      · obtain ⟨r', rfl⟩ : ∃ r', r = y :: r' := by
          cases r with
          | nil => simp at hy
          | cons c r' => simp at hy; exact ⟨r', by rw [hy]⟩
        rw [listPred_head hr]
        simp only [hy, ite_true, listPred_cons a (y :: r') a]
        have hay : ¬ (some y = some a) := by
          intro h; cases h; exact hyx rfl
        simp only [hay, ite_false]
        exact (listPred_eq_none_of_notMem ha).symm
      · simp [hy, hxr]
    · rw [List.erase_cons_tail (by simpa using hax)]
      rw [listPred_cons a (r.erase x) y, listPred_cons a r y]
      by_cases hy : r.head? = some y
      · -- `y` follows `a`: it still does after deleting `x ≠ y`
        have hy' : (r.erase x).head? = some y := by
          cases r with
          | nil => simp at hy
          | cons c r' =>
            simp at hy
            subst hy
            rw [List.erase_cons_tail (by simpa using hyx)]
            simp
        have hax' : ¬ (some a = some x) := fun h => hax (Option.some_injective _ h)
        simp [hy, hy', hax']
      · simp only [hy, ite_false]
        rw [listPred_cons a r x]
        by_cases hrx : r.head? = some x
        · obtain ⟨r', rfl⟩ : ∃ r', r = x :: r' := by
            cases r with
            | nil => simp at hrx
            | cons c r' => simp at hrx; exact ⟨r', by rw [hrx]⟩
          have hxr' : x ∉ r' := (List.nodup_cons.1 hr).1
          rw [List.erase_cons_head, listPred_cons x r' y]
          simp only [List.head?_cons, ite_true]
          by_cases hy2 : r'.head? = some y
          · simp [hy2]
          · have hne : listPred r' y ≠ some x := fun h => hxr' (listPred_mem h).1
            simp [hy2, hne]
        · have hhead : (r.erase x).head? = r.head? := by
            cases r with
            | nil => simp
            | cons c r' =>
              have hcx : c ≠ x := fun h => hrx (by simp [h])
              rw [List.erase_cons_tail (by simpa using hcx)]
              simp
          rw [hhead]
          simp only [hy, ite_false, hrx]
          exact ih hr

end ListPred

/-! ### The reduced diagram: deleting both endpoints of an edge -/

section Diagram

variable {α : Type*} [DecidableEq α]

theorem mem_labels {dg : TwoChain α} {l : α} : l ∈ dg.labels ↔ l ∈ dg.c1 ∨ l ∈ dg.c2 := by
  simp [TwoChain.labels]

theorem nodup_c1 {dg : TwoChain α} (hwf : dg.WF) : dg.c1.Nodup := hwf.nodup.of_append_left

theorem nodup_c2 {dg : TwoChain α} (hwf : dg.WF) : dg.c2.Nodup := hwf.nodup.of_append_right

theorem disj_c12 {dg : TwoChain α} (hwf : dg.WF) {x : α} (h1 : x ∈ dg.c1) (h2 : x ∈ dg.c2) :
    False :=
  (List.nodup_append.1 hwf.nodup).2.2 x h1 x h2 rfl

/-- A label is never its own predecessor. -/
theorem pred_ne_self {dg : TwoChain α} (hwf : dg.WF) (l : α) : dg.pred l ≠ some l := by
  unfold TwoChain.pred
  split_ifs
  · exact listPred_ne_self (nodup_c1 hwf) l
  · exact listPred_ne_self (nodup_c2 hwf) l

/-- The predecessor of a label lies on the same chain. -/
theorem pred_mem {dg : TwoChain α} {l p : α} (h : dg.pred l = some p) :
    (p ∈ dg.c1 ∧ l ∈ dg.c1) ∨ (p ∈ dg.c2 ∧ l ∈ dg.c2) := by
  unfold TwoChain.pred at h
  split_ifs at h
  · exact Or.inl (listPred_mem h)
  · exact Or.inr (listPred_mem h)

theorem pred_some_mem_labels {dg : TwoChain α} {l p : α} (h : dg.pred l = some p) :
    p ∈ dg.labels ∧ l ∈ dg.labels := by
  rcases pred_mem h with h | h
  · exact ⟨mem_labels.2 (Or.inl h.1), mem_labels.2 (Or.inl h.2)⟩
  · exact ⟨mem_labels.2 (Or.inr h.1), mem_labels.2 (Or.inr h.2)⟩

/-- An endpoint is nobody's predecessor, chainwise. -/
theorem listPred_c1_ne_endpoint {dg : TwoChain α} (hwf : dg.WF) {v : α} (hv : dg.IsEndpoint v)
    (y : α) : listPred dg.c1 y ≠ some v := by
  rcases hv with hv | hv
  · exact listPred_ne_last (nodup_c1 hwf) hv y
  · intro h
    exact disj_c12 hwf (listPred_mem h).1 (List.mem_of_getLast? hv)

theorem listPred_c2_ne_endpoint {dg : TwoChain α} (hwf : dg.WF) {v : α} (hv : dg.IsEndpoint v)
    (y : α) : listPred dg.c2 y ≠ some v := by
  rcases hv with hv | hv
  · intro h
    exact disj_c12 hwf (List.mem_of_getLast? hv) (listPred_mem h).1
  · exact listPred_ne_last (nodup_c2 hwf) hv y

/-- An endpoint is nobody's predecessor. -/
theorem pred_ne_endpoint {dg : TwoChain α} (hwf : dg.WF) {v : α} (hv : dg.IsEndpoint v)
    (l : α) : dg.pred l ≠ some v := by
  unfold TwoChain.pred
  split_ifs
  · exact listPred_c1_ne_endpoint hwf hv l
  · exact listPred_c2_ne_endpoint hwf hv l

/-- Two labels with the same predecessor coincide. -/
theorem pred_inj {dg : TwoChain α} (hwf : dg.WF) {x y w : α} (hx : dg.pred x = some w)
    (hy : dg.pred y = some w) : x = y := by
  unfold TwoChain.pred at hx hy
  split_ifs at hx hy
  · exact listPred_inj (nodup_c1 hwf) hx hy
  · exact (disj_c12 hwf (listPred_mem hx).1 (listPred_mem hy).1).elim
  · exact (disj_c12 hwf (listPred_mem hy).1 (listPred_mem hx).1).elim
  · exact listPred_inj (nodup_c2 hwf) hx hy

/-- The edge through `w` or `v` is `{w, v}` (perfect matching). -/
theorem eq_of_mem_edge {dg : TwoChain α} (hwf : dg.WF) {w v : α} (he : s(w, v) ∈ dg.D)
    {e : Sym2 α} (heD : e ∈ dg.D) {x : α} (hx : x = w ∨ x = v) (hxe : x ∈ e) :
    e = s(w, v) := by
  have hxL : x ∈ dg.labels := (hwf.edge _ he).2 x (by rcases hx with rfl | rfl <;> simp)
  obtain ⟨e', _, huniq⟩ := hwf.cover x hxL
  have h1 := huniq e ⟨heD, hxe⟩
  have h2 := huniq s(w, v) ⟨he, by rcases hx with rfl | rfl <;> simp⟩
  rw [h1, h2]

/-- **The reduced diagram**: delete the endpoint `v`, its partner `w` and the edge
`e₀ = {w, v}`. -/
def del2 (dg : TwoChain α) (w v : α) : TwoChain α where
  c1 := (dg.c1.erase v).erase w
  c2 := (dg.c2.erase v).erase w
  D := dg.D.erase s(w, v)

theorem nodup_del2 {dg : TwoChain α} (hwf : dg.WF) (w v : α) :
    ((del2 dg w v).c1 ++ (del2 dg w v).c2).Nodup :=
  hwf.nodup.sublist ((List.erase_sublist.trans List.erase_sublist).append
    (List.erase_sublist.trans List.erase_sublist))

theorem mem_del2_c1 {dg : TwoChain α} {w v l : α} (hlv : l ≠ v) (hlw : l ≠ w) :
    l ∈ (del2 dg w v).c1 ↔ l ∈ dg.c1 := by
  simp only [del2]
  rw [List.mem_erase_of_ne hlw, List.mem_erase_of_ne hlv]

theorem mem_del2_c2 {dg : TwoChain α} {w v l : α} (hlv : l ≠ v) (hlw : l ≠ w) :
    l ∈ (del2 dg w v).c2 ↔ l ∈ dg.c2 := by
  simp only [del2]
  rw [List.mem_erase_of_ne hlw, List.mem_erase_of_ne hlv]

theorem labels_del2 {dg : TwoChain α} (hwf : dg.WF) (w v : α) :
    (del2 dg w v).labels = (dg.labels.erase v).erase w := by
  ext l
  simp only [Finset.mem_erase]
  by_cases hlw : l = w
  · subst hlw
    simp only [ne_eq, not_true_eq_false, false_and, iff_false]
    intro h
    rcases mem_labels.1 h with h | h
    · exact List.Nodup.not_mem_erase ((nodup_c1 hwf).erase v) h
    · exact List.Nodup.not_mem_erase ((nodup_c2 hwf).erase v) h
  by_cases hlv : l = v
  · subst hlv
    simp only [ne_eq, not_true_eq_false, false_and, and_false, iff_false]
    intro h
    rcases mem_labels.1 h with h | h
    · exact List.Nodup.not_mem_erase (nodup_c1 hwf) (List.mem_of_mem_erase h)
    · exact List.Nodup.not_mem_erase (nodup_c2 hwf) (List.mem_of_mem_erase h)
  rw [mem_labels, mem_labels, mem_del2_c1 hlv hlw, mem_del2_c2 hlv hlw]
  tauto

theorem D_del2 (dg : TwoChain α) (w v : α) : (del2 dg w v).D = dg.D.erase s(w, v) := rfl

/-- The reduced diagram is well formed. -/
theorem wf_del2 {dg : TwoChain α} (hwf : dg.WF) {w v : α} (he : s(w, v) ∈ dg.D) :
    (del2 dg w v).WF := by
  refine ⟨nodup_del2 hwf w v, ?_, ?_⟩
  · intro e he2
    rw [D_del2, Finset.mem_erase] at he2
    refine ⟨(hwf.edge e he2.2).1, fun x hx => ?_⟩
    rw [labels_del2 hwf, Finset.mem_erase, Finset.mem_erase]
    exact ⟨fun hxw => he2.1 (eq_of_mem_edge hwf he he2.2 (Or.inl hxw) hx),
      fun hxv => he2.1 (eq_of_mem_edge hwf he he2.2 (Or.inr hxv) hx),
      (hwf.edge e he2.2).2 x hx⟩
  · intro l hl
    rw [labels_del2 hwf, Finset.mem_erase, Finset.mem_erase] at hl
    obtain ⟨e, ⟨heD, hle⟩, huniq⟩ := hwf.cover l hl.2.2
    refine ⟨e, ⟨?_, hle⟩, fun e' ⟨he', hle'⟩ =>
      huniq e' ⟨(Finset.mem_erase.1 (D_del2 dg w v ▸ he')).2, hle'⟩⟩
    rw [D_del2, Finset.mem_erase]
    refine ⟨fun h => ?_, heD⟩
    rw [h] at hle
    rcases Sym2.mem_iff.1 hle with h' | h'
    · exact hl.1 h'
    · exact hl.2.1 h'

theorem card_del2 {dg : TwoChain α} {w v : α} (he : s(w, v) ∈ dg.D) {n : ℕ}
    (hcard : dg.D.card = n + 1) : (del2 dg w v).D.card = n := by
  rw [D_del2, Finset.card_erase_of_mem he, hcard]; rfl

/-- **Predecessors in the reduced diagram**: the successor of `w` inherits the predecessor of
`w` (the origin if `w` was a first vertex); every other predecessor is unchanged. -/
theorem pred_del2 {dg : TwoChain α} (hwf : dg.WF) {w v : α} (hv : dg.IsEndpoint v) (hwv : w ≠ v)
    {l : α} (hlv : l ≠ v) (hlw : l ≠ w) :
    (del2 dg w v).pred l = if dg.pred l = some w then dg.pred w else dg.pred l := by
  have key : ∀ c : List α, c.Nodup → (∀ y, listPred c y ≠ some v) →
      listPred ((c.erase v).erase w) l =
        if listPred c l = some w then listPred c w else listPred c l := by
    intro c hc hcv
    have he : ∀ y, y ≠ v → listPred (c.erase v) y = listPred c y := fun y hy => by
      rw [listPred_erase hc hy]; simp [hcv y]
    rw [listPred_erase (hc.erase v) hlw, he l hlv, he w hwv]
  unfold TwoChain.pred
  by_cases h1 : l ∈ dg.c1
  · simp only [(mem_del2_c1 hlv hlw).2 h1, h1, ite_true]
    change listPred ((dg.c1.erase v).erase w) l = _
    rw [key dg.c1 (nodup_c1 hwf) (listPred_c1_ne_endpoint hwf hv)]
    by_cases h2 : listPred dg.c1 l = some w
    · simp only [h2, ite_true, (listPred_mem h2).1]
    · simp only [h2, ite_false]
  · have h1' : l ∉ (del2 dg w v).c1 := fun h => h1 ((mem_del2_c1 hlv hlw).1 h)
    simp only [h1', h1, ite_false]
    change listPred ((dg.c2.erase v).erase w) l = _
    rw [key dg.c2 (nodup_c2 hwf) (listPred_c2_ne_endpoint hwf hv)]
    by_cases h2 : listPred dg.c2 l = some w
    · have hw1 : w ∉ dg.c1 := fun h => disj_c12 hwf h (listPred_mem h2).1
      simp only [h2, ite_true, hw1, ite_false]
    · simp only [h2, ite_false]

end Diagram

/-! ### Admissible assignments: the uniform extension and the slot table (TeX 1569-1592) -/

section Assignments

variable {α : Type*} [DecidableEq α]

/-- The envelope over an explicit label set and matching. -/
def envOn (a : ℝ) (ed : Sym2 α → EdgeData d) (G : α → Kernel d) (L : Finset α)
    (D : Finset (Sym2 α)) : ℝ≥0∞ :=
  ⨆ A : Adm L D, prodP a ed G A

theorem env_eq_envOn (a : ℝ) (dg : TwoChain α) (ed : Sym2 α → EdgeData d) (G : α → Kernel d) :
    env a dg ed G = envOn a ed G dg.labels dg.D := rfl

variable {L : Finset α} {D : Finset (Sym2 α)}

theorem adm_sub0 (A : Adm L D) : A.Q0 ⊆ L := by
  intro x hx; rw [← A.cover]; simp [hx]

theorem adm_sub1 (A : Adm L D) : A.Q1 ⊆ L := by
  intro x hx; rw [← A.cover]; simp [hx]

theorem adm_sub2 (A : Adm L D) : A.Q2 ⊆ L := by
  intro x hx; rw [← A.cover]; simp [hx]

/-- **The uniform extension** (all three rows of the slot table and the terminal case, TeX
1561-1562 and 1569-1592): from an admissible assignment of the reduced labels and matching,
put the partner `w` in `Q₀` and the endpoint `v` in `Q₁` with `ι v = e₀ = {w, v}`. -/
def admExtend (A : Adm L D) (w v : α) (hw : w ∉ L) (hv : v ∉ L) (hwv : w ≠ v)
    (hD : s(w, v) ∉ D) : Adm (insert w (insert v L)) (insert s(w, v) D) where
  Q0 := insert w A.Q0
  Q1 := insert v A.Q1
  Q2 := A.Q2
  iota := Function.update A.iota v s(w, v)
  cover := by
    ext x
    have h := Finset.ext_iff.1 A.cover x
    simp only [Finset.mem_union, Finset.mem_insert] at h ⊢
    tauto
  d01 := by
    rw [Finset.disjoint_left]
    intro x hx0 hx1
    rw [Finset.mem_insert] at hx0 hx1
    rcases hx0 with h0 | h0 <;> rcases hx1 with h1 | h1
    · exact hwv (h0 ▸ h1)
    · exact hw (h0 ▸ adm_sub1 A h1)
    · exact hv (h1 ▸ adm_sub0 A h0)
    · exact Finset.disjoint_left.1 A.d01 h0 h1
  d02 := by
    rw [Finset.disjoint_left]
    intro x hx0 hx2
    rcases Finset.mem_insert.1 hx0 with h0 | h0
    · exact hw (h0 ▸ adm_sub2 A hx2)
    · exact Finset.disjoint_left.1 A.d02 h0 hx2
  d12 := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rcases Finset.mem_insert.1 hx1 with h1 | h1
    · exact hv (h1 ▸ adm_sub2 A hx2)
    · exact Finset.disjoint_left.1 A.d12 h1 hx2
  card01 := by
    rw [Finset.card_insert_of_notMem (fun h => hw (adm_sub0 A h)),
      Finset.card_insert_of_notMem (fun h => hv (adm_sub1 A h)), A.card01]
  mapsTo := by
    intro l hl
    by_cases hlv : l = v
    · rw [hlv, Function.update_self]; exact Finset.mem_insert_self _ _
    · rw [Function.update_of_ne hlv]
      have : l ∈ A.Q1 ∪ A.Q2 := by
        simp only [Finset.mem_union, Finset.mem_insert] at hl ⊢
        rcases hl with (h | h) | h
        · exact absurd h hlv
        · exact Or.inl h
        · exact Or.inr h
      exact Finset.mem_insert_of_mem (A.mapsTo l this)
  edge := by
    intro e he
    have hne1 : ∀ l ∈ A.Q1, l ≠ v := fun l hl (h : l = v) => hv (h ▸ adm_sub1 A hl)
    have hne2 : ∀ l ∈ A.Q2, l ≠ v := fun l hl (h : l = v) => hv (h ▸ adm_sub2 A hl)
    have hf1 : (A.Q1.filter fun l => Function.update A.iota v s(w, v) l = e) =
        A.Q1.filter fun l => A.iota l = e :=
      Finset.filter_congr fun l hl => by rw [Function.update_of_ne (hne1 l hl)]
    have hf2 : (A.Q2.filter fun l => Function.update A.iota v s(w, v) l = e) =
        A.Q2.filter fun l => A.iota l = e :=
      Finset.filter_congr fun l hl => by rw [Function.update_of_ne (hne2 l hl)]
    rw [Finset.filter_insert, Function.update_self, hf1, hf2]
    rcases Finset.mem_insert.1 he with rfl | he'
    · have h1 : (A.Q1.filter fun l => A.iota l = s(w, v)) = ∅ :=
        Finset.filter_false_of_mem fun l hl h =>
          hD (h ▸ A.mapsTo l (Finset.mem_union_left _ hl))
      have h2 : (A.Q2.filter fun l => A.iota l = s(w, v)) = ∅ :=
        Finset.filter_false_of_mem fun l hl h =>
          hD (h ▸ A.mapsTo l (Finset.mem_union_right _ hl))
      left
      simp [h1, h2]
    · have hne : s(w, v) ≠ e := fun h => hD (h ▸ he')
      rw [ite_eq_right_iff.2 (fun h => absurd h hne)]
      exact A.edge e he'


/-- The product of the extended assignment: `N₀(G_w) · 2N_{1,e₀}(G_v)` times the reduced one. -/
theorem prodP_extend (a : ℝ) (ed : Sym2 α → EdgeData d) (G : α → Kernel d) (A : Adm L D)
    (w v : α) (hw : w ∉ L) (hv : v ∉ L) (hwv : w ≠ v) (hD : s(w, v) ∉ D) :
    prodP a ed G (admExtend A w v hw hv hwv hD) =
      N0 (G w) * (2 * N1 a (ed s(w, v)) (G v)) * prodP a ed G A := by
  have e1 : ∏ l ∈ A.Q1, 2 * N1 a (ed (Function.update A.iota v s(w, v) l)) (G l) =
      ∏ l ∈ A.Q1, 2 * N1 a (ed (A.iota l)) (G l) :=
    Finset.prod_congr rfl fun l hl => by
      rw [Function.update_of_ne (fun h : l = v => hv (h ▸ adm_sub1 A hl))]
  have e2 : ∏ l ∈ A.Q2, N2 a (ed (Function.update A.iota v s(w, v) l)) (G l) =
      ∏ l ∈ A.Q2, N2 a (ed (A.iota l)) (G l) :=
    Finset.prod_congr rfl fun l hl => by
      rw [Function.update_of_ne (fun h : l = v => hv (h ▸ adm_sub2 A hl))]
  simp only [prodP, admExtend]
  rw [Finset.prod_insert (fun h => hw (adm_sub0 A h)), Finset.prod_insert (fun h => hv (adm_sub1 A h)),
    Function.update_self, e1, e2]
  ring

theorem prod_update_le {s : Finset α} (f : α → Kernel d → ℝ≥0∞) (G : α → Kernel d) {b : α}
    {F : Kernel d} {c : ℝ≥0∞} (hb : b ∈ s) (hF : f b F ≤ c * f b (G b)) :
    ∏ l ∈ s, f l (Function.update G b F l) ≤ c * ∏ l ∈ s, f l (G l) := by
  rw [← Finset.mul_prod_erase s _ hb, ← Finset.mul_prod_erase s _ hb, Function.update_self]
  have : ∏ l ∈ s.erase b, f l (Function.update G b F l) = ∏ l ∈ s.erase b, f l (G l) :=
    Finset.prod_congr rfl fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  rw [this, ← mul_assoc]
  gcongr

theorem prod_update_eq {s : Finset α} (f : α → Kernel d → ℝ≥0∞) (G : α → Kernel d) {b : α}
    {F : Kernel d} (hb : b ∉ s) :
    ∏ l ∈ s, f l (Function.update G b F l) = ∏ l ∈ s, f l (G l) :=
  Finset.prod_congr rfl fun l hl => by rw [Function.update_of_ne (fun h : l = b => hb (h ▸ hl))]

/-- **The slot table (TeX 1569-1592)**: whatever slot the fused kernel `F` occupies at `b`, the
reduced product with `F` at `b` is at most `N₀(G_w)` times the reduced product with `G_b`; the
three rows use the three inequalities of `E:pairing-convolution-norms` (for edges of `D`). -/
theorem prodP_update_le (a : ℝ) (ed : Sym2 α → EdgeData d) (G : α → Kernel d) (A : Adm L D)
    (w b : α) (F : Kernel d) (hb : b ∈ L)
    (h0 : N0 F ≤ N0 (G w) * N0 (G b))
    (h1 : ∀ e ∈ D, N1 a (ed e) F ≤ N0 (G w) * N1 a (ed e) (G b))
    (h2 : ∀ e ∈ D, N2 a (ed e) F ≤ N0 (G w) * N2 a (ed e) (G b)) :
    prodP a ed (Function.update G b F) A ≤ N0 (G w) * prodP a ed G A := by
  have hb' : b ∈ A.Q0 ∪ A.Q1 ∪ A.Q2 := by rw [A.cover]; exact hb
  simp only [Finset.mem_union] at hb'
  have f0 : ∀ {s : Finset α}, b ∉ s →
      ∏ l ∈ s, N0 (Function.update G b F l) = ∏ l ∈ s, N0 (G l) :=
    fun hs => prod_update_eq (fun _ k => N0 k) G hs
  have f1 : ∀ {s : Finset α}, b ∉ s →
      ∏ l ∈ s, 2 * N1 a (ed (A.iota l)) (Function.update G b F l) =
        ∏ l ∈ s, 2 * N1 a (ed (A.iota l)) (G l) :=
    fun hs => prod_update_eq (fun l k => 2 * N1 a (ed (A.iota l)) k) G hs
  have f2 : ∀ {s : Finset α}, b ∉ s →
      ∏ l ∈ s, N2 a (ed (A.iota l)) (Function.update G b F l) =
        ∏ l ∈ s, N2 a (ed (A.iota l)) (G l) :=
    fun hs => prod_update_eq (fun l k => N2 a (ed (A.iota l)) k) G hs
  unfold prodP
  rcases hb' with (h | h) | h
  · -- row `i = 0`: `F` in `Q₀`
    rw [f1 (Finset.disjoint_left.1 A.d01 h), f2 (Finset.disjoint_left.1 A.d02 h)]
    have := prod_update_le (fun _ k => N0 k) G h h0
    calc _ ≤ (N0 (G w) * ∏ l ∈ A.Q0, N0 (G l)) * (∏ l ∈ A.Q1, 2 * N1 a (ed (A.iota l)) (G l)) *
          ∏ l ∈ A.Q2, N2 a (ed (A.iota l)) (G l) := by gcongr
      _ = _ := by ring
  · -- row `i = 1`: `F` in `Q₁`, with the inherited edge `ι b ∈ D`
    rw [f0 (Finset.disjoint_right.1 A.d01 h), f2 (Finset.disjoint_left.1 A.d12 h)]
    have hbD : A.iota b ∈ D := A.mapsTo b (Finset.mem_union_left _ h)
    have := prod_update_le (fun l k => 2 * N1 a (ed (A.iota l)) k) G h (by
      calc 2 * N1 a (ed (A.iota b)) F ≤ 2 * (N0 (G w) * N1 a (ed (A.iota b)) (G b)) := by
            gcongr; exact h1 _ hbD
        _ = _ := by ring)
    calc _ ≤ (∏ l ∈ A.Q0, N0 (G l)) * (N0 (G w) * ∏ l ∈ A.Q1, 2 * N1 a (ed (A.iota l)) (G l)) *
          ∏ l ∈ A.Q2, N2 a (ed (A.iota l)) (G l) := by gcongr
      _ = _ := by ring
  · -- row `i = 2`: `F` in `Q₂`
    rw [f0 (Finset.disjoint_right.1 A.d02 h), f1 (Finset.disjoint_right.1 A.d12 h)]
    have hbD : A.iota b ∈ D := A.mapsTo b (Finset.mem_union_right _ h)
    have := prod_update_le (fun l k => N2 a (ed (A.iota l)) k) G h (h2 _ hbD)
    calc _ ≤ (∏ l ∈ A.Q0, N0 (G l)) * (∏ l ∈ A.Q1, 2 * N1 a (ed (A.iota l)) (G l)) *
          (N0 (G w) * ∏ l ∈ A.Q2, N2 a (ed (A.iota l)) (G l)) := by gcongr
      _ = _ := by ring

/-- Half-bound conclusion, terminal partner (TeX 1558-1562). -/
theorem envOn_terminal (a : ℝ) (ed : Sym2 α → EdgeData d) (G : α → Kernel d) (w v : α)
    (hw : w ∉ L) (hv : v ∉ L) (hwv : w ≠ v) (hD : s(w, v) ∉ D) :
    2 * (N1 a (ed s(w, v)) (G v) * (N0 (G w) * envOn a ed G L D)) ≤
      envOn a ed G (insert w (insert v L)) (insert s(w, v) D) := by
  unfold envOn
  rw [ENNReal.mul_iSup, ENNReal.mul_iSup, ENNReal.mul_iSup]
  refine iSup_le fun A => le_trans (le_of_eq ?_) (le_iSup (fun B => prodP a ed G B)
    (admExtend A w v hw hv hwv hD))
  rw [prodP_extend]; ring

/-- Half-bound conclusion, fused partner: all three rows of the slot table (TeX 1563-1595). -/
theorem envOn_fused (a : ℝ) (ed : Sym2 α → EdgeData d) (G : α → Kernel d) (w v b : α)
    (F : Kernel d) (hw : w ∉ L) (hv : v ∉ L) (hwv : w ≠ v) (hD : s(w, v) ∉ D) (hb : b ∈ L)
    (h0 : N0 F ≤ N0 (G w) * N0 (G b))
    (h1 : ∀ e ∈ D, N1 a (ed e) F ≤ N0 (G w) * N1 a (ed e) (G b))
    (h2 : ∀ e ∈ D, N2 a (ed e) F ≤ N0 (G w) * N2 a (ed e) (G b)) :
    2 * (N1 a (ed s(w, v)) (G v) * envOn a ed (Function.update G b F) L D) ≤
      envOn a ed G (insert w (insert v L)) (insert s(w, v) D) := by
  unfold envOn
  rw [ENNReal.mul_iSup, ENNReal.mul_iSup]
  refine iSup_le fun A => ?_
  calc 2 * (N1 a (ed s(w, v)) (G v) * prodP a ed (Function.update G b F) A)
        ≤ 2 * (N1 a (ed s(w, v)) (G v) * (N0 (G w) * prodP a ed G A)) := by
          gcongr; exact prodP_update_le a ed G A w b F hb h0 h1 h2
    _ = prodP a ed G (admExtend A w v hw hv hwv hD) := by rw [prodP_extend]; ring
    _ ≤ ⨆ B : Adm (insert w (insert v L)) (insert s(w, v) D), prodP a ed G B :=
          le_iSup (fun B => prodP a ed G B) _

end Assignments

/-! ### Analysis: covariances, translations, the endpoint and partner integrations -/

section Analysis

/-- The real covariance `x ↦ ∫ cos(ξ·x) μ(dξ)` is continuous. -/
theorem continuous_cosInt (μ : Measure (Rd d)) [IsFiniteMeasure μ] :
    Continuous fun x : Rd d => ∫ ξ, Real.cos (inner ℝ ξ x) ∂μ := by
  refine continuous_of_dominated (bound := fun _ => (1 : ℝ)) (fun x => ?_) (fun x => ?_)
    (integrable_const 1) (Filter.Eventually.of_forall fun ξ => ?_)
  · exact Continuous.aestronglyMeasurable (by fun_prop)
  · exact Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _
  · fun_prop

theorem measurable_gammaOf (μ : Measure (Rd d)) [IsFiniteMeasure μ] :
    Measurable (gammaOf μ) :=
  ENNReal.measurable_ofReal.comp (continuous_cosInt μ).measurable

/-- The real covariance is the real part of the transform. -/
theorem cosInt_eq_re (μ : Measure (Rd d)) [IsFiniteMeasure μ] (x : Rd d) :
    ∫ ξ, Real.cos (inner ℝ ξ x) ∂μ =
      (∫ ξ, Complex.exp (Complex.I * (inner ℝ ξ x : ℝ)) ∂μ).re := by
  have hI : Integrable (fun ξ : Rd d => Complex.exp (Complex.I * (inner ℝ ξ x : ℝ))) μ := by
    refine Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) 1
      (Filter.Eventually.of_forall ?_)
    intro ξ
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  have hre := integral_re hI
  have hcos : ∀ ξ : Rd d, RCLike.re (Complex.exp (Complex.I * (inner ℝ ξ x : ℝ))) =
      Real.cos (inner ℝ ξ x) := fun ξ => by
    rw [mul_comm]; exact Complex.exp_ofReal_mul_I_re _
  simp only [hcos] at hre
  rw [hre]; rfl

/-- Under `SpecNonneg`, the real covariance is nonnegative. -/
theorem cosInt_nonneg (μ : Measure (Rd d)) [IsFiniteMeasure μ] (hμ : SpecNonneg μ) (x : Rd d) :
    0 ≤ ∫ ξ, Real.cos (inner ℝ ξ x) ∂μ := by
  obtain ⟨r, hr, hint⟩ := hμ x
  rw [cosInt_eq_re, hint, Complex.ofReal_re]; exact hr

theorem abs_cosInt_le (μ : Measure (Rd d)) [IsFiniteMeasure μ] (x : Rd d) :
    |∫ ξ, Real.cos (inner ℝ ξ x) ∂μ| ≤ μ.real univ := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (C := 1)
    (f := fun ξ : Rd d => Real.cos (inner ℝ ξ x))
    (Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  rw [Real.norm_eq_abs, one_mul] at this
  exact this

/-- `ν_e`-almost every `λ` lies in `A_e ⊆ (0,∞)`. -/
theorem ae_nuE_mem (a : ℝ) (E : EdgeData d) : ∀ᵐ l ∂nuE a E.A, l ∈ E.A :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem E.measurableSet_A)

/-- `κ_e` is decreasing in `|t|` (TeX 1551-1552). -/
theorem kappa_anti (a : ℝ) (E : EdgeData d) {s t : ℝ} (h : |s| ≤ |t|) :
    kappa a E t ≤ kappa a E s := by
  unfold kappa
  refine lintegral_mono_ae ?_
  filter_upwards [ae_nuE_mem a E] with l hl
  have hl0 : 0 ≤ l := le_of_lt (E.A_subset hl)
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_left h hl0]))

/-- `ν_e` is s-finite (a density with respect to restricted Lebesgue measure). -/
theorem sFinite_nuE (a : ℝ) (A : Set ℝ) : SFinite (nuE a A) := by
  unfold nuE; infer_instance

theorem measurable_kappa (a : ℝ) (E : EdgeData d) : Measurable (kappa a E) := by
  have := sFinite_nuE a E.A
  unfold kappa
  have : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-(p.2 * |p.1|))) :=
    ENNReal.measurable_ofReal.comp (Continuous.measurable (by fun_prop))
  exact this.lintegral_prod_right'

/-- Translation invariance of Lebesgue measure on `ℝ × ℝ^d`. -/
theorem lintegral_shift (f : ℝ × Rd d → ℝ≥0∞) (c : ℝ × Rd d) :
    ∫⁻ y, f (y - c) = ∫⁻ y, f y := by
  have : (volume : Measure (ℝ × Rd d)).IsAddRightInvariant := by
    rw [Measure.volume_eq_prod]; infer_instance
  exact lintegral_sub_right_eq_self f c

theorem measurable_shiftKernel {G : Kernel d} (hG : Measurable (Function.uncurry G))
    (c : ℝ × Rd d) :
    Measurable fun y : ℝ × Rd d => if c.1 < y.1 then G (y.1 - c.1) (y.2 - c.2) else 0 :=
  Measurable.ite (measurableSet_lt measurable_const measurable_fst)
    (hG.comp ((measurable_fst.sub measurable_const).prodMk (measurable_snd.sub measurable_const)))
    measurable_const

/-- `N_0` as one integral over `ℝ × ℝ^d`. -/
theorem N0_eq_lintegral {G : Kernel d} (hG : Measurable (Function.uncurry G)) :
    N0 G = ∫⁻ y : ℝ × Rd d, if 0 < y.1 then G y.1 y.2 else 0 := by
  have hm : Measurable fun y : ℝ × Rd d => if 0 < y.1 then G y.1 y.2 else 0 :=
    Measurable.ite (measurableSet_lt measurable_const measurable_fst) hG measurable_const
  rw [Measure.volume_eq_prod, lintegral_prod _ hm.aemeasurable]
  unfold N0
  rw [← lintegral_indicator measurableSet_Ioi]
  congr 1; ext t
  by_cases ht : 0 < t
  · simp [ht]
  · simp [ht]

/-- **Integrating a terminal unpaired vertex** gives its mass (TeX 1560-1561). -/
theorem lintegral_shift_N0 {G : Kernel d} (hG : Measurable (Function.uncurry G))
    (c : ℝ × Rd d) :
    ∫⁻ y : ℝ × Rd d, (if c.1 < y.1 then G (y.1 - c.1) (y.2 - c.2) else 0) = N0 G := by
  rw [N0_eq_lintegral hG]
  conv_rhs => rw [← lintegral_shift _ c]
  congr 1; ext y
  simp only [Prod.fst_sub, Prod.snd_sub, sub_pos]

/-- `conv G H t x = 0` for `t ≤ 0`. -/
theorem conv_of_nonpos (G H : Kernel d) {t : ℝ} (ht : t ≤ 0) (x : Rd d) : conv G H t x = 0 := by
  unfold conv
  rw [Set.Ioo_eq_empty (not_lt.2 ht), Measure.restrict_empty, lintegral_zero_measure]

/-- **Integrating an unpaired vertex with a successor** gives the fused kernel `G * H` at the
successor, relative to the predecessor `c` of the integrated vertex (TeX 1563-1566). -/
theorem lintegral_shift_conv {G H : Kernel d} (hG : Measurable (Function.uncurry G))
    (hH : Measurable (Function.uncurry H)) (c : ℝ × Rd d) (s : ℝ) (x : Rd d) :
    ∫⁻ y : ℝ × Rd d, (if c.1 < y.1 then G (y.1 - c.1) (y.2 - c.2) else 0) *
        (if y.1 < s then H (s - y.1) (x - y.2) else 0) = conv G H (s - c.1) (x - c.2) := by
  set F : ℝ × Rd d → ℝ≥0∞ := fun y => (if 0 < y.1 then G y.1 y.2 else 0) *
      (if y.1 < s - c.1 then H (s - c.1 - y.1) (x - c.2 - y.2) else 0) with hF
  have hFm : Measurable F := by
    refine (Measurable.ite (measurableSet_lt measurable_const measurable_fst) hG
      measurable_const).mul (Measurable.ite (measurableSet_lt measurable_fst measurable_const) ?_
      measurable_const)
    exact hH.comp ((measurable_const.sub measurable_fst).prodMk
      (measurable_const.sub measurable_snd))
  have h1 : (fun y : ℝ × Rd d => (if c.1 < y.1 then G (y.1 - c.1) (y.2 - c.2) else 0) *
      (if y.1 < s then H (s - y.1) (x - y.2) else 0)) = fun y => F (y - c) := by
    ext y
    simp only [hF, Prod.fst_sub, Prod.snd_sub, sub_pos, sub_lt_sub_iff_right,
      sub_sub_sub_cancel_right]
  rw [h1, lintegral_shift F c, Measure.volume_eq_prod, lintegral_prod _ hFm.aemeasurable]
  unfold conv
  rw [← lintegral_indicator measurableSet_Ioo]
  congr 1; ext t
  by_cases ht0 : 0 < t
  · by_cases ht1 : t < s - c.1
    · rw [Set.indicator_of_mem (show t ∈ Ioo 0 (s - c.1) from ⟨ht0, ht1⟩)]
      simp only [hF, ht0, ht1, ite_true]
    · rw [Set.indicator_of_notMem (fun h => ht1 h.2)]
      simp [hF, ht1]
  · rw [Set.indicator_of_notMem (fun h => ht0 h.1)]
    simp [hF, ht0]

/-- **The complex Laplace-Fourier Fubini at fixed `λ ≥ 0`** (TeX 1553-1556, 1520-1521):
`∫_{t>0} ∫ G(t,y) e^{-λt} γ(c - y) dt dy ≤ ∫ |𝓛G(λ,ξ)| μ(dξ)`. -/
theorem inner_le_lapFour (μ : Measure (Rd d)) [IsFiniteMeasure μ] (hμ : SpecNonneg μ)
    {G : Kernel d} (hG : Measurable (Function.uncurry G)) (hN0 : N0 G < ∞) {l : ℝ}
    (hl : 0 ≤ l) (c : Rd d) :
    ∫⁻ y : ℝ × Rd d, (if 0 < y.1 then G y.1 y.2 else 0) *
        (ENNReal.ofReal (Real.exp (-(l * |y.1|))) * gammaOf μ (c - y.2)) ≤
      ∫⁻ ξ, ‖lapFour G l ξ‖ₑ ∂μ := by
  set S : Set (ℝ × Rd d) := Ioi (0 : ℝ) ×ˢ (univ : Set (Rd d)) with hS
  have hSm : MeasurableSet S := measurableSet_Ioi.prod MeasurableSet.univ
  have memS : ∀ y : ℝ × Rd d, y ∈ S ↔ 0 < y.1 := fun y => by simp [S]
  set Γ : Rd d → ℝ := fun x => ∫ ξ, Real.cos (inner ℝ ξ x) ∂μ with hΓ
  have hGm : Measurable fun y : ℝ × Rd d => G y.1 y.2 := hG
  set g : ℝ × Rd d → ℝ := fun y => (G y.1 y.2).toReal with hg
  have hgm : Measurable g := hGm.ennreal_toReal
  have hlin : ∫⁻ y in S, G y.1 y.2 = N0 G := by
    rw [N0_eq_lintegral hG, ← lintegral_indicator hSm]
    congr 1; ext y
    by_cases h : 0 < y.1
    · simp [Set.indicator_of_mem ((memS y).2 h), h]
    · simp [Set.indicator_of_notMem (fun hy => h ((memS y).1 hy)), h]
  have hfin : ∫⁻ y in S, G y.1 y.2 ≠ ∞ := by rw [hlin]; exact hN0.ne
  have hae : ∀ᵐ y ∂volume.restrict S, G y.1 y.2 < ∞ := ae_lt_top hGm hfin
  have hgi : Integrable g (volume.restrict S) :=
    integrable_toReal_of_lintegral_ne_top hGm.aemeasurable hfin
  have hΓm : Continuous Γ := continuous_cosInt μ
  -- the real integrand on `(0,∞) × ℝ^d`
  set F : ℝ × Rd d → ℝ := fun y => g y * Real.exp (-(l * y.1)) * Γ (c - y.2) with hFdef
  have hFm : Measurable F :=
    (hgm.mul (Continuous.measurable (by fun_prop))).mul
      (hΓm.measurable.comp (measurable_const.sub measurable_snd))
  have hexp : ∀ y : ℝ × Rd d, y ∈ S → Real.exp (-(l * y.1)) ≤ 1 := fun y hy => by
    rw [Real.exp_le_one_iff]
    have := (memS y).1 hy
    nlinarith
  have hFi : Integrable F (volume.restrict S) := by
    refine Integrable.mono' (hgi.mul_const (μ.real univ)) hFm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hSm] with y hy
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg,
      abs_of_pos (Real.exp_pos _)]
    have h1 := hexp y hy
    have h2 := abs_cosInt_le μ (c - y.2)
    have h3 : 0 ≤ g y := ENNReal.toReal_nonneg
    calc g y * Real.exp (-(l * y.1)) * |Γ (c - y.2)| ≤ g y * 1 * μ.real univ := by gcongr
      _ = _ := by ring
  have hFnn : 0 ≤ᵐ[volume.restrict S] F := Filter.Eventually.of_forall fun y =>
    mul_nonneg (mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le) (cosInt_nonneg μ hμ _)
  -- step 1: the lower integral is `ofReal` of the real integral
  have e1 : ∫⁻ y : ℝ × Rd d, (if 0 < y.1 then G y.1 y.2 else 0) *
        (ENNReal.ofReal (Real.exp (-(l * |y.1|))) * gammaOf μ (c - y.2)) =
      ENNReal.ofReal (∫ y in S, F y) := by
    rw [ofReal_integral_eq_lintegral_ofReal hFi hFnn, ← lintegral_indicator hSm]
    have : (fun y : ℝ × Rd d => (if 0 < y.1 then G y.1 y.2 else 0) *
        (ENNReal.ofReal (Real.exp (-(l * |y.1|))) * gammaOf μ (c - y.2))) =
        S.indicator fun y => G y.1 y.2 *
          (ENNReal.ofReal (Real.exp (-(l * |y.1|))) * gammaOf μ (c - y.2)) := by
      ext y
      by_cases h : 0 < y.1
      · simp [Set.indicator_of_mem ((memS y).2 h), h]
      · simp [Set.indicator_of_notMem (fun hy => h ((memS y).1 hy)), h]
    rw [this, lintegral_indicator hSm, lintegral_indicator hSm]
    refine lintegral_congr_ae ?_
    filter_upwards [hae, ae_restrict_mem hSm] with y hy hyS
    have hy0 := (memS y).1 hyS
    rw [abs_of_pos hy0, hFdef]
    simp only [hg]
    rw [ENNReal.ofReal_mul (mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le),
      ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hy.ne, gammaOf, mul_assoc]
  -- step 2: Fubini in `(t, x) × ξ`
  set H : (ℝ × Rd d) → Rd d → ℝ :=
    fun y ξ => g y * Real.exp (-(l * y.1)) * Real.cos (inner ℝ ξ (c - y.2)) with hHdef
  have hHm : Measurable (Function.uncurry H) := by
    refine ((hgm.comp measurable_fst).mul ?_).mul ?_
    · exact Continuous.measurable (by fun_prop)
    · exact Continuous.measurable (by fun_prop)
  have hHi : Integrable (Function.uncurry H) ((volume.restrict S).prod μ) := by
    refine Integrable.mono' (hgi.comp_fst μ) hHm.aestronglyMeasurable ?_
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hSm)] with p hp
    simp only [Function.uncurry, hHdef, Real.norm_eq_abs]
    rw [abs_mul, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg, abs_of_pos (Real.exp_pos _)]
    have h1 := hexp p.1 hp
    have h2 := Real.abs_cos_le_one (inner ℝ p.2 (c - p.1.2))
    have h3 : 0 ≤ g p.1 := ENNReal.toReal_nonneg
    calc g p.1 * Real.exp (-(l * p.1.1)) * |Real.cos (inner ℝ p.2 (c - p.1.2))| ≤
        g p.1 * 1 * 1 := by gcongr
      _ = g p.1 := by ring
  have e2 : ∫ y in S, F y = ∫ ξ, (∫ y in S, H y ξ) ∂μ := by
    rw [← integral_integral_swap hHi]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hFdef, hHdef, hΓ]
    rw [integral_const_mul]
  -- step 3: each `ξ`-section is the real part of a unimodular multiple of `𝓛G(λ,ξ)`
  have hK : ∀ ξ : Rd d, |∫ y in S, H y ξ| ≤ ‖lapFour G l ξ‖ := by
    intro ξ
    set φ : ℝ × Rd d → ℂ := fun p => Complex.exp ((-(l * p.1) : ℝ) +
      Complex.I * (inner ℝ ξ p.2 : ℝ)) * ((G p.1 p.2).toReal : ℂ) with hφ
    set u : ℂ := Complex.exp ((-(inner ℝ ξ c) : ℝ) * Complex.I) with hu
    have hφm : Measurable φ := by
      refine Measurable.mul (Continuous.measurable (by fun_prop)) ?_
      exact Complex.measurable_ofReal.comp hgm
    have hφi : Integrable (fun p => u * φ p) (volume.restrict S) := by
      refine Integrable.mono' hgi (measurable_const.mul hφm).aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem hSm] with p hp
      rw [norm_mul, hu, Complex.norm_exp_ofReal_mul_I, one_mul, hφ, norm_mul,
        Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ENNReal.toReal_nonneg]
      have : (((-(l * p.1) : ℝ) : ℂ) + Complex.I * (inner ℝ ξ p.2 : ℝ)).re = -(l * p.1) := by
        simp
      rw [this]
      have h1 := hexp p hp
      have h3 : 0 ≤ g p := ENNReal.toReal_nonneg
      calc Real.exp (-(l * p.1)) * (G p.1 p.2).toReal ≤ 1 * g p := by gcongr
        _ = g p := one_mul _
    have hre : ∀ p : ℝ × Rd d, RCLike.re (u * φ p) = H p ξ := by
      intro p
      simp only [hu, hφ, hHdef, hg]
      rw [← mul_assoc, ← Complex.exp_add, RCLike.re_to_complex, Complex.re_mul_ofReal,
        Complex.exp_re]
      have hr : ((((-(inner ℝ ξ c)) : ℝ) : ℂ) * Complex.I + ((((-(l * p.1)) : ℝ) : ℂ) +
          Complex.I * ((inner ℝ ξ p.2 : ℝ) : ℂ))).re = -(l * p.1) := by simp
      have hi : ((((-(inner ℝ ξ c)) : ℝ) : ℂ) * Complex.I + ((((-(l * p.1)) : ℝ) : ℂ) +
          Complex.I * ((inner ℝ ξ p.2 : ℝ) : ℂ))).im = inner ℝ ξ p.2 - inner ℝ ξ c := by
        simp; ring
      rw [hr, hi, inner_sub_right, ← Real.cos_neg, neg_sub]
      ring
    have hint : ∫ y in S, H y ξ = (u * lapFour G l ξ).re := by
      rw [lapFour, ← integral_const_mul, ← RCLike.re_to_complex, ← integral_re hφi]
      exact integral_congr_ae (Filter.Eventually.of_forall fun p => (hre p).symm)
    rw [hint]
    calc |(u * lapFour G l ξ).re| ≤ ‖u * lapFour G l ξ‖ := Complex.abs_re_le_norm _
      _ = ‖lapFour G l ξ‖ := by rw [norm_mul, hu, Complex.norm_exp_ofReal_mul_I, one_mul]
  -- conclusion
  rw [e1, e2]
  calc ENNReal.ofReal (∫ ξ, (∫ y in S, H y ξ) ∂μ) ≤ ‖∫ ξ, (∫ y in S, H y ξ) ∂μ‖ₑ := by
        rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ ≤ ∫⁻ ξ, ‖∫ y in S, H y ξ‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ ξ, ‖lapFour G l ξ‖ₑ ∂μ := lintegral_mono fun ξ => by
        rw [Real.enorm_eq_ofReal_abs, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hK ξ)

/-- **Endpoint integration** (TeX 1549-1557): on `s_w ≤ s_p`, integrating the endpoint `v`
(relative to its predecessor `p`) against the edge factor of `e₀ = {w, v}` is at most
`N_{1,e₀}(G_v)`. -/
theorem endpoint_le_N1 (a : ℝ) (E : EdgeData d) {G : Kernel d}
    (hG : Measurable (Function.uncurry G)) (hN0 : N0 G < ∞) (p w : ℝ × Rd d) (hwp : w.1 ≤ p.1) :
    ∫⁻ y : ℝ × Rd d, (if p.1 < y.1 then G (y.1 - p.1) (y.2 - p.2) else 0) *
        (kappa a E (w.1 - y.1) * gammaOf E.μ (w.2 - y.2)) ≤ N1 a E G := by
  have := sFinite_nuE a E.A
  have hγ := measurable_gammaOf E.μ
  have m0 : Measurable fun q : (ℝ × Rd d) × ℝ => if 0 < q.1.1 then G q.1.1 q.1.2 else 0 :=
    Measurable.ite (measurableSet_lt measurable_const measurable_fst.fst)
      (hG.comp measurable_fst) measurable_const
  have m1 : Measurable fun q : (ℝ × Rd d) × ℝ => ENNReal.ofReal (Real.exp (-(q.2 * |q.1.1|))) :=
    ENNReal.measurable_ofReal.comp (Continuous.measurable (by fun_prop))
  have m2 : Measurable fun q : (ℝ × Rd d) × ℝ => gammaOf E.μ ((w.2 - p.2) - q.1.2) :=
    hγ.comp (measurable_const.sub measurable_fst.snd)
  have hmeas : Measurable fun q : (ℝ × Rd d) × ℝ =>
      (if 0 < q.1.1 then G q.1.1 q.1.2 else 0) *
        (ENNReal.ofReal (Real.exp (-(q.2 * |q.1.1|))) * gammaOf E.μ ((w.2 - p.2) - q.1.2)) :=
    m0.mul (m1.mul m2)
  calc _ ≤ ∫⁻ y : ℝ × Rd d, (if p.1 < y.1 then G (y.1 - p.1) (y.2 - p.2) else 0) *
        (kappa a E (y.1 - p.1) * gammaOf E.μ (w.2 - y.2)) := by
        refine lintegral_mono fun y => ?_
        by_cases h : p.1 < y.1
        · simp only [h, ite_true]
          gcongr
          apply kappa_anti
          rw [abs_of_pos (sub_pos.2 h), abs_of_nonpos (by linarith)]
          linarith
        · simp [h]
    _ = ∫⁻ y : ℝ × Rd d, (if 0 < y.1 then G y.1 y.2 else 0) *
        (kappa a E y.1 * gammaOf E.μ ((w.2 - p.2) - y.2)) := by
        conv_rhs => rw [← lintegral_shift _ p]
        congr 1; ext y
        simp only [Prod.fst_sub, Prod.snd_sub, sub_pos, sub_sub_sub_cancel_right]
    _ = ∫⁻ y : ℝ × Rd d, ∫⁻ l, (if 0 < y.1 then G y.1 y.2 else 0) *
        (ENNReal.ofReal (Real.exp (-(l * |y.1|))) * gammaOf E.μ ((w.2 - p.2) - y.2))
          ∂nuE a E.A := by
        congr 1; ext y
        unfold kappa
        have hf : Measurable fun l : ℝ => ENNReal.ofReal (Real.exp (-(l * |y.1|))) :=
          ENNReal.measurable_ofReal.comp (Continuous.measurable (by fun_prop))
        rw [← lintegral_mul_const _ hf, ← lintegral_const_mul _ (hf.mul_const _)]
    _ = ∫⁻ l, ∫⁻ y : ℝ × Rd d, (if 0 < y.1 then G y.1 y.2 else 0) *
        (ENNReal.ofReal (Real.exp (-(l * |y.1|))) * gammaOf E.μ ((w.2 - p.2) - y.2))
          ∂volume ∂nuE a E.A :=
        lintegral_lintegral_swap hmeas.aemeasurable
    _ ≤ ∫⁻ l, ∫⁻ ξ, ‖lapFour G l ξ‖ₑ ∂E.μ ∂nuE a E.A := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_nuE_mem a E] with l hl
        exact inner_le_lapFour E.μ E.spec_nonneg hG hN0 (E.A_subset hl).le _
    _ = N1 a E G := rfl

end Analysis

/-! ### The integrand, factor by factor -/

section Integrand

variable {α : Type*} [DecidableEq α]

/-- The factor of a label in `E:pairing-diagram-general` with its simplex constraint:
`1_{s_{p(l)} < s_l} G_l(s_l - s_{p(l)}, x_l - x_{p(l)})`. -/
def vfac (dg : TwoChain α) (G : α → Kernel d) (z : α → ℝ × Rd d) (l : α) : ℝ≥0∞ :=
  if dg.predTime z l < (z l).1 then G l ((z l).1 - dg.predTime z l) ((z l).2 - dg.predPos z l)
  else 0

/-- The integrand is the product of the label factors and the edge factors. -/
theorem integrand_eq (a : ℝ) (dg : TwoChain α) (ed : Sym2 α → EdgeData d) (G : α → Kernel d)
    (z : α → ℝ × Rd d) :
    integrand a dg ed G z =
      (∏ l ∈ dg.labels, vfac dg G z l) * ∏ e ∈ dg.D, edgeWeight a (ed e) z e := by
  unfold integrand vfac
  rw [Finset.prod_ite_zero]
  by_cases h : z ∈ dg.posSimplex
  · have h' : ∀ l ∈ dg.labels, dg.predTime z l < (z l).1 := h
    rw [Set.indicator_of_mem h, ite_eq_left h']
  · have h' : ¬ ∀ l ∈ dg.labels, dg.predTime z l < (z l).1 := h
    rw [Set.indicator_of_notMem h, ite_eq_right h', zero_mul]

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

theorem measurable_vfac (dg : TwoChain α) (G : α → Kernel d) {l : α}
    (hG : Measurable (Function.uncurry (G l))) :
    Measurable fun z : α → ℝ × Rd d => vfac dg G z l :=
  Measurable.ite (measurableSet_lt (measurable_predTime dg l) (measurable_pi_apply l).fst)
    (hG.comp (((measurable_pi_apply l).fst.sub (measurable_predTime dg l)).prodMk
      ((measurable_pi_apply l).snd.sub (measurable_predPos dg l)))) measurable_const

omit [DecidableEq α] in
theorem measurable_edgeWeight (a : ℝ) (E : EdgeData d) (e : Sym2 α) :
    Measurable fun z : α → ℝ × Rd d => edgeWeight a E z e := by
  induction e using Sym2.ind with
  | h j k =>
    simp only [edgeWeight_mk]
    exact ((measurable_kappa a E).comp ((measurable_pi_apply j).fst.sub
      (measurable_pi_apply k).fst)).mul ((measurable_gammaOf E.μ).comp
      ((measurable_pi_apply j).snd.sub (measurable_pi_apply k).snd))

theorem measurable_prodFac (a : ℝ) (dg : TwoChain α) (ed : Sym2 α → EdgeData d)
    (G : α → Kernel d) (S : Finset α) (hG : ∀ l ∈ S, Measurable (Function.uncurry (G l)))
    (D : Finset (Sym2 α)) :
    Measurable fun z : α → ℝ × Rd d =>
      (∏ l ∈ S, vfac dg G z l) * ∏ e ∈ D, edgeWeight a (ed e) z e :=
  (Finset.measurable_prod S fun l hl => measurable_vfac dg G (hG l hl)).mul
    (Finset.measurable_prod D fun e _ => measurable_edgeWeight a (ed e) e)

theorem predTime_update (dg : TwoChain α) (z : α → ℝ × Rd d) {v l : α} (y : ℝ × Rd d)
    (h : dg.pred l ≠ some v) : dg.predTime (Function.update z v y) l = dg.predTime z l := by
  unfold TwoChain.predTime
  cases hp : dg.pred l with
  | none => rfl
  | some p =>
    have hpv : p ≠ v := fun hpv => h (by rw [hp, hpv])
    simp [Function.update_of_ne hpv]

theorem predPos_update (dg : TwoChain α) (z : α → ℝ × Rd d) {v l : α} (y : ℝ × Rd d)
    (h : dg.pred l ≠ some v) : dg.predPos (Function.update z v y) l = dg.predPos z l := by
  unfold TwoChain.predPos
  cases hp : dg.pred l with
  | none => rfl
  | some p =>
    have hpv : p ≠ v := fun hpv => h (by rw [hp, hpv])
    simp [Function.update_of_ne hpv]

theorem vfac_update_of_ne (dg : TwoChain α) (G : α → Kernel d) (z : α → ℝ × Rd d) {v l : α}
    (y : ℝ × Rd d) (hlv : l ≠ v) (h : dg.pred l ≠ some v) :
    vfac dg G (Function.update z v y) l = vfac dg G z l := by
  unfold vfac
  rw [predTime_update dg z y h, predPos_update dg z y h, Function.update_of_ne hlv]

theorem vfac_update_self (dg : TwoChain α) (G : α → Kernel d) (z : α → ℝ × Rd d) {v : α}
    (y : ℝ × Rd d) (h : dg.pred v ≠ some v) :
    vfac dg G (Function.update z v y) v =
      if dg.predTime z v < y.1 then G v (y.1 - dg.predTime z v) (y.2 - dg.predPos z v)
      else 0 := by
  unfold vfac
  rw [predTime_update dg z y h, predPos_update dg z y h, Function.update_self]

theorem vfac_update_succ (dg : TwoChain α) (G : α → Kernel d) (z : α → ℝ × Rd d) {w b : α}
    (y : ℝ × Rd d) (hbw : b ≠ w) (h : dg.pred b = some w) :
    vfac dg G (Function.update z w y) b =
      if y.1 < (z b).1 then G b ((z b).1 - y.1) ((z b).2 - y.2) else 0 := by
  unfold vfac TwoChain.predTime TwoChain.predPos
  rw [h]
  simp only [Option.elim, Function.update_self, Function.update_of_ne hbw]

theorem vfac_congr {dg dg' : TwoChain α} {G G' : α → Kernel d} (z : α → ℝ × Rd d) {l : α}
    (hp : dg'.pred l = dg.pred l) (hG : G' l = G l) : vfac dg' G' z l = vfac dg G z l := by
  unfold vfac TwoChain.predTime TwoChain.predPos
  rw [hp, hG]

theorem edgeWeight_update (a : ℝ) (E : EdgeData d) (z : α → ℝ × Rd d) {v : α} (y : ℝ × Rd d)
    {e : Sym2 α} (hv : v ∉ e) : edgeWeight a E (Function.update z v y) e = edgeWeight a E z e := by
  induction e using Sym2.ind with
  | h j k =>
    have hj : j ≠ v := fun h => hv (by rw [← h]; exact Sym2.mem_mk_left j k)
    have hk : k ≠ v := fun h => hv (by rw [← h]; exact Sym2.mem_mk_right j k)
    simp only [edgeWeight_mk, Function.update_of_ne hj, Function.update_of_ne hk]

theorem edgeWeight_update_endpoint (a : ℝ) (E : EdgeData d) (z : α → ℝ × Rd d) {w v : α}
    (y : ℝ × Rd d) (hwv : w ≠ v) :
    edgeWeight a E (Function.update z v y) s(w, v) =
      kappa a E ((z w).1 - y.1) * gammaOf E.μ ((z w).2 - y.2) := by
  rw [edgeWeight_mk, Function.update_self, Function.update_of_ne hwv]

theorem lmarginal_const_mul (s : Finset α) (f : (α → ℝ × Rd d) → ℝ≥0∞) {c : ℝ≥0∞}
    (hc : c ≠ ∞) (x : α → ℝ × Rd d) :
    (∫⋯∫⁻_s, (fun z => c * f z) ∂fun _ => (volume : Measure (ℝ × Rd d))) x =
      c * (∫⋯∫⁻_s, f ∂fun _ => (volume : Measure (ℝ × Rd d))) x := by
  simp only [lmarginal]
  exact lintegral_const_mul' c _ hc

end Integrand

/-! ### Step 2: the regional half-bound -/

section Regional

/-- **Step 2 of `L:pairing-product-envelope`: the regional half-bound** (TeX lines 1539-1595 at
revision edf7085f (book 1.1.3)).  Assume the full bound at the finite cap for every diagram with
`n` edges (`CappedEnvelopeAt d α a n`, TeX 1547, "the full bound at `n-1`").  For a diagram with
`n + 1` edges, an endpoint `v` with partner `w` (TeX's `a`), and a measurable region `R`
independent of `(s_v, x_v)` on which `s_w ≤ s_{p(v)}`, the integral over `R` is at most half of
the envelope.  The only further input is `E:pairing-convolution-norms` (item B's
`ConvolutionNormsTarget d`, TeX 1522-1535) for the fused kernel. -/
theorem regional_half_bound (hB : ConvolutionNormsTarget d) {α : Type*} [DecidableEq α]
    (a : ℝ) (n : ℕ) : RegionalHalfBoundTarget d α a n := by
  intro ha0 ha1 IH dg ed G hwf hcard hcap hK v w R hv he hRm hRv hRw
  -- basic facts about `e₀ = {w, v}`
  have hwv : w ≠ v := fun h => (hwf.edge _ he).1 (Sym2.mk_isDiag_iff.2 h)
  have hvL : v ∈ dg.labels := (hwf.edge _ he).2 v (Sym2.mem_mk_right w v)
  have hwL : w ∈ dg.labels := (hwf.edge _ he).2 w (Sym2.mem_mk_left w v)
  have hvpred : ∀ l, dg.pred l ≠ some v := pred_ne_endpoint hwf hv
  have hnotin : ∀ e ∈ dg.D.erase s(w, v), w ∉ e ∧ v ∉ e := fun e he' => by
    rw [Finset.mem_erase] at he'
    exact ⟨fun h => he'.1 (eq_of_mem_edge hwf he he'.2 (Or.inl rfl) h),
      fun h => he'.1 (eq_of_mem_edge hwf he he'.2 (Or.inr rfl) h)⟩
  have hcapE : ∀ e ∈ dg.D, ∃ L : ℝ, (ed e).A ⊆ Ioc 0 L := fun e he' => by
    obtain ⟨L, hL⟩ := hcap
    exact ⟨L, hL e he'⟩
  -- the reduced diagram `D \ {e₀}` on the labels without `w`, `v`
  set dg2 := del2 dg w v with hdg2
  have hwf2 : dg2.WF := wf_del2 hwf he
  have hcard2 : dg2.D.card = n := card_del2 he hcard
  have hL2 : dg2.labels = (dg.labels.erase v).erase w := labels_del2 hwf w v
  have hD2 : dg2.D = dg.D.erase s(w, v) := rfl
  have hsubL : dg2.labels ⊆ dg.labels := by
    rw [hL2]; exact (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
  have hsubD : dg2.D ⊆ dg.D := Finset.erase_subset _ _
  have hcap2 : CappedOn dg2.D ed := by
    obtain ⟨L, hL⟩ := hcap
    exact ⟨L, fun e he' => hL e (hsubD he')⟩
  have hw2 : w ∉ dg2.labels := by rw [hL2]; simp
  have hv2 : v ∉ dg2.labels := by rw [hL2]; simp
  have he2 : s(w, v) ∉ dg2.D := by rw [hD2]; simp
  have hLeq : dg.labels = insert w (insert v dg2.labels) := by
    rw [hL2]; ext x
    simp only [Finset.mem_insert, Finset.mem_erase]
    by_cases hxw : x = w
    · subst hxw; simp [hwL]
    · by_cases hxv : x = v
      · subst hxv; simp [hvL]
      · simp [hxw, hxv]
  have hDeq : dg.D = insert s(w, v) dg2.D := by rw [hD2, Finset.insert_erase he]
  have henv : env a dg ed G = envOn a ed G (insert w (insert v dg2.labels)) (insert s(w, v) dg2.D) := by
    rw [env_eq_envOn, ← hLeq, ← hDeq]
  have hmem2 : ∀ l ∈ dg2.labels, l ≠ v ∧ l ≠ w ∧ l ∈ dg.labels := fun l hl => by
    rw [hL2, Finset.mem_erase, Finset.mem_erase] at hl
    exact ⟨hl.2.1, hl.1, hl.2.2⟩
  -- `J`: the endpoint integrated out, the partner `w` unpaired
  set L' := dg.labels.erase v with hL'
  have hwL' : w ∈ L' := Finset.mem_erase.2 ⟨hwv, hwL⟩
  have hL'w : L'.erase w = dg2.labels := hL2.symm
  set J : (α → ℝ × Rd d) → ℝ≥0∞ := fun z =>
    (∏ l ∈ L', vfac dg G z l) * ∏ e ∈ dg.D.erase s(w, v), edgeWeight a (ed e) z e with hJ
  have hJm : Measurable J :=
    measurable_prodFac a dg ed G L' (fun l hl => hK.meas l (Finset.mem_of_mem_erase hl)) _
  have hIm : Measurable (integrand a dg ed G) := by
    have : integrand a dg ed G =
        fun z => (∏ l ∈ dg.labels, vfac dg G z l) * ∏ e ∈ dg.D, edgeWeight a (ed e) z e :=
      funext (integrand_eq a dg ed G)
    rw [this]
    exact measurable_prodFac a dg ed G _ hK.meas _
  -- Step A: endpoint integration (TeX 1549-1557)
  have hN1 : N1 a (ed s(w, v)) (G v) ≠ ∞ := (hK.N1_lt v hvL _ he).ne
  have stepA : regionIntegral a dg ed G R ≤
      N1 a (ed s(w, v)) (G v) * (∫⋯∫⁻_L', J ∂fun _ => (volume : Measure (ℝ × Rd d))) 0 := by
    unfold regionIntegral
    rw [lmarginal_erase' _ (hIm.indicator hRm) hvL, ← lmarginal_const_mul L' J hN1]
    refine lmarginal_mono (fun z => ?_) 0
    simp only
    set z0 := Function.update z v (0 : ℝ × Rd d) with hz0
    have hmemR : ∀ y, Function.update z v y ∈ R ↔ z0 ∈ R := fun y =>
      hRv _ _ (fun l hl => by simp [hz0, Function.update_of_ne hl])
    by_cases hz : z0 ∈ R
    · have hw_le : (z w).1 ≤ dg.predTime z v := by
        have := hRw z0 hz
        rwa [show z0 w = z w from Function.update_of_ne hwv _ _,
          predTime_update dg z 0 (hvpred v)] at this
      have hfac : ∀ y, R.indicator (integrand a dg ed G) (Function.update z v y) =
          ((if dg.predTime z v < y.1 then
              G v (y.1 - dg.predTime z v) (y.2 - dg.predPos z v) else 0) *
            (kappa a (ed s(w, v)) ((z w).1 - y.1) * gammaOf (ed s(w, v)).μ ((z w).2 - y.2))) *
            J z := by
        intro y
        rw [Set.indicator_of_mem ((hmemR y).2 hz), integrand_eq,
          ← Finset.mul_prod_erase dg.labels (fun l => vfac dg G (Function.update z v y) l) hvL,
          ← Finset.mul_prod_erase dg.D
            (fun e => edgeWeight a (ed e) (Function.update z v y) e) he]
        rw [vfac_update_self dg G z y (pred_ne_self hwf v),
          edgeWeight_update_endpoint a _ z y hwv]
        have h1 : ∏ l ∈ L', vfac dg G (Function.update z v y) l = ∏ l ∈ L', vfac dg G z l :=
          Finset.prod_congr rfl fun l hl =>
            vfac_update_of_ne dg G z y (Finset.ne_of_mem_erase hl) (hvpred l)
        have h2 : ∏ e ∈ dg.D.erase s(w, v), edgeWeight a (ed e) (Function.update z v y) e =
            ∏ e ∈ dg.D.erase s(w, v), edgeWeight a (ed e) z e :=
          Finset.prod_congr rfl fun e he' => edgeWeight_update a _ z y (hnotin e he').2
        rw [h1, h2, hJ]
        ring
      rw [show (fun y => R.indicator (integrand a dg ed G) (Function.update z v y)) = _ from
        funext hfac]
      have hm : Measurable fun y : ℝ × Rd d =>
          (if dg.predTime z v < y.1 then
              G v (y.1 - dg.predTime z v) (y.2 - dg.predPos z v) else 0) *
            (kappa a (ed s(w, v)) ((z w).1 - y.1) * gammaOf (ed s(w, v)).μ ((z w).2 - y.2)) :=
        (measurable_shiftKernel (hK.meas v hvL) (dg.predTime z v, dg.predPos z v)).mul
          (((measurable_kappa a _).comp (measurable_const.sub measurable_fst)).mul
            ((measurable_gammaOf _).comp (measurable_const.sub measurable_snd)))
      rw [lintegral_mul_const _ hm]
      gcongr
      exact endpoint_le_N1 a (ed s(w, v)) (hK.meas v hvL) (hK.N0_lt v hvL)
        (dg.predTime z v, dg.predPos z v) (z w) hw_le
    · have h0 : ∀ y, R.indicator (integrand a dg ed G) (Function.update z v y) = 0 := fun y =>
        Set.indicator_of_notMem (fun h => hz ((hmemR y).1 h)) _
      simp [h0]
  -- Step B: partner elimination (TeX 1558-1566)
  have hJsplit : (∫⋯∫⁻_L', J ∂fun _ => (volume : Measure (ℝ × Rd d))) 0 =
      (∫⋯∫⁻_dg2.labels, (fun z => ∫⁻ y, J (Function.update z w y))
        ∂fun _ => (volume : Measure (ℝ × Rd d))) 0 := by
    rw [lmarginal_erase' _ hJm hwL', hL'w]
  have hwpred : dg.pred w ≠ some w := pred_ne_self hwf w
  have hJfac : ∀ z y, J (Function.update z w y) =
      vfac dg G (Function.update z w y) w *
        ((∏ l ∈ dg2.labels, vfac dg G (Function.update z w y) l) *
          ∏ e ∈ dg2.D, edgeWeight a (ed e) z e) := by
    intro z y
    rw [hJ]
    simp only
    rw [← Finset.mul_prod_erase L' (fun l => vfac dg G (Function.update z w y) l) hwL', hL'w,
      ← hD2]
    have h2 : ∏ e ∈ dg2.D, edgeWeight a (ed e) (Function.update z w y) e =
        ∏ e ∈ dg2.D, edgeWeight a (ed e) z e :=
      Finset.prod_congr rfl fun e he' => edgeWeight_update a _ z y (hnotin e he').1
    rw [h2]
    ring
  by_cases hsucc : ∃ b ∈ dg2.labels, dg.pred b = some w
  · -- the partner has a successor `b`: fuse `G_w * G_b` at `b` (TeX 1563-1566)
    obtain ⟨b, hb2, hbw⟩ := hsucc
    obtain ⟨hbv, hbw', hbL⟩ := hmem2 b hb2
    set F := conv (G w) (G b) with hF
    set G' := Function.update G b F with hG'
    have hGw := hK.meas w hwL
    have hGb := hK.meas b hbL
    have hconv := hB a ha0 ha1 (G w) (G b) hGw hGb (hK.N0_lt w hwL) (hK.N0_lt b hbL)
    have hF0 : N0 F = N0 (G w) * N0 (G b) := hconv.1
    have hF12 : ∀ e ∈ dg.D, N1 a (ed e) F ≤ N0 (G w) * N1 a (ed e) (G b) ∧
        N2 a (ed e) F ≤ N0 (G w) * N2 a (ed e) (G b) := fun e he' =>
      hconv.2 (ed e) (hcapE e he')
    -- the kernel hypotheses for the reduced diagram with the fused kernel
    have hK' : KernelHyp a dg2 ed G' := by
      refine ⟨fun l hl => ?_, fun l hl => ?_, fun l hl e he' => ?_, fun l hl e he' => ?_⟩
      · by_cases hlb : l = b
        · rw [hlb, hG', Function.update_self]; exact measurable_conv hGw hGb
        · rw [hG', Function.update_of_ne hlb]; exact hK.meas l (hsubL hl)
      · by_cases hlb : l = b
        · rw [hlb, hG', Function.update_self, hF0]
          exact ENNReal.mul_lt_top (hK.N0_lt w hwL) (hK.N0_lt b hbL)
        · rw [hG', Function.update_of_ne hlb]; exact hK.N0_lt l (hsubL hl)
      · by_cases hlb : l = b
        · rw [hlb, hG', Function.update_self]
          exact lt_of_le_of_lt (hF12 e (hsubD he')).1
            (ENNReal.mul_lt_top (hK.N0_lt w hwL) (hK.N1_lt b hbL e (hsubD he')))
        · rw [hG', Function.update_of_ne hlb]; exact hK.N1_lt l (hsubL hl) e (hsubD he')
      · by_cases hlb : l = b
        · rw [hlb, hG', Function.update_self]
          exact lt_of_le_of_lt (hF12 e (hsubD he')).2
            (ENNReal.mul_lt_top (hK.N0_lt w hwL) (hK.N2_lt b hbL e (hsubD he')))
        · rw [hG', Function.update_of_ne hlb]; exact hK.N2_lt l (hsubL hl) e (hsubD he')
    -- integrating the partner gives the reduced integrand with `F` at `b`
    have hpt : ∀ z, ∫⁻ y, J (Function.update z w y) = integrand a dg2 ed G' z := by
      intro z
      have hrest : ∀ y, J (Function.update z w y) =
          ((if dg.predTime z w < y.1 then
              G w (y.1 - dg.predTime z w) (y.2 - dg.predPos z w) else 0) *
            (if y.1 < (z b).1 then G b ((z b).1 - y.1) ((z b).2 - y.2) else 0)) *
          ((∏ l ∈ dg2.labels.erase b, vfac dg G z l) *
            ∏ e ∈ dg2.D, edgeWeight a (ed e) z e) := by
        intro y
        rw [hJfac, ← Finset.mul_prod_erase dg2.labels
          (fun l => vfac dg G (Function.update z w y) l) hb2]
        rw [vfac_update_self dg G z y hwpred, vfac_update_succ dg G z y hbw' hbw]
        have h1 : ∏ l ∈ dg2.labels.erase b, vfac dg G (Function.update z w y) l =
            ∏ l ∈ dg2.labels.erase b, vfac dg G z l :=
          Finset.prod_congr rfl fun l hl => by
            have hlb := Finset.ne_of_mem_erase hl
            have hl2 := Finset.mem_of_mem_erase hl
            exact vfac_update_of_ne dg G z y (hmem2 l hl2).2.1
              (fun h => hlb (pred_inj hwf h hbw))
        rw [h1]
        ring
      rw [show (fun y => J (Function.update z w y)) = _ from funext hrest]
      have hm : Measurable fun y : ℝ × Rd d =>
          (if dg.predTime z w < y.1 then
              G w (y.1 - dg.predTime z w) (y.2 - dg.predPos z w) else 0) *
            (if y.1 < (z b).1 then G b ((z b).1 - y.1) ((z b).2 - y.2) else 0) :=
        (measurable_shiftKernel hGw (dg.predTime z w, dg.predPos z w)).mul
          (Measurable.ite (measurableSet_lt measurable_fst measurable_const)
            (hGb.comp ((measurable_const.sub measurable_fst).prodMk
              (measurable_const.sub measurable_snd))) measurable_const)
      rw [lintegral_mul_const _ hm, lintegral_shift_conv hGw hGb
        (dg.predTime z w, dg.predPos z w) (z b).1 (z b).2, integrand_eq,
        ← Finset.mul_prod_erase dg2.labels (fun l => vfac dg2 G' z l) hb2]
      simp only
      have hpb : dg2.pred b = dg.pred w := by
        rw [hdg2, pred_del2 hwf hv hwv hbv hbw', ite_eq_left hbw]
      have hvb : vfac dg2 G' z b = F ((z b).1 - dg.predTime z w) ((z b).2 - dg.predPos z w) := by
        unfold vfac
        have ht : dg2.predTime z b = dg.predTime z w := by
          unfold TwoChain.predTime; rw [hpb]
        have hp : dg2.predPos z b = dg.predPos z w := by
          unfold TwoChain.predPos; rw [hpb]
        rw [ht, hp, hG', Function.update_self]
        split_ifs with hlt
        · rfl
        · exact (conv_of_nonpos _ _ (by linarith [not_lt.1 hlt]) _).symm
      have h1 : ∏ l ∈ dg2.labels.erase b, vfac dg2 G' z l =
          ∏ l ∈ dg2.labels.erase b, vfac dg G z l :=
        Finset.prod_congr rfl fun l hl => by
          have hlb := Finset.ne_of_mem_erase hl
          have hl2 := Finset.mem_of_mem_erase hl
          obtain ⟨hlv, hlw, -⟩ := hmem2 l hl2
          refine vfac_congr z ?_ (by rw [hG', Function.update_of_ne hlb])
          rw [hdg2, pred_del2 hwf hv hwv hlv hlw,
            ite_eq_right (fun h => hlb (pred_inj hwf h hbw))]
      rw [hvb, h1, hF]
      ring
    have hIJ : (∫⋯∫⁻_L', J ∂fun _ => (volume : Measure (ℝ × Rd d))) 0 =
        pairingIntegral a dg2 ed G' := by
      rw [hJsplit, pairingIntegral]
      congr 1
      exact funext hpt
    have hIH : pairingIntegral a dg2 ed G' ≤ env a dg2 ed G' :=
      IH dg2 ed G' hwf2 hcard2 hcap2 hK'
    calc 2 * regionIntegral a dg ed G R
        ≤ 2 * (N1 a (ed s(w, v)) (G v) * env a dg2 ed G') := by
          gcongr
          exact stepA.trans (by rw [hIJ]; gcongr)
      _ ≤ env a dg ed G := by
          rw [henv]
          exact envOn_fused a ed G w v b F hw2 hv2 hwv he2 hb2 hF0.le
            (fun e he' => (hF12 e (hsubD he')).1) (fun e he' => (hF12 e (hsubD he')).2)
  · -- the partner is terminal: integrate it to `N₀(G_w)` (TeX 1558-1562)
    push Not at hsucc
    have hK2 : KernelHyp a dg2 ed G :=
      ⟨fun l hl => hK.meas l (hsubL hl), fun l hl => hK.N0_lt l (hsubL hl),
        fun l hl e he' => hK.N1_lt l (hsubL hl) e (hsubD he'),
        fun l hl e he' => hK.N2_lt l (hsubL hl) e (hsubD he')⟩
    have hpt : ∀ z, ∫⁻ y, J (Function.update z w y) = N0 (G w) * integrand a dg2 ed G z := by
      intro z
      have hrest : ∀ y, J (Function.update z w y) =
          (if dg.predTime z w < y.1 then
              G w (y.1 - dg.predTime z w) (y.2 - dg.predPos z w) else 0) *
          ((∏ l ∈ dg2.labels, vfac dg G z l) * ∏ e ∈ dg2.D, edgeWeight a (ed e) z e) := by
        intro y
        rw [hJfac, vfac_update_self dg G z y hwpred]
        have h1 : ∏ l ∈ dg2.labels, vfac dg G (Function.update z w y) l =
            ∏ l ∈ dg2.labels, vfac dg G z l :=
          Finset.prod_congr rfl fun l hl =>
            vfac_update_of_ne dg G z y (hmem2 l hl).2.1 (hsucc l hl)
        rw [h1]
      rw [show (fun y => J (Function.update z w y)) = _ from funext hrest,
        lintegral_mul_const _ (measurable_shiftKernel (hK.meas w hwL)
          (dg.predTime z w, dg.predPos z w)),
        lintegral_shift_N0 (hK.meas w hwL) (dg.predTime z w, dg.predPos z w), integrand_eq]
      congr 2
      refine Finset.prod_congr rfl fun l hl => vfac_congr z ?_ rfl
      obtain ⟨hlv, hlw, -⟩ := hmem2 l hl
      rw [hdg2, pred_del2 hwf hv hwv hlv hlw, ite_eq_right (hsucc l hl)]
    have hN0 : N0 (G w) ≠ ∞ := (hK.N0_lt w hwL).ne
    have hIJ : (∫⋯∫⁻_L', J ∂fun _ => (volume : Measure (ℝ × Rd d))) 0 =
        N0 (G w) * pairingIntegral a dg2 ed G := by
      rw [hJsplit, pairingIntegral, ← lmarginal_const_mul _ _ hN0]
      congr 1
      exact funext hpt
    have hIH : pairingIntegral a dg2 ed G ≤ env a dg2 ed G := IH dg2 ed G hwf2 hcard2 hcap2 hK2
    calc 2 * regionIntegral a dg ed G R
        ≤ 2 * (N1 a (ed s(w, v)) (G v) * (N0 (G w) * env a dg2 ed G)) := by
          gcongr
          exact stepA.trans (by rw [hIJ]; gcongr)
      _ ≤ env a dg ed G := by
          rw [henv]
          exact envOn_terminal a ed G w v hw2 hv2 hwv he2

end Regional

end StratonovichHAMSecondMoment.PairingRegional
