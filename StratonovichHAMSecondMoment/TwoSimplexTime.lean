module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

The temporal half of the two-chain upper bounds (wave L13 item D3): the time
integrals of the diagram model, as used in the proof of `P:d1-upper` and, by
reference ("the temporal symmetry, cube integral and split count ... do not
involve the spatial dimension"), in the proofs of `P:low-alpha-upper` and
`C:d1-first-calibration`.  Main TeX file
`notes/notes_stratonovich_ham_second_moment.tex` at revision 39f2597a:
* the increments of a time vector in `[0,t]^m_< × [0,t]^{2k-m}_<` sum to at most
  `2t` (lines 5484-5485), and to at most `t` for one chain (line 5845);
* `F_k(s) = Σ_{D ∈ Π_k} ∏_{(i,j) ∈ D} |s_i - s_j|^{-α₀}` is symmetric under every
  permutation of the labels (lines 5488-5493);
* `∫_{[0,t]^2} |s - r|^{-α₀} = Z t^{2-α₀}` and the cube integral of one pairing,
  `(Z t^{2-α₀})^k` (lines 5494-5500, "disjoint endpoints of every pairing");
* `E:d1-time-symmetry` (lines 5501-5508, partition of the cube by the orders
  within each block), proved here as the inequality
  `m! (2k-m)! ∫_{simplices} F_k ≤ ∫_{cube} F_k` (only `≤` is used);
* `P_k = (2k)!/(2^k k!)` and `Σ_{m=0}^{2k} 1/(m!(2k-m)!) = 2^{2k}/(2k)!` (lines
  5509-5518), and the product of counts (lines 5518-5526);
* the scalar series inequality `Σ_k z^k/(k!)^q ≤ exp(q z^{1/q})` (lines
  5540-5545), in partial-sum form.

Everything is stated on `DiagramModel` (registered model choice): `twoSimplex`,
`Pi2`, `timeWeight`, `diagram`, `coeffA`.  The generic diagram bounds
`diagram_le`, `coeffA_le`, `oneChain_le` take a uniform bound `B` on the spatial
part over positive increments with `Σ h ≤ 2t` (resp. `≤ t`) and return
`B` times the exact count factor; the spatial bounds are supplied by the callers
(`LowAlphaUpper`).

Shared module: wave L13 item D2 (`P:d1-upper`, `D1Upper`) had proved its own
versions of these facts in parallel; at the L13 integration they were
deduplicated here, and `D1Upper` imports this module.  The exact pair integral
`lintegral_timeCov_square` (via `TimeSchur`), `sum_inv_factorial_gen` and
`card_Pi2_eq` came from D2.

All proved; nothing supplied.  Lemmas marked "Auxiliary" serve only the Lean
route.  Difference from the TeX: `E:d1-time-symmetry` is an equality in the TeX;
only the inequality `≤` is proved and used (the TeX also uses only `≤`, through
the moment bound).  The pair integral is proved as the TeX's equality
(`pairInt_eq`); the bounds use its `≤` form `pairInt_le`.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.DiagramModel
public import StratonovichHAMSecondMoment.D1Spatial
public import StratonovichHAMSecondMoment.TimeSchur

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Filter Topology Set
open scoped ENNReal Nat

namespace StratonovichHAMSecondMoment.TwoSimplexTime

open HomogHypothesis (Rd)
open DiagramModel
open FiniteWick (pairings mem_pairings)
open D1Spatial (pairing_inv filter_not_closing)

/-! ### The increments sum to at most `2t` -/

/-- Auxiliary to the Lean proof route: a time vector extended by `0` to `ℕ`. -/
def ext0 {N : ℕ} (s : Fin N → ℝ) (i : ℕ) : ℝ := if h : i < N then s ⟨i, h⟩ else 0

/-- Auxiliary to the Lean proof route: the increment in `ℕ`-indexed form. -/
theorem incr_eq_ext0 (m : ℕ) {N : ℕ} (s : Fin N → ℝ) (i : Fin N) :
    incr m s i =
      ext0 s i - (if (i : ℕ) = 0 ∨ (i : ℕ) = m then 0 else ext0 s ((i : ℕ) - 1)) := by
  unfold incr predVal pred
  split_ifs with h
  · simp [ext0, i.isLt]
  · simp [ext0, i.isLt, show (i : ℕ) - 1 < N by omega]

/-- The sum of the increments telescopes in each chain to the chain's last time
(`0` for an empty chain): main TeX lines 5484-5485, "the increments sum to the
two terminal times". -/
theorem sum_incr (m n : ℕ) (s : Fin (m + n) → ℝ) :
    ∑ i, incr m s i =
      (if m = 0 then 0 else ext0 s (m - 1)) + (if n = 0 then 0 else ext0 s (m + n - 1)) := by
  let F : ℕ → ℝ := fun j => ext0 s j - (if j = 0 ∨ j = m then 0 else ext0 s (j - 1))
  have h1 : (∑ i, incr m s i) = ∑ i : Fin (m + n), F (i : ℕ) :=
    Finset.sum_congr rfl fun i _ => incr_eq_ext0 m s i
  rw [h1, Fin.sum_univ_eq_sum_range F (m + n), Finset.sum_range_add]
  congr 1
  · let g : ℕ → ℝ := fun j => if j = 0 then 0 else ext0 s (j - 1)
    have hg : ∀ j ∈ Finset.range m,
        ext0 s j - (if j = 0 ∨ j = m then 0 else ext0 s (j - 1)) = g (j + 1) - g j := by
      intro j hj
      rw [Finset.mem_range] at hj
      simp only [g]
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · simp
      · simp [show j ≠ 0 by omega, show j ≠ m by omega]
    rw [Finset.sum_congr rfl hg, Finset.sum_range_sub]
    simp [g]
  · let g : ℕ → ℝ := fun j => if j = 0 then 0 else ext0 s (m + j - 1)
    have hg : ∀ j ∈ Finset.range n,
        ext0 s (m + j) - (if m + j = 0 ∨ m + j = m then 0 else ext0 s (m + j - 1)) =
          g (j + 1) - g j := by
      intro j _
      simp only [g]
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · simp
      · simp [show j ≠ 0 by omega,
          show m + (j + 1) - 1 = m + j by omega]
    rw [Finset.sum_congr rfl hg, Finset.sum_range_sub]
    simp [g]

/-- Auxiliary to the Lean proof route. -/
theorem ext0_le {N : ℕ} {s : Fin N → ℝ} {t : ℝ} (ht : 0 ≤ t) (hs : ∀ i, s i < t) (j : ℕ) :
    ext0 s j ≤ t := by
  unfold ext0; split_ifs
  · exact (hs _).le
  · exact ht

/-- **The increments of a time vector in `[0,t]^m_< × [0,t]^n_<` sum to at most
`2t`** (main TeX lines 5484-5485). -/
theorem sum_incr_le {m n : ℕ} {t : ℝ} (ht : 0 ≤ t) {s : Fin (m + n) → ℝ}
    (hs : s ∈ twoSimplex m n t) : ∑ i, incr m s i ≤ 2 * t := by
  rw [sum_incr]
  have h := ext0_le ht fun i => (hs i).2
  have h1 : (if m = 0 then 0 else ext0 s (m - 1)) ≤ t := by split_ifs; exacts [ht, h _]
  have h2 : (if n = 0 then 0 else ext0 s (m + n - 1)) ≤ t := by split_ifs; exacts [ht, h _]
  linarith

/-- **One chain: the increments sum to at most `t`** (main TeX line 5845, "for one
chain of length `2k`, the increments sum to at most `t`"). -/
theorem sum_incr_le_one {m : ℕ} {t : ℝ} (ht : 0 ≤ t) {s : Fin (m + 0) → ℝ}
    (hs : s ∈ twoSimplex m 0 t) : ∑ i, incr m s i ≤ t := by
  rw [sum_incr]
  have h := ext0_le ht fun i => (hs i).2
  have h1 : (if m = 0 then 0 else ext0 s (m - 1)) ≤ t := by split_ifs; exacts [ht, h _]
  simpa using h1

/-! ### Full symmetry of the pairing sum `F_k` -/

/-- Auxiliary to the Lean proof route: for a fixed-point-free involution `D` and a
symmetric `g`, the square of the product over the openers is the product over all
labels. -/
theorem prod_openers_sq {N : ℕ} {D : Fin N → Fin N} (hD : ∀ i, D i ≠ i ∧ D (D i) = i)
    (g : Fin N → Fin N → ℝ≥0∞) (hg : ∀ i j, g i j = g j i) :
    (∏ i ∈ openers D, g i (D i)) ^ 2 = ∏ i, g i (D i) := by
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => D i < i),
    filter_not_closing (fun i => (hD i).1)]
  have hC : ∏ i ∈ Finset.univ.filter (fun i => D i < i), g i (D i) =
      ∏ i ∈ openers D, g i (D i) := by
    refine Finset.prod_nbij' D D ?_ ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, openers] at hi ⊢
      rw [(hD i).2]; exact hi
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, openers] at hi ⊢
      rw [(hD i).2]; exact hi
    · intro i _; exact (hD i).2
    · intro i _; exact (hD i).2
    · intro i _; rw [(hD i).2]; exact hg _ _
  rw [hC, sq]

/-- Auxiliary to the Lean proof route. -/
theorem eq_of_sq_eq {a b : ℝ≥0∞} (h : a ^ 2 = b ^ 2) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd h (ENNReal.pow_lt_pow_left two_ne_zero hab).ne
  · exact hab
  · exact absurd h (ENNReal.pow_lt_pow_left two_ne_zero hab).ne'

/-- Relabelling a pairing by a permutation `σ` gives a pairing, `σ D σ⁻¹`. -/
theorem conj_mem {N : ℕ} {D : Fin N → Fin N}
    (hD : D ∈ pairings (Finset.univ : Finset (Fin N))) (σ : Equiv.Perm (Fin N)) :
    (σ ∘ D ∘ σ.symm) ∈ pairings (Finset.univ : Finset (Fin N)) := by
  rw [mem_pairings]
  refine ⟨fun x _ => ⟨Finset.mem_univ _, ?_, ?_⟩, fun x hx => absurd (Finset.mem_univ x) hx⟩
  · intro h
    apply (pairing_inv hD (σ.symm x)).1
    have := congrArg σ.symm h
    simpa using this
  · simp [Function.comp, (pairing_inv hD _).2]

/-- `timeWeight` under relabelling: `w_D(s ∘ σ) = w_{σ D σ⁻¹}(s)`. -/
theorem timeWeight_comp_perm {N : ℕ} {D : Fin N → Fin N}
    (hD : D ∈ pairings (Finset.univ : Finset (Fin N))) (σ : Equiv.Perm (Fin N)) (α₀ : ℝ)
    (s : Fin N → ℝ) : timeWeight α₀ D (s ∘ σ) = timeWeight α₀ (σ ∘ D ∘ σ.symm) s := by
  have hD' := conj_mem hD σ
  have hsym : ∀ a b : ℝ, timeCov α₀ a b = timeCov α₀ b a := fun a b => by
    unfold timeCov; rw [abs_sub_comm]
  apply eq_of_sq_eq
  unfold timeWeight
  rw [prod_openers_sq (pairing_inv hD) (fun i j => timeCov α₀ ((s ∘ σ) i) ((s ∘ σ) j))
      (fun i j => hsym _ _),
    prod_openers_sq (pairing_inv hD') (fun i j => timeCov α₀ (s i) (s j)) (fun i j => hsym _ _),
    ← Equiv.prod_comp σ (fun i => timeCov α₀ (s i) (s ((σ ∘ D ∘ σ.symm) i)))]
  simp

/-- **`F_k` is fully symmetric** (main TeX lines 5492-5493, "every permutation of
the `2k` labels bijects `Π_k`"): `Σ_D w_D(s ∘ σ) = Σ_D w_D(s)` for every
permutation `σ` of the labels. -/
theorem sum_timeWeight_comp_perm {N : ℕ} (σ : Equiv.Perm (Fin N)) (α₀ : ℝ)
    (s : Fin N → ℝ) :
    ∑ D ∈ pairings (Finset.univ : Finset (Fin N)), timeWeight α₀ D (s ∘ σ) =
      ∑ D ∈ pairings (Finset.univ : Finset (Fin N)), timeWeight α₀ D s := by
  refine Finset.sum_nbij' (fun D => σ ∘ D ∘ σ.symm) (fun D => σ.symm ∘ D ∘ σ) ?_ ?_ ?_ ?_ ?_
  · intro D hD; exact conj_mem hD σ
  · intro D hD; simpa using conj_mem hD σ.symm
  · intro D _; funext x; simp
  · intro D _; funext x; simp
  · intro D hD; exact timeWeight_comp_perm hD σ α₀ s

/-! ### Symmetrization over the cube -/

/-- Auxiliary to the Lean proof route: `s ↦ s ∘ σ` is `piCongrLeft σ⁻¹`. -/
theorem comp_perm_eq {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    (fun s : Fin N → ℝ => s ∘ σ) = ⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin N => ℝ) σ.symm) := by
  funext s i
  show s (σ i) = (Equiv.piCongrLeft (fun _ : Fin N => ℝ) σ.symm) s i
  conv_rhs => rw [← σ.symm_apply_apply i]
  rw [Equiv.piCongrLeft_apply_apply]

/-- Auxiliary to the Lean proof route: relabelling the times preserves Lebesgue
measure. -/
theorem measurePreserving_comp_perm {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    MeasurePreserving (fun s : Fin N → ℝ => s ∘ σ) volume volume := by
  rw [comp_perm_eq]
  exact volume_measurePreserving_piCongrLeft (fun _ : Fin N => ℝ) σ.symm

/-- **The symmetrization step** (main TeX lines 5500-5506), general form: if `F`
is invariant under a family `G` of relabellings, the relabelled copies of `S`
are pairwise disjoint and lie in `C`, then `#G ∫_S F ≤ ∫_C F`. -/
theorem card_mul_setLIntegral_le {N : ℕ} {S C : Set (Fin N → ℝ)} (hS : MeasurableSet S)
    {F : (Fin N → ℝ) → ℝ≥0∞} (G : Finset (Equiv.Perm (Fin N)))
    (hinv : ∀ σ ∈ G, ∀ s, F (s ∘ σ) = F s)
    (hdisj : ∀ σ ∈ G, ∀ τ ∈ G, ∀ s, s ∘ σ ∈ S → s ∘ τ ∈ S → σ = τ)
    (hsub : ∀ σ ∈ G, ∀ s, s ∘ σ ∈ S → s ∈ C) :
    (G.card : ℝ≥0∞) * ∫⁻ s in S, F s ≤ ∫⁻ s in C, F s := by
  classical
  let P : Equiv.Perm (Fin N) → Set (Fin N → ℝ) := fun σ => (fun s => s ∘ σ) ⁻¹' S
  have hPm : ∀ σ, MeasurableSet (P σ) := fun σ => (measurePreserving_comp_perm σ).measurable hS
  have hP : ∀ σ ∈ G, ∫⁻ s in P σ, F s = ∫⁻ s in S, F s := by
    intro σ hσ
    have hemb : MeasurableEmbedding (fun s : Fin N → ℝ => s ∘ σ) := by
      rw [comp_perm_eq]; exact MeasurableEquiv.measurableEmbedding _
    rw [← (measurePreserving_comp_perm σ).setLIntegral_comp_preimage_emb hemb F S]
    simp only [P, hinv σ hσ]
  have hdis : (G : Set (Equiv.Perm (Fin N))).PairwiseDisjoint P := by
    intro σ hσ τ hτ hne
    rw [Function.onFun, Set.disjoint_left]
    intro s h1 h2
    exact hne (hdisj σ hσ τ hτ s h1 h2)
  have hU : (⋃ σ ∈ G, P σ) ⊆ C := by
    intro s hs
    simp only [Set.mem_iUnion] at hs
    obtain ⟨σ, hσ, h⟩ := hs
    exact hsub σ hσ s h
  calc (G.card : ℝ≥0∞) * ∫⁻ s in S, F s = ∑ σ ∈ G, ∫⁻ s in P σ, F s := by
        rw [Finset.sum_congr rfl hP, Finset.sum_const, nsmul_eq_mul]
    _ = ∫⁻ s in ⋃ σ ∈ G, P σ, F s := (lintegral_biUnion_finset hdis (fun σ _ => hPm σ) F).symm
    _ ≤ ∫⁻ s in C, F s := lintegral_mono_set hU

/-! ### The relabellings that preserve each chain -/

/-- The relabelling of the two chains by a permutation of each. -/
def chainPerm (m n : ℕ) (p : Equiv.Perm (Fin m) × Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (m + n)) :=
  finSumFinEquiv.permCongr (Equiv.sumCongr p.1 p.2)

/-- The `m! n!` chain-preserving relabellings. -/
def chainPerms (m n : ℕ) : Finset (Equiv.Perm (Fin (m + n))) :=
  Finset.univ.image (chainPerm m n)

/-- Auxiliary to the Lean proof route. -/
theorem chainPerm_injective (m n : ℕ) : Function.Injective (chainPerm m n) := by
  intro p q h
  have h2 : Equiv.sumCongr p.1 p.2 = Equiv.sumCongr q.1 q.2 :=
    (Equiv.permCongr finSumFinEquiv).injective h
  refine Prod.ext (Equiv.ext fun i => ?_) (Equiv.ext fun j => ?_)
  · have := congrArg (fun e => e (Sum.inl i)) h2
    simpa using this
  · have := congrArg (fun e => e (Sum.inr j)) h2
    simpa using this

/-- There are `m! n!` chain-preserving relabellings. -/
theorem card_chainPerms (m n : ℕ) : (chainPerms m n).card = m ! * n ! := by
  rw [chainPerms, Finset.card_image_of_injective _ (chainPerm_injective m n), Finset.card_univ,
    Fintype.card_prod, Fintype.card_perm, Fintype.card_perm, Fintype.card_fin, Fintype.card_fin]

/-- A chain-preserving relabelling keeps every label in its chain. -/
theorem sameChain_chainPerm (m n : ℕ) (p : Equiv.Perm (Fin m) × Equiv.Perm (Fin n))
    (i : Fin (m + n)) : SameChain m (chainPerm m n p i) i := by
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective i
  unfold SameChain chainPerm
  rcases x with j | j
  · simp [Equiv.permCongr_apply]
  · simp [Equiv.permCongr_apply]

/-- Auxiliary to the Lean proof route. -/
theorem sameChain_symm {m N : ℕ} {i j : Fin N} (h : SameChain m i j) : SameChain m j i :=
  h.symm

/-- Auxiliary to the Lean proof route. -/
theorem sameChain_trans {m N : ℕ} {i j l : Fin N} (h1 : SameChain m i j)
    (h2 : SameChain m j l) : SameChain m i l :=
  h1.trans h2

/-- In the time simplices the times increase along each chain. -/
theorem lt_of_mem_twoSimplex {m n : ℕ} {t : ℝ} {s : Fin (m + n) → ℝ}
    (hs : s ∈ twoSimplex m n t) : ∀ (k : ℕ) (i j : Fin (m + n)), (j : ℕ) = i + k + 1 →
      SameChain m i j → s i < s j := by
  intro k
  induction k with
  | zero =>
    intro i j hj hc
    unfold SameChain at hc
    exact ((mem_twoSimplex_iff s).1 hs).2 i j (by omega) (by intro h; rw [h] at hj; omega)
  | succ k ih =>
    intro i j hj hc
    unfold SameChain at hc
    let j' : Fin (m + n) := ⟨i + k + 1, by omega⟩
    have hc' : SameChain m i j' := by
      unfold SameChain; simp only [j']; constructor <;> intro h <;> omega
    have h1 := ih i j' rfl hc'
    have h2 := ((mem_twoSimplex_iff s).1 hs).2 j' j (by simp only [j']; omega)
      (by intro h; rw [h] at hj; omega)
    exact h1.trans h2

/-- Auxiliary to the Lean proof route: strict increase along each chain. -/
theorem chainMono_of_mem {m n : ℕ} {t : ℝ} {s : Fin (m + n) → ℝ}
    (hs : s ∈ twoSimplex m n t) (i j : Fin (m + n)) (hc : SameChain m i j) (hij : i < j) :
    s i < s j :=
  lt_of_mem_twoSimplex hs ((j : ℕ) - i - 1) i j (by have : (i : ℕ) < j := hij; omega) hc

/-- Auxiliary to the Lean proof route: a chain-preserving permutation that keeps
a chainwise strictly increasing function chainwise strictly increasing is the
identity. -/
theorem perm_eq_one_of_chain {N m : ℕ} (f : Fin N → ℝ) (π : Equiv.Perm (Fin N))
    (hπ : ∀ i, SameChain m (π i) i)
    (hf : ∀ i j, SameChain m i j → i < j → f i < f j)
    (hfπ : ∀ i j, SameChain m i j → i < j → f (π i) < f (π j)) : π = 1 := by
  have hmono : ∀ i j, SameChain m i j → i < j → π i < π j := by
    intro i j hc hij
    by_contra hcon
    rcases (not_lt.1 hcon).lt_or_eq with h | h
    · have hc' : SameChain m (π j) (π i) :=
        sameChain_trans (hπ j) (sameChain_trans (sameChain_symm hc) (sameChain_symm (hπ i)))
      exact absurd (hf _ _ hc' h) (not_lt.2 (hfπ i j hc hij).le)
    · exact hij.ne (π.injective h.symm)
  have key : ∀ (v : ℕ) (i : Fin N), (i : ℕ) = v → π i = i := by
    intro v
    induction v using Nat.strong_induction_on with
    | _ v ih =>
      intro i hi
      have hge : ¬ π i < i := by
        intro h
        have := ih (π i) (by rw [← hi]; exact h) (π i) rfl
        exact h.ne (π.injective this)
      have hge' : ¬ π.symm i < i := by
        intro h
        have := ih (π.symm i) (by rw [← hi]; exact h) (π.symm i) rfl
        rw [Equiv.apply_symm_apply] at this
        exact h.ne this.symm
      rcases (not_lt.1 hge').lt_or_eq with h | h
      · have hc : SameChain m i (π.symm i) := by
          have := hπ (π.symm i); rwa [Equiv.apply_symm_apply] at this
        have := hmono i (π.symm i) hc h
        rw [Equiv.apply_symm_apply] at this
        exact absurd this hge
      · calc π i = π (π.symm i) := by rw [← h]
          _ = i := π.apply_symm_apply i
  exact Equiv.ext fun i => key i i rfl

/-- The chain-preserving relabellings of the simplices are disjoint. -/
theorem chainPerms_disjoint {m n : ℕ} {t : ℝ} (σ τ : Equiv.Perm (Fin (m + n)))
    (hσ : σ ∈ chainPerms m n) (hτ : τ ∈ chainPerms m n) (s : Fin (m + n) → ℝ)
    (h1 : s ∘ σ ∈ twoSimplex m n t) (h2 : s ∘ τ ∈ twoSimplex m n t) : σ = τ := by
  obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hσ
  obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hτ
  set σ := chainPerm m n p
  set τ := chainPerm m n q
  have hπ : ∀ i, SameChain m ((τ.symm * σ) i) i := by
    intro i
    have h3 : SameChain m (τ.symm (σ i)) (σ i) := by
      have := sameChain_chainPerm m n q (τ.symm (σ i))
      rw [show chainPerm m n q (τ.symm (σ i)) = σ i from τ.apply_symm_apply _] at this
      exact sameChain_symm this
    exact sameChain_trans h3 (sameChain_chainPerm m n p i)
  have h := perm_eq_one_of_chain (s ∘ τ) (τ.symm * σ) hπ (chainMono_of_mem h2)
    (by
      intro i j hc hij
      have := chainMono_of_mem h1 i j hc hij
      simpa using this)
  refine Equiv.ext fun i => ?_
  have := congrArg (fun π : Equiv.Perm (Fin (m + n)) => τ (π i)) h
  simpa using this

/-- The open time cube `(0,t)^N`. -/
def cube (N : ℕ) (t : ℝ) : Set (Fin N → ℝ) := Set.univ.pi fun _ => Ioo (0 : ℝ) t

/-- **`E:d1-time-symmetry` as an inequality** (main TeX lines 5500-5508): for the
pairing sum `F_k = Σ_D w_D`,
`m! n! ∫_{[0,t]^m_< × [0,t]^n_<} F_k ≤ ∫_{(0,t)^{m+n}} F_k`. -/
theorem factorial_mul_twoSimplex_le (m n : ℕ) (t α₀ : ℝ) :
    ((m ! * n ! : ℕ) : ℝ≥0∞) * ∫⁻ s in twoSimplex m n t, ∑ D ∈ Pi2 m n, timeWeight α₀ D s ≤
      ∫⁻ s in cube (m + n) t, ∑ D ∈ Pi2 m n, timeWeight α₀ D s := by
  rw [← card_chainPerms]
  refine card_mul_setLIntegral_le (measurableSet_twoSimplex m n t) _
    (fun σ _ s => sum_timeWeight_comp_perm σ α₀ s)
    (fun σ hσ τ hτ s h1 h2 => chainPerms_disjoint σ τ hσ hτ s h1 h2) ?_
  intro σ _ s hs j _
  have h := (pos_of_mem_twoSimplex hs (σ.symm j))
  have h' := (hs (σ.symm j)).2
  simp only [Function.comp, Equiv.apply_symm_apply] at h h'
  exact ⟨h, h'⟩

/-! ### The cube integral of one pairing -/

/-- Auxiliary to the Lean proof route: `∫ ∏_j f(y_j) dμ^{⊗k} = (∫ f dμ)^k`. -/
theorem lintegral_pi_prod {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    {f : α → ℝ≥0∞} (hf : Measurable f) : ∀ k : ℕ,
    ∫⁻ y, ∏ j, f (y j) ∂(Measure.pi fun _ : Fin k => μ) = (∫⁻ x, f x ∂μ) ^ k
  | 0 => by
    rw [Measure.pi_of_empty (x := fun i => i.elim0)]
    simp
  | k + 1 => by
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => μ) 0
    have h1 : ∀ y : Fin (k + 1) → α, ∏ j, f (y j) =
        (fun p : α × (Fin k → α) => f p.1 * ∏ j, f (p.2 j))
          (MeasurableEquiv.piFinSuccAbove (fun _ => α) 0 y) := by
      intro y
      rw [Fin.prod_univ_succ]
      rfl
    rw [lintegral_congr fun y => h1 y,
      hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)
        (fun p : α × (Fin k → α) => f p.1 * ∏ j, f (p.2 j))]
    rw [lintegral_prod_mul (g := fun v : Fin k → α => ∏ j, f (v j)) hf.aemeasurable
      (Finset.measurable_prod _ fun j _ => hf.comp (measurable_pi_apply j)).aemeasurable,
      lintegral_pi_prod μ hf k, pow_succ']

/-- The pair integral `∫_{(0,t)^2} |s - r|^{-α₀} ds dr`. -/
def pairInt (α₀ t : ℝ) : ℝ≥0∞ :=
  ∫⁻ p : ℝ × ℝ, timeCov α₀ p.1 p.2 ∂((volume.restrict (Ioo 0 t)).prod (volume.restrict (Ioo 0 t)))

/-- Auxiliary to the Lean proof route: a pairing of `2k` labels as
`Fin k ⊕ Fin k ≃ Fin N` (`inl j`: the `j`-th opener; `inr j`: its partner). -/
def pairEquiv {N k : ℕ} {D : Fin N → Fin N} (hD : D ∈ pairings (Finset.univ : Finset (Fin N)))
    (hN : N = 2 * k) : Fin k ⊕ Fin k ≃ Fin N :=
  Equiv.ofBijective
    (Sum.elim (fun j => ((openers D).orderIsoOfFin (card_openers hD hN) j : Fin N))
      (fun j => D ((openers D).orderIsoOfFin (card_openers hD hN) j)))
    (by
      set o := (openers D).orderIsoOfFin (card_openers hD hN)
      have hinv := pairing_inv hD
      have ho : ∀ j, (o j : Fin N) < D (o j) := fun j => by
        exact (Finset.mem_filter.1 (o j).2).2
      have hoi : Function.Injective fun j => (o j : Fin N) :=
        Subtype.val_injective.comp o.injective
      refine (Fintype.bijective_iff_injective_and_card _).2 ⟨?_, ?_⟩
      · refine Function.Injective.sumElim hoi ?_ ?_
        · intro a b h
          apply hoi
          have := congrArg D h
          simpa [(hinv _).2] using this
        · intro a b h
          have h1 := ho a
          rw [h, (hinv _).2] at h1
          exact absurd (h1.trans (ho b)) (lt_irrefl _)
      · simp [hN]; ring)

/-- **The cube integral of one pairing** (main TeX lines 5497-5500, "the
disjoint endpoints of every pairing"): `∫_{(0,t)^{2k}} w_D = (∫_{(0,t)^2}
|s - r|^{-α₀})^k`. -/
theorem lintegral_cube_timeWeight {N k : ℕ} {D : Fin N → Fin N}
    (hD : D ∈ pairings (Finset.univ : Finset (Fin N))) (hN : N = 2 * k) (α₀ t : ℝ) :
    ∫⁻ s in cube N t, timeWeight α₀ D s = pairInt α₀ t ^ k := by
  set ν := volume.restrict (Ioo (0 : ℝ) t)
  set o := (openers D).orderIsoOfFin (card_openers hD hN)
  set e := pairEquiv hD hN
  have hvol : (volume : Measure (Fin N → ℝ)).restrict (cube N t) = Measure.pi fun _ => ν := by
    rw [cube, volume_pi, Measure.restrict_pi_pi]
  rw [hvol]
  have hmp := measurePreserving_piCongrLeft (fun _ : Fin N => ν) e
  rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  have h2 : ∀ x : Fin k ⊕ Fin k → ℝ,
      timeWeight α₀ D (MeasurableEquiv.piCongrLeft (fun _ => ℝ) e x) =
        ∏ j : Fin k, timeCov α₀ (x (Sum.inl j)) (x (Sum.inr j)) := by
    intro x
    unfold timeWeight
    rw [← Finset.prod_coe_sort (openers D), ← o.toEquiv.prod_comp]
    refine Finset.prod_congr rfl fun j _ => ?_
    have he1 : e (Sum.inl j) = o j := rfl
    have he2 : e (Sum.inr j) = D (o j) := rfl
    have h3 := Equiv.piCongrLeft_apply_apply (fun _ : Fin N => ℝ) e x (Sum.inl j)
    have h4 := Equiv.piCongrLeft_apply_apply (fun _ : Fin N => ℝ) e x (Sum.inr j)
    rw [he1] at h3
    rw [he2] at h4
    show timeCov α₀ ((Equiv.piCongrLeft (fun _ : Fin N => ℝ) e) x (o j))
      ((Equiv.piCongrLeft (fun _ : Fin N => ℝ) e) x (D (o j))) = _
    rw [h3, h4]
  simp_rw [h2]
  have hmp2 := measurePreserving_sumPiEquivProdPi (fun _ : Fin k ⊕ Fin k => ν)
  have h5 : ∀ x : Fin k ⊕ Fin k → ℝ, ∏ j : Fin k, timeCov α₀ (x (Sum.inl j)) (x (Sum.inr j)) =
      (fun p : (Fin k → ℝ) × (Fin k → ℝ) => ∏ j, timeCov α₀ (p.1 j) (p.2 j))
        (MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ) x) := fun x => rfl
  rw [lintegral_congr fun x => h5 x,
    hmp2.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)
      (fun p : (Fin k → ℝ) × (Fin k → ℝ) => ∏ j, timeCov α₀ (p.1 j) (p.2 j))]
  have hmp3 := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin k) (fun _ => ν) (fun _ => ν)
  rw [← hmp3.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)
      (fun p : (Fin k → ℝ) × (Fin k → ℝ) => ∏ j, timeCov α₀ (p.1 j) (p.2 j))]
  exact lintegral_pi_prod (ν.prod ν) (measurable_timeCov α₀) k

/-! ### The pair integral -/

/-- `Z = 2/((1-α₀)(2-α₀))` of `E:d1-constants` (main TeX line 5325). -/
def Zc (α₀ : ℝ) : ℝ := 2 / ((1 - α₀) * (2 - α₀))

/-- `0 < Z` for `α₀ < 1`. -/
theorem Zc_pos {α₀ : ℝ} (hα1 : α₀ < 1) : 0 < Zc α₀ := by
  unfold Zc
  have h1 : 0 < 1 - α₀ := by linarith
  have h2 : 0 < 2 - α₀ := by linarith
  positivity

/-- Auxiliary to the Lean proof route:
`∫_0^t (x^{1-a} + (t-x)^{1-a})/(1-a) dx = Z t^{2-a}`, with integrability. -/
theorem integral_row_sum {a t : ℝ} (ha1 : a < 1) (ht : 0 ≤ t) :
    IntegrableOn (fun x : ℝ => (x ^ (1 - a) + (t - x) ^ (1 - a)) / (1 - a)) (Icc 0 t) ∧
      ∫ x in Icc 0 t, (x ^ (1 - a) + (t - x) ^ (1 - a)) / (1 - a) = Zc a * t ^ (2 - a) := by
  have hr : -1 < 1 - a := by linarith
  have h1 : IntervalIntegrable (fun x : ℝ => x ^ (1 - a)) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' hr
  have h2 : IntervalIntegrable (fun x : ℝ => (t - x) ^ (1 - a)) volume 0 t := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := t - t) (b := t - 0) hr).comp_sub_left t
    simpa using this.symm
  have h12 := (h1.add h2).div_const (1 - a)
  refine ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le ht).1 h12, ?_⟩
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht,
    intervalIntegral.integral_div, intervalIntegral.integral_add h1 h2,
    intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (1 - a)) t, sub_self, sub_zero,
    integral_rpow (Or.inl hr), Real.zero_rpow (ne_of_gt (by linarith)), sub_zero]
  have e : 1 - a + 1 = 2 - a := by ring
  rw [e, Zc]
  have h2a : (2 - a) ≠ 0 := by linarith
  have h1a : (1 - a) ≠ 0 := by linarith
  field_simp
  ring

/-- **The pair integral** (main TeX line 5496):
`∫_{[0,t]²} |s-r|^{-α₀} ds dr = Z t^{2-α₀}`, `Z = 2/((1-α₀)(2-α₀))`, for `α₀ < 1`
(the `ℝ≥0∞` kernel, `∞` on the null diagonal). -/
theorem lintegral_timeCov_square {a t : ℝ} (ha1 : a < 1) (ht : 0 ≤ t) :
    ∫⁻ p, timeCov a p.1 p.2 ∂((volume.restrict (Icc 0 t)).prod (volume.restrict (Icc 0 t))) =
      ENNReal.ofReal (Zc a * t ^ (2 - a)) := by
  rw [lintegral_prod _ (measurable_timeCov a).aemeasurable]
  have hrow : ∀ x ∈ Icc 0 t, ∫⁻ y in Icc 0 t, timeCov a x y =
      ENNReal.ofReal ((x ^ (1 - a) + (t - x) ^ (1 - a)) / (1 - a)) := by
    intro x hx
    obtain ⟨hi, he⟩ := TimeSchur.integral_row ha1 hx
    rw [← he, ofReal_integral_eq_lintegral_ofReal hi
      (ae_of_all _ fun s => TimeSchur.kern_nonneg _ _)]
    refine lintegral_congr_ae ?_
    have hne : ∀ᵐ y ∂(volume.restrict (Icc (0 : ℝ) t)), y ≠ x := by
      refine ae_restrict_of_ae ?_
      rw [ae_iff]
      simp
    filter_upwards [hne] with y hy
    simp only [timeCov, TimeSchur.kern]
    exact ENNReal.ofReal_rpow_of_pos (abs_pos.2 (sub_ne_zero.2 hy.symm))
  dsimp only
  rw [setLIntegral_congr_fun measurableSet_Icc hrow]
  obtain ⟨hi, he⟩ := integral_row_sum ha1 ht
  rw [← he, ofReal_integral_eq_lintegral_ofReal hi]
  refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun x hx => ?_)
  have h1a : 0 < 1 - a := by linarith
  exact div_nonneg (add_nonneg (Real.rpow_nonneg hx.1 _)
    (Real.rpow_nonneg (sub_nonneg.2 hx.2) _)) h1a.le

/-- **The pair integral, exact** (main TeX lines 5494-5497):
`∫_{(0,t)^2} |s - r|^{-α₀} ds dr = Z t^{2-α₀}` for `α₀ < 1`, `t ≥ 0`. -/
theorem pairInt_eq {α₀ t : ℝ} (hα1 : α₀ < 1) (ht : 0 ≤ t) :
    pairInt α₀ t = ENNReal.ofReal (Zc α₀ * t ^ (2 - α₀)) := by
  unfold pairInt
  rw [Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := t))]
  exact lintegral_timeCov_square hα1 ht

/-- **`∫_{[0,t]^2} |s - r|^{-α₀} ds dr ≤ Z t^{2-α₀}`** (main TeX lines 5494-5497;
the inequality form used by the bounds, from `pairInt_eq`). -/
theorem pairInt_le {α₀ t : ℝ} (hα1 : α₀ < 1) (ht : 0 ≤ t) :
    pairInt α₀ t ≤ ENNReal.ofReal (Zc α₀ * t ^ (2 - α₀)) :=
  (pairInt_eq hα1 ht).le

/-! ### Counting -/

/-- Auxiliary to the Lean proof route: from `a x ≤ b` with a positive integer
`a` to `x ≤ b/a`. -/
theorem le_ofReal_div {x : ℝ≥0∞} {a : ℕ} (ha : 0 < a) {b : ℝ}
    (h : (a : ℝ≥0∞) * x ≤ ENNReal.ofReal b) : x ≤ ENNReal.ofReal (b / a) := by
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast ha), ENNReal.ofReal_natCast]
  refine (ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast ha.ne'))
    (Or.inl (ENNReal.natCast_ne_top a))).2 ?_
  rwa [mul_comm]

/-- **The split integral** (`E:d1-time-symmetry`, main TeX lines 5500-5508, with
the cube integral of lines 5494-5500): for `m + n = 2k`,
`Σ_{D ∈ Π_k} ∫_{[0,t]^m_< × [0,t]^n_<} w_D ≤ P_k (Z t^{2-α₀})^k/(m! n!)`. -/
theorem split_le {α₀ t : ℝ} (hα1 : α₀ < 1) (ht : 0 ≤ t) {m n k : ℕ} (hmn : m + n = 2 * k) :
    ∑ D ∈ Pi2 m n, ∫⁻ s in twoSimplex m n t, timeWeight α₀ D s ≤
      ENNReal.ofReal ((Pi2 m n).card * (Zc α₀ * t ^ (2 - α₀)) ^ k / (m ! * n ! : ℕ)) := by
  have hZ : 0 ≤ Zc α₀ * t ^ (2 - α₀) :=
    mul_nonneg (Zc_pos hα1).le (Real.rpow_nonneg ht _)
  refine le_ofReal_div (by positivity) ?_
  rw [← lintegral_finsetSum _ fun D _ => (measurable_timeWeight α₀ D)]
  refine (factorial_mul_twoSimplex_le m n t α₀).trans ?_
  rw [lintegral_finsetSum _ fun D _ => (measurable_timeWeight α₀ D)]
  calc ∑ D ∈ Pi2 m n, ∫⁻ s in cube (m + n) t, timeWeight α₀ D s
      = ∑ _D ∈ Pi2 m n, pairInt α₀ t ^ k :=
        Finset.sum_congr rfl fun D hD => lintegral_cube_timeWeight hD hmn α₀ t
    _ ≤ ∑ _D ∈ Pi2 m n, ENNReal.ofReal (Zc α₀ * t ^ (2 - α₀)) ^ k := by
        gcongr; exact pairInt_le hα1 ht
    _ = ENNReal.ofReal ((Pi2 m n).card * (Zc α₀ * t ^ (2 - α₀)) ^ k) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_pow hZ,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]

/-- The binomial identity of main TeX lines 5516-5518, for every `n`:
`Σ_{m=0}^{n} 1/(m!(n-m)!) = 2^n/n!`. -/
theorem sum_inv_factorial_gen (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), (1 : ℝ) / ((m ! : ℝ) * ((n - m) ! : ℝ)) = 2 ^ n / n ! := by
  have h : ∀ m ∈ Finset.range (n + 1),
      (1 : ℝ) / ((m ! : ℝ) * ((n - m) ! : ℝ)) = (n.choose m : ℝ) / n ! := by
    intro m hm
    rw [Nat.cast_choose ℝ (by simp at hm; omega)]
    have h1 : (0 : ℝ) < n ! := by positivity
    have h2 : (0 : ℝ) < m ! := by positivity
    have h3 : (0 : ℝ) < (n - m) ! := by positivity
    field_simp
  rw [Finset.sum_congr rfl h, ← Finset.sum_div, ← Nat.cast_sum, Nat.sum_range_choose]
  push_cast
  ring

/-- The binomial identity of main TeX lines 5516-5518:
`Σ_{m=0}^{2k} 1/(m!(2k-m)!) = 2^{2k}/(2k)!`. -/
theorem sum_inv_factorial (k : ℕ) :
    ∑ m ∈ Finset.range (2 * k + 1), (1 : ℝ) / ((m ! * (2 * k - m) ! : ℕ) : ℝ) =
      2 ^ (2 * k) / ((2 * k) ! : ℝ) := by
  push_cast
  exact sum_inv_factorial_gen (2 * k)

/-- The pairing count `P_k = (2k)!/(2^k k!)` (main TeX lines 5508-5510). -/
theorem card_Pi2_eq {m n k : ℕ} (hmn : m + n = 2 * k) :
    ((Pi2 m n).card : ℝ) = (2 * k)! / (2 ^ k * k !) := by
  have hpos : (0 : ℝ) < 2 ^ k * k ! := by positivity
  rw [eq_div_iff hpos.ne']
  exact_mod_cast card_Pi2_mul hmn

/-- **The product of the counts** (main TeX lines 5509-5526): summed over the
splits `m = 0, …, 2k`, the temporal factors give
`Σ_m Σ_D ∫ w_D ≤ (2 Z t^{2-α₀})^k / k!`. -/
theorem time_total_le {α₀ t : ℝ} (hα1 : α₀ < 1) (ht : 0 ≤ t) (k : ℕ) :
    ∑ m ∈ Finset.range (2 * k + 1), ∑ D ∈ Pi2 m (2 * k - m),
        ∫⁻ s in twoSimplex m (2 * k - m) t, timeWeight α₀ D s ≤
      ENNReal.ofReal ((2 * (Zc α₀ * t ^ (2 - α₀))) ^ k / (k ! : ℝ)) := by
  set z := Zc α₀ * t ^ (2 - α₀)
  have hz : 0 ≤ z := mul_nonneg (Zc_pos hα1).le (Real.rpow_nonneg ht _)
  have hP : ∀ m ∈ Finset.range (2 * k + 1), ((Pi2 m (2 * k - m)).card : ℝ) =
      ((2 * k) ! : ℝ) / (2 ^ k * k ! : ℝ) := by
    intro m hm
    exact card_Pi2_eq (by rw [Finset.mem_range] at hm; omega)
  calc ∑ m ∈ Finset.range (2 * k + 1), ∑ D ∈ Pi2 m (2 * k - m),
        ∫⁻ s in twoSimplex m (2 * k - m) t, timeWeight α₀ D s
      ≤ ∑ m ∈ Finset.range (2 * k + 1), ENNReal.ofReal
          ((Pi2 m (2 * k - m)).card * z ^ k / (m ! * (2 * k - m) ! : ℕ)) :=
        Finset.sum_le_sum fun m hm => split_le hα1 ht
          (by rw [Finset.mem_range] at hm; omega)
    _ = ENNReal.ofReal (∑ m ∈ Finset.range (2 * k + 1),
          (Pi2 m (2 * k - m)).card * z ^ k / (m ! * (2 * k - m) ! : ℕ)) :=
        (ENNReal.ofReal_sum_of_nonneg fun m _ => by positivity).symm
    _ = ENNReal.ofReal ((2 * z) ^ k / (k ! : ℝ)) := by
        congr 1
        have e : ∀ m ∈ Finset.range (2 * k + 1),
            ((Pi2 m (2 * k - m)).card : ℝ) * z ^ k / ((m ! * (2 * k - m) ! : ℕ) : ℝ) =
              ((2 * k) ! : ℝ) / (2 ^ k * k ! : ℝ) * z ^ k *
                ((1 : ℝ) / ((m ! * (2 * k - m) ! : ℕ) : ℝ)) := by
          intro m hm; rw [hP m hm]; ring
        rw [Finset.sum_congr rfl e, ← Finset.mul_sum, sum_inv_factorial, mul_pow,
          pow_mul]
        have : ((2 * k) ! : ℝ) ≠ 0 := by positivity
        field_simp
        rw [show ((2 : ℝ) ^ 2) ^ k = 2 ^ k * 2 ^ k by rw [← mul_pow]; norm_num]
        simp only [z]
        ring

/-! ### Generic diagram bounds -/

/-- A diagram is at most a uniform bound `B` of its spatial part on the time
simplices times its temporal integral (main TeX lines 5485-5487, "extract
`E:d1-spatial-max`, which is independent of the time vector"). -/
theorem diagram_le {d : ℕ} (G : ℝ → Measure (Rd d)) (γ : Rd d → ℝ≥0∞) (α₀ : ℝ) (m n : ℕ)
    (D : Fin (m + n) → Fin (m + n)) (t : ℝ) (B : ℝ≥0∞)
    (hB : ∀ s ∈ twoSimplex m n t, spatial G γ m D (incr m s) ≤ B) :
    diagram G γ α₀ m n D t ≤ B * ∫⁻ s in twoSimplex m n t, timeWeight α₀ D s := by
  unfold diagram
  calc ∫⁻ s in twoSimplex m n t, timeWeight α₀ D s * spatial G γ m D (incr m s)
      ≤ ∫⁻ s in twoSimplex m n t, timeWeight α₀ D s * B :=
        setLIntegral_mono ((measurable_timeWeight α₀ D).mul_const B) fun s hs =>
          by gcongr; exact hB s hs
    _ = B * ∫⁻ s in twoSimplex m n t, timeWeight α₀ D s := by
        rw [lintegral_mul_const _ (measurable_timeWeight α₀ D), mul_comm]

/-- **The coefficient bound from a uniform spatial bound** (main TeX lines
5468-5526; the same multiplication of counts is invoked for every dimension at
lines 5774-5779): if `spatial G γ m D h ≤ B` for every split `m + n = 2k`,
pairing `D`, and positive increments with `Σ h ≤ 2t`, then
`A_k(t) = coeffA G γ α₀ k t ≤ B (2 Z t^{2-α₀})^k / k!`. -/
theorem coeffA_le {d : ℕ} (G : ℝ → Measure (Rd d)) (γ : Rd d → ℝ≥0∞) {α₀ : ℝ}
    (hα1 : α₀ < 1) (k : ℕ) {t : ℝ} (ht : 0 ≤ t) (B : ℝ≥0∞)
    (hB : ∀ m n : ℕ, m + n = 2 * k → ∀ D ∈ Pi2 m n, ∀ h : Fin (m + n) → ℝ, (∀ i, 0 < h i) →
      ∑ i, h i ≤ 2 * t → spatial G γ m D h ≤ B) :
    coeffA G γ α₀ k t ≤ B * ENNReal.ofReal ((2 * (Zc α₀ * t ^ (2 - α₀))) ^ k / (k ! : ℝ)) := by
  unfold coeffA
  calc ∑ m ∈ Finset.range (2 * k + 1), ∑ D ∈ Pi2 m (2 * k - m),
        diagram G γ α₀ m (2 * k - m) D t
      ≤ ∑ m ∈ Finset.range (2 * k + 1), ∑ D ∈ Pi2 m (2 * k - m),
          B * ∫⁻ s in twoSimplex m (2 * k - m) t, timeWeight α₀ D s := by
        refine Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun D hD => ?_
        have hmn : m + (2 * k - m) = 2 * k := by rw [Finset.mem_range] at hm; omega
        exact diagram_le G γ α₀ m _ D t B fun s hs =>
          hB m _ hmn D hD _ (incr_pos hs) (sum_incr_le ht hs)
    _ = B * ∑ m ∈ Finset.range (2 * k + 1), ∑ D ∈ Pi2 m (2 * k - m),
          ∫⁻ s in twoSimplex m (2 * k - m) t, timeWeight α₀ D s := by
        rw [Finset.mul_sum]; simp_rw [Finset.mul_sum]
    _ ≤ _ := by gcongr; exact time_total_le hα1 ht k

/-- **One chain** (proof of `C:d1-first-calibration`, main TeX lines 5845-5852):
if `spatial G γ (2k) D h ≤ B` for every pairing of one chain of length `2k` and
positive increments with `Σ h ≤ t`, then
`Σ_D J_{2k,0,D}(t) ≤ B (Z t^{2-α₀})^k / (2^k k!)` (`= B P_k (Z t^{2-α₀})^k/(2k)!`). -/
theorem oneChain_le {d : ℕ} (G : ℝ → Measure (Rd d)) (γ : Rd d → ℝ≥0∞) {α₀ : ℝ}
    (hα1 : α₀ < 1) (k : ℕ) {t : ℝ} (ht : 0 ≤ t) (B : ℝ≥0∞)
    (hB : ∀ D ∈ Pi2 (2 * k) 0, ∀ h : Fin (2 * k + 0) → ℝ, (∀ i, 0 < h i) →
      ∑ i, h i ≤ t → spatial G γ (2 * k) D h ≤ B) :
    ∑ D ∈ Pi2 (2 * k) 0, diagram G γ α₀ (2 * k) 0 D t ≤
      B * ENNReal.ofReal ((Zc α₀ * t ^ (2 - α₀)) ^ k / (2 ^ k * k ! : ℝ)) := by
  have hmn : 2 * k + 0 = 2 * k := by omega
  calc ∑ D ∈ Pi2 (2 * k) 0, diagram G γ α₀ (2 * k) 0 D t
      ≤ ∑ D ∈ Pi2 (2 * k) 0, B * ∫⁻ s in twoSimplex (2 * k) 0 t, timeWeight α₀ D s :=
        Finset.sum_le_sum fun D hD => diagram_le G γ α₀ _ 0 D t B fun s hs =>
          hB D hD _ (incr_pos hs) (sum_incr_le_one ht hs)
    _ = B * ∑ D ∈ Pi2 (2 * k) 0, ∫⁻ s in twoSimplex (2 * k) 0 t, timeWeight α₀ D s := by
        rw [Finset.mul_sum]
    _ ≤ _ := by
        gcongr
        refine (split_le hα1 ht hmn).trans (le_of_eq ?_)
        congr 1
        rw [card_Pi2_eq hmn]
        have : ((2 * k) ! : ℝ) ≠ 0 := by positivity
        push_cast
        field_simp
        simp

/-! ### The scalar series inequality -/

/-- Auxiliary to the Lean proof route: `Σ x_i^q ≤ (Σ x_i)^q` for `x_i ≥ 0`, `q ≥ 1`. -/
theorem sum_rpow_le_rpow_sum {q : ℝ} (hq : 1 ≤ q) (x : ℕ → ℝ) (hx : ∀ i, 0 ≤ x i) (n : ℕ) :
    ∑ i ∈ Finset.range n, x i ^ q ≤ (∑ i ∈ Finset.range n, x i) ^ q := by
  induction n with
  | zero => simp [Real.zero_rpow (by linarith : q ≠ 0)]
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    exact (add_le_add ih le_rfl).trans
      (Real.add_rpow_le_rpow_add (Finset.sum_nonneg fun i _ => hx i) (hx n) hq)

/-- **The scalar inequality** of main TeX lines 5540-5545, in partial-sum form:
for `z ≥ 0`, `q ≥ 1` and every `n`, `Σ_{k<n} z^k/(k!)^q ≤ exp(q z^{1/q})`. -/
theorem sum_div_factorial_rpow_le {q z : ℝ} (hq : 1 ≤ q) (hz : 0 ≤ z) (n : ℕ) :
    ∑ k ∈ Finset.range n, z ^ k / (k ! : ℝ) ^ q ≤ Real.exp (q * z ^ (1 / q)) := by
  have hq0 : 0 < q := by linarith
  set w := z ^ (1 / q)
  have hw : 0 ≤ w := Real.rpow_nonneg hz _
  have e : ∀ k : ℕ, z ^ k / (k ! : ℝ) ^ q = (w ^ k / (k ! : ℝ)) ^ q := by
    intro k
    rw [Real.div_rpow (pow_nonneg hw _) (by positivity), ← Real.rpow_natCast w,
      ← Real.rpow_mul hw, ← Real.rpow_mul hz, show 1 / q * ((k : ℝ) * q) = k by field_simp,
      Real.rpow_natCast]
  simp_rw [e]
  refine (sum_rpow_le_rpow_sum hq _ (fun k => by positivity) n).trans ?_
  calc (∑ k ∈ Finset.range n, w ^ k / (k ! : ℝ)) ^ q ≤ Real.exp w ^ q :=
        Real.rpow_le_rpow (Finset.sum_nonneg fun k _ => by positivity)
          (Real.sum_le_exp_of_nonneg hw n) hq0.le
    _ = Real.exp (q * w) := by rw [← Real.exp_mul, mul_comm]

end StratonovichHAMSecondMoment.TwoSimplexTime
