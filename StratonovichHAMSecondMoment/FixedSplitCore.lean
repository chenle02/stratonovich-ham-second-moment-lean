module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

The model-free core of `L:fixed-split` (A fixed degree-split estimate) of
`notes/notes_stratonovich_ham_second_moment.tex` (main TeX file; all line
numbers below are at revision 39f2597a): statement lines 3675-3716, proof
3718-4051.  Wave item L10-FS0.

Formalized here (the steps of the proof that do not involve the Gaussian
fields, the Fock spaces or the phase evolution):

* `E:interval-copy-metric` (lines 3809-3837, display 3831-3834):
  `metric_telescoping` is a GENERAL telescoping lemma for any finite family
  of weights whose activity pattern along the cuts is order-convex (each
  color is active on one block of consecutive segments):
  `∏_{j<N} max{1, Λ_j/Λ_{j+1}} ≤ ∏_{i∈A} (1 + ω_i/λ)`.  `interval_copy_metric`
  instantiates it for the intervals `(a_i, b_i)` and a monotone partition
  `τ_0 ≤ ⋯ ≤ τ_M` (heights `Λ_0 = Λ_{M+1} = λ`); `intervalLambda_eq_height`
  identifies `Λ_j` with the value of `Λ(t)` (line 3765) on `(τ_{j-1}, τ_j)`
  when every endpoint in `(τ_0, τ_M)` is a cut; `interval_copy_metric_paper`
  is the TeX form with `ω_i = k_i/h_i`, `λ = k/T` and a strict partition.
* `E:split-segment-product` (lines 3787-3804, display 3792-3801): the
  exponent identity and bound `∑_j Λ_j (τ_j - τ_{j-1}) ≤ 2k`
  (`segSum_eq`, `segSum_le`), `M ≤ 3k + 1` (`partition_count_le`), the
  product `∏ ‖P_j‖ ≤ 100^M exp(2∑) ≤ M_k = 100^{3k+1} e^{4k}`
  (`split_segment_product`, `split_segment_product_paper`) with the segment
  norm bound `‖P_j‖ ≤ 100 e^{2Λ_j(τ_j - τ_{j-1})}` of `L:interval-complex`
  as the premise of the implication, and `M_k² ≤ (100^8 e^8)^k`
  (`Mk_sq_le`, line 4037).
* The radius step after `E:split-radii` (lines 3743-3777):
  `split_radius_sum`, `D(t) ≤ δ Λ(t)^{2-a}` with `a = α/2`, through
  `∑ x_i^q ≤ (∑ x_i)^q` for `q ≥ 1` (`sum_rpow_le_rpow_sum`).
* `E:split-word-product` (lines 3907-3930): `split_word_product` (the norm
  of the chronological word is at most the product of the factor bounds),
  `insertion_product_le` (insertion cuts carry `∏_{i∈𝒞} c_i`, other cuts at
  most one), `split_word_bound` (`≤ M_k D_𝒜 ∏ c_i ‖v‖`).  The word is
  represented by the sequence of norms of its partial products.
* `E:split-vector-cauchy` (lines 3973-3988): `torus_coefficient` is the
  normalized torus extraction for an absolutely convergent multivariate power
  series with values in a complex Banach space, with integrability, and
  `torus_coefficient_norm_le` the resulting Cauchy bound
  `‖c_r‖ ≤ ∏ ϱ_i^{-r_i} sup_torus ‖Φ‖`.  The proof is by orthogonality of
  the exponentials on `[0, 2π]^n` and dominated convergence; no
  multivariable Cauchy integral formula is used (the main risk of the item
  did not materialize: no fallback was needed).
* `E:split-before-absorption` (lines 3997-4020): `split_before_absorption`,
  the scalar product of the two per-copy bounds; the metric product
  `D_{𝒜_r} D_{𝒜_q} = ∏_{i∈ℬ} (1 + k_i/(λh_i))^{ℓ_i}` is `metric_product_eq`,
  and the radius product `∏_{𝒜_r} ϱ_i^{-r_i} ∏_{𝒜_q} ϱ_i^{-q_i} =
  ∏_{ℬ} ϱ_i^{-2k_i}` is proved inside `two_copy_product`.
* `E:split-radius-factorial` (lines 4022-4036): `split_radius_factorial`
  (all three lines of the display) and `split_radius_factorial_paper`.
* `E:split-explicit-constant` (lines 4037-4050): `split_absorption` and
  `split_explicit_constant_paper`: the before-absorption bound implies
  `E:fixed-split-bound` with `C_split = 100^8 e^8 max{1, 12 δ^{-2}}`, in
  exactly the form of the `hfixed` hypothesis of
  `IntervalScalarCompleted.interval_coefficient_assembly_paper_completed`
  (with `Cs = splitConst δ`); `interval_coefficient_of_before_absorption_paper`
  is that step row with `hfixed` replaced by the before-absorption bound.

Not formalized here (they need the Fock layer and are the later item FS1):
the subspaces `𝒵_S`, `E:split-fresh-insertion`, the Dyson cube identity
`E:interval-cross-cube`, `E:interval-cross-vector`, the identification of
`U_r v` with a coefficient of `Φ_𝒜`, the norm comparisons
`‖w‖_{1/T} ≤ k‖w‖_λ`, `‖v‖_λ ≤ ‖v‖_{1/T}`, and Cauchy-Schwarz.  These enter
the statements below only as premises of implications (norm bounds of the
factors of a word, the per-copy bounds, the before-absorption bound); no
named analytic input is introduced.

Constants: `δ > 0` is arbitrary; the TeX uses `δ = δ_{α/2}` of
`L:complex-phase` (lines 2751ff.), which the package does not define.
Narrower or different from the TeX: the copy-metric lemma needs only a
monotone partition (the TeX's is strict); the exponent identity is replaced
by the inequality `∑_{j: i active} (τ_j - τ_{j-1}) ≤ max{0, b_i - a_i}`
(the TeX states equality with `ω_i(b_i - a_i)` for the intersected
intervals); the word product is stated for the norms of the partial words.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.IntervalScalarCompleted

@[expose] public section

noncomputable section

set_option autoImplicit false

open Finset Real MeasureTheory
open scoped Nat

namespace StratonovichHAMSecondMoment.FixedSplitCore

open StratonovichHAMSecondMoment.IntervalScalar

/-! ### The interval metric `E:interval-copy-metric` -/

section CopyMetric

variable {ι : Type*} [DecidableEq ι]

/-- An activity pattern `j ↦ act j` (the set of colors active on segment
`j`) is order-convex if every color is active on a block of consecutive
segments: the combinatorial content of "each connected `I_i^T`" (main TeX
line 3830). -/
def ActivityConvex (act : ℕ → Finset ι) : Prop :=
  ∀ (i : ι) (j₁ j j₂ : ℕ), j₁ ≤ j → j ≤ j₂ → i ∈ act j₁ → i ∈ act j₂ → i ∈ act j

/-- The height `Λ_j = λ + ∑_{i active on segment j} ω_i` (main TeX lines
3765-3766 and 3788). -/
def height (lam : ℝ) (ω : ι → ℝ) (act : ℕ → Finset ι) (j : ℕ) : ℝ := lam + ∑ i ∈ act j, ω i

/-- `D_𝒜 = ∏_{i∈𝒜} (1 + k_i/(λ h_i))` (main TeX lines 3833-3834). -/
def metricD (lam : ℝ) (h : ι → ℝ) (κ : ι → ℕ) (S : Finset ι) : ℝ :=
  ∏ i ∈ S, (1 + κ i / (lam * h i))

omit [DecidableEq ι] in
/-- Auxiliary (Lean route): `1 + ∑ x_i ≤ ∏ (1 + x_i)` for `x_i ≥ 0` (the
last inequality of main TeX lines 3821-3825). -/
theorem one_add_sum_le_prod (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i) :
    1 + ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 + x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hxa := hx a (Finset.mem_insert_self a s)
    have ih' := ih fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have hs : 0 ≤ ∑ i ∈ s, x i :=
      Finset.sum_nonneg fun i hi => hx i (Finset.mem_insert_of_mem hi)
    nlinarith

omit [DecidableEq ι] in
/-- Auxiliary (Lean route): `∏ (1 + x_i) ≥ 1` for `x_i ≥ 0`. -/
theorem one_le_prod_one_add (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i) :
    1 ≤ ∏ i ∈ s, (1 + x i) :=
  Finset.one_le_prod₀ fun i hi => by linarith [hx i hi]

/-- One cut (main TeX lines 3818-3827): for active sets `X` (left of the cut)
and `Y` (right of it), `max{1, Λ_X/Λ_Y} ≤ ∏_{i∈X∖Y} (1 + ω_i/λ)`; the colors
in `X ∖ Y` are those ending at the cut.  Requires `λ > 0` and `ω ≥ 0` on a
set containing `X` and `Y`. -/
theorem cut_ratio_le (lam : ℝ) (hlam : 0 < lam) (ω : ι → ℝ) (A : Finset ι)
    (hω : ∀ i ∈ A, 0 ≤ ω i) (X Y : Finset ι) (hX : X ⊆ A) (hY : Y ⊆ A) :
    max 1 ((lam + ∑ i ∈ X, ω i) / (lam + ∑ i ∈ Y, ω i)) ≤ ∏ i ∈ X \ Y, (1 + ω i / lam) := by
  have hnn : ∀ S ⊆ A, 0 ≤ ∑ i ∈ S, ω i := fun S hS =>
    Finset.sum_nonneg fun i hi => hω i (hS hi)
  have hR := hnn (X ∩ Y) (Finset.inter_subset_left.trans hX)
  have hsplit : ∑ i ∈ X, ω i = ∑ i ∈ X ∩ Y, ω i + ∑ i ∈ X \ Y, ω i :=
    (Finset.sum_inter_add_sum_sdiff X Y ω).symm
  have hYge : ∑ i ∈ X ∩ Y, ω i ≤ ∑ i ∈ Y, ω i :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      fun i hi _ => hω i (hY hi)
  have hden : 0 < lam + ∑ i ∈ Y, ω i := by linarith
  have hx : ∀ i ∈ X \ Y, 0 ≤ ω i / lam := fun i hi =>
    div_nonneg (hω i (hX (Finset.mem_sdiff.1 hi).1)) hlam.le
  have hprod := one_add_sum_le_prod (X \ Y) (fun i => ω i / lam) hx
  have hge1 := one_le_prod_one_add (X \ Y) (fun i => ω i / lam) hx
  refine max_le hge1 ?_
  rw [div_le_iff₀ hden]
  rw [← Finset.sum_div] at hprod
  have key : lam + ∑ i ∈ X, ω i ≤ (1 + (∑ i ∈ X \ Y, ω i) / lam) * (lam + ∑ i ∈ Y, ω i) := by
    rw [hsplit]
    have : (∑ i ∈ X \ Y, ω i) / lam * (lam + ∑ i ∈ Y, ω i) ≥ ∑ i ∈ X \ Y, ω i := by
      rw [div_mul_eq_mul_div, ge_iff_le, le_div_iff₀ hlam]
      nlinarith [hnn Y hY, hnn (X \ Y) (Finset.sdiff_subset.trans hX)]
    nlinarith
  calc lam + ∑ i ∈ X, ω i ≤ (1 + (∑ i ∈ X \ Y, ω i) / lam) * (lam + ∑ i ∈ Y, ω i) := key
    _ ≤ (∏ i ∈ X \ Y, (1 + ω i / lam)) * (lam + ∑ i ∈ Y, ω i) :=
        mul_le_mul_of_nonneg_right hprod hden.le

/-- Each color ends at most once (main TeX line 3830, "Each connected
`I_i^T` ends at precisely one such cut"): for an order-convex pattern, at
most one `j < N` has `i ∈ act j ∖ act (j+1)`. -/
theorem ending_card_le_one (act : ℕ → Finset ι) (hconv : ActivityConvex act) (N : ℕ) (i : ι) :
    ((Finset.range N).filter fun j => i ∈ act j \ act (j + 1)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro j hj j' hj'
  simp only [Finset.mem_filter, Finset.mem_sdiff] at hj hj'
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact hj.2.2 (hconv i j (j + 1) j' (by omega) (by omega) hj.2.1 hj'.2.1)
  · exact hj'.2.2 (hconv i j' (j' + 1) j (by omega) (by omega) hj'.2.1 hj.2.1)

/-- **General telescoping lemma for the interval metric**
(`E:interval-copy-metric`, main TeX lines 3809-3837): for `λ > 0`, weights
`ω_i ≥ 0` on a finite set `A`, and an order-convex activity pattern with
values in `A`, the conversion factors `q_j = max{1, Λ_j/Λ_{j+1}}` over any
`N` consecutive cuts satisfy `∏_{j<N} q_j ≤ ∏_{i∈A} (1 + ω_i/λ)`.  Cuts
where no color ends (insertion cuts, starts of overlapping colors) are
charged one. -/
theorem metric_telescoping (lam : ℝ) (hlam : 0 < lam) (ω : ι → ℝ) (A : Finset ι)
    (hω : ∀ i ∈ A, 0 ≤ ω i) (act : ℕ → Finset ι) (hA : ∀ j, act j ⊆ A)
    (hconv : ActivityConvex act) (N : ℕ) :
    ∏ j ∈ Finset.range N, max 1 (height lam ω act j / height lam ω act (j + 1)) ≤
      ∏ i ∈ A, (1 + ω i / lam) := by
  have hf1 : ∀ i ∈ A, 1 ≤ 1 + ω i / lam := fun i hi => by
    have := div_nonneg (hω i hi) hlam.le; linarith
  calc ∏ j ∈ Finset.range N, max 1 (height lam ω act j / height lam ω act (j + 1))
      ≤ ∏ j ∈ Finset.range N, ∏ i ∈ act j \ act (j + 1), (1 + ω i / lam) :=
        Finset.prod_le_prod₀ (fun j _ => le_trans zero_le_one (le_max_left _ _))
          fun j _ => cut_ratio_le lam hlam ω A hω _ _ (hA j) (hA (j + 1))
    _ = ∏ j ∈ Finset.range N, ∏ i ∈ A,
          if i ∈ act j \ act (j + 1) then 1 + ω i / lam else 1 := by
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [Finset.prod_ite_mem, Finset.inter_eq_right.2 (Finset.sdiff_subset.trans (hA j))]
    _ = ∏ i ∈ A, ∏ j ∈ Finset.range N,
          if i ∈ act j \ act (j + 1) then 1 + ω i / lam else 1 :=
        Finset.prod_comm
    _ ≤ ∏ i ∈ A, (1 + ω i / lam) := by
        refine Finset.prod_le_prod₀ (fun i hi => Finset.prod_nonneg fun j _ => ?_)
          fun i hi => ?_
        · split_ifs
          · linarith [hf1 i hi]
          · exact zero_le_one
        · rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
          calc (1 + ω i / lam) ^ ((Finset.range N).filter fun j => i ∈ act j \ act (j + 1)).card
              ≤ (1 + ω i / lam) ^ 1 :=
                pow_le_pow_right₀ (hf1 i hi) (ending_card_le_one act hconv N i)
            _ = 1 + ω i / lam := pow_one _

/-- The activity pattern of the intervals `(a_i, b_i)`, `i ∈ A`, along a
partition `τ_0, …, τ_M` (main TeX lines 3784-3788): segment `j`
(`1 ≤ j ≤ M`) is `(τ_{j-1}, τ_j)` and color `i` is active on it iff
`a_i ≤ τ_{j-1}` and `τ_j ≤ b_i`; the outer segments `0` and `M+1` (heights
`Λ_0 = Λ_{M+1} = λ`, line 3809) have no active color. -/
def intervalAct (A : Finset ι) (a b : ι → ℝ) (τ : ℕ → ℝ) (M j : ℕ) : Finset ι :=
  if 1 ≤ j ∧ j ≤ M then A.filter (fun i => a i ≤ τ (j - 1) ∧ τ j ≤ b i) else ∅

/-- Auxiliary (Lean route): steps `τ_j ≤ τ_{j+1}` for `j < M` give
monotonicity on `{0, …, M}`. -/
theorem monotone_of_steps (τ : ℕ → ℝ) (M : ℕ) (hst : ∀ j < M, τ j ≤ τ (j + 1)) :
    ∀ m n, m ≤ n → n ≤ M → τ m ≤ τ n := by
  intro m n hmn hnM
  induction n with
  | zero =>
    have : m = 0 := by omega
    rw [this]
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with h | h
    · exact (ih (by omega) (by omega)).trans (hst n (by omega))
    · have : m = n + 1 := by omega
      rw [this]

omit [DecidableEq ι] in
/-- Auxiliary (Lean route): the interval activity sets lie in `A`. -/
theorem intervalAct_subset (A : Finset ι) (a b : ι → ℝ) (τ : ℕ → ℝ) (M j : ℕ) :
    intervalAct A a b τ M j ⊆ A := by
  unfold intervalAct; split_ifs
  · exact Finset.filter_subset _ _
  · exact Finset.empty_subset _

omit [DecidableEq ι] in
/-- Auxiliary (Lean route): no color is active on the outer segments. -/
theorem intervalAct_outer (A : Finset ι) (a b : ι → ℝ) (τ : ℕ → ℝ) (M : ℕ) :
    intervalAct A a b τ M 0 = ∅ ∧ intervalAct A a b τ M (M + 1) = ∅ := by
  unfold intervalAct
  constructor
  · rw [ite_eq_right_iff]; omega
  · rw [ite_eq_right_iff]; omega

omit [DecidableEq ι] in
/-- Each interval is active on consecutive segments (main TeX line 3830)
when the partition is monotone. -/
theorem intervalAct_convex (A : Finset ι) (a b : ι → ℝ) (τ : ℕ → ℝ) (M : ℕ)
    (hst : ∀ j < M, τ j ≤ τ (j + 1)) : ActivityConvex (intervalAct A a b τ M) := by
  intro i j₁ j j₂ h1 h2 hi1 hi2
  have hm := monotone_of_steps τ M hst
  unfold intervalAct at *
  split_ifs at hi1 hi2 with c1 c2
  · have hc : 1 ≤ j ∧ j ≤ M := by omega
    simp only [hc, and_self, ↓reduceIte, Finset.mem_filter] at hi1 hi2 ⊢
    exact ⟨hi1.1, hi1.2.1.trans (hm _ _ (by omega) (by omega)),
      (hm _ _ h2 c2.2).trans hi2.2.2⟩
  all_goals simp at hi1 hi2

/-- Auxiliary (Lean route): on a segment `(τ_{j-1}, τ_j)` of a monotone
partition whose cuts include every endpoint of `(a, b)` lying in
`(τ_0, τ_M)`, a point `t` of the segment lies in `(a, b)` iff the whole
segment does. -/
theorem seg_mem_iff (τ : ℕ → ℝ) (M j : ℕ) (hst : ∀ j < M, τ j ≤ τ (j + 1)) (hj1 : 1 ≤ j)
    (hjM : j ≤ M) (t : ℝ) (ht : t ∈ Set.Ioo (τ (j - 1)) (τ j)) (a b : ℝ)
    (ha : τ 0 < a → a < τ M → ∃ m ≤ M, τ m = a)
    (hb : τ 0 < b → b < τ M → ∃ m ≤ M, τ m = b) :
    t ∈ Set.Ioo a b ↔ a ≤ τ (j - 1) ∧ τ j ≤ b := by
  have hm := monotone_of_steps τ M hst
  have no_cut : ∀ m ≤ M, ¬ (τ (j - 1) < τ m ∧ τ m < τ j) := by
    rintro m hmM ⟨h1, h2⟩
    rcases Nat.lt_or_ge m j with h | h
    · exact absurd (hm m (j - 1) (by omega) (by omega)) (not_le.2 h1)
    · exact absurd (hm j m h hmM) (not_le.2 h2)
  have h0j : τ 0 ≤ τ (j - 1) := hm 0 (j - 1) (by omega) (by omega)
  have hjM' : τ j ≤ τ M := hm j M hjM le_rfl
  obtain ⟨ht1, ht2⟩ := ht
  constructor
  · rintro ⟨hat, htb⟩
    constructor
    · by_contra hcon
      push Not at hcon
      obtain ⟨m, hmM, hma⟩ := ha (by linarith) (by linarith)
      exact no_cut m hmM ⟨by rw [hma]; exact hcon, by rw [hma]; linarith⟩
    · by_contra hcon
      push Not at hcon
      obtain ⟨m, hmM, hmb⟩ := hb (by linarith) (by linarith)
      exact no_cut m hmM ⟨by rw [hmb]; linarith, by rw [hmb]; exact hcon⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

/-- `Λ(t) = λ + ∑_{i∈A} ω_i 1_{(a_i, b_i)}(t)` (main TeX lines 3765-3766). -/
def intervalLambda (lam : ℝ) (ω : ι → ℝ) (A : Finset ι) (a b : ι → ℝ) (t : ℝ) : ℝ :=
  lam + ∑ i ∈ A, (Set.Ioo (a i) (b i)).indicator (fun _ => ω i) t

omit [DecidableEq ι] in
/-- `Λ_j` is the constant value of `Λ` on `(τ_{j-1}, τ_j)` (main TeX lines
3787-3788), for a monotone partition containing every endpoint that lies in
`(τ_0, τ_M)`. -/
theorem intervalLambda_eq_height (lam : ℝ) (ω : ι → ℝ) (A : Finset ι) (a b : ι → ℝ)
    (τ : ℕ → ℝ) (M j : ℕ) (hst : ∀ j < M, τ j ≤ τ (j + 1)) (hj1 : 1 ≤ j) (hjM : j ≤ M)
    (hcut : ∀ i ∈ A, (τ 0 < a i → a i < τ M → ∃ m ≤ M, τ m = a i) ∧
      (τ 0 < b i → b i < τ M → ∃ m ≤ M, τ m = b i))
    (t : ℝ) (ht : t ∈ Set.Ioo (τ (j - 1)) (τ j)) :
    intervalLambda lam ω A a b t = height lam ω (intervalAct A a b τ M) j := by
  unfold intervalLambda height intervalAct
  have hc : 1 ≤ j ∧ j ≤ M := ⟨hj1, hjM⟩
  simp only [hc, and_self, ↓reduceIte]
  rw [Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Set.indicator_apply]
  have := seg_mem_iff τ M j hst hj1 hjM t ht (a i) (b i) (hcut i hi).1 (hcut i hi).2
  simp only [this]

omit [DecidableEq ι] in
/-- Auxiliary (Lean route): the outer heights are `λ`. -/
theorem height_outer (lam : ℝ) (ω : ι → ℝ) (A : Finset ι) (a b : ι → ℝ) (τ : ℕ → ℝ) (M : ℕ) :
    height lam ω (intervalAct A a b τ M) 0 = lam ∧
      height lam ω (intervalAct A a b τ M) (M + 1) = lam := by
  obtain ⟨h0, h1⟩ := intervalAct_outer A a b τ M
  unfold height
  rw [h0, h1]
  simp

/-- `E:interval-copy-metric` for intervals (main TeX lines 3809-3837): for a
monotone partition `τ_0 ≤ ⋯ ≤ τ_M`, `λ > 0` and `ω_i ≥ 0`, the conversions
`q_j = max{1, Λ_j/Λ_{j+1}}`, `0 ≤ j ≤ M`, with `Λ_0 = Λ_{M+1} = λ`,
satisfy `∏_{j=0}^M q_j ≤ ∏_{i∈A} (1 + ω_i/λ)`.  This includes the initial
and final conversions. -/
theorem interval_copy_metric (lam : ℝ) (hlam : 0 < lam) (ω : ι → ℝ) (A : Finset ι)
    (hω : ∀ i ∈ A, 0 ≤ ω i) (a b : ι → ℝ) (τ : ℕ → ℝ) (M : ℕ)
    (hst : ∀ j < M, τ j ≤ τ (j + 1)) :
    ∏ j ∈ Finset.range (M + 1),
        max 1 (height lam ω (intervalAct A a b τ M) j /
          height lam ω (intervalAct A a b τ M) (j + 1)) ≤
      ∏ i ∈ A, (1 + ω i / lam) :=
  metric_telescoping lam hlam ω A hω _ (intervalAct_subset A a b τ M)
    (intervalAct_convex A a b τ M hst) (M + 1)

/-- **`E:interval-copy-metric`, TeX form** (main TeX lines 3809-3837, with
`ω_i = k_i/h_i` from `E:split-radii`, lines 3745-3749, and `λ = k/T`): for
a strict partition `τ_0 < ⋯ < τ_M`, `T > 0`, `k ≥ 1` and `h_i > 0`,
`∏_{j=0}^M q_j ≤ D_𝒜 = ∏_{i∈𝒜} (1 + k_i/(λh_i))`.  The step does not
involve the covariance, so `H:homog` is not carried; the requirement that
the cuts contain the endpoints is not needed for this inequality (it is
used only in `intervalLambda_eq_height`). -/
theorem interval_copy_metric_paper (A : Finset ι) (a b h : ι → ℝ) (κ : ι → ℕ) (τ : ℕ → ℝ)
    (M k : ℕ) (T : ℝ) (hT : 0 < T) (hk : 1 ≤ k) (hh : ∀ i ∈ A, 0 < h i)
    (hst : ∀ j < M, τ j < τ (j + 1)) :
    ∏ j ∈ Finset.range (M + 1),
        max 1 (height (k / T) (fun i => κ i / h i) (intervalAct A a b τ M) j /
          height (k / T) (fun i => κ i / h i) (intervalAct A a b τ M) (j + 1)) ≤
      metricD (k / T) h κ A := by
  have hlam : (0 : ℝ) < k / T := div_pos (by exact_mod_cast hk) hT
  refine (interval_copy_metric (k / T) hlam (fun i => κ i / h i) A
    (fun i hi => div_nonneg (Nat.cast_nonneg _) (hh i hi).le) a b τ M
    (fun j hj => (hst j hj).le)).trans (le_of_eq ?_)
  unfold metricD
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [div_div, mul_comm (h i)]

end CopyMetric

/-! ### The segment product `E:split-segment-product` -/

section Segments

variable {ι : Type*} [DecidableEq ι]

/-- `∑_{j=1}^M Λ_j (τ_j - τ_{j-1})` (main TeX lines 3796-3797), written
with `j + 1` for the TeX's `j`. -/
def segSum (lam : ℝ) (ω : ι → ℝ) (act : ℕ → Finset ι) (τ : ℕ → ℝ) (M : ℕ) : ℝ :=
  ∑ j ∈ range M, height lam ω act (j + 1) * (τ (j + 1) - τ j)

/-- The exponent identity (main TeX lines 3802-3803): `∑_j Λ_j(τ_j - τ_{j-1})
= λ(τ_M - τ_0) + ∑_{i∈A} ω_i ∑_{j: i active}(τ_j - τ_{j-1})`. -/
theorem segSum_eq (lam : ℝ) (ω : ι → ℝ) (A : Finset ι) (act : ℕ → Finset ι)
    (hA : ∀ j, act j ⊆ A) (τ : ℕ → ℝ) (M : ℕ) :
    segSum lam ω act τ M = lam * (τ M - τ 0) +
      ∑ i ∈ A, ω i * ∑ j ∈ range M, (if i ∈ act (j + 1) then τ (j + 1) - τ j else 0) := by
  unfold segSum height
  have h1 : ∀ j, (lam + ∑ i ∈ act (j + 1), ω i) * (τ (j + 1) - τ j) =
      lam * (τ (j + 1) - τ j) +
        ∑ i ∈ A, ω i * (if i ∈ act (j + 1) then τ (j + 1) - τ j else 0) := by
    intro j
    rw [add_mul, Finset.sum_mul]
    congr 1
    simp_rw [mul_ite, mul_zero]
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 (hA (j + 1))]
  simp_rw [h1]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_range_sub, Finset.sum_comm]
  simp_rw [Finset.mul_sum]

/-- Auxiliary (Lean route): the total length of the segments of a monotone
partition lying in `[a, b]` is at most `max{0, b - a}` (replaces the TeX's
exact value `b_i - a_i`, line 3803). -/
theorem occupation_le (τ : ℕ → ℝ) (M : ℕ) (hmono : ∀ j < M, τ j ≤ τ (j + 1)) (a b : ℝ) :
    ∀ n ≤ M, ∑ j ∈ range n, (if a ≤ τ j ∧ τ (j + 1) ≤ b then τ (j + 1) - τ j else 0) ≤
      max 0 (min (τ n) b - a) := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have ih' := ih (by omega)
    have hst := hmono n (by omega)
    rw [Finset.sum_range_succ]
    split_ifs with hc
    · have hmin : min (τ n) b = τ n := min_eq_left (hst.trans hc.2)
      have hmin' : min (τ (n + 1)) b = τ (n + 1) := min_eq_left hc.2
      rw [hmin, max_eq_right (by linarith [hc.1])] at ih'
      rw [hmin']
      exact le_max_of_le_right (by linarith)
    · rw [add_zero]
      exact ih'.trans (max_le_max le_rfl (sub_le_sub_right (min_le_min_right b hst) a))

/-- The exponent bound of `E:split-segment-product` (main TeX lines
3802-3804): with `τ_0 = 0`, `τ_M = T`, a monotone partition, `λ = k/T`,
`ω_i = k_i/h_i`, `b_i - a_i ≤ h_i`, `h_i > 0` and `∑_{i∈A} k_i ≤ k`,
`∑_j Λ_j (τ_j - τ_{j-1}) ≤ 2k`. -/
theorem segSum_le (A : Finset ι) (a b h : ι → ℝ) (κ : ι → ℕ) (τ : ℕ → ℝ) (M k : ℕ) (T : ℝ)
    (hT : 0 < T) (hτ0 : τ 0 = 0) (hτM : τ M = T) (hst : ∀ j < M, τ j ≤ τ (j + 1))
    (hh : ∀ i ∈ A, 0 < h i) (hlen : ∀ i ∈ A, b i - a i ≤ h i) (hκ : ∑ i ∈ A, κ i ≤ k) :
    segSum (k / T) (fun i => κ i / h i) (intervalAct A a b τ M) τ M ≤ 2 * k := by
  rw [segSum_eq (k / T) _ A _ (intervalAct_subset A a b τ M) τ M, hτ0, hτM, sub_zero,
    div_mul_cancel₀ _ hT.ne']
  have hocc : ∀ i ∈ A, (κ i : ℝ) / h i * ∑ j ∈ range M,
      (if i ∈ intervalAct A a b τ M (j + 1) then τ (j + 1) - τ j else 0) ≤ κ i := by
    intro i hi
    have hcongr : ∑ j ∈ range M,
        (if i ∈ intervalAct A a b τ M (j + 1) then τ (j + 1) - τ j else 0) =
        ∑ j ∈ range M, (if a i ≤ τ j ∧ τ (j + 1) ≤ b i then τ (j + 1) - τ j else 0) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjM : j < M := Finset.mem_range.1 hj
      have hc : 1 ≤ j + 1 ∧ j + 1 ≤ M := ⟨by omega, by omega⟩
      simp only [intervalAct, hc, and_self, ↓reduceIte, Finset.mem_filter, hi, true_and,
        Nat.add_sub_cancel]
    rw [hcongr]
    have hle := occupation_le τ M hst (a i) (b i) M le_rfl
    have hmax : max 0 (min (τ M) (b i) - a i) ≤ h i :=
      max_le (hh i hi).le (by linarith [min_le_right (τ M) (b i), hlen i hi])
    calc (κ i : ℝ) / h i * ∑ j ∈ range M,
          (if a i ≤ τ j ∧ τ (j + 1) ≤ b i then τ (j + 1) - τ j else 0)
        ≤ (κ i : ℝ) / h i * h i :=
          mul_le_mul_of_nonneg_left (hle.trans hmax)
            (div_nonneg (Nat.cast_nonneg _) (hh i hi).le)
      _ = κ i := div_mul_cancel₀ _ (hh i hi).ne'
  have hsum : ∑ i ∈ A, (κ i : ℝ) / h i * ∑ j ∈ range M,
      (if i ∈ intervalAct A a b τ M (j + 1) then τ (j + 1) - τ j else 0) ≤ k := by
    refine (Finset.sum_le_sum hocc).trans ?_
    exact_mod_cast hκ
  linarith

/-- The partition count (main TeX lines 3789-3790): `M ≤ 2|𝒜| + m + 1` with
`|𝒜| ≤ k` and `m ≤ k` gives `M ≤ 3k + 1`. -/
theorem partition_count_le (M nA m k : ℕ) (hM : M ≤ 2 * nA + m + 1) (hA : nA ≤ k)
    (hm : m ≤ k) : M ≤ 3 * k + 1 := by
  omega

/-- Auxiliary (Lean route): `∏_j p_j ≤ 100^M exp(2 ∑_j e_j)` from
`p_j ≤ 100 e^{2 e_j}` (first line of `E:split-segment-product`). -/
theorem exp_sum_le_product (p e : ℕ → ℝ) (M : ℕ) (hp : ∀ j < M, 0 ≤ p j)
    (hpe : ∀ j < M, p j ≤ 100 * Real.exp (2 * e j)) :
    ∏ j ∈ range M, p j ≤ 100 ^ M * Real.exp (2 * ∑ j ∈ range M, e j) := by
  calc ∏ j ∈ range M, p j ≤ ∏ j ∈ range M, (100 * Real.exp (2 * e j)) :=
        Finset.prod_le_prod₀ (fun j hj => hp j (Finset.mem_range.1 hj))
          fun j hj => hpe j (Finset.mem_range.1 hj)
    _ = 100 ^ M * Real.exp (2 * ∑ j ∈ range M, e j) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, Finset.mul_sum,
          Real.exp_sum]

/-- `M_k = 100^{3k+1} e^{4k}` (main TeX line 3798). -/
def Mk (k : ℕ) : ℝ := 100 ^ (3 * k + 1) * Real.exp (4 * k)

/-- `M_k² = 100^{6k+2} e^{8k} ≤ (100^8 e^8)^k` for `k ≥ 1` (main TeX lines
4037-4038). -/
theorem Mk_sq_le (k : ℕ) (hk : 1 ≤ k) : Mk k ^ 2 ≤ (100 ^ 8 * Real.exp 8) ^ k := by
  unfold Mk
  rw [mul_pow, mul_pow, ← pow_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
  have h1 : (100 : ℝ) ^ ((3 * k + 1) * 2) ≤ 100 ^ (8 * k) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : Real.exp ((2 : ℕ) * (4 * (k : ℝ))) = Real.exp ((k : ℕ) * 8) := by
    congr 1; push_cast; ring
  rw [h2, ← pow_mul]
  exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le

/-- `E:split-segment-product`, general form (main TeX lines 3791-3801): if
the segment factors satisfy `0 ≤ p_j ≤ 100 e^{2 e_j}` (in the TeX
`p_j = ‖P_j‖` and `e_j = Λ_j(τ_j - τ_{j-1})`, the bound being that of
`L:interval-complex`), `M ≤ 3k + 1` and `∑ e_j ≤ 2k`, then
`∏ p_j ≤ M_k`. -/
theorem split_segment_product (p e : ℕ → ℝ) (M k : ℕ) (hp : ∀ j < M, 0 ≤ p j)
    (hpe : ∀ j < M, p j ≤ 100 * Real.exp (2 * e j)) (hM : M ≤ 3 * k + 1)
    (he : ∑ j ∈ range M, e j ≤ 2 * k) : ∏ j ∈ range M, p j ≤ Mk k := by
  refine (exp_sum_le_product p e M hp hpe).trans ?_
  unfold Mk
  exact mul_le_mul (pow_le_pow_right₀ (by norm_num) hM)
    (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le (by positivity)

/-- **`E:split-segment-product`, TeX form** (main TeX lines 3781-3804):
for the partition `0 = τ_0 < ⋯ < τ_M = T` with `M ≤ 3k + 1`, `λ = k/T`,
`ω_i = k_i/h_i`, intervals `(a_i, b_i)` with `b_i - a_i ≤ h_i`, `h_i > 0`
and `∑_{i∈𝒜} k_i ≤ k`: segment factors with
`0 ≤ p_j ≤ 100 e^{2Λ_{j+1}(τ_{j+1} - τ_j)}` (the bound supplied by
`L:interval-complex` in the TeX) have `∏_{j<M} p_j ≤ M_k`.  The step does
not involve the covariance, so `H:homog` is not carried. -/
theorem split_segment_product_paper (A : Finset ι) (a b h : ι → ℝ) (κ : ι → ℕ) (τ : ℕ → ℝ)
    (M k : ℕ) (T : ℝ) (hT : 0 < T) (hτ0 : τ 0 = 0) (hτM : τ M = T)
    (hst : ∀ j < M, τ j < τ (j + 1)) (hh : ∀ i ∈ A, 0 < h i)
    (hlen : ∀ i ∈ A, b i - a i ≤ h i) (hκ : ∑ i ∈ A, κ i ≤ k) (hM : M ≤ 3 * k + 1)
    (p : ℕ → ℝ) (hp : ∀ j < M, 0 ≤ p j)
    (hpe : ∀ j < M, p j ≤ 100 * Real.exp (2 *
      (height (k / T) (fun i => κ i / h i) (intervalAct A a b τ M) (j + 1) *
        (τ (j + 1) - τ j)))) :
    ∏ j ∈ range M, p j ≤ Mk k :=
  split_segment_product p _ M k hp hpe hM
    (segSum_le A a b h κ τ M k T hT hτ0 hτM (fun j hj => (hst j hj).le) hh hlen hκ)

end Segments

/-! ### The radii `E:split-radii` -/

section Radii

/-- `d_i = 2 √(2k_i + 1) √R_α` (main TeX line 3747). -/
def splitD (R : ℝ) (k : ℕ) : ℝ := 2 * √(2 * k + 1) * √R

/-- `ϱ_i = δ ω_i^{2-a}/(σ_i d_i)` with `ω_i = k_i/h_i` and `a = α/2` (main
TeX lines 3743-3748). -/
def splitRadius (alpha δ σ R h : ℝ) (k : ℕ) : ℝ :=
  δ * ((k : ℝ) / h) ^ (2 - alpha / 2) / (σ * splitD R k)

/-- Auxiliary (Lean route): `d_i² = 4(2k_i + 1) R_α`. -/
theorem splitD_sq (R : ℝ) (hR : 0 ≤ R) (k : ℕ) : splitD R k ^ 2 = 4 * (2 * k + 1) * R := by
  unfold splitD
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hR]; ring

/-- `d_i² ≤ 12 k_i R_α` for `k_i ≥ 1` (main TeX line 4022). -/
theorem splitD_sq_le (R : ℝ) (hR : 0 ≤ R) (k : ℕ) (hk : 1 ≤ k) : splitD R k ^ 2 ≤ 12 * k * R := by
  rw [splitD_sq R hR]
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith

/-- Auxiliary (Lean route): `ϱ_i > 0`. -/
theorem splitRadius_pos (alpha δ σ R h : ℝ) (k : ℕ) (hδ : 0 < δ) (hσ : 0 < σ) (hR : 0 < R)
    (hh : 0 < h) (hk : 1 ≤ k) : 0 < splitRadius alpha δ σ R h k := by
  unfold splitRadius splitD
  have : (0 : ℝ) < k := by exact_mod_cast hk
  positivity

/-- `∑ x_i^q ≤ (∑ x_i)^q` for `x_i ≥ 0` and `q ≥ 1` (main TeX lines
3776-3777, with `q = 2 - a`). -/
theorem sum_rpow_le_rpow_sum {ι : Type*} (S : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ S, 0 ≤ x i)
    (q : ℝ) (hq : 1 ≤ q) : ∑ i ∈ S, x i ^ q ≤ (∑ i ∈ S, x i) ^ q := by
  set T := ∑ i ∈ S, x i
  have hT : 0 ≤ T := Finset.sum_nonneg hx
  have hle : ∀ i ∈ S, x i ^ q ≤ x i * T ^ (q - 1) := by
    intro i hi
    have hxi := hx i hi
    have hxT : x i ≤ T := Finset.single_le_sum hx hi
    rw [show q = 1 + (q - 1) by ring, Real.rpow_add' hxi (by linarith), Real.rpow_one]
    rw [show 1 + (q - 1) - 1 = q - 1 by ring]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hxi hxT (by linarith)) hxi
  calc ∑ i ∈ S, x i ^ q ≤ ∑ i ∈ S, x i * T ^ (q - 1) := Finset.sum_le_sum hle
    _ = T * T ^ (q - 1) := by rw [Finset.sum_mul]
    _ = T ^ q := by
        conv_rhs => rw [show q = 1 + (q - 1) by ring]
        rw [Real.rpow_add' hT (by linarith), Real.rpow_one]

/-- The radius step after `E:split-radii` (main TeX lines 3768-3777): for
active colors `S` with `|z_i| = ϱ_i`, `D = ∑_{i∈S} ϱ_i σ_i d_i ≤
δ (λ + ∑_{i∈S} ω_i)^{2-a}`, `a = α/2`, `ω_i = k_i/h_i`, under `α ≤ 2`,
`λ ≥ 0`, `δ ≥ 0`, `R > 0`, `σ_i > 0`, `h_i > 0`.  Applied with `S` the
colors active at `t`, the right side is `δ Λ(t)^{2-a}`. -/
theorem split_radius_sum {ι : Type*} (S : Finset ι) (alpha δ R lam : ℝ) (σ h : ι → ℝ)
    (κ : ι → ℕ) (hα : alpha ≤ 2) (hlam : 0 ≤ lam) (hδ : 0 ≤ δ) (hR : 0 < R)
    (hσ : ∀ i ∈ S, 0 < σ i) (hh : ∀ i ∈ S, 0 < h i) :
    ∑ i ∈ S, splitRadius alpha δ (σ i) R (h i) (κ i) * σ i * splitD R (κ i) ≤
      δ * (lam + ∑ i ∈ S, (κ i : ℝ) / h i) ^ (2 - alpha / 2) := by
  have hq : 1 ≤ 2 - alpha / 2 := by linarith
  have hx : ∀ i ∈ S, 0 ≤ (κ i : ℝ) / h i := fun i hi => div_nonneg (Nat.cast_nonneg _) (hh i hi).le
  have heq : ∀ i ∈ S, splitRadius alpha δ (σ i) R (h i) (κ i) * σ i * splitD R (κ i) =
      δ * ((κ i : ℝ) / h i) ^ (2 - alpha / 2) := by
    intro i hi
    have hd : 0 < splitD R (κ i) := by unfold splitD; have := hR; positivity
    have hs := hσ i hi
    unfold splitRadius
    field_simp
  rw [Finset.sum_congr rfl heq, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hδ
  refine (sum_rpow_le_rpow_sum S _ hx _ hq).trans ?_
  exact Real.rpow_le_rpow (Finset.sum_nonneg hx) (by linarith) (by linarith)

end Radii

/-! ### The word product `E:split-word-product` -/

section Word

variable {ι : Type*}

/-- Auxiliary (Lean route): a chain `x_{j+1} ≤ a_j x_j` with `a_j ≥ 0`
gives `x_N ≤ (∏_{j<N} a_j) x_0`. -/
theorem norm_chain_le (x a : ℕ → ℝ) (N : ℕ) (ha : ∀ j < N, 0 ≤ a j)
    (hstep : ∀ j < N, x (j + 1) ≤ a j * x j) : x N ≤ (∏ j ∈ range N, a j) * x 0 := by
  induction N with
  | zero => simp
  | succ n ih =>
    have ih' := ih (fun j hj => ha j (by omega)) (fun j hj => hstep j (by omega))
    rw [Finset.prod_range_succ]
    calc x (n + 1) ≤ a n * x n := hstep n (by omega)
      _ ≤ a n * ((∏ j ∈ range n, a j) * x 0) := mul_le_mul_of_nonneg_left ih' (ha n (by omega))
      _ = _ := by ring

/-- `E:split-word-product`, first inequality (main TeX lines 3907-3926), for
the norms of the partial words: with `w_0 = ‖𝓘_0 v‖ ≤ q_0 ‖v‖` and
`w_{s+1} = ‖𝓘_{s+1} P_{s+1} B_s(⋯)‖ ≤ q_{s+1} p_s b_s w_s` (`p_s` the bound
of segment `s + 1`, `b_s` that of the cut `s`; in the TeX there is no
insertion at the cut `0`, so `b_0` bounds an identity),
`w_M ≤ (∏_{s<M} p_s)(∏_{s≤M} q_s)(∏_{s<M} b_s)‖v‖`. -/
theorem split_word_product (w p q b : ℕ → ℝ) (M : ℕ) (nv : ℝ)
    (hp : ∀ s < M, 0 ≤ p s) (hq : ∀ s ≤ M, 0 ≤ q s) (hb : ∀ s < M, 0 ≤ b s)
    (h0 : w 0 ≤ q 0 * nv) (hstep : ∀ s < M, w (s + 1) ≤ q (s + 1) * p s * b s * w s) :
    w M ≤ (∏ s ∈ range M, p s) * (∏ s ∈ range (M + 1), q s) * (∏ s ∈ range M, b s) * nv := by
  have hc := norm_chain_le w (fun s => q (s + 1) * p s * b s) M
    (fun s hs => mul_nonneg (mul_nonneg (hq (s + 1) (by omega)) (hp s hs)) (hb s hs)) hstep
  have hA : 0 ≤ ∏ s ∈ range M, q (s + 1) * p s * b s :=
    Finset.prod_nonneg fun s hs => mul_nonneg (mul_nonneg (hq (s + 1) (by
      have := Finset.mem_range.1 hs; omega)) (hp s (Finset.mem_range.1 hs)))
      (hb s (Finset.mem_range.1 hs))
  calc w M ≤ (∏ s ∈ range M, q (s + 1) * p s * b s) * w 0 := hc
    _ ≤ (∏ s ∈ range M, q (s + 1) * p s * b s) * (q 0 * nv) := mul_le_mul_of_nonneg_left h0 hA
    _ = _ := by
        rw [Finset.prod_range_succ' q M, Finset.prod_mul_distrib, Finset.prod_mul_distrib]; ring

/-- The insertion cuts (main TeX lines 3907-3909 with
`E:split-fresh-insertion`, 3890-3894): if each cross color `i ∈ 𝒞` is
inserted at its own cut `σ(i) < M` (injective) with `b_{σ(i)} = c_i`, and
every other cut factor lies in `[0, 1]` (an identity), then
`∏_{s<M} b_s ≤ ∏_{i∈𝒞} c_i`. -/
theorem insertion_product_le (C : Finset ι) (σ : ι → ℕ) (M : ℕ) (hσ : Set.InjOn σ C)
    (hσM : ∀ i ∈ C, σ i < M) (b : ℕ → ℝ) (c : ι → ℝ) (hbc : ∀ i ∈ C, b (σ i) = c i)
    (hb0 : ∀ s < M, 0 ≤ b s) (hb1 : ∀ s < M, s ∉ C.image σ → b s ≤ 1) :
    ∏ s ∈ range M, b s ≤ ∏ i ∈ C, c i := by
  have hsub : C.image σ ⊆ range M := by
    intro s hs; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hs; exact Finset.mem_range.2 (hσM i hi)
  rw [← Finset.prod_sdiff hsub, Finset.prod_image hσ]
  have hc : ∏ i ∈ C, b (σ i) = ∏ i ∈ C, c i := Finset.prod_congr rfl hbc
  rw [hc]
  have hcnn : 0 ≤ ∏ i ∈ C, c i := by
    rw [← hc]; exact Finset.prod_nonneg fun i hi => hb0 _ (hσM i hi)
  have hrest : ∏ s ∈ range M \ C.image σ, b s ≤ 1 :=
    Finset.prod_le_one₀ (fun s hs => hb0 s (Finset.mem_range.1 (Finset.mem_sdiff.1 hs).1))
      fun s hs => hb1 s (Finset.mem_range.1 (Finset.mem_sdiff.1 hs).1) (Finset.mem_sdiff.1 hs).2
  calc (∏ s ∈ range M \ C.image σ, b s) * ∏ i ∈ C, c i ≤ 1 * ∏ i ∈ C, c i :=
        mul_le_mul_of_nonneg_right hrest hcnn
    _ = _ := one_mul _

/-- **`E:split-word-product`** (main TeX lines 3907-3930): under the
hypotheses of `split_word_product` and `insertion_product_le`, with
`∏_s p_s ≤ M` (for instance `M_k` by `split_segment_product`) and
`∏_s q_s ≤ D` (for instance `D_𝒜` by `interval_copy_metric_paper`),
`w_M ≤ M D (∏_{i∈𝒞} c_i) ‖v‖`. -/
theorem split_word_bound (w p q b : ℕ → ℝ) (M : ℕ) (nv Mbd D : ℝ) (C : Finset ι)
    (σ : ι → ℕ) (c : ι → ℝ) (hnv : 0 ≤ nv)
    (hp : ∀ s < M, 0 ≤ p s) (hq : ∀ s ≤ M, 0 ≤ q s) (hb : ∀ s < M, 0 ≤ b s)
    (h0 : w 0 ≤ q 0 * nv) (hstep : ∀ s < M, w (s + 1) ≤ q (s + 1) * p s * b s * w s)
    (hσ : Set.InjOn σ C) (hσM : ∀ i ∈ C, σ i < M) (hbc : ∀ i ∈ C, b (σ i) = c i)
    (hb1 : ∀ s < M, s ∉ C.image σ → b s ≤ 1)
    (hP : ∏ s ∈ range M, p s ≤ Mbd) (hQ : ∏ s ∈ range (M + 1), q s ≤ D) :
    w M ≤ Mbd * D * (∏ i ∈ C, c i) * nv := by
  have hw := split_word_product w p q b M nv hp hq hb h0 hstep
  have hB := insertion_product_le C σ M hσ hσM b c hbc hb hb1
  have hP0 : 0 ≤ ∏ s ∈ range M, p s :=
    Finset.prod_nonneg fun s hs => hp s (Finset.mem_range.1 hs)
  have hQ0 : 0 ≤ ∏ s ∈ range (M + 1), q s :=
    Finset.prod_nonneg fun s hs => hq s (by have := Finset.mem_range.1 hs; omega)
  have hB0 : 0 ≤ ∏ s ∈ range M, b s :=
    Finset.prod_nonneg fun s hs => hb s (Finset.mem_range.1 hs)
  have hM0 : 0 ≤ Mbd := hP0.trans hP
  refine hw.trans (mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul hP hQ hQ0 hM0) hB hB0
    (mul_nonneg hM0 (hQ0.trans hQ))) hnv)

end Word

/-! ### Torus extraction `E:split-vector-cauchy` -/

section Torus

variable {ι : Type*} [Fintype ι]

/-- The torus point `(ϱ_i e^{iθ_i})_i`. -/
def torusPoint (ρ θ : ι → ℝ) : ι → ℂ := fun i => (ρ i : ℂ) * Complex.exp ((θ i : ℂ) * Complex.I)

/-- The monomial `z^r = ∏_i z_i^{r_i}`. -/
def monom (z : ι → ℂ) (r : ι → ℕ) : ℂ := ∏ i, z i ^ r i

/-- The phase `e^{-i ∑_i r_i θ_i}` of `E:split-vector-cauchy`. -/
def phase (r : ι → ℕ) (θ : ι → ℝ) : ℂ :=
  Complex.exp (((-∑ i, (r i : ℝ) * θ i : ℝ) : ℂ) * Complex.I)

/-- The angular box `[0, 2π]^ι`. -/
def angularBox (ι : Type*) : Set (ι → ℝ) := Set.univ.pi fun _ : ι => Set.Icc (0 : ℝ) (2 * π)

/-- Auxiliary (Lean route): `‖e^{-i r·θ}‖ = 1`. -/
theorem norm_phase (r : ι → ℕ) (θ : ι → ℝ) : ‖phase r θ‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- Auxiliary (Lean route): `∫_{[0,2π]} e^{imx} dx = 2π 1_{m=0}`. -/
theorem integral_circle_exp (m : ℤ) :
    ∫ x in Set.Icc (0 : ℝ) (2 * π), Complex.exp ((m : ℂ) * Complex.I * x) =
      if m = 0 then ((2 * π : ℝ) : ℂ) else 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by positivity)]
  split_ifs with hm
  · subst hm; simp
  · have hc : (m : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hm) Complex.I_ne_zero
    have h1 : Complex.exp ((m : ℂ) * Complex.I * ((2 * π : ℝ) : ℂ)) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I m]; congr 1; push_cast; ring
    rw [integral_exp_mul_complex hc, h1]
    simp

/-- Auxiliary (Lean route): `‖(ϱe^{iθ})^s‖ = ∏ ϱ_i^{s_i}` for `ϱ ≥ 0`. -/
theorem norm_monom_torusPoint (ρ θ : ι → ℝ) (hρ : ∀ i, 0 ≤ ρ i) (s : ι → ℕ) :
    ‖monom (torusPoint ρ θ) s‖ = ∏ i, ρ i ^ s i := by
  unfold monom torusPoint
  rw [norm_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [norm_pow, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (hρ i)]

/-- Auxiliary (Lean route): continuity of `θ ↦ (ϱe^{iθ})^s`. -/
theorem continuous_monom_torusPoint (ρ : ι → ℝ) (s : ι → ℕ) :
    Continuous fun θ : ι → ℝ => monom (torusPoint ρ θ) s := by
  unfold monom torusPoint
  fun_prop

/-- Auxiliary (Lean route): continuity of the phase. -/
theorem continuous_phase (r : ι → ℕ) : Continuous (phase (ι := ι) r) := by
  unfold phase; fun_prop

/-- Auxiliary (Lean route): Fubini for a product over the box. -/
theorem box_integral_prod (f : ι → ℝ → ℂ) :
    ∫ θ in angularBox ι, ∏ i, f i (θ i) = ∏ i, ∫ x in Set.Icc (0 : ℝ) (2 * π), f i x := by
  rw [angularBox, volume_pi, Measure.restrict_pi_pi]
  exact integral_fintype_prod_eq_prod (μ := fun _ => volume.restrict (Set.Icc (0 : ℝ) (2 * π))) f

omit [Fintype ι] in
/-- Auxiliary (Lean route): the box is compact. -/
theorem isCompact_angularBox : IsCompact (angularBox ι) :=
  isCompact_univ_pi fun _ => isCompact_Icc

/-- Auxiliary (Lean route): `|[0, 2π]^n| = (2π)^n`. -/
theorem volume_real_angularBox :
    (volume : Measure (ι → ℝ)).real (angularBox ι) = (2 * π) ^ Fintype.card ι := by
  rw [angularBox, Set.pi_univ_Icc, measureReal_def, Real.volume_Icc_pi]
  simp [Finset.prod_const, Finset.card_univ, Real.pi_pos.le]

/-- Auxiliary (Lean route): orthogonality of the exponentials on the torus,
`∫_{[0,2π]^n} ∏_i e^{i m_i θ_i} dθ = (2π)^n 1_{m=0}`. -/
theorem integral_box_exp [DecidableEq ι] (m : ι → ℤ) :
    ∫ θ in angularBox ι, ∏ i, Complex.exp ((m i : ℂ) * Complex.I * θ i) =
      if m = 0 then (((2 * π) ^ Fintype.card ι : ℝ) : ℂ) else 0 := by
  rw [box_integral_prod (fun i x => Complex.exp ((m i : ℂ) * Complex.I * x))]
  simp_rw [integral_circle_exp]
  split_ifs with hm
  · subst hm; simp [Finset.prod_const, Finset.card_univ]
  · obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
      by_contra h; push Not at h; exact hm (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- Auxiliary (Lean route): `e^{-ir·θ}(ϱe^{iθ})^s = ϱ^s ∏_i e^{i(s_i - r_i)θ_i}`. -/
theorem phase_monom_eq (ρ θ : ι → ℝ) (r s : ι → ℕ) :
    phase r θ * monom (torusPoint ρ θ) s =
      ((∏ i, ρ i ^ s i : ℝ) : ℂ) *
        ∏ i, Complex.exp ((((s i : ℤ) - (r i : ℤ) : ℤ) : ℂ) * Complex.I * θ i) := by
  unfold monom torusPoint phase
  have : Complex.exp (((-∑ i, (r i : ℝ) * θ i : ℝ) : ℂ) * Complex.I) =
      ∏ i, Complex.exp (-((r i : ℂ) * θ i) * Complex.I) := by
    rw [← Complex.exp_sum]; congr 1; push_cast; rw [← Finset.sum_neg_distrib, Finset.sum_mul]
  rw [this, ← Finset.prod_mul_distrib, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [mul_pow, ← Complex.exp_nat_mul]
  push_cast
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- **`E:split-vector-cauchy`** (main TeX lines 3973-3984): torus
coefficient extraction for an absolutely convergent multivariate power
series with values in a complex Banach space `E`.  If `ϱ_i ≥ 0`,
`∑_s ‖c_s‖ ϱ^s < ∞` and `Φ(ϱe^{iθ}) = ∑_s (ϱe^{iθ})^s c_s` on the torus,
then `θ ↦ e^{-ir·θ}Φ(ϱe^{iθ})` is integrable on `[0, 2π]^n` and
`(2π)^{-n} ∫_{[0,2π]^n} e^{-ir·θ} Φ(ϱe^{iθ}) dθ = ϱ^r c_r`.  The TeX's
display is this identity divided by `ϱ^r`. -/
theorem torus_coefficient [DecidableEq ι] (c : (ι → ℕ) → E) (Φ : (ι → ℂ) → E) (ρ : ι → ℝ)
    (r : ι → ℕ) (hρ : ∀ i, 0 ≤ ρ i)
    (hsum : Summable fun s : ι → ℕ => ‖c s‖ * ∏ i, ρ i ^ s i)
    (hΦ : ∀ θ : ι → ℝ, HasSum (fun s => monom (torusPoint ρ θ) s • c s) (Φ (torusPoint ρ θ))) :
    IntegrableOn (fun θ => phase r θ • Φ (torusPoint ρ θ)) (angularBox ι) ∧
      ((2 * π) ^ Fintype.card ι)⁻¹ • ∫ θ in angularBox ι, phase r θ • Φ (torusPoint ρ θ) =
        ((∏ i, ρ i ^ r i : ℝ) : ℂ) • c r := by
  set F : (ι → ℕ) → (ι → ℝ) → E := fun s θ => phase r θ • (monom (torusPoint ρ θ) s • c s)
    with hF
  have hFcont : ∀ s, Continuous (F s) := fun s =>
    (continuous_phase r).smul ((continuous_monom_torusPoint ρ s).smul continuous_const)
  have hFnorm : ∀ s θ, ‖F s θ‖ = ‖c s‖ * ∏ i, ρ i ^ s i := by
    intro s θ
    rw [hF]; dsimp only
    rw [norm_smul, norm_smul, norm_phase, norm_monom_torusPoint ρ θ hρ, one_mul, mul_comm]
  have hFsum : ∀ θ, HasSum (fun s => F s θ) (phase r θ • Φ (torusPoint ρ θ)) :=
    fun θ => (hΦ θ).const_smul _
  have hcont : Continuous fun θ => phase r θ • Φ (torusPoint ρ θ) := by
    have h := continuous_tsum hFcont hsum (fun s θ => (hFnorm s θ).le)
    exact h.congr fun θ => (hFsum θ).tsum_eq
  have hint : IntegrableOn (fun θ => phase r θ • Φ (torusPoint ρ θ)) (angularBox ι) :=
    hcont.continuousOn.integrableOn_compact isCompact_angularBox
  refine ⟨hint, ?_⟩
  have : IsFiniteMeasure (volume.restrict (angularBox ι)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact isCompact_angularBox.measure_lt_top⟩
  have hHas : HasSum (fun s => ∫ θ in angularBox ι, F s θ)
      (∫ θ in angularBox ι, phase r θ • Φ (torusPoint ρ θ)) :=
    hasSum_integral_of_dominated_convergence (fun s _ => ‖c s‖ * ∏ i, ρ i ^ s i)
      (fun s => (hFcont s).aestronglyMeasurable)
      (fun s => Filter.Eventually.of_forall fun θ => (hFnorm s θ).le)
      (Filter.Eventually.of_forall fun _ => hsum)
      (integrable_const _)
      (Filter.Eventually.of_forall hFsum)
  have hterm : ∀ s, ∫ θ in angularBox ι, F s θ =
      if s = r then ((((∏ i, ρ i ^ r i) * (2 * π) ^ Fintype.card ι : ℝ)) : ℂ) • c r
      else 0 := by
    intro s
    have h1 : ∀ θ, F s θ = (((∏ i, ρ i ^ s i : ℝ) : ℂ) *
        ∏ i, Complex.exp ((((s i : ℤ) - (r i : ℤ) : ℤ) : ℂ) * Complex.I * θ i)) • c s := by
      intro θ; rw [hF]; dsimp only; rw [smul_smul, phase_monom_eq]
    simp_rw [h1]
    rw [integral_smul_const, integral_const_mul,
      integral_box_exp (fun i => ((s i : ℤ) - (r i : ℤ)))]
    by_cases hs : s = r
    · subst hs
      have h0 : (fun i => ((s i : ℤ) - (s i : ℤ))) = 0 := by funext i; simp
      rw [ite_eq_left_of_eq_true _ _ (eq_true h0), ite_eq_left_of_eq_true _ _ (eq_true rfl),
        Complex.ofReal_mul]
    · have : (fun i => ((s i : ℤ) - (r i : ℤ))) ≠ 0 := by
        intro h; apply hs; funext i; have := congrFun h i; simp at this; omega
      simp [hs, this]
  have hHas2 : HasSum (fun s => ∫ θ in angularBox ι, F s θ)
      (((((∏ i, ρ i ^ r i) * (2 * π) ^ Fintype.card ι : ℝ)) : ℂ) • c r) := by
    simp_rw [hterm]; exact hasSum_ite_eq r _
  rw [hHas.unique hHas2, ← smul_assoc, Complex.real_smul]
  congr 1
  have h2 : (2 * π) ^ Fintype.card ι ≠ 0 := pow_ne_zero _ (by positivity)
  push_cast
  field_simp

/-- The Cauchy bound from `E:split-vector-cauchy` (main TeX lines
3985-3991): under the hypotheses of `torus_coefficient` with `ϱ_i > 0`, if
`‖Φ‖ ≤ K` on the torus `|z_i| = ϱ_i`, then `‖c_r‖ ≤ (∏_i ϱ_i^{-r_i}) K`. -/
theorem torus_coefficient_norm_le [DecidableEq ι] (c : (ι → ℕ) → E) (Φ : (ι → ℂ) → E)
    (ρ : ι → ℝ) (r : ι → ℕ) (hρ : ∀ i, 0 < ρ i)
    (hsum : Summable fun s : ι → ℕ => ‖c s‖ * ∏ i, ρ i ^ s i)
    (hΦ : ∀ θ : ι → ℝ, HasSum (fun s => monom (torusPoint ρ θ) s • c s) (Φ (torusPoint ρ θ)))
    (K : ℝ) (hK : ∀ θ : ι → ℝ, ‖Φ (torusPoint ρ θ)‖ ≤ K) :
    ‖c r‖ ≤ (∏ i, (ρ i ^ r i)⁻¹) * K := by
  obtain ⟨-, hform⟩ := torus_coefficient c Φ ρ r (fun i => (hρ i).le) hsum hΦ
  have hpos : 0 < ∏ i, ρ i ^ r i := Finset.prod_pos fun i _ => pow_pos (hρ i) _
  have hvol : (volume : Measure (ι → ℝ)) (angularBox ι) < ⊤ := isCompact_angularBox.measure_lt_top
  have hbound : ‖∫ θ in angularBox ι, phase r θ • Φ (torusPoint ρ θ)‖ ≤
      K * (2 * π) ^ Fintype.card ι := by
    rw [← volume_real_angularBox]
    refine norm_setIntegral_le_of_norm_le_const hvol fun θ _ => ?_
    rw [norm_smul, norm_phase, one_mul]; exact hK θ
  have hnorm := congrArg norm hform
  rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg hpos.le,
    Real.norm_of_nonneg (by positivity)] at hnorm
  have h2 : 0 < (2 * π) ^ Fintype.card ι := by positivity
  rw [Finset.prod_inv_distrib, ← div_eq_inv_mul, le_div_iff₀ hpos, mul_comm, ← hnorm]
  rw [inv_mul_le_iff₀ h2]
  linarith [hbound]

end Torus

/-! ### `E:split-radius-factorial` -/

section RadiusFactorial

/-- Auxiliary (Lean route): `ϱ_i^{-2} = (σ_i² d_i²/δ²)(h_i/k_i)^{4-α}`. -/
theorem splitRadius_inv_sq (alpha δ σ R h : ℝ) (k : ℕ) (hδ : 0 < δ) (hσ : 0 < σ) (hR : 0 < R)
    (hh : 0 < h) (hk : 1 ≤ k) :
    (splitRadius alpha δ σ R h k ^ 2)⁻¹ =
      σ ^ 2 * splitD R k ^ 2 / δ ^ 2 * (h / k) ^ (4 - alpha) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hD : 0 < splitD R k := by unfold splitD; positivity
  unfold splitRadius
  have hw : (((k : ℝ) / h) ^ (2 - alpha / 2)) ^ 2 = ((k : ℝ) / h) ^ (4 - alpha) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; congr 1; push_cast; ring
  have hinv : ((k : ℝ) / h) ^ (4 - alpha) * (h / k) ^ (4 - alpha) = 1 := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    rw [div_mul_div_comm, mul_comm (k : ℝ) h, div_self (by positivity), Real.one_rpow]
  have hpos : 0 < ((k : ℝ) / h) ^ (4 - alpha) := by positivity
  rw [div_pow, mul_pow, hw, inv_div]
  field_simp
  exact hinv.symm

/-- **`E:split-radius-factorial`** (main TeX lines 4022-4036), the three lines as two
bounds from the left-hand side: for `k_i ≥ 1`, `h_i, σ_i, R_α, δ > 0` and `α ≤ 3`,
`ϱ_i^{-2k_i} = (σ_i²d_i²/δ²)^{k_i}(h_i/k_i)^{(4-α)k_i}`,
`ϱ_i^{-2k_i} ≤ (12δ^{-2})^{k_i}(R_ασ_i²h_i^{4-α})^{k_i} k_i^{-(3-α)k_i}` and
`ϱ_i^{-2k_i} ≤ (12δ^{-2})^{k_i}(R_ασ_i²h_i^{4-α})^{k_i}/(k_i!)^{3-α}`. The comparison of the
last two right-hand sides is used inside the proof, not exported. -/
theorem split_radius_factorial (alpha δ σ R h : ℝ) (k : ℕ) (hδ : 0 < δ) (hσ : 0 < σ)
    (hR : 0 < R) (hh : 0 < h) (hk : 1 ≤ k) (hα : alpha ≤ 3) :
    (splitRadius alpha δ σ R h k ^ (2 * k))⁻¹ =
        (σ ^ 2 * splitD R k ^ 2 / δ ^ 2) ^ k * (h / k) ^ ((4 - alpha) * k) ∧
      (splitRadius alpha δ σ R h k ^ (2 * k))⁻¹ ≤
        (12 / δ ^ 2) ^ k * (R * σ ^ 2 * h ^ (4 - alpha)) ^ k * (k : ℝ) ^ (-((3 - alpha) * k)) ∧
      (splitRadius alpha δ σ R h k ^ (2 * k))⁻¹ ≤
        (12 / δ ^ 2) ^ k * (R * σ ^ 2 * h ^ (4 - alpha)) ^ k / (k ! : ℝ) ^ (3 - alpha) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hbase := splitRadius_inv_sq alpha δ σ R h k hδ hσ hR hh hk
  have hpow : (splitRadius alpha δ σ R h k ^ (2 * k))⁻¹ =
      ((splitRadius alpha δ σ R h k ^ 2)⁻¹) ^ k := by
    rw [pow_mul, inv_pow]
  have heq : (splitRadius alpha δ σ R h k ^ (2 * k))⁻¹ =
      (σ ^ 2 * splitD R k ^ 2 / δ ^ 2) ^ k * (h / k) ^ ((4 - alpha) * k) := by
    rw [hpow, hbase, mul_pow, ← Real.rpow_natCast ((h / k) ^ (4 - alpha)),
      ← Real.rpow_mul (by positivity)]
  have hper : (splitRadius alpha δ σ R h k ^ 2)⁻¹ ≤
      12 / δ ^ 2 * (R * σ ^ 2 * h ^ (4 - alpha)) * (k : ℝ) ^ (-(3 - alpha)) := by
    rw [hbase]
    have hD := splitD_sq_le R hR.le k hk
    have hsplit : (h / k) ^ (4 - alpha) = h ^ (4 - alpha) * (k : ℝ) ^ (-(4 - alpha)) := by
      rw [Real.div_rpow hh.le hk'.le, Real.rpow_neg hk'.le, div_eq_mul_inv]
    have hkk : (k : ℝ) * (k : ℝ) ^ (-(4 - alpha)) = (k : ℝ) ^ (-(3 - alpha)) := by
      rw [show (-(3 - alpha)) = 1 + (-(4 - alpha)) by ring, Real.rpow_add hk', Real.rpow_one]
    rw [hsplit]
    have hA : 0 ≤ h ^ (4 - alpha) * (k : ℝ) ^ (-(4 - alpha)) := by positivity
    calc σ ^ 2 * splitD R k ^ 2 / δ ^ 2 * (h ^ (4 - alpha) * (k : ℝ) ^ (-(4 - alpha)))
        ≤ σ ^ 2 * (12 * k * R) / δ ^ 2 * (h ^ (4 - alpha) * (k : ℝ) ^ (-(4 - alpha))) := by
          gcongr
      _ = 12 / δ ^ 2 * (R * σ ^ 2 * h ^ (4 - alpha)) *
            ((k : ℝ) * (k : ℝ) ^ (-(4 - alpha))) := by
          ring
      _ = _ := by rw [hkk]
  have hle1 : (splitRadius alpha δ σ R h k ^ (2 * k))⁻¹ ≤
      (12 / δ ^ 2) ^ k * (R * σ ^ 2 * h ^ (4 - alpha)) ^ k * (k : ℝ) ^ (-((3 - alpha) * k)) := by
    rw [hpow]
    have hnn : 0 ≤ (splitRadius alpha δ σ R h k ^ 2)⁻¹ := by positivity
    calc ((splitRadius alpha δ σ R h k ^ 2)⁻¹) ^ k
        ≤ (12 / δ ^ 2 * (R * σ ^ 2 * h ^ (4 - alpha)) * (k : ℝ) ^ (-(3 - alpha))) ^ k :=
          pow_le_pow_left₀ hnn hper k
      _ = _ := by
          rw [mul_pow, mul_pow, ← Real.rpow_natCast ((k : ℝ) ^ (-(3 - alpha))),
            ← Real.rpow_mul hk'.le]
          congr 2; ring
  refine ⟨heq, hle1, hle1.trans ?_⟩
  have hfac : (k ! : ℝ) ≤ (k : ℝ) ^ k := by exact_mod_cast Nat.factorial_le_pow k
  have hfpos : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
  have h3 : 0 ≤ 3 - alpha := by linarith
  have hkey : (k : ℝ) ^ (-((3 - alpha) * k)) ≤ ((k ! : ℝ) ^ (3 - alpha))⁻¹ := by
    have hpk : (k : ℝ) ^ (-((3 - alpha) * k)) = (((k : ℝ) ^ k) ^ (3 - alpha))⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hk'.le, Real.rpow_neg hk'.le]
      congr 2; ring
    rw [hpk]
    exact inv_anti₀ (by positivity) (Real.rpow_le_rpow hfpos.le hfac h3)
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left hkey (by positivity)

/-- **`E:split-radius-factorial` under the manuscript's hypotheses** (main
TeX lines 4022-4036; `L:fixed-split`, lines 3675-3680, assumes `R_α > 0`
and `σ_i > 0`, under the section's `H:homog` with
`R_α = απ μ(B_1)/(2 sin(πα/2))`): for `k_i ≥ 1`, `h_i > 0` and any `δ > 0`
(the TeX's `δ_{α/2}`), `ϱ_i^{-2k_i} ≤ (12δ^{-2})^{k_i}
(R_ασ_i²h_i^{4-α})^{k_i}/(k_i!)^{3-α}`.  `H:homog` is used for `α < 2`;
`_hRdef` is carried and unused. -/
theorem split_radius_factorial_paper {d : ℕ} {alpha alpha0 : ℝ}
    {Γ μ : Measure (HomogHypothesis.Rd d)}
    (hH : HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ) {R δ σ h : ℝ} {k : ℕ}
    (_hRdef : R = alpha * π * (μ (Metric.ball 0 1)).toReal / (2 * Real.sin (π * alpha / 2)))
    (hRpos : 0 < R) (hσ : 0 < σ) (hh : 0 < h) (hk : 1 ≤ k) (hδ : 0 < δ) :
    (splitRadius alpha δ σ R h k ^ (2 * k))⁻¹ ≤
      (12 / δ ^ 2) ^ k * (R * σ ^ 2 * h ^ (4 - alpha)) ^ k / (k ! : ℝ) ^ (3 - alpha) := by
  obtain ⟨-, hα2, -⟩ := homog_alpha_range hH
  exact (split_radius_factorial alpha δ σ R h k hδ hσ hRpos hh hk (by linarith)).2.2

end RadiusFactorial

/-! ### `E:split-before-absorption` -/

section BeforeAbsorption

/-- The per-color factor of `E:split-before-absorption` (main TeX lines
4005-4014, with the metric product of lines 4016-4019): `1` if `k_i = 0`;
`R_α σ_i² h_i² λ^{α-2}` on the cross set `𝒞` (`k_i = 1`, `(r_i,q_i) = (1,1)`);
`ϱ_i^{-2k_i} (1 + k_i/(λh_i))^{ℓ_i}` on `ℬ`. -/
def beforeFactor (alpha δ R σ h lam : ℝ) (κ : ℕ) (p : ℕ × ℕ) : ℝ :=
  if κ = 0 then 1
  else if κ = 1 ∧ p = (1, 1) then R * σ ^ 2 * h ^ 2 * lam ^ (alpha - 2)
  else (splitRadius alpha δ σ R h κ ^ (2 * κ))⁻¹ * (1 + κ / (lam * h)) ^ splitEll p

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The cross set `𝒞 = {i : k_i = 1, r_i = q_i = 1}` (main TeX line 3695). -/
def crossSet (κ : ι → ℕ) (p : ι → ℕ × ℕ) : Finset ι :=
  univ.filter fun i => κ i = 1 ∧ p i = (1, 1)

/-- The background set `ℬ = ℐ ∖ 𝒞` (main TeX lines 3694-3696). -/
def backSet (κ : ι → ℕ) (p : ι → ℕ × ℕ) : Finset ι :=
  univ.filter fun i => κ i ≠ 0 ∧ ¬(κ i = 1 ∧ p i = (1, 1))

/-- `𝒜_r = {i ∈ ℬ : r_i > 0}` (main TeX lines 3750-3751). -/
def copyFirst (κ : ι → ℕ) (p : ι → ℕ × ℕ) : Finset ι := (backSet κ p).filter fun i => 0 < (p i).1

/-- `𝒜_q = {i ∈ ℬ : q_i > 0}` (main TeX line 3751). -/
def copySecond (κ : ι → ℕ) (p : ι → ℕ × ℕ) : Finset ι :=
  (backSet κ p).filter fun i => 0 < (p i).2

/-- `c_i = σ_i √R_α λ^{(α-2)/2}` (`E:split-fresh-insertion`, main TeX
lines 3890-3894). -/
def insertConst (alpha R lam σ : ℝ) : ℝ := σ * √R * lam ^ ((alpha - 2) / 2)

omit [Fintype ι] [DecidableEq ι] in
/-- Auxiliary (Lean route): `c_i² = R_α σ_i² λ^{α-2}`. -/
theorem insertConst_sq (alpha R lam σ : ℝ) (hR : 0 ≤ R) (hlam : 0 < lam) :
    insertConst alpha R lam σ ^ 2 = R * σ ^ 2 * lam ^ (alpha - 2) := by
  unfold insertConst
  rw [mul_pow, mul_pow, Real.sq_sqrt hR, ← Real.rpow_natCast (lam ^ ((alpha - 2) / 2)),
    ← Real.rpow_mul hlam.le]
  push_cast
  rw [show (alpha - 2) / 2 * 2 = alpha - 2 by ring]; ring

omit [DecidableEq ι] in
/-- The metric product (main TeX lines 4016-4019):
`D_{𝒜_r} D_{𝒜_q} = ∏_{i∈ℬ} (1 + k_i/(λh_i))^{ℓ_i}`. -/
theorem metric_product_eq (lam : ℝ) (h : ι → ℝ) (κ : ι → ℕ) (p : ι → ℕ × ℕ) :
    metricD lam h κ (copyFirst κ p) * metricD lam h κ (copySecond κ p) =
      ∏ i ∈ backSet κ p, (1 + κ i / (lam * h i)) ^ splitEll (p i) := by
  unfold metricD copyFirst copySecond
  rw [Finset.prod_filter, Finset.prod_filter, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  unfold splitEll
  split_ifs <;> simp [sq]

/-- The per-copy bound of `E:split-vector-cauchy` with
`E:interval-cross-vector` (main TeX lines 3963-3988):
`(∏_{i∈S} ϱ_i^{-deg_i}) M D_S ‖v‖ ∏_{i∈𝒞} c_i h_i`. -/
def copyBound (alpha δ R lam Mbd nv : ℝ) (σ h : ι → ℝ) (κ : ι → ℕ) (p : ι → ℕ × ℕ)
    (deg : ι → ℕ) (S : Finset ι) : ℝ :=
  (∏ i ∈ S, (splitRadius alpha δ (σ i) R (h i) (κ i) ^ deg i)⁻¹) * Mbd * metricD lam h κ S * nv *
    ∏ i ∈ crossSet κ p, insertConst alpha R lam (σ i) * h i

/-- Auxiliary (Lean route): the product of the two per-copy bounds is
`M² ‖v‖² ∏_i beforeFactor_i`, using `r_i + q_i = 2k_i` (main TeX lines
4016-4020). -/
theorem two_copy_product (alpha δ R lam Mbd nv : ℝ) (σ h : ι → ℝ) (κ : ι → ℕ)
    (p : ι → ℕ × ℕ) (hp : ∀ i, (p i).1 + (p i).2 = 2 * κ i) (hR : 0 ≤ R) (hlam : 0 < lam) :
    copyBound alpha δ R lam Mbd nv σ h κ p (fun i => (p i).1) (copyFirst κ p) *
        copyBound alpha δ R lam Mbd nv σ h κ p (fun i => (p i).2) (copySecond κ p) =
      Mbd ^ 2 * nv ^ 2 * ∏ i, beforeFactor alpha δ R (σ i) (h i) lam (κ i) (p i) := by
  unfold copyBound metricD
  have e : ∀ (S : Finset ι) (g : ι → ℝ), ∏ i ∈ S, g i = ∏ i, if i ∈ S then g i else 1 := by
    intro S g; rw [Finset.prod_ite_mem, Finset.univ_inter]
  rw [e (copyFirst κ p), e (copyFirst κ p), e (copySecond κ p), e (copySecond κ p),
    e (crossSet κ p)]
  have hreg : ∀ (A B C D E : ℝ), A * Mbd * B * nv * E * (C * Mbd * D * nv * E) =
      Mbd ^ 2 * nv ^ 2 * (A * B * (C * D) * E ^ 2) := by intros; ring
  rw [hreg]
  congr 1
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hpi := hp i
  simp only [copyFirst, copySecond, backSet, crossSet, Finset.mem_filter, Finset.mem_univ,
    true_and]
  unfold beforeFactor
  by_cases h0 : κ i = 0
  · have h1 : (p i).1 = 0 := by omega
    have h2 : (p i).2 = 0 := by omega
    simp [h0, h1, h2]
  by_cases hc : κ i = 1 ∧ p i = (1, 1)
  · obtain ⟨hk1, hp1⟩ := hc
    simp only [hk1, hp1, one_ne_zero, ne_eq, not_true_eq_false, and_false, false_and, and_self,
      one_mul, not_false_eq_true, ↓reduceIte]
    rw [mul_pow, insertConst_sq alpha R lam (σ i) hR hlam]; ring
  · simp only [h0, hc, ne_eq, not_false_eq_true, true_and, ite_false]
    unfold splitEll
    have hsum : 2 * κ i = (p i).1 + (p i).2 := hpi.symm
    rw [hsum, pow_add, mul_inv]
    by_cases hr : 0 < (p i).1 <;> by_cases hq : 0 < (p i).2
    · simp [hr, hq]; ring
    · have : (p i).2 = 0 := by omega
      simp [hr, this]
    · have : (p i).1 = 0 := by omega
      simp [hq, this]
    · omega

/-- **`E:split-before-absorption`** (main TeX lines 3997-4020), scalar
assembly: if `|⟨U_r v, U_q v⟩| ≤ k² u_r u_q` (Cauchy-Schwarz and the norm
comparisons of lines 3997-4004, with `u_r, u_q ≥ 0` the `λ`-norms) and each
`u` is at most its per-copy bound `copyBound` (with degrees `r_i` on `𝒜_r`
and `q_i` on `𝒜_q`), then `|⟨U_r v, U_q v⟩| ≤ k² M² ‖v‖² ∏_i beforeFactor_i`,
which is the TeX's right side with `M = M_k` and `‖v‖ = ‖v‖_{1/T}`.
Requires `r_i + q_i = 2k_i`, `R_α ≥ 0`, `λ > 0`. -/
theorem split_before_absorption (alpha δ R lam Mbd nv X ur uq : ℝ) (k : ℕ) (σ h : ι → ℝ)
    (κ : ι → ℕ) (p : ι → ℕ × ℕ)
    (hp : ∀ i, (p i).1 + (p i).2 = 2 * κ i) (hR : 0 ≤ R) (hlam : 0 < lam)
    (hX : X ≤ (k : ℝ) ^ 2 * ur * uq) (hur : 0 ≤ ur) (huq : 0 ≤ uq)
    (hr : ur ≤ copyBound alpha δ R lam Mbd nv σ h κ p (fun i => (p i).1) (copyFirst κ p))
    (hq : uq ≤ copyBound alpha δ R lam Mbd nv σ h κ p (fun i => (p i).2) (copySecond κ p)) :
    X ≤ (k : ℝ) ^ 2 * Mbd ^ 2 * nv ^ 2 *
      ∏ i, beforeFactor alpha δ R (σ i) (h i) lam (κ i) (p i) := by
  have := mul_le_mul hr hq huq (hur.trans hr)
  rw [two_copy_product alpha δ R lam Mbd nv σ h κ p hp hR hlam] at this
  calc X ≤ (k : ℝ) ^ 2 * ur * uq := hX
    _ = (k : ℝ) ^ 2 * (ur * uq) := by ring
    _ ≤ (k : ℝ) ^ 2 * (Mbd ^ 2 * nv ^ 2 *
          ∏ i, beforeFactor alpha δ R (σ i) (h i) lam (κ i) (p i)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by ring

end BeforeAbsorption

/-! ### `E:split-explicit-constant` -/

section Absorption

/-- `C_split = 100^8 e^8 max{1, 12 δ^{-2}}` (`E:split-explicit-constant`,
main TeX lines 4043-4046, with `δ` for `δ_{α/2}`). -/
def splitConst (δ : ℝ) : ℝ := 100 ^ 8 * Real.exp 8 * max 1 (12 / δ ^ 2)

/-- Auxiliary (Lean route): `C_split ≥ 0`. -/
theorem splitConst_nonneg (δ : ℝ) : 0 ≤ splitConst δ := by
  unfold splitConst; positivity

/-- Auxiliary (Lean route): the per-color absorption,
`beforeFactor_i ≤ (max{1, 12δ^{-2}} R_α)^{k_i} · splitFactor_i` (main TeX
lines 4022-4046), for `δ, σ_i, R_α, h_i, λ > 0` and `α ≤ 3`. -/
theorem beforeFactor_le (alpha δ R σ h lam : ℝ) (κ : ℕ) (p : ℕ × ℕ) (hδ : 0 < δ) (hσ : 0 < σ)
    (hR : 0 < R) (hh : 0 < h) (hlam : 0 < lam) (hα : alpha ≤ 3) :
    beforeFactor alpha δ R σ h lam κ p ≤
      (max 1 (12 / δ ^ 2) * R) ^ κ * splitFactor alpha σ h lam κ p := by
  have hC1 : (1 : ℝ) ≤ max 1 (12 / δ ^ 2) := le_max_left _ _
  unfold beforeFactor splitFactor
  split_ifs with h0 h1
  · subst h0; simp
  · obtain ⟨rfl, -⟩ := h1
    rw [pow_one]
    have hX : 0 ≤ σ ^ 2 * h ^ 2 * lam ^ (alpha - 2) := by positivity
    nlinarith [mul_nonneg (sub_nonneg.2 hC1) (mul_nonneg hR.le hX)]
  · have hk : 1 ≤ κ := Nat.one_le_iff_ne_zero.2 h0
    obtain ⟨-, -, hfac⟩ := split_radius_factorial alpha δ σ R h κ hδ hσ hR hh hk hα
    have hD : 0 ≤ (1 + (κ : ℝ) / (lam * h)) ^ splitEll p := by positivity
    calc (splitRadius alpha δ σ R h κ ^ (2 * κ))⁻¹ * (1 + (κ : ℝ) / (lam * h)) ^ splitEll p
        ≤ (12 / δ ^ 2) ^ κ * (R * σ ^ 2 * h ^ (4 - alpha)) ^ κ / (κ ! : ℝ) ^ (3 - alpha) *
            (1 + (κ : ℝ) / (lam * h)) ^ splitEll p := mul_le_mul_of_nonneg_right hfac hD
      _ ≤ (max 1 (12 / δ ^ 2)) ^ κ * (R * σ ^ 2 * h ^ (4 - alpha)) ^ κ /
            (κ ! : ℝ) ^ (3 - alpha) * (1 + (κ : ℝ) / (lam * h)) ^ splitEll p := by
          gcongr
          exact le_max_right _ _
      _ = (max 1 (12 / δ ^ 2) * R) ^ κ * ((σ ^ 2 * h ^ (4 - alpha)) ^ κ /
            (κ ! : ℝ) ^ (3 - alpha) * (1 + (κ : ℝ) / (lam * h)) ^ splitEll p) := by
          simp only [mul_pow]; ring

/-- Auxiliary (Lean route): `beforeFactor_i ≥ 0`. -/
theorem beforeFactor_nonneg (alpha δ R σ h lam : ℝ) (κ : ℕ) (p : ℕ × ℕ) (hδ : 0 < δ)
    (hσ : 0 < σ) (hR : 0 < R) (hh : 0 < h) (hlam : 0 < lam) :
    0 ≤ beforeFactor alpha δ R σ h lam κ p := by
  unfold beforeFactor
  split_ifs with h0 h1
  · exact zero_le_one
  · positivity
  · have := splitRadius_pos alpha δ σ R h κ hδ hσ hR hh (Nat.one_le_iff_ne_zero.2 h0)
    positivity

/-- **Absorption into `C_split`** (`E:split-before-absorption` implies
`E:fixed-split-bound` with `E:split-explicit-constant`, main TeX lines
4022-4050): for `∑_{i∈s} k_i = k ≥ 1`, `δ, R_α, λ > 0`, `σ_i, h_i > 0`,
`α ≤ 3` and `V ≥ 0`, `X ≤ k² M_k² V ∏ beforeFactor_i` implies
`X ≤ k² C_split^k R_α^k V ∏ splitFactor_i`.  (`|𝒞| + ∑_ℬ k_i = k`, line 4038,
is `∑ k_i = k`.) -/
theorem split_absorption {ι : Type*} (s : Finset ι) (alpha δ R lam X V : ℝ) (σ h : ι → ℝ)
    (κ : ι → ℕ) (p : ι → ℕ × ℕ) (k : ℕ) (hk : 1 ≤ k) (hsum : ∑ i ∈ s, κ i = k)
    (hδ : 0 < δ) (hR : 0 < R) (hlam : 0 < lam) (hα : alpha ≤ 3) (hV : 0 ≤ V)
    (hσ : ∀ i ∈ s, 0 < σ i) (hh : ∀ i ∈ s, 0 < h i)
    (hX : X ≤ (k : ℝ) ^ 2 * Mk k ^ 2 * V *
      ∏ i ∈ s, beforeFactor alpha δ R (σ i) (h i) lam (κ i) (p i)) :
    X ≤ (k : ℝ) ^ 2 * splitConst δ ^ k * R ^ k * V *
      ∏ i ∈ s, splitFactor alpha (σ i) (h i) lam (κ i) (p i) := by
  have hprod : ∏ i ∈ s, beforeFactor alpha δ R (σ i) (h i) lam (κ i) (p i) ≤
      (max 1 (12 / δ ^ 2) * R) ^ k * ∏ i ∈ s, splitFactor alpha (σ i) (h i) lam (κ i) (p i) := by
    calc ∏ i ∈ s, beforeFactor alpha δ R (σ i) (h i) lam (κ i) (p i)
        ≤ ∏ i ∈ s, ((max 1 (12 / δ ^ 2) * R) ^ κ i *
            splitFactor alpha (σ i) (h i) lam (κ i) (p i)) :=
          Finset.prod_le_prod₀
            (fun i hi => beforeFactor_nonneg alpha δ R (σ i) (h i) lam (κ i) (p i) hδ (hσ i hi)
              hR (hh i hi) hlam)
            fun i hi => beforeFactor_le alpha δ R (σ i) (h i) lam (κ i) (p i) hδ (hσ i hi) hR
              (hh i hi) hlam hα
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum]
  have hb : 0 ≤ ∏ i ∈ s, beforeFactor alpha δ R (σ i) (h i) lam (κ i) (p i) :=
    Finset.prod_nonneg fun i hi =>
      beforeFactor_nonneg alpha δ R (σ i) (h i) lam (κ i) (p i) hδ (hσ i hi) hR (hh i hi) hlam
  have hMk := Mk_sq_le k hk
  calc X ≤ (k : ℝ) ^ 2 * Mk k ^ 2 * V *
        ∏ i ∈ s, beforeFactor alpha δ R (σ i) (h i) lam (κ i) (p i) := hX
    _ ≤ (k : ℝ) ^ 2 * (100 ^ 8 * Real.exp 8) ^ k * V *
          ((max 1 (12 / δ ^ 2) * R) ^ k *
            ∏ i ∈ s, splitFactor alpha (σ i) (h i) lam (κ i) (p i)) := by
        gcongr
    _ = (k : ℝ) ^ 2 * splitConst δ ^ k * R ^ k * V *
          ∏ i ∈ s, splitFactor alpha (σ i) (h i) lam (κ i) (p i) := by
        unfold splitConst; rw [mul_pow, mul_pow]; ring

/-- **`E:split-explicit-constant` under the manuscript's hypotheses**
(main TeX lines 4022-4050; `L:fixed-split`, lines 3675-3680, assumes
`R_α > 0`, `σ_i > 0`, `k ≥ 1`, `λ = k/T`, under the section's `H:homog` with
`R_α = απ μ(B_1)/(2 sin(πα/2))`): for every degree split `κ` of `k` over
`M` colors and every `p ∈ ∏_i antidiagonal(2κ_i)`, the bound
`E:split-before-absorption` (`|Q p| ≤ k² M_k² V ∏ beforeFactor_i` with
`λ = k/T`) implies `E:fixed-split-bound` with `C_split = splitConst δ`,
in exactly the form of the `hfixed` hypothesis of
`IntervalScalarCompleted.interval_coefficient_assembly_paper_completed`.
`H:homog` is used for `α < 2`; `_hRdef` is carried and unused.  `δ > 0` is
arbitrary (the TeX's `δ_{α/2}`). -/
theorem split_explicit_constant_paper {d : ℕ} {alpha alpha0 : ℝ}
    {Γ μ : Measure (HomogHypothesis.Rd d)}
    (hH : HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ)
    {R T δ V : ℝ} {M k : ℕ} (h σ : Fin M → ℝ) (Q : (Fin M → ℕ × ℕ) → ℝ)
    (_hRdef : R = alpha * π * (μ (Metric.ball 0 1)).toReal / (2 * Real.sin (π * alpha / 2)))
    (hRpos : 0 < R) (hk : 1 ≤ k) (hT : 0 < T) (hV : 0 ≤ V) (hδ : 0 < δ)
    (hh : ∀ i, 0 < h i) (hσpos : ∀ i, 0 < σ i)
    (hbefore : ∀ κ ∈ (univ : Finset (Fin M)).finsuppAntidiag k,
      ∀ p ∈ Fintype.piFinset (fun i => antidiagonal (2 * κ i)),
        |Q p| ≤ (k : ℝ) ^ 2 * Mk k ^ 2 * V *
          ∏ i, beforeFactor alpha δ R (σ i) (h i) (k / T) (κ i) (p i)) :
    ∀ κ ∈ (univ : Finset (Fin M)).finsuppAntidiag k,
      ∀ p ∈ Fintype.piFinset (fun i => antidiagonal (2 * κ i)),
        |Q p| ≤ (k : ℝ) ^ 2 * splitConst δ ^ k * R ^ k * V *
          ∏ i, splitFactor alpha (σ i) (h i) (k / T) (κ i) (p i) := by
  obtain ⟨-, hα2, -⟩ := homog_alpha_range hH
  intro κ hκ p hp
  have hsum : ∑ i, κ i = k := ((mem_finsuppAntidiag).1 hκ).1
  have hlam : (0 : ℝ) < k / T := div_pos (by exact_mod_cast hk) hT
  exact split_absorption univ alpha δ R (k / T) |Q p| V σ h (fun i => κ i) p k hk hsum hδ hRpos
    hlam (by linarith) hV (fun i _ => hσpos i) (fun i _ => hh i) (hbefore κ hκ p hp)

/-- **Step row of `P:interval-coefficients` with the absorption of
`L:fixed-split` done** (main TeX lines 4057-4060; proof 4068-4082 and
4147-4228): `IntervalScalarCompleted.interval_coefficient_assembly_paper_completed`
with its input `hfixed` (`E:fixed-split-bound`) replaced by the
before-absorption bound `hbefore` (`E:split-before-absorption`, lines
4005-4014) and `C_split = splitConst δ`.  Every other hypothesis is exactly
that of `interval_coefficient_assembly_paper_completed`; `hsplits` and
`hbefore` remain supplied, and the narrowings recorded there (`R_α > 0`,
`σ_i > 0`, zero-noise case and sign reduction not covered) are unchanged. -/
theorem interval_coefficient_of_before_absorption_paper {d : ℕ} {alpha alpha0 : ℝ}
    {Γ μ : Measure (HomogHypothesis.Rd d)}
    (hH : HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ)
    {R T L c δ V coef : ℝ} {M k : ℕ}
    (h σ : Fin M → ℝ) (Q : (Fin M → ℕ × ℕ) → ℝ)
    (hRdef : R = alpha * π * (μ (Metric.ball 0 1)).toReal / (2 * Real.sin (π * alpha / 2)))
    (hRpos : 0 < R) (hk : 1 ≤ k) (hT : 0 < T) (hV : 0 ≤ V) (hδ : 0 < δ)
    (hh : ∀ i, 0 < h i) (hσpos : ∀ i, 0 < σ i)
    (hlen : ∀ i : Fin M, h i ≤ L * T / ((i : ℕ) + 1 : ℕ))
    (hσ : ∀ i, σ i ^ 2 ≤ c * h i ^ (-alpha0))
    (hsplits : coef = ∑ κ ∈ (univ : Finset (Fin M)).finsuppAntidiag k,
      ∑ p ∈ Fintype.piFinset (fun i => antidiagonal (2 * κ i)), Q p)
    (hbefore : ∀ κ ∈ (univ : Finset (Fin M)).finsuppAntidiag k,
      ∀ p ∈ Fintype.piFinset (fun i => antidiagonal (2 * κ i)),
        |Q p| ≤ (k : ℝ) ^ 2 * Mk k ^ 2 * V *
          ∏ i, beforeFactor alpha δ R (σ i) (h i) (k / T) (κ i) (p i)) :
    |coef| ≤ (12 * max c 0 * max 1 L ^ (4 - alpha - alpha0) * splitConst δ *
        InventoryProduct.inventoryConst alpha alpha0) ^ k * R ^ k *
      T ^ ((4 - alpha - alpha0) * k) / (k ! : ℝ) ^ (3 - alpha) * V :=
  IntervalScalarCompleted.interval_coefficient_assembly_paper_completed hH h σ Q hRdef hRpos hk hT
    hV (splitConst_nonneg δ) hh hσpos hlen hσ hsplits
    (split_explicit_constant_paper hH h σ Q hRdef hRpos hk hT hV hδ hh hσpos hbefore)

end Absorption

end StratonovichHAMSecondMoment.FixedSplitCore
