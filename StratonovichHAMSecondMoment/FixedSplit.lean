module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

The assembly of `L:fixed-split` (A fixed degree-split estimate) of
`notes/notes_stratonovich_ham_second_moment.tex` (main TeX file; all line
numbers below are at revision 39f2597a): statement lines 3675-3716
(`E:fixed-split-bound`, 3702-3713), proof 3718-4051.  Wave item L10-FS1, on
the model-free core `FixedSplitCore` (L10-FS0) and the Fock layer
`HermiteFock`/`FockForm` (L9-H).

The Fock model and the identification of `𝒵_S`.  The Gaussian modes are
`Fin m`, mode `j` belonging to the color (interval) `col j`; a cutoff vector
of Gaussian `L²` with values in the spatial band space `X` is a coefficient
vector `f : cutIdx col N → X` in the normalized Hermite basis, where
`cutIdx col N` is the set of multi-indices with color degree `≤ N_i` in every
color (the range of `P = ⊗_i P_{N_i}`, here with `N_i = 2k_i`).  Phase
vectors are pairs `(f, g)`; the phase norm `‖(f,g)‖_ρ² = ‖f‖² +
‖A_ρ^{-1/2} g‖²` (lines 3370-3372) is the norm of `fockEmb S ρ (f, g)` in
`ℓ²`, with `S_ρ` for `A_ρ^{-1/2}` (the coefficient norm is the Gaussian `L²`
norm by `HermiteFock.integral_norm_sq_iota`).  The TeX's tensor subspace
`𝒵_S = ⊗_{𝒜} 𝒢_i^{≤N_i} ⊗ ⊗_S 𝒢_i^{(1)} ⊗ ⊗_{𝒞∖S} 𝒢_i^{(0)}`, every
omitted color in its vacuum (lines 3845-3855), is spanned by the Hermite
functions whose multi-index has color degree one on `S`, zero off `𝒜 ∪ S`
and `≤ N_i` on `𝒜`; so the phase over `𝒵_S` is `fockZ`: both components
supported on those multi-indices (`ZCoef`).  The insertion
`J_i(u, w) = (0, σ_i B_i u)` (line 3861) is `fockJ`, with the color-`i`
field `∑_{col j = i} g_j ⊗ S_b M_{e_j} S_b` acting by `HermiteFock.gmul` and
followed by the cutoff.

Formalized (proved):
* the common partition (`E:split-partition`, lines 3779-3790): `cutSet`,
  `cutPt` (sorted by `Finset.orderEmbOfFin`), `cutPt_spec`, `nCut_le`
  (`M ≤ 2|𝒜| + |𝒞| + 1`);
* the chronological word (lines 3907-3916) `word` and `E:split-word-product`
  for it (`word_chain`): the inserted sets `{i ∈ 𝒞 : t_i ≤ τ_j}` describe
  every partial word (lines 3895-3898, `insertedSet_succ`), and the norms of
  the partial words feed `FixedSplitCore.split_word_bound`,
  `split_segment_product_paper` and `interval_copy_metric_paper`;
* `E:split-fresh-insertion` (lines 3861-3894) on the Fock model:
  `coef_insertion` (vacuum insertion on coefficients: on a color in its
  vacuum the field acts by creation only and its mode terms have disjoint
  supports; the coefficient form of `HermiteFock.vacuum_insertion_isometry`
  with the other colors as an arbitrary factor), `fock_insertion`
  (`J_i(𝒵_S) ⊆ 𝒵_{S∪{i}}` and the column bound) and `fock_insertion_bound`
  (`‖J_i x‖_ρ ≤ c_i ‖x‖_ρ` for `ρ ≥ λ`, `c_i = σ_i √R_α λ^{(α-2)/2}`), from
  the named input `FockForm.FockColumn` through `FockForm.interval_contractions`
  (band compression, `fockColumn_masked`);
* the vacuum start (`vacPhase_mem`, `fockEmb_vacPhase`) and the identities
  between phase norms (`fockEmb_cmp`, lines 3811-3817);
* `E:interval-cross-vector` from `E:interval-cross-cube` (lines 3947-3967):
  the simplices `D_π` are measurable and pairwise disjoint, `∑_π |D_π| ≤
  ∏_{i∈𝒞} h_i` (`sum_volume_simplex_le`), and Minkowski
  (`dysonSum_norm_le`); no factor `m!` enters;
* `E:split-vector-cauchy` (lines 3973-3991) through
  `FixedSplitCore.torus_coefficient_norm_le` in the phase norm
  (`copy_coefficient_bound`: the per-copy bound);
* `E:split-before-absorption` and `E:fixed-split-bound` (lines 3997-4050):
  Cauchy-Schwarz, `‖w‖_{1/T} ≤ k‖w‖_λ`, `‖v‖_λ ≤ ‖v‖_{1/T}` and the FS0
  absorption (`fixed_split_abstract`, `fixed_split`, `fixed_split_paper`);
* `interval_coefficient_assembly_paper_fixed`: the step row
  `IntervalScalarCompleted.interval_coefficient_assembly_paper_completed`
  with its input `hfixed` discharged (`C_split = splitConst δ`).

Supplied inputs (named `Prop`s; the first is reused from `FockForm`):
* `FockForm.FockColumn` (`E:interval-column`, lines 3388-3391) for the modes
  of each color, at every `ρ > 0`;
* `SegmentBound` (`L:interval-complex`, lines 3473-3491, as applied in
  `E:split-segment-product`, lines 3760-3801): the segment bound
  `‖P_z(t,s)‖ ≤ 100 e^{2Λ(t-s)}` on intervals free of background endpoints;
* `DysonCrossCube` (`E:interval-cross-cube`, lines 3937-3960);
* `BackgroundPreserves` (lines 3855-3859): the background propagator
  preserves the phase over every `𝒵_S`;
* `EntireCoefficients` (lines 3729-3733): absolute convergence of the ordinary
  coefficients on every polydisc.
The background propagator `P_z(t, s)` and the ordinary coefficients `c_r`
(`U_r v = c_r`) of the cutoff evolution are not constructed in the package;
they are parameters, constrained only by these inputs.  `SplitInputs`
bundles the inputs of one split.

Hypotheses made explicit (properties of the abstract spatial operators, as
in `FockForm`): `S_ρ` symmetric with `‖S_ρ‖ ≤ ρ^{-1}` and the spectral
comparison `‖S_{ρ'} g‖ ≤ max{1, ρ/ρ'} ‖S_ρ g‖` (from `A_{ρ'}^{-1} ≤ q²
A_ρ^{-1}`, line 3817); `M_{e_j}` symmetric; `S_b` a symmetric idempotent
commuting with `S_ρ`; `V ≥ ‖(u, w)‖_{1/T}²`; `I_i^T = (a_i, b_i)` with
`b_i - a_i ≤ h_i` and, for the cross colors, `[a_i, b_i] ⊆ [0, T]`.

Differences from the TeX.  `δ > 0` is a free parameter: it is not specialized to
`StaticPhaseCauchy.deltaA (α/2)` (the TeX's `δ_{α/2}` of `L:complex-phase`, defined there);
the inputs are taken at that `δ`.  The reductions of lines 3736-3741 (`k_i = 0`, zero-length
intervals) are not needed: empty intervals give empty simplices or inactive
colors.  The identity norms are bounded by the general telescoping lemma at
every cut (no use of `q_j = 1` at insertion cuts).  The insertion bound is
proved in every norm `ρ ≥ λ` (the TeX uses `ρ = Λ(t_i)`).  `DysonCrossCube`
is required only on the torus `|z_i| = ϱ_i`.  The comparison of the
projected initial phase with the original data (line 4049) is the free bound
`V`.  In the step row, `Q_{r,q}` stays abstract: the new hypothesis `hQ`
bounds `|Q_{r,q}|` by the modulus of the cutoff inner product (in the TeX
`Q_{r,q}` is that inner product, line 4142, and the cutoff preserves the
selected coefficients exactly, lines 4163-4170, by `L:finite-word-cutoff`).

Junk values: none.  Real powers have positive bases (`ρ, λ > 0`); the Dyson
integrals are Bochner integrals of integrable functions (`DysonCrossCube`
includes integrability; the bound `dysonSum_norm_le` holds in either case);
`cutPt` returns `T` beyond the last index, never used; `extTime` and the
choice in `cutOp` are used only on `𝒞` and on distinct insertion times.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.FixedSplitCore
public import StratonovichHAMSecondMoment.FockForm

@[expose] public section

noncomputable section

set_option autoImplicit false

open Finset Real MeasureTheory
open scoped Nat

namespace StratonovichHAMSecondMoment.FixedSplit

open StratonovichHAMSecondMoment.IntervalScalar StratonovichHAMSecondMoment.FixedSplitCore

/-! ### The common partition `E:split-partition` -/

section Partition

variable {ι : Type*}

/-- The cut points of one copy (main TeX lines 3779-3790): `0`, `T`, the
insertion times `t_i` of the cross colors `i ∈ 𝒞` and the background endpoints
`a_i, b_i` (`i ∈ 𝒜`) lying in `(0, T)`. -/
def cutSet (A C : Finset ι) (a b t : ι → ℝ) (T : ℝ) : Finset ℝ :=
  insert 0 (insert T (C.image t ∪ ((A.image a ∪ A.image b).filter fun x => 0 < x ∧ x < T)))

/-- The sorted cut points `0 = τ_0 < τ_1 < ⋯ < τ_M = T` (`E:split-partition`,
main TeX lines 3784-3786), through `Finset.orderEmbOfFin`; `T` beyond the
last index. -/
def cutPt (A C : Finset ι) (a b t : ι → ℝ) (T : ℝ) (j : ℕ) : ℝ :=
  if h : j < (cutSet A C a b t T).card then (cutSet A C a b t T).orderEmbOfFin rfl ⟨j, h⟩
  else T

/-- The number `M` of segments of the common partition. -/
def nCut (A C : Finset ι) (a b t : ι → ℝ) (T : ℝ) : ℕ := (cutSet A C a b t T).card - 1

/-- Auxiliary (Lean route): every cut point lies in `[0, T]`. -/
theorem mem_cutSet_bounds (A C : Finset ι) (a b t : ι → ℝ) (T : ℝ) (hT : 0 < T)
    (ht : ∀ i ∈ C, 0 < t i ∧ t i < T) (x : ℝ) (hx : x ∈ cutSet A C a b t T) :
    0 ≤ x ∧ x ≤ T := by
  simp only [cutSet, mem_insert, mem_union, mem_image, mem_filter] at hx
  rcases hx with rfl | rfl | ⟨i, hi, rfl⟩ | ⟨-, h1, h2⟩
  · exact ⟨le_rfl, hT.le⟩
  · exact ⟨hT.le, le_rfl⟩
  · exact ⟨(ht i hi).1.le, (ht i hi).2.le⟩
  · exact ⟨h1.le, h2.le⟩

/-- Auxiliary (Lean route): the cut set has at least two points. -/
theorem two_le_card_cutSet (A C : Finset ι) (a b t : ι → ℝ) (T : ℝ) (hT : 0 < T) :
    2 ≤ (cutSet A C a b t T).card := by
  have h0 : (0 : ℝ) ∈ cutSet A C a b t T := mem_insert_self _ _
  have hT' : T ∈ cutSet A C a b t T := mem_insert_of_mem (mem_insert_self _ _)
  have : ({0, T} : Finset ℝ) ⊆ cutSet A C a b t T := by
    intro x hx; simp only [mem_insert, mem_singleton] at hx; rcases hx with rfl | rfl <;> assumption
  have hc : ({0, T} : Finset ℝ).card = 2 := card_pair hT.ne
  exact hc ▸ card_le_card this

/-- The partition count (main TeX lines 3788-3790): `M ≤ 2|𝒜| + |𝒞| + 1`. -/
theorem nCut_le (A C : Finset ι) (a b t : ι → ℝ) (T : ℝ) :
    nCut A C a b t T ≤ 2 * A.card + C.card + 1 := by
  unfold nCut cutSet
  have h1 := card_insert_le (0 : ℝ) (insert T (C.image t ∪
    ((A.image a ∪ A.image b).filter fun x => 0 < x ∧ x < T)))
  have h2 := card_insert_le T (C.image t ∪
    ((A.image a ∪ A.image b).filter fun x => 0 < x ∧ x < T))
  have h3 := card_union_le (C.image t)
    ((A.image a ∪ A.image b).filter fun x => 0 < x ∧ x < T)
  have h4 := card_image_le (s := C) (f := t)
  have h5 := card_filter_le (A.image a ∪ A.image b) fun x => 0 < x ∧ x < T
  have h6 := card_union_le (A.image a) (A.image b)
  have h7 := card_image_le (s := A) (f := a)
  have h8 := card_image_le (s := A) (f := b)
  omega

/-- The partition properties used below (main TeX lines 3779-3790): with
`T > 0` and every insertion time in `(0, T)`, the sorted cut points satisfy
`τ_0 = 0`, `τ_M = T`, `τ_j < τ_{j+1}`, every cut point is some `τ_m`
(`m ≤ M`), and every `τ_m` is a cut point. -/
theorem cutPt_spec (A C : Finset ι) (a b t : ι → ℝ) (T : ℝ) (hT : 0 < T)
    (ht : ∀ i ∈ C, 0 < t i ∧ t i < T) :
    cutPt A C a b t T 0 = 0 ∧ cutPt A C a b t T (nCut A C a b t T) = T ∧
      (∀ j < nCut A C a b t T, cutPt A C a b t T j < cutPt A C a b t T (j + 1)) ∧
      (∀ x ∈ cutSet A C a b t T, ∃ m ≤ nCut A C a b t T, cutPt A C a b t T m = x) := by
  set s := cutSet A C a b t T with hs
  have hn : nCut A C a b t T = s.card - 1 := rfl
  rw [hn]
  have hc2 : 2 ≤ s.card := two_le_card_cutSet A C a b t T hT
  have hbd := mem_cutSet_bounds A C a b t T hT ht
  have h0 : (0 : ℝ) ∈ s := mem_insert_self _ _
  have hTm : T ∈ s := mem_insert_of_mem (mem_insert_self _ _)
  have hne : s.Nonempty := ⟨0, h0⟩
  have hpos : 0 < s.card := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [cutPt, ← hs, hpos, ↓reduceDIte]
    rw [orderEmbOfFin_zero rfl hpos]
    exact le_antisymm (min'_le s 0 h0) (le_min' s hne 0 fun y hy => (hbd y hy).1)
  · have hlt : s.card - 1 < s.card := by omega
    simp only [cutPt, ← hs, hlt, ↓reduceDIte]
    rw [orderEmbOfFin_last rfl hpos]
    exact le_antisymm (max'_le s hne T fun y hy => (hbd y hy).2) (le_max' s T hTm)
  · intro j hj
    have hj1 : j < s.card := by omega
    have hj2 : j + 1 < s.card := by omega
    simp only [cutPt, ← hs, hj1, hj2, ↓reduceDIte]
    exact (s.orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.2 (Nat.lt_succ_self j))
  · intro x hx
    have hr := range_orderEmbOfFin s (rfl : s.card = s.card)
    have : x ∈ Set.range (s.orderEmbOfFin rfl) := by rw [hr]; exact hx
    obtain ⟨⟨m, hm⟩, hmx⟩ := this
    refine ⟨m, by omega, ?_⟩
    simp only [cutPt, ← hs, hm, ↓reduceDIte]
    exact hmx

end Partition

/-! ### The chronological word and `E:split-word-product` -/

section Word

variable {ι : Type*} [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The operator at a cut `x₀` (main TeX lines 3907-3909): `B^cut = J_i` if
`x₀ = t_i` for a cross color `i ∈ 𝒞`, the identity otherwise.  (On the Dyson
simplices the insertion times are distinct, so `i` is unique.) -/
def cutOp (C : Finset ι) (J : ι → E → E) (t : ι → ℝ) (x0 : ℝ) (x : E) : E :=
  if h : ∃ i ∈ C, t i = x0 then J h.choose x else x

/-- The partial words along a partition `τ` (main TeX lines 3907-3913):
`w_0 = v` and `w_{j+1} = B^cut_{j+1} P(τ_{j+1}, τ_j) w_j`.  The identities
`𝓘_j` of the TeX change only the norm, so they do not appear in the operator
product. -/
def wordSeq (P : ℝ → ℝ → E → E) (τ : ℕ → ℝ) (op : ℝ → E → E) (v : E) : ℕ → E
  | 0 => v
  | j + 1 => op (τ (j + 1)) (P (τ (j + 1)) (τ j) (wordSeq P τ op v j))

/-- **The chronological word** `𝒲_𝒜(z, t) v` (main TeX lines 3909-3913) for
the background propagator `P_z(t, s)` (`P z t s`), the insertions `J_i`, the
insertion times `t_i` and the common partition `cutPt`: the composition
`P_M B^cut_{M-1} P_{M-1} ⋯ B^cut_1 P_1` applied to `v`. -/
def word (A C : Finset ι) (a b : ι → ℝ) (T : ℝ) (J : ι → E → E)
    (P : (ι → ℂ) → ℝ → ℝ → E → E) (v : E) (z : ι → ℂ) (t : ι → ℝ) : E :=
  wordSeq (P z) (cutPt A C a b t T) (cutOp C J t) v (nCut A C a b t T)

/-- The inserted cross colors after the cut `τ_j`. -/
def insertedSet (C : Finset ι) (t : ι → ℝ) (τ : ℕ → ℝ) (j : ℕ) : Finset ι :=
  C.filter fun i => t i ≤ τ j

/-- Auxiliary (Lean route): strict steps give strict monotonicity on
`{0, …, M}`. -/
theorem lt_of_steps (τ : ℕ → ℝ) (M : ℕ) (hst : ∀ j < M, τ j < τ (j + 1)) :
    ∀ m n, m < n → n ≤ M → τ m < τ n := by
  intro m n hmn hnM
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge m n with h | h
    · exact (ih h (by omega)).trans (hst n (by omega))
    · have : m = n := by omega
      subst this; exact hst m (by omega)

/-- Auxiliary (Lean route): on `{0, …, M}` the partition reflects `≤`. -/
theorem le_iff_of_steps (τ : ℕ → ℝ) (M : ℕ) (hst : ∀ j < M, τ j < τ (j + 1)) (m n : ℕ)
    (hm : m ≤ M) (hn : n ≤ M) : τ m ≤ τ n ↔ m ≤ n := by
  have hlt := lt_of_steps τ M hst
  constructor
  · intro h; by_contra hc; exact absurd h (not_le.2 (hlt n m (by omega) hm))
  · intro h
    rcases Nat.lt_or_ge m n with h' | h'
    · exact (hlt m n h' hn).le
    · have : m = n := by omega
      rw [this]

/-- Auxiliary (Lean route): the partition is injective on `{0, …, M}`. -/
theorem eq_of_steps (τ : ℕ → ℝ) (M : ℕ) (hst : ∀ j < M, τ j < τ (j + 1)) (m n : ℕ)
    (hm : m ≤ M) (hn : n ≤ M) (h : τ m = τ n) : m = n :=
  le_antisymm ((le_iff_of_steps τ M hst m n hm hn).1 h.le)
    ((le_iff_of_steps τ M hst n m hn hm).1 h.ge)

/-- Auxiliary (Lean route): no cut point lies strictly between consecutive
cuts. -/
theorem not_mem_Ioo_of_steps (τ : ℕ → ℝ) (M : ℕ) (hst : ∀ j < M, τ j < τ (j + 1)) (s : ℕ)
    (hs : s < M) (m : ℕ) (hm : m ≤ M) : τ m ∉ Set.Ioo (τ s) (τ (s + 1)) := by
  rintro ⟨h1, h2⟩
  have e1 := (le_iff_of_steps τ M hst s m (by omega) hm).1 h1.le
  have e2 := (le_iff_of_steps τ M hst m (s + 1) hm (by omega)).1 h2.le
  rcases Nat.lt_or_ge s m with h | h
  · have : m = s + 1 := by omega
    subst this; exact lt_irrefl _ h2
  · have : m = s := by omega
    subst this; exact lt_irrefl _ h1

/-- The inserted set after the next cut (main TeX lines 3895-3898): it gains
the color inserted at `τ_{j+1}`, if any, and nothing else. -/
theorem insertedSet_succ (C : Finset ι) (t : ι → ℝ) (τ : ℕ → ℝ) (M : ℕ)
    (hst : ∀ j < M, τ j < τ (j + 1)) (hcutC : ∀ i ∈ C, ∃ m ≤ M, τ m = t i)
    (hinj : Set.InjOn t C) (s : ℕ) (hs : s < M) :
    insertedSet C t τ (s + 1) =
      if h : ∃ i ∈ C, t i = τ (s + 1) then insert h.choose (insertedSet C t τ s)
      else insertedSet C t τ s := by
  have key : ∀ i ∈ C, (t i ≤ τ (s + 1) ↔ t i ≤ τ s ∨ t i = τ (s + 1)) := by
    intro i hi
    obtain ⟨m, hm, hmt⟩ := hcutC i hi
    rw [← hmt, le_iff_of_steps τ M hst m (s + 1) hm (by omega),
      le_iff_of_steps τ M hst m s hm (by omega)]
    constructor
    · intro h
      rcases Nat.lt_or_ge m (s + 1) with h' | h'
      · left; omega
      · right; rw [show m = s + 1 by omega]
    · rintro (h | h)
      · omega
      · exact (eq_of_steps τ M hst m (s + 1) hm (by omega) h).le
  split_ifs with h
  · obtain ⟨hc, ht⟩ := h.choose_spec
    ext i
    simp only [insertedSet, mem_filter, mem_insert]
    constructor
    · rintro ⟨hi, hle⟩
      rcases (key i hi).1 hle with h1 | h1
      · right; exact ⟨hi, h1⟩
      · left; exact hinj hi hc (h1.trans ht.symm)
    · rintro (rfl | ⟨hi, hle⟩)
      · exact ⟨hc, ht.le⟩
      · exact ⟨hi, (key i hi).2 (Or.inl hle)⟩
  · ext i
    simp only [insertedSet, mem_filter]
    constructor
    · rintro ⟨hi, hle⟩
      rcases (key i hi).1 hle with h1 | h1
      · exact ⟨hi, h1⟩
      · exact absurd ⟨i, hi, h1⟩ h
    · rintro ⟨hi, hle⟩
      exact ⟨hi, (key i hi).2 (Or.inl hle)⟩

/-- `Λ(t) = λ + ∑_{i∈𝒜} (k_i/h_i) 1_{(a_i,b_i)}(t)` with `λ = k/T` (main TeX
lines 3763-3766 with `E:split-radii`, line 3746). -/
def segLam (A : Finset ι) (a b h : ι → ℝ) (κ : ι → ℕ) (k : ℕ) (T : ℝ) (t : ℝ) : ℝ :=
  intervalLambda ((k : ℝ) / T) (fun i => (κ i : ℝ) / h i) A a b t

/-- **`E:split-word-product` for the operator word** (main TeX lines
3779-3930).  Along any strict partition `0 = τ_0 < ⋯ < τ_M = T` whose cuts
contain the background endpoints in `(0, T)` and the insertion times `t_i ∈
(0, T)` (injective on `𝒞`), with `M ≤ 3k + 1`, suppose:
* `hcmp`: the identity between phase norms has norm `≤ max{1, ρ/ρ'}` from
  `‖·‖_ρ` to `‖·‖_{ρ'}` (lines 3811-3817);
* `hv`, `hPZ`: `v ∈ 𝒵_∅` and the background propagator preserves every
  `𝒵_S`, `S ⊆ 𝒞` (lines 3855-3859);
* `hseg`: the segment bound of `L:interval-complex` on every interval free of
  background endpoints, in the norm of the constant height `Λ` (lines
  3791-3801);
* `hJ`: `E:split-fresh-insertion` on `𝒵_S` for `i ∉ S` in every norm
  `ρ ≥ λ`, with `J_i(𝒵_S) ⊆ 𝒵_{S∪{i}}` (lines 3861-3894).
Then `‖𝒲 v‖_λ ≤ M_k D_𝒜 (∏_{i∈𝒞} c_i) ‖v‖_λ`.  The proof tracks the
inserted set `{i ∈ 𝒞 : t_i ≤ τ_j}` along the word (lines 3895-3898) and
feeds the norms of the partial words to `split_word_bound`,
`split_segment_product_paper` and `interval_copy_metric_paper` (L10-FS0). -/
theorem word_chain (A C : Finset ι) (Z : Finset ι → Set E) (emb : ℝ → E →L[ℂ] F)
    (J : ι → E → E) (P : ℝ → ℝ → E → E) (v : E) (a b h t cI : ι → ℝ) (κ : ι → ℕ) (k : ℕ)
    (T : ℝ) (τ : ℕ → ℝ) (M : ℕ) (hT : 0 < T) (hk : 1 ≤ k)
    (hτ0 : τ 0 = 0) (hτM : τ M = T) (hst : ∀ j < M, τ j < τ (j + 1))
    (hcutA : ∀ i ∈ A, (0 < a i → a i < T → ∃ m ≤ M, τ m = a i) ∧
      (0 < b i → b i < T → ∃ m ≤ M, τ m = b i))
    (hcutC : ∀ i ∈ C, ∃ m ≤ M, τ m = t i) (htC : ∀ i ∈ C, 0 < t i ∧ t i < T)
    (hinj : Set.InjOn t C) (hM : M ≤ 3 * k + 1)
    (hh : ∀ i ∈ A, 0 < h i) (hlen : ∀ i ∈ A, b i - a i ≤ h i) (hκ : ∑ i ∈ A, κ i ≤ k)
    (hcI : ∀ i ∈ C, 0 ≤ cI i)
    (hcmp : ∀ ρ ρ' : ℝ, 0 < ρ → 0 < ρ' → ∀ x, ‖emb ρ' x‖ ≤ max 1 (ρ / ρ') * ‖emb ρ x‖)
    (hv : v ∈ Z ∅) (hPZ : ∀ S ⊆ C, ∀ s t', ∀ x ∈ Z S, P t' s x ∈ Z S)
    (hseg : ∀ s t', 0 ≤ s → s < t' → t' ≤ T →
      (∀ i ∈ A, a i ∉ Set.Ioo s t' ∧ b i ∉ Set.Ioo s t') → ∀ x,
        ‖emb (segLam A a b h κ k T ((s + t') / 2)) (P t' s x)‖ ≤
          100 * Real.exp (2 * (segLam A a b h κ k T ((s + t') / 2) * (t' - s))) *
            ‖emb (segLam A a b h κ k T ((s + t') / 2)) x‖)
    (hJ : ∀ i ∈ C, ∀ S ⊆ C, i ∉ S → ∀ x ∈ Z S, J i x ∈ Z (insert i S) ∧
      ∀ ρ, (k : ℝ) / T ≤ ρ → ‖emb ρ (J i x)‖ ≤ cI i * ‖emb ρ x‖) :
    ‖emb ((k : ℝ) / T) (wordSeq P τ (cutOp C J t) v M)‖ ≤
      Mk k * metricD ((k : ℝ) / T) h κ A * (∏ i ∈ C, cI i) * ‖emb ((k : ℝ) / T) v‖ := by
  classical
  set lam : ℝ := (k : ℝ) / T with hlamdef
  have hlam : 0 < lam := div_pos (by exact_mod_cast hk) hT
  set ω : ι → ℝ := fun i => (κ i : ℝ) / h i with hω
  set Hh : ℕ → ℝ := fun j => height lam ω (intervalAct A a b τ M) j with hHh
  set W : ℕ → E := wordSeq P τ (cutOp C J t) v with hW
  have hω0 : ∀ i ∈ A, 0 ≤ ω i := fun i hi => div_nonneg (Nat.cast_nonneg _) (hh i hi).le
  have hHge : ∀ j, lam ≤ Hh j := fun j => by
    simp only [hHh, height]
    have := Finset.sum_nonneg fun i hi => hω0 i (intervalAct_subset A a b τ M j hi)
    linarith
  have hHpos : ∀ j, 0 < Hh j := fun j => hlam.trans_le (hHge j)
  obtain ⟨hH0, hH1⟩ := height_outer lam ω A a b τ M
  have hle := le_iff_of_steps τ M hst
  -- the factors
  set p : ℕ → ℝ := fun s => 100 * Real.exp (2 * (Hh (s + 1) * (τ (s + 1) - τ s))) with hp
  set q : ℕ → ℝ := fun j => max 1 (Hh j / Hh (j + 1)) with hq
  set bc : ℕ → ℝ := fun s => if hs : ∃ i ∈ C, t i = τ (s + 1) then cI hs.choose else 1 with hbc
  set w : ℕ → ℝ := fun s => ‖emb (Hh (s + 1)) (W s)‖ with hw
  -- inserted set at the start
  have hS0 : insertedSet C t τ 0 = ∅ := by
    refine Finset.filter_false_of_mem fun i hi => ?_
    rw [hτ0]; exact not_le.2 (htC i hi).1
  -- one step
  have key : ∀ s < M, W s ∈ Z (insertedSet C t τ s) →
      W (s + 1) ∈ Z (insertedSet C t τ (s + 1)) ∧ w (s + 1) ≤ q (s + 1) * p s * bc s * w s := by
    intro s hs hin
    set y := P (τ (s + 1)) (τ s) (W s) with hy
    have hyZ : y ∈ Z (insertedSet C t τ s) := hPZ _ (filter_subset _ _) _ _ _ hin
    have h0s : 0 ≤ τ s := by rw [← hτ0]; exact (hle 0 s (Nat.zero_le _) hs.le).2 (Nat.zero_le _)
    have hsT : τ (s + 1) ≤ T := by rw [← hτM]; exact (hle (s + 1) M hs le_rfl).2 hs
    have hexcl : ∀ i ∈ A, a i ∉ Set.Ioo (τ s) (τ (s + 1)) ∧ b i ∉ Set.Ioo (τ s) (τ (s + 1)) := by
      intro i hi
      constructor
      · intro hin'
        obtain ⟨m, hm, hma⟩ := (hcutA i hi).1 (h0s.trans_lt hin'.1) (hin'.2.trans_le hsT)
        exact not_mem_Ioo_of_steps τ M hst s hs m hm (hma ▸ hin')
      · intro hin'
        obtain ⟨m, hm, hma⟩ := (hcutA i hi).2 (h0s.trans_lt hin'.1) (hin'.2.trans_le hsT)
        exact not_mem_Ioo_of_steps τ M hst s hs m hm (hma ▸ hin')
    have hmid : segLam A a b h κ k T ((τ s + τ (s + 1)) / 2) = Hh (s + 1) := by
      have hcut' : ∀ i ∈ A, (τ 0 < a i → a i < τ M → ∃ m ≤ M, τ m = a i) ∧
          (τ 0 < b i → b i < τ M → ∃ m ≤ M, τ m = b i) := by
        rw [hτ0, hτM]; exact hcutA
      have hst' := hst s hs
      have := intervalLambda_eq_height lam ω A a b τ M (s + 1) (fun j hj => (hst j hj).le)
        (by omega) (by omega) hcut' ((τ s + τ (s + 1)) / 2)
        (by simp only [Nat.add_sub_cancel]; constructor <;> linarith)
      exact this
    have hsegb : ‖emb (Hh (s + 1)) y‖ ≤ p s * w s := by
      have := hseg (τ s) (τ (s + 1)) h0s (hst s hs) hsT hexcl (W s)
      rw [hmid] at this
      exact this
    have hconv : ‖emb (Hh (s + 1 + 1)) y‖ ≤ q (s + 1) * ‖emb (Hh (s + 1)) y‖ :=
      hcmp _ _ (hHpos _) (hHpos _) y
    have hWs : W (s + 1) = cutOp C J t (τ (s + 1)) y := rfl
    have hq0 : 0 ≤ q (s + 1) := le_trans zero_le_one (le_max_left _ _)
    by_cases hex : ∃ i ∈ C, t i = τ (s + 1)
    · obtain ⟨hc0, ht0⟩ := hex.choose_spec
      have hnot : hex.choose ∉ insertedSet C t τ s := by
        simp only [insertedSet, mem_filter, not_and, not_le]
        intro _; rw [ht0]; exact hst s hs
      obtain ⟨hmem, hnorm⟩ := hJ hex.choose hc0 _ (filter_subset _ _) hnot y hyZ
      have hcut : W (s + 1) = J hex.choose y := by rw [hWs]; simp only [cutOp, dite_eq_left hex]
      have hb : bc s = cI hex.choose := by simp only [hbc, dite_eq_left hex]
      rw [insertedSet_succ C t τ M hst hcutC hinj s hs, dite_eq_left hex]
      refine ⟨hcut ▸ hmem, ?_⟩
      have h1 := hnorm (Hh (s + 1 + 1)) (hHge _)
      have hcI0 := hcI _ hc0
      calc w (s + 1) = ‖emb (Hh (s + 1 + 1)) (J hex.choose y)‖ := by simp only [hw, hcut]
        _ ≤ cI hex.choose * ‖emb (Hh (s + 1 + 1)) y‖ := h1
        _ ≤ cI hex.choose * (q (s + 1) * (p s * w s)) :=
            mul_le_mul_of_nonneg_left (hconv.trans (mul_le_mul_of_nonneg_left hsegb hq0)) hcI0
        _ = q (s + 1) * p s * bc s * w s := by rw [hb]; ring
    · have hcut : W (s + 1) = y := by rw [hWs]; simp only [cutOp, dite_eq_right hex]
      have hb : bc s = 1 := by simp only [hbc, dite_eq_right hex]
      rw [insertedSet_succ C t τ M hst hcutC hinj s hs, dite_eq_right hex]
      refine ⟨hcut ▸ hyZ, ?_⟩
      calc w (s + 1) = ‖emb (Hh (s + 1 + 1)) y‖ := by simp only [hw, hcut]
        _ ≤ q (s + 1) * (p s * w s) := hconv.trans (mul_le_mul_of_nonneg_left hsegb hq0)
        _ = q (s + 1) * p s * bc s * w s := by rw [hb]; ring
  have hinv : ∀ s ≤ M, W s ∈ Z (insertedSet C t τ s) := by
    intro s
    induction s with
    | zero => intro _; rw [hS0]; exact hv
    | succ n ih => intro hn; exact (key n (by omega) (ih (by omega))).1
  -- the insertion indices
  set σf : ι → ℕ := fun i => if hi : i ∈ C then (hcutC i hi).choose - 1 else 0 with hσf
  have hσspec : ∀ i (hi : i ∈ C), σf i + 1 ≤ M ∧ τ (σf i + 1) = t i := by
    intro i hi
    obtain ⟨hm, hmt⟩ := (hcutC i hi).choose_spec
    have hne0 : (hcutC i hi).choose ≠ 0 := by
      intro h0; rw [h0, hτ0] at hmt; exact absurd hmt (htC i hi).1.ne
    simp only [hσf, dite_eq_left hi]
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hne0)]
    exact ⟨hm, hmt⟩
  have hσM : ∀ i ∈ C, σf i < M := by
    intro i hi
    obtain ⟨h1, h2⟩ := hσspec i hi
    rcases Nat.lt_or_ge (σf i + 1) M with h | h
    · omega
    · have : σf i + 1 = M := by omega
      rw [this, hτM] at h2; exact absurd h2.symm (htC i hi).2.ne
  have hσinj : Set.InjOn σf C := by
    intro i hi i' hi' heq
    have e1 := (hσspec i hi).2
    have e2 := (hσspec i' hi').2
    rw [heq] at e1
    exact hinj hi hi' (e1.symm.trans e2)
  have hbcσ : ∀ i ∈ C, bc (σf i) = cI i := by
    intro i hi
    have hex : ∃ i' ∈ C, t i' = τ (σf i + 1) := ⟨i, hi, (hσspec i hi).2.symm⟩
    obtain ⟨hc', ht'⟩ := hex.choose_spec
    have : hex.choose = i := hinj hc' hi (ht'.trans (hσspec i hi).2)
    simp only [hbc, dite_eq_left hex, this]
  have hb1 : ∀ s < M, s ∉ C.image σf → bc s ≤ 1 := by
    intro s hs hsn
    by_cases hex : ∃ i ∈ C, t i = τ (s + 1)
    · exfalso
      obtain ⟨hc', ht'⟩ := hex.choose_spec
      apply hsn
      refine Finset.mem_image.2 ⟨hex.choose, hc', ?_⟩
      have h1 := hσspec _ hc'
      have := eq_of_steps τ M hst _ _ h1.1 (by omega) (h1.2.trans ht')
      omega
    · simp only [hbc, dite_eq_right hex, le_refl]
  have hbnn : ∀ s < M, 0 ≤ bc s := by
    intro s _
    simp only [hbc]
    split_ifs with hex
    · exact hcI _ hex.choose_spec.1
    · exact zero_le_one
  have hpnn : ∀ s < M, 0 ≤ p s := fun s _ => by positivity
  have hqnn : ∀ s ≤ M, 0 ≤ q s := fun s _ => le_trans zero_le_one (le_max_left _ _)
  have h0 : w 0 ≤ q 0 * ‖emb lam v‖ := by
    have := hcmp (Hh 0) (Hh (0 + 1)) (hHpos _) (hHpos _) v
    simp only [hw, hq]
    rw [show Hh 0 = lam from hH0] at this ⊢
    exact this
  have hP : ∏ s ∈ range M, p s ≤ Mk k :=
    split_segment_product_paper A a b h κ τ M k T hT hτ0 hτM hst hh hlen hκ hM p hpnn
      fun j _ => le_rfl
  have hQ : ∏ s ∈ range (M + 1), q s ≤ metricD lam h κ A :=
    interval_copy_metric_paper A a b h κ τ M k T hT hk hh hst
  have hfin := split_word_bound w p q bc M ‖emb lam v‖ (Mk k) (metricD lam h κ A) C σf cI
    (norm_nonneg _) hpnn hqnn hbnn h0 (fun s hs => (key s hs (hinv s hs.le)).2) hσinj hσM
    hbcσ hb1 hP hQ
  have hwM : w M = ‖emb lam (W M)‖ := by
    simp only [hw]; rw [show Hh (M + 1) = lam from hH1]
  rw [← hwM]
  exact hfin

end Word

/-! ### The insertion cube `E:interval-cross-cube` and `E:interval-cross-vector` -/

section Cube

variable {ι : Type*} [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The ordered simplex `D_π = {t ∈ ∏_{i∈𝒞} I_i^T : t_{π_1} < ⋯ < t_{π_m}}`
(main TeX lines 3947-3953), for an ordering `π : Fin m ≃ 𝒞`, with
`I_i^T = (a_i, b_i)`. -/
def simplex (C : Finset ι) (a b : ι → ℝ) (o : Fin (Fintype.card C) ≃ C) : Set (C → ℝ) :=
  {t | (∀ i : C, t i ∈ Set.Ioo (a i) (b i)) ∧ StrictMono (t ∘ o)}

/-- The insertion times `t : 𝒞 → ℝ` as a function on all colors (zero off
`𝒞`; only the values on `𝒞` are used). -/
def extTime (C : Finset ι) (t : C → ℝ) : ι → ℝ := fun i => if h : i ∈ C then t ⟨i, h⟩ else 0

/-- The right side of `E:interval-cross-cube` (main TeX lines 3947-3953):
`∑_π ∫_{D_π} 𝒲(t) v dt` for a vector-valued word `W`. -/
def dysonSum (C : Finset ι) (a b : ι → ℝ) (W : (ι → ℝ) → E) : E :=
  ∑ o : Fin (Fintype.card C) ≃ C, ∫ t in simplex C a b o, W (extTime C t)

omit [DecidableEq ι] in
/-- Auxiliary (Lean route): `D_π` is measurable. -/
theorem measurableSet_simplex (C : Finset ι) (a b : ι → ℝ) (o : Fin (Fintype.card C) ≃ C) :
    MeasurableSet (simplex C a b o) := by
  have h1 : simplex C a b o = (⋂ i : C, ({t : C → ℝ | a i < t i} ∩ {t | t i < b i})) ∩
      ⋂ j : Fin (Fintype.card C), ⋂ j' : Fin (Fintype.card C),
        {t : C → ℝ | j < j' → t (o j) < t (o j')} := by
    ext t
    simp only [simplex, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_Ioo,
      StrictMono, Function.comp_apply]
  rw [h1]
  refine MeasurableSet.inter (MeasurableSet.iInter fun i => ?_)
    (MeasurableSet.iInter fun j => MeasurableSet.iInter fun j' => ?_)
  · exact (measurableSet_lt measurable_const (measurable_pi_apply _)).inter
      (measurableSet_lt (measurable_pi_apply _) measurable_const)
  · by_cases hjj : j < j'
    · simp only [hjj, true_implies]
      exact measurableSet_lt (measurable_pi_apply _) (measurable_pi_apply _)
    · simp only [hjj, false_implies, Set.ofPred_true, MeasurableSet.univ]

omit [DecidableEq ι] in
/-- The simplices are pairwise disjoint (main TeX lines 3954-3956): a point
with distinct coordinates has one increasing ordering. -/
theorem simplex_disjoint (C : Finset ι) (a b : ι → ℝ) {o o' : Fin (Fintype.card C) ≃ C}
    (hne : o ≠ o') : Disjoint (simplex C a b o) (simplex C a b o') := by
  rw [Set.disjoint_left]
  rintro t ⟨-, h1⟩ ⟨-, h2⟩
  apply hne
  have hr : Set.range (t ∘ o) = Set.range (t ∘ o') := by
    rw [Set.range_comp, Set.range_comp, o.range_eq_univ, o'.range_eq_univ]
  have heq := (StrictMono.range_inj_of_wellFoundedLT h1 h2).1 hr
  have htinj : Function.Injective t := by
    intro x y hxy
    have := h1.injective (a₁ := o.symm x) (a₂ := o.symm y) (by simp [hxy])
    simpa using this
  ext j
  exact congrArg Subtype.val (htinj (congrFun heq j))

omit [DecidableEq ι] in
/-- Auxiliary (Lean route): `D_π` lies in the cube `∏_{i∈𝒞} (a_i, b_i)`. -/
theorem simplex_subset_cube (C : Finset ι) (a b : ι → ℝ) (o : Fin (Fintype.card C) ≃ C) :
    simplex C a b o ⊆ Set.univ.pi fun i : C => Set.Ioo (a i) (b i) :=
  fun _ ht i _ => ht.1 i

/-- `∑_π |D_π| ≤ ∏_{i∈𝒞} |I_i^T| ≤ ∏_{i∈𝒞} h_i` (main TeX lines 3954-3958),
for `b_i - a_i ≤ h_i` and `h_i ≥ 0`. -/
theorem sum_volume_simplex_le (C : Finset ι) (a b h : ι → ℝ) (hh : ∀ i ∈ C, 0 ≤ h i)
    (hlen : ∀ i ∈ C, b i - a i ≤ h i) :
    ∑ o : Fin (Fintype.card C) ≃ C, volume.real (simplex C a b o) ≤ ∏ i ∈ C, h i := by
  set cube : Set (C → ℝ) := Set.univ.pi fun i : C => Set.Ioo (a i) (b i) with hcube
  have hcv : volume cube = ∏ i : C, ENNReal.ofReal (b i - a i) := Real.volume_pi_Ioo
  have hcfin : volume cube ≠ ⊤ := by rw [hcv]; exact ENNReal.prod_ne_top fun _ _ => by simp
  have hunion : volume (⋃ o ∈ (univ : Finset (Fin (Fintype.card C) ≃ C)), simplex C a b o) =
      ∑ o : Fin (Fintype.card C) ≃ C, volume (simplex C a b o) :=
    measure_biUnion_finset (fun o _ o' _ hne => simplex_disjoint C a b hne)
      fun o _ => measurableSet_simplex C a b o
  have hsub : (⋃ o ∈ (univ : Finset (Fin (Fintype.card C) ≃ C)), simplex C a b o) ⊆ cube :=
    Set.iUnion₂_subset fun o _ => simplex_subset_cube C a b o
  have hle : ∑ o : Fin (Fintype.card C) ≃ C, volume (simplex C a b o) ≤ volume cube :=
    hunion ▸ measure_mono hsub
  have hfin : ∀ o : Fin (Fintype.card C) ≃ C, volume (simplex C a b o) ≠ ⊤ := fun o =>
    ne_top_of_le_ne_top hcfin (measure_mono (simplex_subset_cube C a b o))
  calc ∑ o : Fin (Fintype.card C) ≃ C, volume.real (simplex C a b o)
      = (∑ o : Fin (Fintype.card C) ≃ C, volume (simplex C a b o)).toReal := by
        rw [ENNReal.toReal_sum fun o _ => hfin o]; rfl
    _ ≤ (volume cube).toReal := ENNReal.toReal_mono hcfin hle
    _ = ∏ i : C, max (b i - a i) 0 := by
        rw [hcv, ENNReal.toReal_prod]
        exact Finset.prod_congr rfl fun i _ => ENNReal.toReal_ofReal'
    _ ≤ ∏ i : C, h i := by
        refine Finset.prod_le_prod₀ (fun i _ => le_max_right _ _) fun i _ => ?_
        exact max_le (hlen i i.2) (hh i i.2)
    _ = ∏ i ∈ C, h i := Finset.prod_coe_sort C h

/-- **`E:interval-cross-vector` from `E:interval-cross-cube`** (main TeX
lines 3961-3967): if `‖𝒲(t) v‖_λ ≤ K` on every simplex, then Minkowski
gives `‖∑_π ∫_{D_π} 𝒲(t) v dt‖_λ ≤ K ∏_{i∈𝒞} h_i`.  The phase norm is
`‖emb_λ ·‖`; no factor `m!` or `1/m!` enters. -/
theorem dysonSum_norm_le (C : Finset ι) (a b h : ι → ℝ) (emb : E →L[ℂ] F) (W : (ι → ℝ) → E)
    (K : ℝ) (hK0 : 0 ≤ K) (hh : ∀ i ∈ C, 0 ≤ h i) (hlen : ∀ i ∈ C, b i - a i ≤ h i)
    (hK : ∀ o : Fin (Fintype.card C) ≃ C, ∀ t ∈ simplex C a b o, ‖emb (W (extTime C t))‖ ≤ K) :
    ‖emb (dysonSum C a b W)‖ ≤ K * ∏ i ∈ C, h i := by
  have hcfin : ∀ o : Fin (Fintype.card C) ≃ C, volume (simplex C a b o) < ⊤ := by
    intro o
    refine (measure_mono (simplex_subset_cube C a b o)).trans_lt ?_
    rw [Real.volume_pi_Ioo]
    exact ENNReal.prod_lt_top fun _ _ => ENNReal.ofReal_lt_top
  have hone : ∀ o : Fin (Fintype.card C) ≃ C,
      ‖emb (∫ t in simplex C a b o, W (extTime C t))‖ ≤ K * volume.real (simplex C a b o) := by
    intro o
    by_cases hint : IntegrableOn (fun t => W (extTime C t)) (simplex C a b o)
    · rw [← ContinuousLinearMap.integral_comp_comm emb hint]
      exact norm_setIntegral_le_of_norm_le_const (hcfin o) (hK o)
    · rw [integral_undef hint, map_zero, norm_zero]
      exact mul_nonneg hK0 measureReal_nonneg
  unfold dysonSum
  rw [map_sum]
  calc ‖∑ o : Fin (Fintype.card C) ≃ C, emb (∫ t in simplex C a b o, W (extTime C t))‖
      ≤ ∑ o : Fin (Fintype.card C) ≃ C, ‖emb (∫ t in simplex C a b o, W (extTime C t))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ o : Fin (Fintype.card C) ≃ C, K * volume.real (simplex C a b o) :=
        Finset.sum_le_sum fun o _ => hone o
    _ = K * ∑ o : Fin (Fintype.card C) ≃ C, volume.real (simplex C a b o) := by
        rw [Finset.mul_sum]
    _ ≤ K * ∏ i ∈ C, h i :=
        mul_le_mul_of_nonneg_left (sum_volume_simplex_le C a b h hh hlen) hK0

/-- Auxiliary (Lean route): on `D_π` the insertion times lie in their
intervals and are distinct. -/
theorem extTime_of_simplex (C : Finset ι) (a b : ι → ℝ) (o : Fin (Fintype.card C) ≃ C)
    (t : C → ℝ) (ht : t ∈ simplex C a b o) :
    (∀ i ∈ C, a i < extTime C t i ∧ extTime C t i < b i) ∧ Set.InjOn (extTime C t) C := by
  refine ⟨fun i hi => ?_, fun i hi i' hi' heq => ?_⟩
  · simp only [extTime, hi, ↓reduceDIte]
    exact ht.1 ⟨i, hi⟩
  · have hi1 : i ∈ C := hi
    have hi2 : i' ∈ C := hi'
    simp only [extTime, hi1, hi2, ↓reduceDIte] at heq
    have h2 := ht.2.injective (a₁ := o.symm ⟨i, hi1⟩) (a₂ := o.symm ⟨i', hi2⟩) (by simpa using heq)
    simpa using h2

end Cube

/-! ### Named inputs and the per-copy bound -/

section Copy

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The full multi-index `(s_𝒜, 1_𝒞, 0)` of a background multi-index
`s : 𝒜 → ℕ`: degree `s_i` on `𝒜`, one on every cross color, zero elsewhere
(main TeX lines 3943-3946 and 3985-3987). -/
def liftIdx (A C : Finset ι) (s : A → ℕ) : ι → ℕ :=
  fun i => if h : i ∈ A then s ⟨i, h⟩ else if i ∈ C then 1 else 0

/-- Background amplitudes `z : 𝒜 → ℂ` extended by zero ("Evaluate every
unused amplitude at zero", main TeX line 3752; the cross amplitudes are zero
in `P_z`, line 3762). -/
def extAmp (A : Finset ι) (z : A → ℂ) : ι → ℂ := fun i => if h : i ∈ A then z ⟨i, h⟩ else 0

/-- **Supplied input `SegmentBound`** (`L:interval-complex`, main TeX lines
3473-3491, applied as in `E:split-segment-product`, lines 3791-3801).  For
background amplitudes supported on `𝒜` with `|z_i| ≤ ϱ_i`, the background
propagator `P_z(t, s)` over an interval `(s, t) ⊆ [0, T]` containing no
background endpoint has norm at most `100 e^{2Λ(t-s)}` in the phase norm of
the constant height `Λ` of `Λ(·)` on `(s, t)` (evaluated at the midpoint).
In the TeX this combines the sandwich bound `D(t) ≤ δ_a Λ(t)^{2-a}` (lines
3764-3777: `L:interval-contractions` with `E:interval-fock` at `N_i = 2k_i`
and `E:split-radii`; its scalar part is `FixedSplitCore.split_radius_sum`)
with the complex phase bound `100 e^{2Λh}` of `L:interval-complex`, whose
operator theory (Crouzeix-Palencia, inverse roots) is not formalized. -/
def SegmentBound (A : Finset ι) (emb : ℝ → E →L[ℂ] F) (P : (ι → ℂ) → ℝ → ℝ → E → E)
    (ϱ a b h : ι → ℝ) (κ : ι → ℕ) (k : ℕ) (T : ℝ) : Prop :=
  ∀ z : ι → ℂ, (∀ i, i ∉ A → z i = 0) → (∀ i ∈ A, ‖z i‖ ≤ ϱ i) →
    ∀ s t, 0 ≤ s → s < t → t ≤ T → (∀ i ∈ A, a i ∉ Set.Ioo s t ∧ b i ∉ Set.Ioo s t) → ∀ x,
      ‖emb (segLam A a b h κ k T ((s + t) / 2)) (P z t s x)‖ ≤
        100 * Real.exp (2 * (segLam A a b h κ k T ((s + t) / 2) * (t - s))) *
          ‖emb (segLam A a b h κ k T ((s + t) / 2)) x‖

/-- **Supplied input `BackgroundPreserves`** (main TeX lines 3855-3859): with
amplitudes supported on `𝒜`, the background propagator preserves the phase
over every cross subspace `𝒵_S`, `S ⊆ 𝒞` ("its potential acts only on colors
in `𝒜`, and its spatial operators act identically on all cross Gaussian
factors").  The propagator is not constructed in the package, so this
structural property of it is supplied. -/
def BackgroundPreserves (A C : Finset ι) (Z : Finset ι → Set E)
    (P : (ι → ℂ) → ℝ → ℝ → E → E) : Prop :=
  ∀ z : ι → ℂ, (∀ i, i ∉ A → z i = 0) → ∀ S ⊆ C, ∀ s t, ∀ x ∈ Z S, P z t s x ∈ Z S

/-- **Supplied input `EntireCoefficients`** (main TeX lines 3729-3733, "hence
is entire in every amplitude", and lines 4092-4136 of `P:interval-coefficients`,
`E:interval-entire-majorant`): the ordinary coefficients `U_r v = c_r` of the
cutoff evolution `𝓜^cut_z(T) v = ∑_r z^r c_r` are absolutely summable on
every polydisc. -/
def EntireCoefficients (c : (ι → ℕ) → E) : Prop :=
  ∀ ρ : ι → ℝ, (∀ i, 0 ≤ ρ i) → Summable fun s : ι → ℕ => ‖c s‖ * ∏ i, ρ i ^ s i

/-- **Supplied input `DysonCrossCube`** (`E:interval-cross-cube`, main TeX
lines 3937-3960): on the torus `|z_i| = ϱ_i` of the background amplitudes,
the vector `Φ_𝒜(z) = [∏_{i∈𝒞} y_i] 𝓜^cut_{(z,y,0)}(T) v`, written as the
series `∑_{s_𝒜} z^{s_𝒜} c_{(s_𝒜, 1_𝒞, 0)}` of the ordinary coefficients
(lines 3937-3946 and 3985-3987), equals `∑_π ∫_{D_π} 𝒲_𝒜(z, t) v dt` with the
chronological word `W z t` (variation of constants about `P_z` and
iteration; each ordered Dyson integral has coefficient one).  The word is
integrable on every simplex (in the TeX it is bounded and piecewise
continuous there), so no Bochner junk value enters. -/
def DysonCrossCube (A C : Finset ι) (c : (ι → ℕ) → E) (ϱ a b : ι → ℝ)
    (W : (ι → ℂ) → (ι → ℝ) → E) : Prop :=
  ∀ z : A → ℂ, (∀ i, ‖z i‖ = ϱ i) →
    (∀ o : Fin (Fintype.card C) ≃ C,
      IntegrableOn (fun t => W (extAmp A z) (extTime C t)) (simplex C a b o)) ∧
    HasSum (fun s : A → ℕ => monom z s • c (liftIdx A C s)) (dysonSum C a b (W (extAmp A z)))

omit [Fintype ι] in
/-- Auxiliary (Lean route): a point of the torus `(ϱ_i e^{iθ_i})` has
moduli `ϱ_i ≥ 0`. -/
theorem norm_torusPoint {ι' : Type*} (ρ θ : ι' → ℝ) (hρ : ∀ i, 0 ≤ ρ i) (i : ι') :
    ‖torusPoint ρ θ i‖ = ρ i := by
  simp only [torusPoint, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hρ i),
    Complex.norm_exp_ofReal_mul_I, mul_one]

/-- **The per-copy coefficient bound** (`E:split-word-product`,
`E:interval-cross-cube`, `E:interval-cross-vector` and
`E:split-vector-cauchy`, main TeX lines 3750-3991): for one copy with
background set `𝒜`, cross set `𝒞` (disjoint), the phase norms
`‖·‖_ρ = ‖emb_ρ ·‖`, and a multi-index `r` equal to one on `𝒞` and zero off
`𝒜 ∪ 𝒞`,
`‖U_r v‖_λ ≤ (∏_{i∈𝒜} ϱ_i^{-r_i}) M_k D_𝒜 ‖v‖_λ ∏_{i∈𝒞} c_i h_i`,
`λ = k/T`.  Inputs: `SegmentBound`, `BackgroundPreserves`,
`EntireCoefficients`, `DysonCrossCube`; hypotheses on the model: the norm
comparison `hcmp`, the vacuum start `hv` and `E:split-fresh-insertion`
(`hJ`, proved for the Fock model in `fock_insertion`). -/
theorem copy_coefficient_bound (A C : Finset ι) (Z : Finset ι → Set E)
    (emb : ℝ → E →L[ℂ] F) (J : ι → E → E) (P : (ι → ℂ) → ℝ → ℝ → E → E) (v : E)
    (c : (ι → ℕ) → E) (r : ι → ℕ) (a b h ϱ cI : ι → ℝ) (κ : ι → ℕ) (k : ℕ) (T : ℝ)
    (hT : 0 < T) (hk : 1 ≤ k) (hAk : A.card ≤ k) (hCk : C.card ≤ k) (hκ : ∑ i ∈ A, κ i ≤ k)
    (hh : ∀ i, 0 < h i) (hlen : ∀ i, b i - a i ≤ h i) (habC : ∀ i ∈ C, 0 ≤ a i ∧ b i ≤ T)
    (hϱ : ∀ i ∈ A, 0 < ϱ i) (hcI : ∀ i ∈ C, 0 ≤ cI i)
    (hr : ∀ i, i ∉ A → r i = if i ∈ C then 1 else 0)
    (hcmp : ∀ ρ ρ' : ℝ, 0 < ρ → 0 < ρ' → ∀ x, ‖emb ρ' x‖ ≤ max 1 (ρ / ρ') * ‖emb ρ x‖)
    (hv : v ∈ Z ∅)
    (hJ : ∀ i ∈ C, ∀ S ⊆ C, i ∉ S → ∀ x ∈ Z S, J i x ∈ Z (insert i S) ∧
      ∀ ρ, (k : ℝ) / T ≤ ρ → ‖emb ρ (J i x)‖ ≤ cI i * ‖emb ρ x‖)
    (hPZ : BackgroundPreserves A C Z P) (hseg : SegmentBound A emb P ϱ a b h κ k T)
    (hent : EntireCoefficients c) (hdys : DysonCrossCube A C c ϱ a b (word A C a b T J P v)) :
    ‖emb ((k : ℝ) / T) (c r)‖ ≤ (∏ i ∈ A, (ϱ i ^ r i)⁻¹) * Mk k *
      metricD ((k : ℝ) / T) h κ A * ‖emb ((k : ℝ) / T) v‖ * ∏ i ∈ C, cI i * h i := by
  set lam : ℝ := (k : ℝ) / T with hlamdef
  have hlam : 0 < lam := div_pos (by exact_mod_cast hk) hT
  set K : ℝ := Mk k * metricD lam h κ A * (∏ i ∈ C, cI i) * ‖emb lam v‖ with hKdef
  have hK0 : 0 ≤ K := by
    have h1 : 0 ≤ Mk k := by unfold Mk; positivity
    have h2 : 0 ≤ metricD lam h κ A :=
      Finset.prod_nonneg fun i _ => by have := hh i; positivity
    have h3 : 0 ≤ ∏ i ∈ C, cI i := Finset.prod_nonneg hcI
    positivity
  -- the word bound on every simplex
  have hword : ∀ z : ι → ℂ, (∀ i, i ∉ A → z i = 0) → (∀ i ∈ A, ‖z i‖ ≤ ϱ i) →
      ∀ o : Fin (Fintype.card C) ≃ C, ∀ tC ∈ simplex C a b o,
        ‖emb lam (word A C a b T J P v z (extTime C tC))‖ ≤ K := by
    intro z hz0 hzϱ o tC htC
    set t := extTime C tC with ht
    obtain ⟨hab, hinj⟩ := extTime_of_simplex C a b o tC htC
    have htT : ∀ i ∈ C, 0 < t i ∧ t i < T := fun i hi =>
      ⟨(habC i hi).1.trans_lt (hab i hi).1, (hab i hi).2.trans_le (habC i hi).2⟩
    obtain ⟨h0, hMT, hst, hcov⟩ := cutPt_spec A C a b t T hT htT
    have hcutA : ∀ i ∈ A, (0 < a i → a i < T → ∃ m ≤ nCut A C a b t T, cutPt A C a b t T m = a i) ∧
        (0 < b i → b i < T → ∃ m ≤ nCut A C a b t T, cutPt A C a b t T m = b i) := by
      intro i hi
      refine ⟨fun h1 h2 => hcov _ ?_, fun h1 h2 => hcov _ ?_⟩
      · exact mem_insert_of_mem (mem_insert_of_mem (mem_union_right _ (mem_filter.2
          ⟨mem_union_left _ (mem_image_of_mem a hi), h1, h2⟩)))
      · exact mem_insert_of_mem (mem_insert_of_mem (mem_union_right _ (mem_filter.2
          ⟨mem_union_right _ (mem_image_of_mem b hi), h1, h2⟩)))
    have hcutC : ∀ i ∈ C, ∃ m ≤ nCut A C a b t T, cutPt A C a b t T m = t i := fun i hi =>
      hcov _ (mem_insert_of_mem (mem_insert_of_mem (mem_union_left _ (mem_image_of_mem t hi))))
    have hM : nCut A C a b t T ≤ 3 * k + 1 :=
      partition_count_le _ A.card C.card k (nCut_le A C a b t T) hAk hCk
    exact word_chain A C Z emb J (P z) v a b h t cI κ k T (cutPt A C a b t T) (nCut A C a b t T)
      hT hk h0 hMT hst hcutA hcutC htT hinj hM (fun i _ => hh i) (fun i _ => hlen i) hκ hcI hcmp
      hv (hPZ z hz0) (hseg z hz0 hzϱ) hJ
  -- the cube bound on the torus
  have hext0 : ∀ z' : A → ℂ, ∀ i, i ∉ A → extAmp A z' i = 0 := fun z' i hi => by
    simp only [extAmp, hi, ↓reduceDIte]
  have hcube : ∀ z' : A → ℂ, (∀ i, ‖z' i‖ = ϱ i) →
      ‖emb lam (dysonSum C a b (word A C a b T J P v (extAmp A z')))‖ ≤ K * ∏ i ∈ C, h i := by
    intro z' hz'
    refine dysonSum_norm_le C a b h (emb lam) _ K hK0 (fun i _ => (hh i).le) (fun i _ => hlen i)
      fun o tC htC => hword _ (hext0 z') (fun i hi => ?_) o tC htC
    simp only [extAmp, hi, ↓reduceDIte]
    exact (hz' ⟨i, hi⟩).le
  -- torus extraction in `F`
  set ρA : A → ℝ := fun i => ϱ i with hρA
  have hρApos : ∀ i, 0 < ρA i := fun i => hϱ i i.2
  set cA : (A → ℕ) → F := fun s => emb lam (c (liftIdx A C s)) with hcA
  set ΦA : (A → ℂ) → F := fun z' => emb lam (dysonSum C a b (word A C a b T J P v (extAmp A z')))
    with hΦA
  have hsum : Summable fun s : A → ℕ => ‖cA s‖ * ∏ i, ρA i ^ s i := by
    set ρι : ι → ℝ := fun i => if i ∈ A then ϱ i else 1 with hρι
    have hρι0 : ∀ i, 0 ≤ ρι i := fun i => by
      simp only [hρι]; split_ifs with hi
      · exact (hϱ i hi).le
      · exact zero_le_one
    have hinjL : Function.Injective (liftIdx A C) := by
      intro s s' hss
      funext i
      have := congrFun hss i
      simpa [liftIdx, i.2] using this
    have hs2 := (hent ρι hρι0).comp_injective hinjL
    have hprod : ∀ s : A → ℕ, ∏ i, ρι i ^ liftIdx A C s i = ∏ i, ρA i ^ s i := by
      intro s
      rw [← Finset.prod_subset (subset_univ A) fun i _ hi => by
        simp only [hρι, liftIdx, hi, ↓reduceDIte, ↓reduceIte, one_pow]]
      rw [← Finset.prod_coe_sort A]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [hρι, hρA, liftIdx, i.2, ↓reduceDIte, ↓reduceIte, Subtype.coe_eta]
    refine Summable.of_nonneg_of_le
      (fun s => mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun i _ =>
        pow_nonneg (hρApos i).le _)) (fun s => ?_)
      (hs2.mul_left ‖emb lam‖)
    simp only [Function.comp_apply, hcA, ← hprod s]
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right ((emb lam).le_opNorm _)
      (Finset.prod_nonneg fun i _ => pow_nonneg (hρι0 i) _)
  have hΦ : ∀ θ : A → ℝ, HasSum (fun s => monom (torusPoint ρA θ) s • cA s)
      (ΦA (torusPoint ρA θ)) := by
    intro θ
    have h1 := (hdys (torusPoint ρA θ)
      (fun i => norm_torusPoint ρA θ (fun i => (hρApos i).le) i)).2.mapL (emb lam)
    simp only [map_smul] at h1
    exact h1
  have hK : ∀ θ : A → ℝ, ‖ΦA (torusPoint ρA θ)‖ ≤ K * ∏ i ∈ C, h i := fun θ =>
    hcube _ fun i => norm_torusPoint ρA θ (fun i => (hρApos i).le) i
  have htor := torus_coefficient_norm_le cA ΦA ρA (fun i => r i) hρApos hsum hΦ _ hK
  have hlift : liftIdx A C (fun i => r i) = r := by
    funext i
    by_cases hi : i ∈ A
    · simp only [liftIdx, hi, ↓reduceDIte]
    · simp only [liftIdx, hi, ↓reduceDIte]; rw [hr i hi]
  have hcr : cA (fun i => r i) = emb lam (c r) := by simp only [hcA, hlift]
  rw [hcr] at htor
  have hpA : ∏ i : A, (ρA i ^ r i)⁻¹ = ∏ i ∈ A, (ϱ i ^ r i)⁻¹ :=
    Finset.prod_coe_sort A fun i => (ϱ i ^ r i)⁻¹
  rw [hpA] at htor
  refine htor.trans (le_of_eq ?_)
  rw [Finset.prod_mul_distrib, hKdef]; ring

end Copy

/-! ### The two copies: `E:split-before-absorption` and `E:fixed-split-bound` -/

section TwoCopies

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [DecidableEq ι] in
/-- Auxiliary (Lean route): the counting facts of main TeX lines 3750-3754
for one copy: `|𝒜| ≤ k`, `|𝒞| ≤ k`, `∑_{i∈𝒜} k_i ≤ k`, from
`∑_i k_i = k`, `𝒜 ⊆ ℬ` and `k_i = 1` on `𝒞`. -/
theorem copy_counts (κ : ι → ℕ) (p : ι → ℕ × ℕ) (k : ℕ) (hsum : ∑ i, κ i = k)
    (A : Finset ι) (hA : A ⊆ backSet κ p) :
    A.card ≤ k ∧ (crossSet κ p).card ≤ k ∧ ∑ i ∈ A, κ i ≤ k := by
  have hle : ∀ S : Finset ι, ∑ i ∈ S, κ i ≤ k := fun S =>
    hsum ▸ Finset.sum_le_sum_of_subset_of_nonneg (subset_univ S) fun _ _ _ => Nat.zero_le _
  refine ⟨?_, ?_, hle A⟩
  · refine le_trans ?_ (hle A)
    rw [card_eq_sum_ones]
    refine Finset.sum_le_sum fun i hi => ?_
    have := (mem_filter.1 (hA hi)).2.1
    omega
  · refine le_trans (le_of_eq ?_) (hle (crossSet κ p))
    rw [card_eq_sum_ones]
    exact Finset.sum_congr rfl fun i hi => ((mem_filter.1 hi).2.1).symm

/-- Auxiliary (Lean route): the degrees of each copy are one on `𝒞` and
zero off `𝒜_r ∪ 𝒞` (resp. `𝒜_q ∪ 𝒞`), main TeX lines 3750-3754 and
3985-3987. -/
theorem copy_degrees (κ : ι → ℕ) (p : ι → ℕ × ℕ) (hp : ∀ i, (p i).1 + (p i).2 = 2 * κ i) :
    (∀ i, i ∉ copyFirst κ p → (p i).1 = if i ∈ crossSet κ p then 1 else 0) ∧
      ∀ i, i ∉ copySecond κ p → (p i).2 = if i ∈ crossSet κ p then 1 else 0 := by
  constructor <;> intro i hi <;>
    simp only [copyFirst, copySecond, backSet, crossSet, mem_filter, mem_univ, true_and,
      not_and, not_lt] at hi ⊢ <;> have := hp i <;> split_ifs with hc
  · rw [hc.2]
  · by_cases h0 : κ i = 0
    · omega
    · exact Nat.le_zero.1 (hi ⟨h0, fun h1 h2 => hc ⟨h1, h2⟩⟩)
  · rw [hc.2]
  · by_cases h0 : κ i = 0
    · omega
    · exact Nat.le_zero.1 (hi ⟨h0, fun h1 h2 => hc ⟨h1, h2⟩⟩)

/-- **`L:fixed-split` in an abstract phase model** (main TeX lines
3675-4050).  Phase norms are `‖emb_ρ ·‖` for continuous linear maps into an
inner product space `F` (in the TeX `‖(f,g)‖_ρ² = ‖f‖² + ‖A_ρ^{-1/2}g‖²` on
`L²(Ω; X_ρ)`), and the inner product of `E:fixed-split-bound` is
`⟪emb_{1/T} ·, emb_{1/T} ·⟫`.  For a degree split `κ` (`∑ k_i = k ≥ 1`)
and a split `p_i = (r_i, q_i)` (`r_i + q_i = 2k_i`), with the cutoff
evolution's ordinary coefficients `c` (`U_r v = c_r`), the per-copy model
data (cross subspaces `Z₁`, `Z₂` over `𝒜_r`, `𝒜_q`) and the supplied inputs
of `copy_coefficient_bound` for both copies,
`|⟪U_r v, U_q v⟫_{1/T}| ≤ k² C_split^k R_α^k V ∏_i splitFactor_i` with
`C_split = splitConst δ` and `V ≥ ‖v‖_{1/T}²`. -/
theorem fixed_split_abstract (Z₁ Z₂ : Finset ι → Set E) (emb : ℝ → E →L[ℂ] F)
    (J : ι → E → E) (P : (ι → ℂ) → ℝ → ℝ → E → E) (v : E) (c : (ι → ℕ) → E)
    (κ : ι → ℕ) (p : ι → ℕ × ℕ) (a b h σ : ι → ℝ) (alpha δ R T V : ℝ) (k : ℕ)
    (hT : 0 < T) (hk : 1 ≤ k) (hsum : ∑ i, κ i = k) (hp : ∀ i, (p i).1 + (p i).2 = 2 * κ i)
    (hδ : 0 < δ) (hR : 0 < R) (hα : alpha ≤ 3) (hσ : ∀ i, 0 < σ i) (hh : ∀ i, 0 < h i)
    (hlen : ∀ i, b i - a i ≤ h i) (habC : ∀ i ∈ crossSet κ p, 0 ≤ a i ∧ b i ≤ T)
    (hcmp : ∀ ρ ρ' : ℝ, 0 < ρ → 0 < ρ' → ∀ x, ‖emb ρ' x‖ ≤ max 1 (ρ / ρ') * ‖emb ρ x‖)
    (hV : ‖emb (1 / T) v‖ ^ 2 ≤ V) (hv₁ : v ∈ Z₁ ∅) (hv₂ : v ∈ Z₂ ∅)
    (hJ₁ : ∀ i ∈ crossSet κ p, ∀ S ⊆ crossSet κ p, i ∉ S → ∀ x ∈ Z₁ S,
      J i x ∈ Z₁ (insert i S) ∧ ∀ ρ, (k : ℝ) / T ≤ ρ →
        ‖emb ρ (J i x)‖ ≤ insertConst alpha R ((k : ℝ) / T) (σ i) * ‖emb ρ x‖)
    (hJ₂ : ∀ i ∈ crossSet κ p, ∀ S ⊆ crossSet κ p, i ∉ S → ∀ x ∈ Z₂ S,
      J i x ∈ Z₂ (insert i S) ∧ ∀ ρ, (k : ℝ) / T ≤ ρ →
        ‖emb ρ (J i x)‖ ≤ insertConst alpha R ((k : ℝ) / T) (σ i) * ‖emb ρ x‖)
    (hPZ₁ : BackgroundPreserves (copyFirst κ p) (crossSet κ p) Z₁ P)
    (hPZ₂ : BackgroundPreserves (copySecond κ p) (crossSet κ p) Z₂ P)
    (hseg₁ : SegmentBound (copyFirst κ p) emb P
      (fun i => splitRadius alpha δ (σ i) R (h i) (κ i)) a b h κ k T)
    (hseg₂ : SegmentBound (copySecond κ p) emb P
      (fun i => splitRadius alpha δ (σ i) R (h i) (κ i)) a b h κ k T)
    (hent : EntireCoefficients c)
    (hdys₁ : DysonCrossCube (copyFirst κ p) (crossSet κ p) c
      (fun i => splitRadius alpha δ (σ i) R (h i) (κ i)) a b
      (word (copyFirst κ p) (crossSet κ p) a b T J P v))
    (hdys₂ : DysonCrossCube (copySecond κ p) (crossSet κ p) c
      (fun i => splitRadius alpha δ (σ i) R (h i) (κ i)) a b
      (word (copySecond κ p) (crossSet κ p) a b T J P v)) :
    ‖inner ℂ (emb (1 / T) (c fun i => (p i).1)) (emb (1 / T) (c fun i => (p i).2))‖ ≤
      (k : ℝ) ^ 2 * splitConst δ ^ k * R ^ k * V *
        ∏ i, splitFactor alpha (σ i) (h i) ((k : ℝ) / T) (κ i) (p i) := by
  set lam : ℝ := (k : ℝ) / T with hlamdef
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hlam : 0 < lam := div_pos hk0 hT
  have hT1 : (0 : ℝ) < 1 / T := one_div_pos.2 hT
  have hratio1 : lam / (1 / T) = k := by rw [hlamdef]; field_simp
  have hratio2 : (1 / T) / lam = 1 / k := by rw [hlamdef]; field_simp
  have hup : ∀ x, ‖emb (1 / T) x‖ ≤ k * ‖emb lam x‖ := fun x => by
    have := hcmp lam (1 / T) hlam hT1 x
    rwa [hratio1, max_eq_right (by exact_mod_cast hk)] at this
  have hdown : ‖emb lam v‖ ≤ ‖emb (1 / T) v‖ := by
    have := hcmp (1 / T) lam hT1 hlam v
    rwa [hratio2, max_eq_left (by rw [div_le_one hk0]; exact_mod_cast hk), one_mul] at this
  obtain ⟨hdeg₁, hdeg₂⟩ := copy_degrees κ p hp
  have hA₁ : copyFirst κ p ⊆ backSet κ p := filter_subset _ _
  have hA₂ : copySecond κ p ⊆ backSet κ p := filter_subset _ _
  obtain ⟨hAk₁, hCk, hκ₁⟩ := copy_counts κ p k hsum _ hA₁
  obtain ⟨hAk₂, -, hκ₂⟩ := copy_counts κ p k hsum _ hA₂
  have hϱ : ∀ A ⊆ backSet κ p, ∀ i ∈ A, 0 < splitRadius alpha δ (σ i) R (h i) (κ i) :=
    fun A hA i hi => splitRadius_pos alpha δ (σ i) R (h i) (κ i) hδ (hσ i) hR (hh i)
      (Nat.one_le_iff_ne_zero.2 (mem_filter.1 (hA hi)).2.1)
  have hcI : ∀ i ∈ crossSet κ p, 0 ≤ insertConst alpha R lam (σ i) := fun i _ => by
    unfold insertConst; have := hσ i; positivity
  have hu₁ := copy_coefficient_bound (copyFirst κ p) (crossSet κ p) Z₁ emb J P v c
    (fun i => (p i).1) a b h (fun i => splitRadius alpha δ (σ i) R (h i) (κ i))
    (fun i => insertConst alpha R lam (σ i)) κ k T hT hk hAk₁ hCk hκ₁ hh hlen habC
    (hϱ _ hA₁) hcI hdeg₁ hcmp hv₁ hJ₁ hPZ₁ hseg₁ hent hdys₁
  have hu₂ := copy_coefficient_bound (copySecond κ p) (crossSet κ p) Z₂ emb J P v c
    (fun i => (p i).2) a b h (fun i => splitRadius alpha δ (σ i) R (h i) (κ i))
    (fun i => insertConst alpha R lam (σ i)) κ k T hT hk hAk₂ hCk hκ₂ hh hlen habC
    (hϱ _ hA₂) hcI hdeg₂ hcmp hv₂ hJ₂ hPZ₂ hseg₂ hent hdys₂
  set X := ‖inner ℂ (emb (1 / T) (c fun i => (p i).1)) (emb (1 / T) (c fun i => (p i).2))‖
  have hX : X ≤ (k : ℝ) ^ 2 * ‖emb lam (c fun i => (p i).1)‖ * ‖emb lam (c fun i => (p i).2)‖ :=
    (norm_inner_le_norm _ _).trans (by
      have h1 := hup (c fun i => (p i).1)
      have h2 := hup (c fun i => (p i).2)
      calc ‖emb (1 / T) (c fun i => (p i).1)‖ * ‖emb (1 / T) (c fun i => (p i).2)‖
          ≤ (k * ‖emb lam (c fun i => (p i).1)‖) * (k * ‖emb lam (c fun i => (p i).2)‖) :=
            mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ = _ := by ring)
  have hbefore := split_before_absorption alpha δ R lam (Mk k) ‖emb lam v‖ X _ _ k σ h κ p hp
    hR.le hlam hX (norm_nonneg _) (norm_nonneg _) hu₁ hu₂
  have hbf0 : 0 ≤ ∏ i, beforeFactor alpha δ R (σ i) (h i) lam (κ i) (p i) :=
    Finset.prod_nonneg fun i _ =>
      beforeFactor_nonneg alpha δ R (σ i) (h i) lam (κ i) (p i) hδ (hσ i) hR (hh i) hlam
  have hnv : ‖emb lam v‖ ^ 2 ≤ V :=
    (pow_le_pow_left₀ (norm_nonneg _) hdown 2).trans hV
  have hX2 : X ≤ (k : ℝ) ^ 2 * Mk k ^ 2 * V *
      ∏ i, beforeFactor alpha δ R (σ i) (h i) lam (κ i) (p i) := by
    have hM0 : 0 ≤ (k : ℝ) ^ 2 * Mk k ^ 2 := by positivity
    exact hbefore.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnv hM0) hbf0)
  exact split_absorption univ alpha δ R lam X V σ h κ p k hk hsum hδ hR hlam hα
    ((sq_nonneg _).trans hV) (fun i _ => hσ i) (fun i _ => hh i) hX2

end TwoCopies

/-! ### The Fock model: `𝒵_S` as coefficient subspaces, `E:split-fresh-insertion` -/

section Fock

open StratonovichHAMSecondMoment.HermiteFock
open StratonovichHAMSecondMoment.GaussianHermite (unitIdx)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
variable {m : ℕ}

/-- The Hermite degree of color `i` of a multi-index over the Gaussian modes
`Fin m`, each mode `j` belonging to the color `col j` (the modes `g_{ij}` of
the field `W_i`, main TeX lines 3678-3680). -/
def colorDeg (col : Fin m → ι) (k : Fin m → ℕ) (i : ι) : ℕ :=
  ∑ j ∈ univ.filter (fun j => col j = i), k j

/-- The multi-indices retained by the Hermite cutoffs `P = ⊗_i P_{N_i}`
(main TeX lines 3680-3682): color degree at most `N_i` in every color. -/
def cutIdx (col : Fin m → ι) (N : ι → ℕ) : Finset (Fin m → ℕ) :=
  (Fintype.piFinset fun j => range (N (col j) + 1)).filter fun k => ∀ i, colorDeg col k i ≤ N i

/-- Coefficient vectors of the cutoff Gaussian space with values in the
spatial band space `X`: the Hermite expansion `∑_k hk_k ⊗ f_k`. -/
abbrev CoefSp (X : Type*) (col : Fin m → ι) (N : ι → ℕ) := ↥(cutIdx col N) → X

/-- Phase vectors `(f, g)` over the cutoff Gaussian space (`ℋ_ρ` as a
vector space). -/
abbrev PhaseSp (X : Type*) (col : Fin m → ι) (N : ι → ℕ) := CoefSp X col N × CoefSp X col N

omit [Fintype ι] in
/-- Auxiliary (Lean route): `k j ≤ colorDeg k (col j)`. -/
theorem le_colorDeg (col : Fin m → ι) (k : Fin m → ℕ) (j : Fin m) : k j ≤ colorDeg col k (col j) :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_filter.2 ⟨mem_univ j, rfl⟩)

/-- Membership in the cutoff: every color degree is at most `N_i`. -/
theorem mem_cutIdx (col : Fin m → ι) (N : ι → ℕ) (k : Fin m → ℕ) :
    k ∈ cutIdx col N ↔ ∀ i, colorDeg col k i ≤ N i := by
  simp only [cutIdx, mem_filter, Fintype.mem_piFinset, mem_range, and_iff_right_iff_imp]
  intro h j
  have := (le_colorDeg col k j).trans (h (col j))
  omega

omit [Fintype ι] in
/-- Auxiliary (Lean route): adding the unit index of mode `j` raises the
degree of the color `col j` by one. -/
theorem colorDeg_add_unitIdx (col : Fin m → ι) (k : Fin m → ℕ) (j : Fin m) (i : ι) :
    colorDeg col (k + unitIdx j) i = colorDeg col k i + if col j = i then 1 else 0 := by
  unfold colorDeg
  simp only [Pi.add_apply, Finset.sum_add_distrib, unitIdx]
  congr 1
  rw [Finset.sum_pi_single']
  simp only [mem_filter, mem_univ, true_and]

omit [Fintype ι] in
/-- Auxiliary (Lean route): for `k_j ≠ 0`,
`colorDeg k i = colorDeg (k - e_j) i + [col j = i]`. -/
theorem colorDeg_sub_unitIdx (col : Fin m → ι) {k : Fin m → ℕ} {j : Fin m} (hk : k j ≠ 0)
    (i : ι) : colorDeg col k i = colorDeg col (k - unitIdx j) i + if col j = i then 1 else 0 := by
  conv_lhs => rw [← sub_add_unitIdx hk]
  exact colorDeg_add_unitIdx col _ j i

omit [Fintype ι] in
/-- Auxiliary (Lean route): `colorDeg` is monotone in the multi-index. -/
theorem colorDeg_mono (col : Fin m → ι) {l k : Fin m → ℕ} (h : ∀ j, l j ≤ k j) (i : ι) :
    colorDeg col l i ≤ colorDeg col k i :=
  Finset.sum_le_sum fun j _ => h j

/-- Extension of a cutoff coefficient vector by zero to all multi-indices. -/
def extC {col : Fin m → ι} {N : ι → ℕ} (f : CoefSp X col N) : (Fin m → ℕ) → X :=
  fun l => if h : l ∈ cutIdx col N then f ⟨l, h⟩ else 0

/-- **The cross subspace `𝒵_S` on coefficients** (main TeX lines 3845-3855):
coefficient vectors supported on multi-indices with color degree one on every
`i ∈ S` and zero on every color outside `𝒜 ∪ S` (in particular on
`𝒞 ∖ S`); background colors `i ∈ 𝒜` keep every degree `≤ N_i` retained by
the cutoff.  In the Hermite basis this is the tensor subspace
`⊗_{𝒜} 𝒢_i^{≤N_i} ⊗ ⊗_S 𝒢_i^{(1)} ⊗ ⊗_{𝒞∖S} 𝒢_i^{(0)}` with every omitted
color in its vacuum, tensored with the spatial band. -/
def ZCoef (X : Type*) [NormedAddCommGroup X] (col : Fin m → ι) (N : ι → ℕ) (A S : Finset ι) :
    Set (CoefSp X col N) :=
  {f | ∀ k, f k ≠ 0 → (∀ i ∈ S, colorDeg col k.1 i = 1) ∧
    ∀ i, i ∉ A → i ∉ S → colorDeg col k.1 i = 0}

/-- The phase over `𝒵_S`: both components in `ZCoef`. -/
def fockZ (X : Type*) [NormedAddCommGroup X] (col : Fin m → ι) (N : ι → ℕ) (A S : Finset ι) :
    Set (PhaseSp X col N) :=
  {x | x.1 ∈ ZCoef X col N A S ∧ x.2 ∈ ZCoef X col N A S}

/-- The color-`i` field `∑_{j: col j = i} g_{ij} ⊗ B_j` on coefficients,
followed by the cutoff (restriction to `cutIdx`), with `B_j = S_b M_{e_{ij}}
S_b` (main TeX lines 3682-3685). -/
def insField {col : Fin m → ι} {N : ι → ℕ} (B : Fin m → X →L[ℂ] X) (i : ι)
    (f : CoefSp X col N) : CoefSp X col N :=
  fun k => ∑ j ∈ univ.filter (fun j => col j = i), gmul j (fun l => B j (extC f l)) k.1

/-- **The insertion `J_i(u, w) = (0, σ_i B_i u)`** (main TeX line 3861). -/
def fockJ {col : Fin m → ι} {N : ι → ℕ} (σ : ι → ℝ) (B : Fin m → X →L[ℂ] X) (i : ι)
    (x : PhaseSp X col N) : PhaseSp X col N :=
  (0, ((σ i : ℝ) : ℂ) • insField B i x.1)

/-- The phase norm `‖(f, g)‖_ρ² = ‖f‖² + ‖A_ρ^{-1/2} g‖²` on `L²(Ω; X)`
(main TeX lines 3370-3372), realized as the norm of the vector
`(f_k, S_ρ g_k)_k` in `ℓ²` over two copies of the cutoff multi-indices
(`S_ρ` standing for `A_ρ^{-1/2}`).  By the Hermite isometry
(`HermiteFock.integral_norm_sq_iota`) the coefficient norm is the Gaussian
`L²` norm. -/
def fockEmb {col : Fin m → ι} {N : ι → ℕ} (S : ℝ → X →L[ℂ] X) (ρ : ℝ) :
    PhaseSp X col N →L[ℂ] PiLp 2 (fun _ : ↥(cutIdx col N) ⊕ ↥(cutIdx col N) => X) :=
  (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : ↥(cutIdx col N) ⊕ ↥(cutIdx col N) => X)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi
      (Sum.elim (fun k => (ContinuousLinearMap.proj k) ∘L ContinuousLinearMap.fst ℂ _ _)
        fun k => S ρ ∘L (ContinuousLinearMap.proj k) ∘L ContinuousLinearMap.snd ℂ _ _)

/-- The phase norm formula. -/
theorem fockEmb_norm_sq {col : Fin m → ι} {N : ι → ℕ} (S : ℝ → X →L[ℂ] X) (ρ : ℝ)
    (x : PhaseSp X col N) :
    ‖fockEmb S ρ x‖ ^ 2 = ∑ k, ‖x.1 k‖ ^ 2 + ∑ k, ‖S ρ (x.2 k)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_sum_type]
  simp [fockEmb]

/-- The vacuum vector `1 ⊗ u` on the cutoff space. -/
def vacC {col : Fin m → ι} {N : ι → ℕ} (u : X) : CoefSp X col N :=
  fun k => if k.1 = 0 then u else 0

/-- The projected deterministic initial phase `(u, w)` in the Gaussian vacuum
(main TeX lines 3689-3691). -/
def vacPhase {col : Fin m → ι} {N : ι → ℕ} (u w : X) : PhaseSp X col N := (vacC u, vacC w)

omit [InnerProductSpace ℂ X] in
/-- The vacuum phase lies in `𝒵_∅` (main TeX line 3895, "Starting with
`𝒵_∅`"). -/
theorem vacPhase_mem (col : Fin m → ι) (N : ι → ℕ) (A : Finset ι) (u w : X) :
    (vacPhase u w : PhaseSp X col N) ∈ fockZ X col N A ∅ := by
  have h : ∀ y : X, (vacC y : CoefSp X col N) ∈ ZCoef X col N A ∅ := by
    intro y k hk
    have hk0 : k.1 = 0 := by by_contra h; exact hk (by simp [vacC, h])
    refine ⟨fun i hi => absurd hi (Finset.notMem_empty i), fun i _ _ => ?_⟩
    simp [colorDeg, hk0]
  exact ⟨h u, h w⟩

/-- The norm of the vacuum phase: `‖(u, w)‖_ρ² = ‖u‖² + ‖A_ρ^{-1/2} w‖²`. -/
theorem fockEmb_vacPhase (col : Fin m → ι) (N : ι → ℕ) (S : ℝ → X →L[ℂ] X) (ρ : ℝ) (u w : X) :
    ‖fockEmb S ρ (vacPhase u w : PhaseSp X col N)‖ ^ 2 = ‖u‖ ^ 2 + ‖S ρ w‖ ^ 2 := by
  have h0 : (0 : Fin m → ℕ) ∈ cutIdx col N := (mem_cutIdx col N 0).2 fun i => by
    simp [colorDeg]
  have hsum : ∀ g : X → ℝ, g 0 = 0 → ∀ y : X,
      ∑ k : ↥(cutIdx col N), g (if k.1 = 0 then y else 0) = g y := by
    intro g hg y
    rw [Finset.sum_eq_single (⟨0, h0⟩ : ↥(cutIdx col N))]
    · simp
    · intro k _ hk
      have : k.1 ≠ 0 := fun h => hk (Subtype.ext h)
      simp [this, hg]
    · intro h; exact absurd (mem_univ _) h
  rw [fockEmb_norm_sq]
  simp only [vacPhase, vacC]
  rw [hsum (fun y => ‖y‖ ^ 2) (by simp) u]
  have := hsum (fun y => ‖S ρ y‖ ^ 2) (by simp) w
  simpa using this

/-- The identity between phase norms (main TeX lines 3811-3817): from the
spectral inequality `‖S_{ρ'} g‖ ≤ max{1, ρ/ρ'} ‖S_ρ g‖` for the spatial
`A^{-1/2}`, the identity from `‖·‖_ρ` to `‖·‖_{ρ'}` has norm at most
`max{1, ρ/ρ'}` (the first component is unweighted). -/
theorem fockEmb_cmp {col : Fin m → ι} {N : ι → ℕ} (S : ℝ → X →L[ℂ] X)
    (hScmp : ∀ ρ ρ' : ℝ, 0 < ρ → 0 < ρ' → ∀ g, ‖S ρ' g‖ ≤ max 1 (ρ / ρ') * ‖S ρ g‖) :
    ∀ ρ ρ' : ℝ, 0 < ρ → 0 < ρ' → ∀ x : PhaseSp X col N,
      ‖fockEmb S ρ' x‖ ≤ max 1 (ρ / ρ') * ‖fockEmb S ρ x‖ := by
  intro ρ ρ' hρ hρ' x
  set q := max 1 (ρ / ρ') with hq
  have hq1 : 1 ≤ q := le_max_left _ _
  have hsq : ‖fockEmb S ρ' x‖ ^ 2 ≤ (q * ‖fockEmb S ρ x‖) ^ 2 := by
    rw [mul_pow, fockEmb_norm_sq, fockEmb_norm_sq]
    have h1 : ∑ k, ‖S ρ' (x.2 k)‖ ^ 2 ≤ q ^ 2 * ∑ k, ‖S ρ (x.2 k)‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hScmp ρ ρ' hρ hρ' _) 2
    have h2 : 0 ≤ ∑ k, ‖x.1 k‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    have h3 : (1 : ℝ) ≤ q ^ 2 := by nlinarith
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

/-- Auxiliary (Lean route): a continuous linear map on `X` commutes with
`g_j` acting on coefficients. -/
theorem gmul_map (L : X →L[ℂ] X) (j : Fin m) (v : (Fin m → ℕ) → X) (k : Fin m → ℕ) :
    L (gmul j v k) = gmul j (fun l => L (v l)) k := by
  simp only [gmul, cre, ann, map_add, map_smul]

/-- **Vacuum insertion on coefficients** (the coefficient form of
`HermiteFock.vacuum_insertion_isometry`, with the other colors as an
arbitrary coefficient factor, main TeX lines 3861-3889): if every `w_j`
(`col j = i`) vanishes off color-`i` degree zero, then the color-`i` field
`∑_{col j = i} g_j w_j` acts only by creation from the vacuum of color `i`,
its terms have disjoint supports, and
`∑_{k ∈ cutoff} ‖∑_j (g_j w_j)_k‖² ≤ ∑_j ∑_{l ∈ cutoff} ‖w_{j,l}‖²`. -/
theorem coef_insertion (col : Fin m → ι) (N : ι → ℕ) (i : ι) (w : Fin m → (Fin m → ℕ) → X)
    (hw : ∀ j, col j = i → ∀ l, w j l ≠ 0 → colorDeg col l i = 0) :
    ∑ k ∈ cutIdx col N, ‖∑ j ∈ univ.filter (fun j => col j = i), gmul j (w j) k‖ ^ 2 ≤
      ∑ j ∈ univ.filter (fun j => col j = i), ∑ l ∈ cutIdx col N, ‖w j l‖ ^ 2 := by
  set Ji := univ.filter (fun j : Fin m => col j = i) with hJi
  have hmemJ : ∀ j, j ∈ Ji ↔ col j = i := fun j => by simp [hJi]
  -- annihilation vanishes
  have hgm : ∀ j ∈ Ji, ∀ k, gmul j (w j) k = cre j (w j) k := by
    intro j hj k
    have hz : w j (k + unitIdx j) = 0 := by
      by_contra hne
      have h1 := hw j ((hmemJ j).1 hj) _ hne
      rw [colorDeg_add_unitIdx, ite_eq_left_of_eq_true _ _ (eq_true ((hmemJ j).1 hj))] at h1
      omega
    simp [gmul, ann, hz]
  -- a nonzero creation term pins the color-`i` part of `k` to `e_j`
  have hpin : ∀ j ∈ Ji, ∀ k, cre j (w j) k ≠ 0 → k j = 1 ∧ colorDeg col k i = 1 := by
    intro j hj k hne
    have hkj : k j ≠ 0 := fun h => hne (cre_of_eq_zero j (w j) h)
    have hw0 : w j (k - unitIdx j) ≠ 0 := fun h => hne (by simp [cre, h])
    have h1 := hw j ((hmemJ j).1 hj) _ hw0
    have h2 := colorDeg_sub_unitIdx col hkj i
    rw [ite_eq_left_of_eq_true _ _ (eq_true ((hmemJ j).1 hj)), h1] at h2
    have h3 := le_colorDeg col k j
    rw [(hmemJ j).1 hj] at h3
    omega
  -- step B: at most one term
  have hB : ∀ k, ‖∑ j ∈ Ji, gmul j (w j) k‖ ^ 2 ≤ ∑ j ∈ Ji, ‖cre j (w j) k‖ ^ 2 := by
    intro k
    rw [Finset.sum_congr rfl fun j hj => hgm j hj k]
    by_cases hex : ∃ j ∈ Ji, cre j (w j) k ≠ 0
    · obtain ⟨j0, hj0, hne0⟩ := hex
      rw [Finset.sum_eq_single_of_mem j0 hj0 fun j hj hne => ?_]
      · exact Finset.single_le_sum (f := fun j => ‖cre j (w j) k‖ ^ 2)
          (fun _ _ => by positivity) hj0
      · by_contra hcj
        obtain ⟨hk1, hdeg⟩ := hpin j hj k hcj
        obtain ⟨hk0, -⟩ := hpin j0 hj0 k hne0
        have hsub : ({j, j0} : Finset (Fin m)) ⊆ Ji := by
          intro x hx; simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
        have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := k) hsub
          fun _ _ _ => Nat.zero_le _
        rw [Finset.sum_pair hne] at hle
        have : colorDeg col k i = ∑ x ∈ Ji, k x := rfl
        omega
    · push Not at hex
      rw [Finset.sum_eq_zero hex, norm_zero, sq, mul_zero]
      exact Finset.sum_nonneg fun _ _ => by positivity
  -- step D: reindex each creation sum
  have hD : ∀ j ∈ Ji, ∑ k ∈ cutIdx col N, ‖cre j (w j) k‖ ^ 2 ≤
      ∑ l ∈ cutIdx col N, ‖w j l‖ ^ 2 := by
    intro j hj
    set s' := (cutIdx col N).filter fun k => k j ≠ 0 with hs'
    have h1 : ∑ k ∈ cutIdx col N, ‖cre j (w j) k‖ ^ 2 = ∑ k ∈ s', ‖w j (k - unitIdx j)‖ ^ 2 := by
      rw [hs', Finset.sum_filter]
      refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs with hk
      · by_cases hz : w j (k - unitIdx j) = 0
        · simp [cre, hz]
        · have hk1 := (hpin j hj k (by
            simp only [cre, ne_eq, smul_eq_zero, Complex.ofReal_eq_zero, Real.sqrt_eq_zero',
              not_or, not_le]
            exact ⟨by exact_mod_cast Nat.pos_of_ne_zero hk, hz⟩)).1
          simp [cre, hk1]
      · simp [cre_of_eq_zero j (w j) (by omega : k j = 0)]
    have hinj : Set.InjOn (fun k => k - unitIdx j) (s' : Set (Fin m → ℕ)) := by
      intro k hk k' hk' heq
      have e1 := sub_add_unitIdx (k := k) (mem_filter.1 hk).2
      have e2 := sub_add_unitIdx (k := k') (mem_filter.1 hk').2
      simp only at heq
      rw [← e1, ← e2, heq]
    have hsub : s'.image (fun k => k - unitIdx j) ⊆ cutIdx col N := by
      intro l hl
      obtain ⟨k, hk, rfl⟩ := mem_image.1 hl
      rw [mem_cutIdx]
      exact fun i' => (colorDeg_mono col (fun j' => by simp [Pi.sub_apply])) i' |>.trans
        ((mem_cutIdx col N k).1 (mem_filter.1 hk).1 i')
    rw [h1, ← Finset.sum_image (f := fun l => ‖w j l‖ ^ 2) hinj]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
  calc ∑ k ∈ cutIdx col N, ‖∑ j ∈ Ji, gmul j (w j) k‖ ^ 2
      ≤ ∑ k ∈ cutIdx col N, ∑ j ∈ Ji, ‖cre j (w j) k‖ ^ 2 := Finset.sum_le_sum fun k _ => hB k
    _ = ∑ j ∈ Ji, ∑ k ∈ cutIdx col N, ‖cre j (w j) k‖ ^ 2 := Finset.sum_comm
    _ ≤ ∑ j ∈ Ji, ∑ l ∈ cutIdx col N, ‖w j l‖ ^ 2 := Finset.sum_le_sum hD


/-- The modes of color `i` only: `M_{e_j}` for `col j = i`, zero otherwise
(the field `W_i^ε = ∑_j g_{ij} e_{ij}` of one color, main TeX lines 3678-3680). -/
def colorMask (col : Fin m → ι) (i : ι) (Mlt : Fin m → X →L[ℂ] X) (j : Fin m) : X →L[ℂ] X :=
  if col j = i then Mlt j else 0

omit [Fintype ι] in
/-- The band-compressed column bound of one color (main TeX lines 3444-3447,
through `FockForm.interval_contractions` (a)): the named input `FockColumn`
for `A_ρ^{-1/2} M_{e_{ij}}` (`E:interval-column`, lines 3388-3391) gives it
for `A_ρ^{-1/2} S_b M_{e_{ij}} S_b`. -/
theorem fockColumn_masked (col : Fin m → ι) (i : ι) {R ρ alpha : ℝ} (hR : 0 ≤ R) (hρ : 0 < ρ)
    (Sρ : X →L[ℂ] X) (hSs : ∀ u w, inner ℂ (Sρ u) w = inner ℂ u (Sρ w))
    (hSn : ∀ f, ‖Sρ f‖ ≤ ρ⁻¹ * ‖f‖) (Mlt : Fin m → X →L[ℂ] X)
    (hM : ∀ j u w, inner ℂ (Mlt j u) w = inner ℂ u (Mlt j w))
    (hcol : FockForm.FockColumn (fun j => Sρ ∘L colorMask col i Mlt j) (R * ρ ^ (alpha - 2)))
    (Pb : X →L[ℂ] X) (hPs : ∀ u w, inner ℂ (Pb u) w = inner ℂ u (Pb w))
    (hPP : ∀ u, Pb (Pb u) = Pb u) (hPS : ∀ u, Pb (Sρ u) = Sρ (Pb u)) :
    FockForm.FockColumn (fun j => if col j = i then Sρ ∘L (Pb ∘L Mlt j ∘L Pb) else 0)
      (R * ρ ^ (alpha - 2)) := by
  have hMm : ∀ j u w, inner ℂ (colorMask col i Mlt j u) w =
      inner ℂ u (colorMask col i Mlt j w) := by
    intro j u w; unfold colorMask; split_ifs
    · exact hM j u w
    · simp
  have h := (FockForm.interval_contractions hR hρ Sρ hSs hSn (colorMask col i Mlt) hMm hcol Pb
    hPs hPP hPS).1
  intro u
  refine (le_of_eq (Finset.sum_congr rfl fun j _ => ?_)).trans (h u)
  dsimp only
  unfold colorMask; split_ifs <;> simp

/-- **`E:split-fresh-insertion` on the Fock model** (main TeX lines
3861-3894).  Let `x` be a phase vector over `𝒵_S` (background set `𝒜`) and
`i ∉ 𝒜 ∪ S`, so that color `i` is in its vacuum.  Then
(a) `J_i x` lies over `𝒵_{S∪{i}}` (multiplication by the color-`i` field
takes its vacuum into its first degree; the cutoff `N_i` is not needed for
this step, the remaining cutoffs act on unchanged degrees), and
(b) `∑_k ‖S_ρ (J_i x)_{2,k}‖² ≤ σ_i² c ∑_k ‖x_{1,k}‖²` whenever the
color-`i` column bound `∑_{col j = i} ‖S_ρ B_j u‖² ≤ c‖u‖²` holds
(`FockColumn`).  The proof is the vacuum insertion on coefficients
(`coef_insertion`); the dependence of `x` on the background and earlier
cross colors is arbitrary. -/
theorem fock_insertion (col : Fin m → ι) (N : ι → ℕ) (A S : Finset ι) (i : ι) (hiA : i ∉ A)
    (hiS : i ∉ S) (σ : ι → ℝ) (B : Fin m → X →L[ℂ] X) (Sρ : X →L[ℂ] X) (cc : ℝ)
    (hcol : FockForm.FockColumn (fun j => if col j = i then Sρ ∘L B j else 0) cc)
    (x : PhaseSp X col N) (hx : x ∈ fockZ X col N A S) :
    fockJ σ B i x ∈ fockZ X col N A (insert i S) ∧
      ∑ k, ‖Sρ ((fockJ σ B i x).2 k)‖ ^ 2 ≤ σ i ^ 2 * cc * ∑ k, ‖x.1 k‖ ^ 2 := by
  have hext : ∀ (L : X →L[ℂ] X) l, L (extC x.1 l) ≠ 0 →
      (∀ i' ∈ S, colorDeg col l i' = 1) ∧ ∀ i', i' ∉ A → i' ∉ S → colorDeg col l i' = 0 := by
    intro L l hne
    by_cases hl : l ∈ cutIdx col N
    · have hx1 : x.1 ⟨l, hl⟩ ≠ 0 := by
        intro h0; apply hne; simp [extC, hl, h0]
      exact hx.1 ⟨l, hl⟩ hx1
    · exact absurd (by simp [extC, hl]) hne
  refine ⟨⟨fun k hk => absurd rfl hk, fun k hk => ?_⟩, ?_⟩
  · -- membership of the inserted component
    have hk' : insField B i x.1 k ≠ 0 := fun h0 => hk (by simp [fockJ, h0])
    obtain ⟨j, hj, hjne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk'
    have hcj : col j = i := (mem_filter.1 hj).2
    set w : (Fin m → ℕ) → X := fun l => B j (extC x.1 l) with hw
    have hann : ann j w k.1 = 0 := by
      have : w (k.1 + unitIdx j) = 0 := by
        by_contra hne
        have h1 := (hext (B j) _ hne).2 i hiA hiS
        rw [colorDeg_add_unitIdx, ite_eq_left_of_eq_true _ _ (eq_true hcj)] at h1
        omega
      simp [ann, this]
    have hcre : cre j w k.1 ≠ 0 := by
      intro h0; apply hjne; simp only [gmul]; rw [h0, hann, add_zero]
    have hkj : k.1 j ≠ 0 := fun h => hcre (cre_of_eq_zero j w h)
    have hw0 : w (k.1 - unitIdx j) ≠ 0 := fun h => hcre (by simp [cre, h])
    obtain ⟨hS1, hS0⟩ := hext (B j) _ hw0
    have hdeg := colorDeg_sub_unitIdx col hkj
    refine ⟨fun i' hi' => ?_, fun i' hA' hS' => ?_⟩
    · rw [hdeg i']
      rcases mem_insert.1 hi' with rfl | hi'S
      · rw [hS0 i' hiA hiS, ite_eq_left_of_eq_true _ _ (eq_true hcj)]
      · have hne : col j ≠ i' := fun h => hiS (by rw [← hcj, h]; exact hi'S)
        rw [hS1 i' hi'S]; simp [hne]
    · have hne : col j ≠ i' := fun h => hS' (mem_insert.2 (Or.inl (h.symm.trans hcj)))
      have hS'' : i' ∉ S := fun h => hS' (mem_insert_of_mem h)
      rw [hdeg i', hS0 i' hA' hS'']; simp [hne]
  · -- the norm
    set Ji := univ.filter (fun j : Fin m => col j = i) with hJi
    set w : Fin m → (Fin m → ℕ) → X := fun j l => (Sρ ∘L B j) (extC x.1 l) with hw
    have hpt : ∀ k : ↥(cutIdx col N), ‖Sρ ((fockJ σ B i x).2 k)‖ ^ 2 =
        σ i ^ 2 * ‖∑ j ∈ Ji, gmul j (w j) k.1‖ ^ 2 := by
      intro k
      simp only [fockJ, insField, Pi.smul_apply, map_smul, map_sum, gmul_map, norm_smul,
        Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, hw, ContinuousLinearMap.comp_apply,
        hJi]
    have hwz : ∀ j, col j = i → ∀ l, w j l ≠ 0 → colorDeg col l i = 0 :=
      fun j _ l hne => (hext (Sρ ∘L B j) l hne).2 i hiA hiS
    have hci := coef_insertion col N i w hwz
    have hcolsum : ∀ l : ↥(cutIdx col N), ∑ j ∈ Ji, ‖w j l.1‖ ^ 2 ≤ cc * ‖x.1 l‖ ^ 2 := by
      intro l
      have hl : extC x.1 l.1 = x.1 l := by simp [extC, l.2]
      have := hcol (x.1 l)
      rw [hJi, Finset.sum_filter]
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_)) this
      simp only [hw, hl]
      split_ifs <;> simp
    calc ∑ k, ‖Sρ ((fockJ σ B i x).2 k)‖ ^ 2
        = σ i ^ 2 * ∑ k : ↥(cutIdx col N), ‖∑ j ∈ Ji, gmul j (w j) k.1‖ ^ 2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => hpt k
      _ = σ i ^ 2 * ∑ k ∈ cutIdx col N, ‖∑ j ∈ Ji, gmul j (w j) k‖ ^ 2 := by
          rw [Finset.sum_coe_sort (cutIdx col N) (fun k => ‖∑ j ∈ Ji, gmul j (w j) k‖ ^ 2)]
      _ ≤ σ i ^ 2 * ∑ j ∈ Ji, ∑ l ∈ cutIdx col N, ‖w j l‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hci (sq_nonneg _)
      _ = σ i ^ 2 * ∑ l : ↥(cutIdx col N), ∑ j ∈ Ji, ‖w j l.1‖ ^ 2 := by
          rw [Finset.sum_comm, ← Finset.sum_coe_sort (cutIdx col N)]
      _ ≤ σ i ^ 2 * ∑ l : ↥(cutIdx col N), cc * ‖x.1 l‖ ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ => hcolsum l) (sq_nonneg _)
      _ = σ i ^ 2 * cc * ∑ k, ‖x.1 k‖ ^ 2 := by rw [← Finset.mul_sum, mul_assoc]

/-- **`E:split-fresh-insertion` in the phase norm** (main TeX lines
3861-3894), in the form used by `word_chain`: for a background set `𝒜`
disjoint from the cross set `𝒞`, every `i ∈ 𝒞 ∖ S` and `x` over `𝒵_S`,
`J_i x` lies over `𝒵_{S∪{i}}` and, for every `ρ ≥ λ > 0`,
`‖J_i x‖_ρ ≤ σ_i √R_α ρ^{(α-2)/2} ‖x‖_ρ ≤ c_i ‖x‖_ρ`,
`c_i = σ_i √R_α λ^{(α-2)/2}` (`α ≤ 2`), from the color column bounds
`hcolc` (band-compressed `FockColumn` at every `ρ > 0`). -/
theorem fock_insertion_bound (col : Fin m → ι) (N : ι → ℕ) (A C : Finset ι) (hAC : Disjoint A C)
    (σ : ι → ℝ) (B : Fin m → X →L[ℂ] X) (S : ℝ → X →L[ℂ] X) {alpha R lam : ℝ}
    (hα : alpha ≤ 2) (hR : 0 ≤ R) (hlam : 0 < lam) (hσ : ∀ i, 0 ≤ σ i)
    (hcolc : ∀ i (ρ : ℝ), 0 < ρ → FockForm.FockColumn
      (fun j => if col j = i then S ρ ∘L B j else 0) (R * ρ ^ (alpha - 2))) :
    ∀ i ∈ C, ∀ T ⊆ C, i ∉ T → ∀ x ∈ fockZ X col N A T,
      fockJ σ B i x ∈ fockZ X col N A (insert i T) ∧ ∀ ρ, lam ≤ ρ →
        ‖fockEmb S ρ (fockJ σ B i x)‖ ≤ insertConst alpha R lam (σ i) * ‖fockEmb S ρ x‖ := by
  intro i hi T _ hiT x hx
  have hiA : i ∉ A := fun h => Finset.disjoint_left.1 hAC h hi
  refine ⟨(fock_insertion col N A T i hiA hiT σ B (S lam) _ (hcolc i lam hlam) x hx).1,
    fun ρ hρ => ?_⟩
  have hρ0 : 0 < ρ := hlam.trans_le hρ
  obtain ⟨-, hn⟩ := fock_insertion col N A T i hiA hiT σ B (S ρ) _ (hcolc i ρ hρ0) x hx
  have hpow : ρ ^ (alpha - 2) ≤ lam ^ (alpha - 2) :=
    Real.rpow_le_rpow_of_nonpos hlam hρ (by linarith)
  have hcI0 : 0 ≤ insertConst alpha R lam (σ i) := by unfold insertConst; have := hσ i; positivity
  have hsq : ‖fockEmb S ρ (fockJ σ B i x)‖ ^ 2 ≤
      (insertConst alpha R lam (σ i) * ‖fockEmb S ρ x‖) ^ 2 := by
    rw [mul_pow, insertConst_sq alpha R lam (σ i) hR hlam, fockEmb_norm_sq, fockEmb_norm_sq]
    have h0 : ∑ k, ‖(fockJ σ B i x).1 k‖ ^ 2 = 0 := by simp [fockJ]
    rw [h0, zero_add]
    have hA : 0 ≤ ∑ k, ‖x.1 k‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hB : 0 ≤ ∑ k, ‖S ρ (x.2 k)‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hσ2 : 0 ≤ σ i ^ 2 := sq_nonneg _
    have hRp : 0 ≤ R * ρ ^ (alpha - 2) := mul_nonneg hR (Real.rpow_nonneg hρ0.le _)
    calc ∑ k, ‖S ρ ((fockJ σ B i x).2 k)‖ ^ 2 ≤ σ i ^ 2 * (R * ρ ^ (alpha - 2)) *
          ∑ k, ‖x.1 k‖ ^ 2 := hn
      _ ≤ σ i ^ 2 * (R * lam ^ (alpha - 2)) * ∑ k, ‖x.1 k‖ ^ 2 := by gcongr
      _ ≤ R * σ i ^ 2 * lam ^ (alpha - 2) * (∑ k, ‖x.1 k‖ ^ 2 + ∑ k, ‖S ρ (x.2 k)‖ ^ 2) := by
          have : 0 ≤ R * σ i ^ 2 * lam ^ (alpha - 2) := by
            have := Real.rpow_nonneg hlam.le (alpha - 2); positivity
          nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
end Fock

/-! ### `L:fixed-split` on the Fock model and the step row of `P:interval-coefficients` -/

section Headline

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
variable {m : ℕ}

/-- **The supplied inputs of `L:fixed-split` for one split** `(κ, p)`: the
two copies' `BackgroundPreserves`, `SegmentBound` and `DysonCrossCube`
inputs and `EntireCoefficients`, for the Fock model with cutoffs
`N_i = 2k_i`, phase norms `fockEmb S`, insertions `J_i = fockJ σ B` with
`B_j = S_b M_{e_j} S_b`, initial phase `vacPhase u w`, propagator `P` and
coefficients `c`. -/
def SplitInputs (col : Fin m → ι) (κ : ι → ℕ) (p : ι → ℕ × ℕ) (S : ℝ → X →L[ℂ] X)
    (Mlt : Fin m → X →L[ℂ] X) (Pb : X →L[ℂ] X)
    (P : (ι → ℂ) → ℝ → ℝ → PhaseSp X col (fun i => 2 * κ i) →
      PhaseSp X col (fun i => 2 * κ i))
    (c : (ι → ℕ) → PhaseSp X col (fun i => 2 * κ i)) (u w : X) (a b h σ : ι → ℝ)
    (alpha δ R T : ℝ) (k : ℕ) : Prop :=
  BackgroundPreserves (copyFirst κ p) (crossSet κ p)
      (fockZ X col (fun i => 2 * κ i) (copyFirst κ p)) P ∧
    BackgroundPreserves (copySecond κ p) (crossSet κ p)
      (fockZ X col (fun i => 2 * κ i) (copySecond κ p)) P ∧
    SegmentBound (copyFirst κ p) (fockEmb S) P
      (fun i => splitRadius alpha δ (σ i) R (h i) (κ i)) a b h κ k T ∧
    SegmentBound (copySecond κ p) (fockEmb S) P
      (fun i => splitRadius alpha δ (σ i) R (h i) (κ i)) a b h κ k T ∧
    EntireCoefficients c ∧
    DysonCrossCube (copyFirst κ p) (crossSet κ p) c
      (fun i => splitRadius alpha δ (σ i) R (h i) (κ i)) a b
      (word (copyFirst κ p) (crossSet κ p) a b T (fockJ σ fun j => Pb ∘L Mlt j ∘L Pb) P
        (vacPhase u w)) ∧
    DysonCrossCube (copySecond κ p) (crossSet κ p) c
      (fun i => splitRadius alpha δ (σ i) R (h i) (κ i)) a b
      (word (copySecond κ p) (crossSet κ p) a b T (fockJ σ fun j => Pb ∘L Mlt j ∘L Pb) P
        (vacPhase u w))

/-- **`L:fixed-split`** (A fixed degree-split estimate, main TeX lines
3675-3716, `E:fixed-split-bound` 3702-3713, proof 3718-4051), on the finite
Fock model.  Colors `ι` (the intervals), Gaussian modes `Fin m` with colors
`col`, Hermite cutoffs `N_i = 2k_i`, spatial band space `X` with `S_ρ` for
`A_ρ^{-1/2}` (symmetric, `‖S_ρ‖ ≤ ρ^{-1}`, the spectral comparison
`hScmp`), symmetric multiplications `M_{e_j}`, the band projection `S_b`
(symmetric idempotent commuting with `S_ρ`), and the color column bounds
`FockColumn` (`E:interval-column`, named input of `FockForm`).  For a degree
split `κ` (`∑ k_i = k ≥ 1`), a split `p_i = (r_i, q_i)` (`r_i + q_i = 2k_i`),
intervals `I_i^T = (a_i, b_i)` with `b_i - a_i ≤ h_i` (cross intervals in
`[0, T]`), `R_α, σ_i, h_i, δ > 0`, `α ≤ 2`, and `V ≥ ‖(u, w)‖_{1/T}²`
for the vacuum initial phase `(u, w)`: under the supplied inputs
(`SplitInputs`),
`|⟨U_r v, U_q v⟩_{L²(Ω; X_{1/T})}| ≤ k² C_split^k R_α^k V ∏_i splitFactor_i`
with `C_split = 100^8 e^8 max{1, 12δ^{-2}}` (`splitConst δ`) and `splitFactor`
the per-color factor of `E:fixed-split-bound`. -/
theorem fixed_split (col : Fin m → ι) (κ : ι → ℕ) (p : ι → ℕ × ℕ) (S : ℝ → X →L[ℂ] X)
    (Mlt : Fin m → X →L[ℂ] X) (Pb : X →L[ℂ] X)
    (P : (ι → ℂ) → ℝ → ℝ → PhaseSp X col (fun i => 2 * κ i) →
      PhaseSp X col (fun i => 2 * κ i))
    (c : (ι → ℕ) → PhaseSp X col (fun i => 2 * κ i)) (u w : X) (a b h σ : ι → ℝ)
    (alpha δ R T V : ℝ) (k : ℕ)
    (hT : 0 < T) (hk : 1 ≤ k) (hsum : ∑ i, κ i = k) (hp : ∀ i, (p i).1 + (p i).2 = 2 * κ i)
    (hδ : 0 < δ) (hR : 0 < R) (hα : alpha ≤ 2) (hσ : ∀ i, 0 < σ i) (hh : ∀ i, 0 < h i)
    (hlen : ∀ i, b i - a i ≤ h i) (habC : ∀ i ∈ crossSet κ p, 0 ≤ a i ∧ b i ≤ T)
    (hSs : ∀ ρ u w, inner ℂ (S ρ u) w = inner ℂ u (S ρ w))
    (hSn : ∀ ρ : ℝ, 0 < ρ → ∀ f, ‖S ρ f‖ ≤ ρ⁻¹ * ‖f‖)
    (hScmp : ∀ ρ ρ' : ℝ, 0 < ρ → 0 < ρ' → ∀ g, ‖S ρ' g‖ ≤ max 1 (ρ / ρ') * ‖S ρ g‖)
    (hM : ∀ j u w, inner ℂ (Mlt j u) w = inner ℂ u (Mlt j w))
    (hPs : ∀ u w, inner ℂ (Pb u) w = inner ℂ u (Pb w)) (hPP : ∀ u, Pb (Pb u) = Pb u)
    (hPS : ∀ ρ u, Pb (S ρ u) = S ρ (Pb u))
    (hcol : ∀ i (ρ : ℝ), 0 < ρ →
      FockForm.FockColumn (fun j => S ρ ∘L colorMask col i Mlt j) (R * ρ ^ (alpha - 2)))
    (hV : ‖u‖ ^ 2 + ‖S (1 / T) w‖ ^ 2 ≤ V)
    (hin : SplitInputs col κ p S Mlt Pb P c u w a b h σ alpha δ R T k) :
    ‖inner ℂ (fockEmb S (1 / T) (c fun i => (p i).1)) (fockEmb S (1 / T) (c fun i => (p i).2))‖ ≤
      (k : ℝ) ^ 2 * splitConst δ ^ k * R ^ k * V *
        ∏ i, splitFactor alpha (σ i) (h i) ((k : ℝ) / T) (κ i) (p i) := by
  obtain ⟨hPZ₁, hPZ₂, hseg₁, hseg₂, hent, hdys₁, hdys₂⟩ := hin
  have hlam : (0 : ℝ) < (k : ℝ) / T := div_pos (by exact_mod_cast hk) hT
  have hcolc : ∀ i (ρ : ℝ), 0 < ρ → FockForm.FockColumn
      (fun j => if col j = i then S ρ ∘L (fun j => Pb ∘L Mlt j ∘L Pb) j else 0)
      (R * ρ ^ (alpha - 2)) := fun i ρ hρ =>
    fockColumn_masked col i hR.le hρ (S ρ) (hSs ρ) (hSn ρ hρ) Mlt hM (hcol i ρ hρ) Pb hPs hPP
      (hPS ρ)
  have hdisj : ∀ A ⊆ backSet κ p, Disjoint A (crossSet κ p) := fun A hA =>
    Finset.disjoint_left.2 fun i h1 h2 => (mem_filter.1 (hA h1)).2.2 (mem_filter.1 h2).2
  exact fixed_split_abstract (fockZ X col (fun i => 2 * κ i) (copyFirst κ p))
    (fockZ X col (fun i => 2 * κ i) (copySecond κ p)) (fockEmb S)
    (fockJ σ fun j => Pb ∘L Mlt j ∘L Pb) P (vacPhase u w) c κ p a b h σ alpha δ R T V k hT hk
    hsum hp hδ hR (by linarith) hσ hh hlen habC (fockEmb_cmp S hScmp)
    (by rw [fockEmb_vacPhase]; exact hV) (vacPhase_mem _ _ _ u w) (vacPhase_mem _ _ _ u w)
    (fock_insertion_bound col _ _ _ (hdisj _ (filter_subset _ _)) σ _ S hα hR.le hlam
      (fun i => (hσ i).le) hcolc)
    (fock_insertion_bound col _ _ _ (hdisj _ (filter_subset _ _)) σ _ S hα hR.le hlam
      (fun i => (hσ i).le) hcolc)
    hPZ₁ hPZ₂ hseg₁ hseg₂ hent hdys₁ hdys₂

/-- **`L:fixed-split` under the manuscript's hypotheses** (main TeX lines
3675-3716): `fixed_split` under `H:homog` (`HomogCovariance`, the standing
class of `S:interval-upper`, lines 3353-3374) with
`R = R_α = απ μ(B_1)/(2 sin(πα/2)) > 0` and `σ_i > 0`, as the lemma
assumes.  `H:homog` is used for `α < 2`; `_hRdef` is carried and unused (the
covariance enters only through the supplied `FockColumn`, `SegmentBound` and
`DysonCrossCube`). -/
theorem fixed_split_paper {d : ℕ} {alpha alpha0 : ℝ} {Γ μ : Measure (HomogHypothesis.Rd d)}
    (hH : HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ)
    (col : Fin m → ι) (κ : ι → ℕ) (p : ι → ℕ × ℕ) (S : ℝ → X →L[ℂ] X)
    (Mlt : Fin m → X →L[ℂ] X) (Pb : X →L[ℂ] X)
    (P : (ι → ℂ) → ℝ → ℝ → PhaseSp X col (fun i => 2 * κ i) →
      PhaseSp X col (fun i => 2 * κ i))
    (c : (ι → ℕ) → PhaseSp X col (fun i => 2 * κ i)) (u w : X) (a b h σ : ι → ℝ)
    {δ R T V : ℝ} {k : ℕ}
    (_hRdef : R = alpha * π * (μ (Metric.ball 0 1)).toReal / (2 * Real.sin (π * alpha / 2)))
    (hRpos : 0 < R) (hT : 0 < T) (hk : 1 ≤ k) (hsum : ∑ i, κ i = k)
    (hp : ∀ i, (p i).1 + (p i).2 = 2 * κ i) (hδ : 0 < δ) (hσ : ∀ i, 0 < σ i) (hh : ∀ i, 0 < h i)
    (hlen : ∀ i, b i - a i ≤ h i) (habC : ∀ i ∈ crossSet κ p, 0 ≤ a i ∧ b i ≤ T)
    (hSs : ∀ ρ u w, inner ℂ (S ρ u) w = inner ℂ u (S ρ w))
    (hSn : ∀ ρ : ℝ, 0 < ρ → ∀ f, ‖S ρ f‖ ≤ ρ⁻¹ * ‖f‖)
    (hScmp : ∀ ρ ρ' : ℝ, 0 < ρ → 0 < ρ' → ∀ g, ‖S ρ' g‖ ≤ max 1 (ρ / ρ') * ‖S ρ g‖)
    (hM : ∀ j u w, inner ℂ (Mlt j u) w = inner ℂ u (Mlt j w))
    (hPs : ∀ u w, inner ℂ (Pb u) w = inner ℂ u (Pb w)) (hPP : ∀ u, Pb (Pb u) = Pb u)
    (hPS : ∀ ρ u, Pb (S ρ u) = S ρ (Pb u))
    (hcol : ∀ i (ρ : ℝ), 0 < ρ →
      FockForm.FockColumn (fun j => S ρ ∘L colorMask col i Mlt j) (R * ρ ^ (alpha - 2)))
    (hV : ‖u‖ ^ 2 + ‖S (1 / T) w‖ ^ 2 ≤ V)
    (hin : SplitInputs col κ p S Mlt Pb P c u w a b h σ alpha δ R T k) :
    ‖inner ℂ (fockEmb S (1 / T) (c fun i => (p i).1)) (fockEmb S (1 / T) (c fun i => (p i).2))‖ ≤
      (k : ℝ) ^ 2 * splitConst δ ^ k * R ^ k * V *
        ∏ i, splitFactor alpha (σ i) (h i) ((k : ℝ) / T) (κ i) (p i) := by
  obtain ⟨-, hα2, -⟩ := homog_alpha_range hH
  exact fixed_split col κ p S Mlt Pb P c u w a b h σ alpha δ R T V k hT hk hsum hp hδ hRpos
    hα2.le hσ hh hlen habC hSs hSn hScmp hM hPs hPP hPS hcol hV hin

end Headline

/-- **Step row of `P:interval-coefficients` with `L:fixed-split` supplied by
its proof** (main TeX lines 4054-4060, proof 4068-4228):
`IntervalScalarCompleted.interval_coefficient_assembly_paper_completed` with
`hfixed` discharged by `fixed_split_paper` and `C_split = splitConst δ`.
For every degree split `κ` of `k` and every split `p`, the Fock model with
cutoffs `N_i = 2κ_i` carries a propagator `P κ` and coefficients `cf κ`
satisfying `SplitInputs`, and `Q_{r,q}` is bounded by the modulus of the
cutoff inner product `⟨U_r v, U_q v⟩_{1/T}` (`hQ`: in the TeX `Q_{r,q}` is
that inner product, line 4143, and the cutoff preserves the selected
coefficients exactly, lines 4163-4170).  Every other hypothesis is exactly
that of `interval_coefficient_assembly_paper_completed` (`hsplits` remains
supplied); added: the interval endpoints `I_i^T = (a_i, b_i) ⊆ [0, T]` with
`b_i - a_i ≤ h_i` (lines 3739-3741), `δ > 0`, the spatial operator hypotheses of
`fixed_split` and `V ≥ ‖(u, w)‖_{1/T}²`. -/
theorem interval_coefficient_assembly_paper_fixed {d : ℕ} {alpha alpha0 : ℝ}
    {Γ μ : Measure (HomogHypothesis.Rd d)}
    (hH : HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ)
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    {R T L c δ V coef : ℝ} {M k m : ℕ}
    (h σ a b : Fin M → ℝ) (Q : (Fin M → ℕ × ℕ) → ℝ)
    (hRdef : R = alpha * π * (μ (Metric.ball 0 1)).toReal / (2 * Real.sin (π * alpha / 2)))
    (hRpos : 0 < R) (hk : 1 ≤ k) (hT : 0 < T) (hδ : 0 < δ)
    (hh : ∀ i, 0 < h i) (hσpos : ∀ i, 0 < σ i)
    (hlen : ∀ i : Fin M, h i ≤ L * T / ((i : ℕ) + 1 : ℕ))
    (hσ : ∀ i, σ i ^ 2 ≤ c * h i ^ (-alpha0))
    (hsplits : coef = ∑ κ ∈ (univ : Finset (Fin M)).finsuppAntidiag k,
      ∑ p ∈ Fintype.piFinset (fun i => antidiagonal (2 * κ i)), Q p)
    (hIlen : ∀ i, b i - a i ≤ h i) (hab : ∀ i, 0 ≤ a i ∧ b i ≤ T)
    (col : Fin m → Fin M) (S : ℝ → X →L[ℂ] X) (Mlt : Fin m → X →L[ℂ] X) (Pb : X →L[ℂ] X)
    (u w : X)
    (hSs : ∀ ρ u w, inner ℂ (S ρ u) w = inner ℂ u (S ρ w))
    (hSn : ∀ ρ : ℝ, 0 < ρ → ∀ f, ‖S ρ f‖ ≤ ρ⁻¹ * ‖f‖)
    (hScmp : ∀ ρ ρ' : ℝ, 0 < ρ → 0 < ρ' → ∀ g, ‖S ρ' g‖ ≤ max 1 (ρ / ρ') * ‖S ρ g‖)
    (hM : ∀ j u w, inner ℂ (Mlt j u) w = inner ℂ u (Mlt j w))
    (hPs : ∀ u w, inner ℂ (Pb u) w = inner ℂ u (Pb w)) (hPP : ∀ u, Pb (Pb u) = Pb u)
    (hPS : ∀ ρ u, Pb (S ρ u) = S ρ (Pb u))
    (hcol : ∀ i (ρ : ℝ), 0 < ρ →
      FockForm.FockColumn (fun j => S ρ ∘L colorMask col i Mlt j) (R * ρ ^ (alpha - 2)))
    (hV : ‖u‖ ^ 2 + ‖S (1 / T) w‖ ^ 2 ≤ V)
    (P : ∀ κ : Fin M → ℕ, (Fin M → ℂ) → ℝ → ℝ → PhaseSp X col (fun i => 2 * κ i) →
      PhaseSp X col (fun i => 2 * κ i))
    (cf : ∀ κ : Fin M → ℕ, (Fin M → ℕ) → PhaseSp X col (fun i => 2 * κ i))
    (hQ : ∀ κ ∈ (univ : Finset (Fin M)).finsuppAntidiag k,
      ∀ p ∈ Fintype.piFinset (fun i => antidiagonal (2 * κ i)),
        |Q p| ≤ ‖inner ℂ (fockEmb S (1 / T) (cf κ fun i => (p i).1))
          (fockEmb S (1 / T) (cf κ fun i => (p i).2))‖)
    (hin : ∀ κ ∈ (univ : Finset (Fin M)).finsuppAntidiag k,
      ∀ p ∈ Fintype.piFinset (fun i => antidiagonal (2 * κ i)),
        SplitInputs col κ p S Mlt Pb (P κ) (cf κ) u w a b h σ alpha δ R T k) :
    |coef| ≤ (12 * max c 0 * max 1 L ^ (4 - alpha - alpha0) * splitConst δ *
        InventoryProduct.inventoryConst alpha alpha0) ^ k * R ^ k *
      T ^ ((4 - alpha - alpha0) * k) / (k ! : ℝ) ^ (3 - alpha) * V := by
  have hV0 : 0 ≤ V := (add_nonneg (sq_nonneg _) (sq_nonneg _)).trans hV
  refine IntervalScalarCompleted.interval_coefficient_assembly_paper_completed hH h σ Q hRdef
    hRpos hk hT hV0 (splitConst_nonneg δ) hh hσpos hlen hσ hsplits fun κ hκ p hp => ?_
  have hsum : ∑ i, κ i = k := ((mem_finsuppAntidiag).1 hκ).1
  have hpp : ∀ i, (p i).1 + (p i).2 = 2 * κ i := fun i =>
    mem_antidiagonal.1 (Fintype.mem_piFinset.1 hp i)
  exact (hQ κ hκ p hp).trans (fixed_split_paper hH col κ p S Mlt Pb (P κ) (cf κ) u w a b h σ
    hRdef hRpos hT hk hsum hpp hδ hσpos hh hIlen (fun i _ => hab i) hSs hSn hScmp hM hPs hPP hPS
    hcol hV (hin κ hκ p hp))

end StratonovichHAMSecondMoment.FixedSplit
