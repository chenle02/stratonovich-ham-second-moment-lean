module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

The finite Gaussian Fock layer (a reusable foundation; no manuscript label of
its own).

Source: `notes/notes_stratonovich_ham_second_moment.tex` (main TeX) at commit
`a284420`: the Fock half of the proof of `L:fock-form` (lines 2515-2526), the
Fock sentences of the proof of `L:interval-contractions` (lines 2887-2891), the
phase insertion on a vacuum color (lines 2838-2841, 2878-2880) and the Hermite
step of `E:occupied-multiplication` (lines 1805-1810).  The TeX cites Janson
(lines 2467-2468) for the creation and annihilation algebra; this module proves
what is used.

Model (decision 5 of wave L9): the Gaussian `L²` space with values in a complex
inner product space `X` is represented on the finite coefficient spaces
`(Fin m → ℕ) → X` indexed by multi-indices of total degree at most `N`
(`degLE m N`), through the expansion `iota N v x = ∑_{|k| ≤ N} hk_k(x) v_k` in
the normalized Hermite functions of `GaussianHermite`.  No tensor-product inner
product is used; the "other Hilbert factor" of the TeX is `X` itself.

Contents (everything proved, nothing supplied):
* the creation and annihilation operators on coefficients,
  `(a_i v)_k = √(k_i+1) v_{k+e_i}`, `(a_i^* v)_k = √(k_i) v_{k-e_i}`
  (`ann`, `cre`), and multiplication by `g_i`, `gmul i = a_i^* + a_i`;
* the number identity `∑_i a_i^* a_i = |k|` on the coefficient of index `k`
  (`number_identity`), and the adjoint relation between `a_i` and `a_i^*`
  (`sum_inner_ann`);
* the creation row `(u_i) ↦ ∑_i a_i^* u_i` from degrees `≤ j` to degrees
  `≤ j+1` has norm at most `√(j+1)` (`creRow_bound`), attained on
  `u_i = a_i w` for `w` of exact degree `j+1` (`creRow_attained`);
* for `H_1, …, H_m` symmetric (self-adjoint) operators on `X` with
  `∑_i ‖H_i u‖² ≤ c ‖u‖²`, the field operator `∑_i (a_i^* + a_i) ⊗ H_i`
  (`fieldOp`) maps degrees `≤ N` to degrees `≤ N+1` with norm at most
  `2√(N+1)√c`, untruncated (`fieldOp_bound`) and after truncation to degrees
  `≤ N` (`fieldOp_bound_trunc`); the truncated operator is symmetric
  (`fieldOp_symm_trunc`);
* the Gaussian side: the expansion is an isometry
  (`integral_norm_sq_iota`), multiplication by the coordinate `x_i` is `gmul i`
  on coefficients (`coord_smul_iota`), and `∑_i x_i H_i` acting on `iota N v`
  is `iota (N+1) (fieldOp H v)` (`sum_coord_smul_iota`), so the two Fock bounds
  are bounds for Gaussian `L²(X)` norms (`gaussian_field_bound`,
  `gaussian_field_bound_trunc`);
* vacuum insertion: `∫ ‖∑_i x_i w_i‖² dγ_m = ∑_i ‖w_i‖²`
  (`vacuum_insertion_isometry`).

Route difference: the TeX bounds the annihilation part as the adjoint of the
creation part; here the same adjoint relation is used through the finite
identity `sum_inner_ann` and Cauchy-Schwarz, giving the annihilation bound
`(N+1)c` (the TeX's `N c` is not needed for the constant `4(N+1)c`).  The TeX
rotates `H/‖H‖` to the first coordinate; the general column form with
operators `H_i` makes that step unnecessary.

Junk values: the truncated subtraction `k - e_i` occurs only multiplied by
`√(k_i)`, which vanishes exactly when it truncates; `c ≥ 0` is a hypothesis
where it is used; every integral conclusion includes integrability.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.GaussianIBP
public import StratonovichHAMSecondMoment.GaussianHermite

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Finset
open StratonovichHAMSecondMoment.GaussianHermite (hk unitIdx)

namespace StratonovichHAMSecondMoment.HermiteFock

variable {m : ℕ}

/-! ### Multi-indices -/

/-- The total degree `|k| = ∑_i k_i` of a multi-index. -/
def deg (k : Fin m → ℕ) : ℕ := ∑ i, k i

/-- The multi-indices of total degree at most `N`. -/
def degLE (m N : ℕ) : Finset (Fin m → ℕ) :=
  (Fintype.piFinset fun _ => range (N + 1)).filter fun k => ∑ i, k i ≤ N

/-- Membership in `degLE m N` is `|k| ≤ N`. -/
theorem mem_degLE {N : ℕ} {k : Fin m → ℕ} : k ∈ degLE m N ↔ deg k ≤ N := by
  simp only [degLE, mem_filter, Fintype.mem_piFinset, mem_range, deg]
  refine ⟨fun h => h.2, fun h => ⟨fun i => ?_, h⟩⟩
  have := Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) (mem_univ i)
  omega

/-- Auxiliary: `degLE m N ⊆ degLE m M` for `N ≤ M`. -/
theorem degLE_mono {N M : ℕ} (h : N ≤ M) : degLE m N ⊆ degLE m M :=
  fun _ hk => mem_degLE.2 ((mem_degLE.1 hk).trans h)

/-- Auxiliary: `0 ∈ degLE m N`. -/
theorem zero_mem_degLE (N : ℕ) : (0 : Fin m → ℕ) ∈ degLE m N := mem_degLE.2 (by simp [deg])

/-- Auxiliary: `|k + e_i| = |k| + 1`. -/
theorem deg_add_unitIdx (k : Fin m → ℕ) (i : Fin m) : deg (k + unitIdx i) = deg k + 1 := by
  simp [deg, Finset.sum_add_distrib, unitIdx]

/-- Auxiliary: `(k - e_i) + e_i = k` when `k_i ≠ 0`. -/
theorem sub_add_unitIdx {k : Fin m → ℕ} {i : Fin m} (h : k i ≠ 0) :
    k - unitIdx i + unitIdx i = k := by
  funext j
  by_cases hj : j = i
  · subst hj; simp; omega
  · simp [unitIdx, hj]

/-- Auxiliary: `(k + e_i) - e_i = k`. -/
theorem add_sub_unitIdx (k : Fin m → ℕ) (i : Fin m) : k + unitIdx i - unitIdx i = k := by
  funext j; simp

/-- Auxiliary: `|k - e_i| + 1 = |k|` when `k_i ≠ 0`. -/
theorem deg_sub_unitIdx {k : Fin m → ℕ} {i : Fin m} (h : k i ≠ 0) :
    deg (k - unitIdx i) + 1 = deg k := by
  conv_rhs => rw [← sub_add_unitIdx h]
  rw [deg_add_unitIdx]

/-- Auxiliary: `(k - e_i)_i = k_i - 1`. -/
theorem sub_unitIdx_apply (k : Fin m → ℕ) (i : Fin m) : (k - unitIdx i) i = k i - 1 := by
  simp

/-- Auxiliary: `(k + e_i)_i = k_i + 1`. -/
theorem add_unitIdx_apply (k : Fin m → ℕ) (i : Fin m) : (k + unitIdx i) i = k i + 1 := by
  simp

/-- Auxiliary (reindexing): a function vanishing on `k_i = 0`, summed over
degrees `≤ N+1`, equals its shift by `e_i` summed over degrees `≤ N`. -/
theorem sum_degLE_succ_eq (i : Fin m) (N : ℕ) {M : Type*} [AddCommMonoid M]
    (g : (Fin m → ℕ) → M) (hg : ∀ k, k i = 0 → g k = 0) :
    ∑ k ∈ degLE m (N + 1), g k = ∑ j ∈ degLE m N, g (j + unitIdx i) := by
  classical
  rw [← Finset.sum_filter_of_ne (p := fun k => k i ≠ 0) (fun k _ hne h0 => hne (hg k h0))]
  symm
  refine Finset.sum_nbij' (fun j => j + unitIdx i) (fun k => k - unitIdx i) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [mem_filter] at hj ⊢
    refine ⟨mem_degLE.2 ?_, by simp⟩
    rw [deg_add_unitIdx]; have := mem_degLE.1 hj; omega
  · intro k hk
    simp only [mem_filter] at hk ⊢
    have h1 := deg_sub_unitIdx hk.2
    have h2 := mem_degLE.1 hk.1
    exact mem_degLE.2 (by omega)
  · intro j _; exact add_sub_unitIdx j i
  · intro k hk
    simp only [mem_filter] at hk
    exact sub_add_unitIdx hk.2
  · intro j _; rfl

/-- Auxiliary: a function vanishing in degrees above `N` has the same sum over
`degLE m M` for every `M ≥ N`. -/
theorem sum_degLE_eq_of_vanish {N M : ℕ} (hNM : N ≤ M) {E : Type*} [AddCommMonoid E]
    (g : (Fin m → ℕ) → E) (hg : ∀ k, N < deg k → g k = 0) :
    ∑ k ∈ degLE m M, g k = ∑ k ∈ degLE m N, g k := by
  symm
  refine Finset.sum_subset (degLE_mono hNM) fun k _ hk => hg k ?_
  rw [mem_degLE] at hk; omega

/-! ### Coefficient operators -/

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

/-- A coefficient vector vanishes in degrees above `N`. -/
def Supp (N : ℕ) (v : (Fin m → ℕ) → X) : Prop := ∀ k, N < deg k → v k = 0

/-- The annihilation operator `(a_i v)_k = √(k_i+1) v_{k+e_i}`. -/
def ann (i : Fin m) (v : (Fin m → ℕ) → X) (k : Fin m → ℕ) : X :=
  (Real.sqrt ((k i : ℝ) + 1) : ℂ) • v (k + unitIdx i)

/-- The creation operator `(a_i^* v)_k = √(k_i) v_{k-e_i}`. -/
def cre (i : Fin m) (v : (Fin m → ℕ) → X) (k : Fin m → ℕ) : X :=
  (Real.sqrt (k i : ℝ) : ℂ) • v (k - unitIdx i)

/-- Multiplication by the coordinate `g_i` on coefficients, `a_i^* + a_i`. -/
def gmul (i : Fin m) (v : (Fin m → ℕ) → X) (k : Fin m → ℕ) : X := cre i v k + ann i v k

/-- The creation row `(u_i)_i ↦ ∑_i a_i^* u_i`. -/
def creRow (u : Fin m → (Fin m → ℕ) → X) (k : Fin m → ℕ) : X := ∑ i, cre i (u i) k

/-- The field operator `∑_i (a_i^* + a_i) ⊗ H_i` on coefficients. -/
def fieldOp (H : Fin m → X →L[ℂ] X) (v : (Fin m → ℕ) → X) (k : Fin m → ℕ) : X :=
  ∑ i, gmul i (fun l => H i (v l)) k

/-- The vacuum vector `1 ⊗ u` (coefficient `u` at `k = 0`). -/
def vac (u : X) : (Fin m → ℕ) → X := fun k => if k = 0 then u else 0

/-- Auxiliary: `(a_i^* v)_k = 0` when `k_i = 0`. -/
theorem cre_of_eq_zero (i : Fin m) (v : (Fin m → ℕ) → X) {k : Fin m → ℕ} (h : k i = 0) :
    cre i v k = 0 := by simp [cre, h]

/-- `a_i^* a_i` multiplies the coefficient of index `k` by `k_i`. -/
theorem cre_ann (i : Fin m) (v : (Fin m → ℕ) → X) (k : Fin m → ℕ) :
    cre i (ann i v) k = ((k i : ℝ) : ℂ) • v k := by
  unfold cre ann
  by_cases h : k i = 0
  · simp [h]
  · rw [sub_add_unitIdx h, smul_smul, ← Complex.ofReal_mul, sub_unitIdx_apply]
    have : ((k i - 1 : ℕ) : ℝ) + 1 = k i := by
      rw [Nat.cast_sub (by omega)]; ring
    rw [this, Real.mul_self_sqrt (Nat.cast_nonneg _)]

/-- **Number identity** `∑_i a_i^* a_i = |k|` on the coefficient of index `k`. -/
theorem number_identity (v : (Fin m → ℕ) → X) (k : Fin m → ℕ) :
    ∑ i, cre i (ann i v) k = ((deg k : ℝ) : ℂ) • v k := by
  simp only [cre_ann, ← Finset.sum_smul, deg]
  push_cast; rfl

/-- **Adjoint relation** of `a_i` and `a_i^*`:
`∑_{|k| ≤ N} ⟨(a_i v)_k, w_k⟩ = ∑_{|k| ≤ N+1} ⟨v_k, (a_i^* w)_k⟩`. -/
theorem sum_inner_ann (i : Fin m) (N : ℕ) (v w : (Fin m → ℕ) → X) :
    ∑ k ∈ degLE m N, inner ℂ (ann i v k) (w k) =
      ∑ k ∈ degLE m (N + 1), inner ℂ (v k) (cre i w k) := by
  rw [sum_degLE_succ_eq i N (fun k => inner ℂ (v k) (cre i w k))
    (fun k hk => by simp [cre_of_eq_zero i w hk])]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [ann, cre, add_unitIdx_apply, add_sub_unitIdx, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal]
  push_cast; ring

/-- The conjugate form of `sum_inner_ann`. -/
theorem sum_inner_cre (i : Fin m) (N : ℕ) (v w : (Fin m → ℕ) → X) :
    ∑ k ∈ degLE m (N + 1), inner ℂ (cre i v k) (w k) =
      ∑ k ∈ degLE m N, inner ℂ (v k) (ann i w k) := by
  have h := congrArg (starRingEnd ℂ) (sum_inner_ann i N w v)
  simp only [map_sum, inner_conj_symm] at h
  exact h.symm

/-! ### Norm bounds -/

/-- Auxiliary: `(∑ re⟨x_k, y_k⟩)² ≤ (∑ ‖x_k‖²)(∑ ‖y_k‖²)` when the left sum
is nonnegative. -/
theorem sq_sum_re_inner_le {ι : Type*} (s : Finset ι) (x y : ι → X)
    (h0 : 0 ≤ ∑ k ∈ s, RCLike.re (inner ℂ (x k) (y k))) :
    (∑ k ∈ s, RCLike.re (inner ℂ (x k) (y k))) ^ 2 ≤
      (∑ k ∈ s, ‖x k‖ ^ 2) * ∑ k ∈ s, ‖y k‖ ^ 2 := by
  have h1 : ∑ k ∈ s, RCLike.re (inner ℂ (x k) (y k)) ≤ ∑ k ∈ s, ‖x k‖ * ‖y k‖ :=
    Finset.sum_le_sum fun k _ => re_inner_le_norm _ _
  calc _ ≤ (∑ k ∈ s, ‖x k‖ * ‖y k‖) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq s _ _

/-- **Creation-row bound**: `(u_i) ↦ ∑_i a_i^* u_i` from degrees `≤ N` to
degrees `≤ N+1` has norm at most `√(N+1)`, in the form
`∑_{|k| ≤ N+1} ‖∑_i (a_i^* u_i)_k‖² ≤ (N+1) ∑_i ∑_{|j| ≤ N} ‖u_{i,j}‖²`. -/
theorem creRow_bound (N : ℕ) (u : Fin m → (Fin m → ℕ) → X) :
    ∑ k ∈ degLE m (N + 1), ‖creRow u k‖ ^ 2 ≤
      ((N : ℝ) + 1) * ∑ i, ∑ j ∈ degLE m N, ‖u i j‖ ^ 2 := by
  classical
  set g : Fin m → (Fin m → ℕ) → ℝ := fun i k => if k i = 0 then 0 else ‖u i (k - unitIdx i)‖
  have hpt : ∀ k ∈ degLE m (N + 1), ‖creRow u k‖ ^ 2 ≤ ((N : ℝ) + 1) * ∑ i, g i k ^ 2 := by
    intro k hk
    have h1 : ‖creRow u k‖ ≤ ∑ i, Real.sqrt (k i) * g i k := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      by_cases h : k i = 0
      · simp [cre, h, g]
      · simp only [cre, norm_smul, Complex.norm_real, Real.norm_eq_abs, g, h, ↓reduceIte,
          abs_of_nonneg (Real.sqrt_nonneg _)]
        exact le_rfl
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq univ (fun i => Real.sqrt (k i)) (g · k)
    have h3 : ∑ i, Real.sqrt (k i : ℝ) ^ 2 ≤ (N : ℝ) + 1 := by
      simp only [Real.sq_sqrt (Nat.cast_nonneg _)]
      have := mem_degLE.1 hk
      exact_mod_cast (show deg k ≤ N + 1 from this)
    calc ‖creRow u k‖ ^ 2 ≤ (∑ i, Real.sqrt (k i) * g i k) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2.trans (mul_le_mul_of_nonneg_right h3
          (Finset.sum_nonneg fun i _ => sq_nonneg _))
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum, Finset.sum_comm]
  refine mul_le_mul_of_nonneg_left (le_of_eq (Finset.sum_congr rfl fun i _ => ?_)) (by positivity)
  rw [sum_degLE_succ_eq i N (fun k => g i k ^ 2) (fun k hk => by simp [g, hk])]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [g]

/-- The creation part `∑_i a_i^* ⊗ H_i` of the field operator. -/
def creOp (H : Fin m → X →L[ℂ] X) (v : (Fin m → ℕ) → X) (k : Fin m → ℕ) : X :=
  creRow (fun i l => H i (v l)) k

/-- The annihilation part `∑_i a_i ⊗ H_i` of the field operator. -/
def annOp (H : Fin m → X →L[ℂ] X) (v : (Fin m → ℕ) → X) (k : Fin m → ℕ) : X :=
  ∑ i, ann i (fun l => H i (v l)) k

/-- The field operator is the sum of its creation and annihilation parts. -/
theorem fieldOp_eq (H : Fin m → X →L[ℂ] X) (v : (Fin m → ℕ) → X) (k : Fin m → ℕ) :
    fieldOp H v k = creOp H v k + annOp H v k := by
  simp [fieldOp, creOp, annOp, creRow, gmul, Finset.sum_add_distrib]

/-- The creation part with a column bound `∑_i ‖H_i u‖² ≤ c ‖u‖²`:
`∑_{|k| ≤ N+1} ‖(creOp H v)_k‖² ≤ (N+1) c ∑_{|j| ≤ N} ‖v_j‖²`. -/
theorem creOp_bound (N : ℕ) (H : Fin m → X →L[ℂ] X) {c : ℝ}
    (hc : ∀ u, ∑ i, ‖H i u‖ ^ 2 ≤ c * ‖u‖ ^ 2) (v : (Fin m → ℕ) → X) :
    ∑ k ∈ degLE m (N + 1), ‖creOp H v k‖ ^ 2 ≤
      ((N : ℝ) + 1) * c * ∑ j ∈ degLE m N, ‖v j‖ ^ 2 := by
  refine (creRow_bound N _).trans ?_
  rw [Finset.sum_comm]
  calc ((N : ℝ) + 1) * ∑ j ∈ degLE m N, ∑ i, ‖H i (v j)‖ ^ 2
      ≤ ((N : ℝ) + 1) * ∑ j ∈ degLE m N, c * ‖v j‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hc (v j)) (by positivity)
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- The annihilation part, for symmetric `H_i` with column bound `c ≥ 0`:
`∑_{|k| ≤ N} ‖(annOp H v)_k‖² ≤ (N+1) c ∑_{|k| ≤ N+1} ‖v_k‖²` (adjoint of the
creation part). -/
theorem annOp_bound (N : ℕ) (H : Fin m → X →L[ℂ] X)
    (hH : ∀ i u w, inner ℂ (H i u) w = inner ℂ u (H i w)) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ u, ∑ i, ‖H i u‖ ^ 2 ≤ c * ‖u‖ ^ 2) (v : (Fin m → ℕ) → X) :
    ∑ k ∈ degLE m N, ‖annOp H v k‖ ^ 2 ≤
      ((N : ℝ) + 1) * c * ∑ k ∈ degLE m (N + 1), ‖v k‖ ^ 2 := by
  set a := annOp H v
  set S := ∑ k ∈ degLE m N, ‖a k‖ ^ 2
  set V := ∑ k ∈ degLE m (N + 1), ‖v k‖ ^ 2
  have hS : S = ∑ k ∈ degLE m (N + 1), RCLike.re (inner ℂ (v k) (creOp H a k)) := by
    have e1 : ∀ k, ‖a k‖ ^ 2 = RCLike.re (∑ i, inner ℂ (ann i v k) (H i (a k))) := by
      intro k
      rw [@norm_sq_eq_re_inner ℂ]
      congr 1
      have : inner ℂ (a k) (a k) = ∑ i, inner ℂ (ann i (fun l => H i (v l)) k) (a k) := by
        show inner ℂ (annOp H v k) (a k) = _
        rw [annOp, sum_inner]
      rw [this]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [ann, inner_smul_left, hH]
    simp only [S, e1, ← map_sum]
    rw [Finset.sum_comm]
    simp only [sum_inner_ann]
    rw [Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [creOp, creRow, inner_sum]
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hsq : S ^ 2 ≤ V * (((N : ℝ) + 1) * c * S) := by
    have := sq_sum_re_inner_le (degLE m (N + 1)) v (creOp H a) (hS ▸ hS0)
    rw [← hS] at this
    exact this.trans (mul_le_mul_of_nonneg_left (creOp_bound N H hc a)
      (Finset.sum_nonneg fun k _ => sq_nonneg _))
  rcases hS0.eq_or_lt with h | h
  · rw [← h]; exact mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => sq_nonneg _)
  · have : S * S ≤ ((N : ℝ) + 1) * c * V * S := by nlinarith
    exact le_of_mul_le_mul_right this h

/-- Coefficient vectors supported in degrees `≤ N` have annihilation parts
supported in degrees `≤ N`. -/
theorem annOp_supp {N : ℕ} (H : Fin m → X →L[ℂ] X) {v : (Fin m → ℕ) → X} (hv : Supp N v) :
    Supp N (annOp H v) := by
  intro k hk
  refine Finset.sum_eq_zero fun i _ => ?_
  simp [ann, hv (k + unitIdx i) (by rw [deg_add_unitIdx]; omega)]

/-- The field operator maps degrees `≤ N` to degrees `≤ N+1`. -/
theorem fieldOp_supp {N : ℕ} (H : Fin m → X →L[ℂ] X) {v : (Fin m → ℕ) → X} (hv : Supp N v) :
    Supp (N + 1) (fieldOp H v) := by
  intro k hk
  refine Finset.sum_eq_zero fun i _ => ?_
  simp only [gmul, cre, ann]
  have h1 : v (k + unitIdx i) = 0 := hv _ (by rw [deg_add_unitIdx]; omega)
  by_cases h : k i = 0
  · simp [h, h1]
  · have h2 := deg_sub_unitIdx h
    simp [h1, hv (k - unitIdx i) (by omega)]

/-- **Fock bound, untruncated**: for symmetric `H_1, …, H_m` with
`∑_i ‖H_i u‖² ≤ c ‖u‖²`, `c ≥ 0`, and `v` supported in degrees `≤ N`,
`∑_{|k| ≤ N+1} ‖(fieldOp H v)_k‖² ≤ (2√(N+1)√c)² ∑_{|k| ≤ N} ‖v_k‖²`;
`fieldOp H v` is supported in degrees `≤ N+1` (`fieldOp_supp`). -/
theorem fieldOp_bound (N : ℕ) (H : Fin m → X →L[ℂ] X)
    (hH : ∀ i u w, inner ℂ (H i u) w = inner ℂ u (H i w)) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ u, ∑ i, ‖H i u‖ ^ 2 ≤ c * ‖u‖ ^ 2) {v : (Fin m → ℕ) → X} (hv : Supp N v) :
    ∑ k ∈ degLE m (N + 1), ‖fieldOp H v k‖ ^ 2 ≤
      (2 * Real.sqrt ((N : ℝ) + 1) * Real.sqrt c) ^ 2 * ∑ k ∈ degLE m N, ‖v k‖ ^ 2 := by
  have hsq : (2 * Real.sqrt ((N : ℝ) + 1) * Real.sqrt c) ^ 2 = 4 * ((N + 1) * c) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hc0]; ring
  have hV : ∑ k ∈ degLE m (N + 1), ‖v k‖ ^ 2 = ∑ k ∈ degLE m N, ‖v k‖ ^ 2 :=
    sum_degLE_eq_of_vanish (Nat.le_succ N) _ fun k hk => by simp [hv k hk]
  have hA : ∑ k ∈ degLE m (N + 1), ‖annOp H v k‖ ^ 2 = ∑ k ∈ degLE m N, ‖annOp H v k‖ ^ 2 :=
    sum_degLE_eq_of_vanish (Nat.le_succ N) _ fun k hk => by simp [annOp_supp H hv k hk]
  have hC := creOp_bound N H hc v
  have hAn := annOp_bound N H hH hc0 hc v
  rw [hV] at hAn
  have hpt : ∀ k, ‖fieldOp H v k‖ ^ 2 ≤ 2 * ‖creOp H v k‖ ^ 2 + 2 * ‖annOp H v k‖ ^ 2 := by
    intro k
    rw [fieldOp_eq]
    have := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (creOp H v k) (annOp H v k)) 2
    nlinarith [sq_nonneg (‖creOp H v k‖ - ‖annOp H v k‖)]
  calc _ ≤ ∑ k ∈ degLE m (N + 1), (2 * ‖creOp H v k‖ ^ 2 + 2 * ‖annOp H v k‖ ^ 2) :=
        Finset.sum_le_sum fun k _ => hpt k
    _ = 2 * ∑ k ∈ degLE m (N + 1), ‖creOp H v k‖ ^ 2 +
          2 * ∑ k ∈ degLE m N, ‖annOp H v k‖ ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hA]
    _ ≤ _ := by rw [hsq]; nlinarith

/-- **Fock bound, truncated** (`P_N` on both sides): for `v` supported in degrees
`≤ N`, `∑_{|k| ≤ N} ‖(fieldOp H v)_k‖² ≤ (2√(N+1)√c)² ∑_{|k| ≤ N} ‖v_k‖²`. -/
theorem fieldOp_bound_trunc (N : ℕ) (H : Fin m → X →L[ℂ] X)
    (hH : ∀ i u w, inner ℂ (H i u) w = inner ℂ u (H i w)) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ u, ∑ i, ‖H i u‖ ^ 2 ≤ c * ‖u‖ ^ 2) {v : (Fin m → ℕ) → X} (hv : Supp N v) :
    ∑ k ∈ degLE m N, ‖fieldOp H v k‖ ^ 2 ≤
      (2 * Real.sqrt ((N : ℝ) + 1) * Real.sqrt c) ^ 2 * ∑ k ∈ degLE m N, ‖v k‖ ^ 2 :=
  (Finset.sum_le_sum_of_subset_of_nonneg (degLE_mono (Nat.le_succ N))
    fun _ _ _ => sq_nonneg _).trans (fieldOp_bound N H hH hc0 hc hv)

/-- The truncated field operator is symmetric: for `v, w` supported in degrees
`≤ N`, `∑_{|k| ≤ N} ⟨(fieldOp H v)_k, w_k⟩ = ∑_{|k| ≤ N} ⟨v_k, (fieldOp H w)_k⟩`. -/
theorem fieldOp_symm_trunc (N : ℕ) (H : Fin m → X →L[ℂ] X)
    (hH : ∀ i u w, inner ℂ (H i u) w = inner ℂ u (H i w)) {v w : (Fin m → ℕ) → X}
    (hv : Supp N v) (hw : Supp N w) :
    ∑ k ∈ degLE m N, inner ℂ (fieldOp H v k) (w k) =
      ∑ k ∈ degLE m N, inner ℂ (v k) (fieldOp H w k) := by
  have hcre : ∀ i, ∑ k ∈ degLE m N, inner ℂ (cre i (fun l => H i (v l)) k) (w k) =
      ∑ k ∈ degLE m N, inner ℂ (v k) (ann i (fun l => H i (w l)) k) := by
    intro i
    rw [← sum_degLE_eq_of_vanish (Nat.le_succ N) _ (fun k hk => by simp [hw k hk]),
      sum_inner_cre]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [ann, inner_smul_right, map_smul, hH]
  have hann : ∀ i, ∑ k ∈ degLE m N, inner ℂ (ann i (fun l => H i (v l)) k) (w k) =
      ∑ k ∈ degLE m N, inner ℂ (v k) (cre i (fun l => H i (w l)) k) := by
    intro i
    rw [sum_inner_ann, sum_degLE_eq_of_vanish (Nat.le_succ N) _ (fun k hk => by simp [hv k hk])]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [cre, map_smul, inner_smul_right, hH]
  have hL : ∑ k ∈ degLE m N, inner ℂ (fieldOp H v k) (w k) =
      ∑ i, (∑ k ∈ degLE m N, inner ℂ (cre i (fun l => H i (v l)) k) (w k) +
        ∑ k ∈ degLE m N, inner ℂ (ann i (fun l => H i (v l)) k) (w k)) := by
    simp only [fieldOp, gmul, sum_inner, inner_add_left]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib
  have hR : ∑ k ∈ degLE m N, inner ℂ (v k) (fieldOp H w k) =
      ∑ i, (∑ k ∈ degLE m N, inner ℂ (v k) (cre i (fun l => H i (w l)) k) +
        ∑ k ∈ degLE m N, inner ℂ (v k) (ann i (fun l => H i (w l)) k)) := by
    simp only [fieldOp, gmul, inner_sum, inner_add_right]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib
  rw [hL, hR]
  exact Finset.sum_congr rfl fun i _ => by rw [hcre, hann, add_comm]

/-- **Creation-row norm attained**: for `w` of exact degree `j+1` (coefficients
outside `|k| = j+1` vanish), `u_i = a_i w` has degree `j` and
`∑_{|k| ≤ j+1} ‖∑_i (a_i^* u_i)_k‖² = (j+1) ∑_i ∑_{|k| ≤ j} ‖u_{i,k}‖²`, so the
bound `creRow_bound` with constant `j+1` is an equality on these vectors; also
`∑_i ∑_{|k| ≤ j} ‖(a_i w)_k‖² = (j+1) ∑_{|k| ≤ j+1} ‖w_k‖²`. -/
theorem creRow_attained (j : ℕ) {w : (Fin m → ℕ) → X} (hw : ∀ k, deg k ≠ j + 1 → w k = 0) :
    (∑ i, ∑ k ∈ degLE m j, ‖ann i w k‖ ^ 2 = ((j : ℝ) + 1) * ∑ k ∈ degLE m (j + 1), ‖w k‖ ^ 2) ∧
      ∑ k ∈ degLE m (j + 1), ‖creRow (fun i => ann i w) k‖ ^ 2 =
        ((j : ℝ) + 1) * ∑ i, ∑ k ∈ degLE m j, ‖ann i w k‖ ^ 2 := by
  have hdeg : ∀ k, ((deg k : ℝ) : ℂ) • w k = (((j : ℝ) + 1 : ℝ) : ℂ) • w k := by
    intro k
    by_cases h : deg k = j + 1
    · rw [h]; push_cast; rfl
    · simp [hw k h]
  have h1 : ∑ i, ∑ k ∈ degLE m j, ‖ann i w k‖ ^ 2 =
      ((j : ℝ) + 1) * ∑ k ∈ degLE m (j + 1), ‖w k‖ ^ 2 := by
    have e : ∀ i, ∑ k ∈ degLE m j, ‖ann i w k‖ ^ 2 =
        RCLike.re (∑ k ∈ degLE m (j + 1), inner ℂ (w k) (cre i (ann i w) k)) := by
      intro i
      rw [← sum_inner_ann, map_sum]
      exact Finset.sum_congr rfl fun k _ => @norm_sq_eq_re_inner ℂ _ _ _ _ _
    simp only [e, ← map_sum]
    rw [Finset.sum_comm]
    simp only [← inner_sum, number_identity, hdeg, inner_smul_right, map_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  refine ⟨h1, ?_⟩
  rw [h1]
  simp only [creRow, number_identity, hdeg, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [abs_of_nonneg (by positivity)]; ring

/-! ### The Gaussian side -/

/-- Auxiliary: for real functions `f_a` with integrable products and Gram
matrix `∫ f_a f_b dμ = δ_{ab}` on `s`, the map `(c_a) ↦ ∑_a f_a c_a` is an
isometry into `L²(μ; X)`; the integrand is integrable. -/
theorem integral_norm_sq_sum_smul {Ω ι : Type*} [DecidableEq ι] [MeasurableSpace Ω]
    (μ : Measure Ω)
    (s : Finset ι) (f : ι → Ω → ℝ) (c : ι → X)
    (hint : ∀ a ∈ s, ∀ b ∈ s, Integrable (fun x => f a x * f b x) μ)
    (horth : ∀ a ∈ s, ∀ b ∈ s, ∫ x, f a x * f b x ∂μ = if a = b then 1 else 0) :
    Integrable (fun x => ‖∑ a ∈ s, (f a x : ℂ) • c a‖ ^ 2) μ ∧
      ∫ x, ‖∑ a ∈ s, (f a x : ℂ) • c a‖ ^ 2 ∂μ = ∑ a ∈ s, ‖c a‖ ^ 2 := by
  have hpt : ∀ x, ‖∑ a ∈ s, (f a x : ℂ) • c a‖ ^ 2 =
      ∑ a ∈ s, ∑ b ∈ s, f a x * f b x * RCLike.re (inner ℂ (c a) (c b)) := by
    intro x
    rw [@norm_sq_eq_re_inner ℂ, sum_inner, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [inner_sum, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc,
      ← Complex.ofReal_mul]
    exact Complex.re_ofReal_mul _ _
  have hfun : (fun x => ‖∑ a ∈ s, (f a x : ℂ) • c a‖ ^ 2) =
      fun x => ∑ a ∈ s, ∑ b ∈ s, f a x * f b x * RCLike.re (inner ℂ (c a) (c b)) :=
    funext hpt
  have hI : Integrable (fun x => ∑ a ∈ s, ∑ b ∈ s,
      f a x * f b x * RCLike.re (inner ℂ (c a) (c b))) μ :=
    integrable_finsetSum _ fun a ha => integrable_finsetSum _ fun b hb =>
      (hint a ha b hb).mul_const _
  refine ⟨hfun ▸ hI, ?_⟩
  rw [hfun, integral_finsetSum _ fun a ha => integrable_finsetSum _ fun b hb =>
    (hint a ha b hb).mul_const _]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [integral_finsetSum _ fun b hb => (hint a ha b hb).mul_const _]
  simp only [integral_mul_const]
  rw [Finset.sum_eq_single a (fun b hb hba => by rw [horth a ha b hb]; simp [Ne.symm hba])
    (fun h => absurd ha h), horth a ha a ha]
  simp only [↓reduceIte, one_mul]
  rw [inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

/-- The Hermite expansion `iota N v x = ∑_{|k| ≤ N} hk_k(x) v_k` of a
coefficient vector, an `X`-valued function on `ℝ^m`. -/
def iota (N : ℕ) (v : (Fin m → ℕ) → X) (x : Fin m → ℝ) : X :=
  ∑ k ∈ degLE m N, (hk k x : ℂ) • v k

/-- **Isometry of the expansion**: `∫ ‖iota N v‖² dγ_m = ∑_{|k| ≤ N} ‖v_k‖²`,
with integrability, under the standard Gaussian `stdPi m`. -/
theorem integral_norm_sq_iota (N : ℕ) (v : (Fin m → ℕ) → X) :
    Integrable (fun x => ‖iota N v x‖ ^ 2) (GaussianIBP.stdPi m) ∧
      ∫ x, ‖iota N v x‖ ^ 2 ∂GaussianIBP.stdPi m = ∑ k ∈ degLE m N, ‖v k‖ ^ 2 :=
  integral_norm_sq_sum_smul _ _ (fun k x => hk k x) v
    (fun k _ l _ => GaussianHermite.integrable_hk_mul_hk k l)
    (fun k _ l _ => GaussianHermite.integral_hk_mul_hk k l)

/-- The expansion of the vacuum vector `1 ⊗ u` is the constant `u`. -/
theorem iota_vac (N : ℕ) (u : X) (x : Fin m → ℝ) : iota N (vac u) x = u := by
  classical
  rw [iota, Finset.sum_eq_single (0 : Fin m → ℕ) (fun k _ hk => by simp [vac, hk])
    (fun h => absurd (zero_mem_degLE N) h)]
  simp [vac, GaussianHermite.hk_zero]

/-- **Coordinate multiplication** on the expansion: for `v` supported in degrees
`≤ N`, `x_i · iota N v = iota (N+1) (gmul i v)`. -/
theorem coord_smul_iota (N : ℕ) (i : Fin m) {v : (Fin m → ℕ) → X} (hv : Supp N v)
    (x : Fin m → ℝ) :
    ((x i : ℝ) : ℂ) • iota N v x = iota (N + 1) (gmul i v) x := by
  -- left side, split by the coordinate recurrence
  have hL : ((x i : ℝ) : ℂ) • iota N v x =
      ∑ k ∈ degLE m N, ((Real.sqrt ((k i : ℝ) + 1) * hk (k + unitIdx i) x : ℝ) : ℂ) • v k +
      ∑ k ∈ degLE m N, ((Real.sqrt (k i : ℝ) * hk (k - unitIdx i) x : ℝ) : ℂ) • v k := by
    rw [iota, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul, ← Complex.ofReal_mul, GaussianHermite.coord_mul_hk, Complex.ofReal_add,
      add_smul]
  -- creation part of the right side
  have hC : ∑ k ∈ degLE m (N + 1), (hk k x : ℂ) • cre i v k =
      ∑ k ∈ degLE m N, ((Real.sqrt ((k i : ℝ) + 1) * hk (k + unitIdx i) x : ℝ) : ℂ) • v k := by
    rw [sum_degLE_succ_eq i N _ (fun k hk => by simp [cre_of_eq_zero i v hk])]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [cre, add_unitIdx_apply, add_sub_unitIdx, smul_smul]
    push_cast; congr 1; ring
  -- annihilation part of the right side
  have hA : ∑ k ∈ degLE m (N + 1), (hk k x : ℂ) • ann i v k =
      ∑ k ∈ degLE m N, ((Real.sqrt (k i : ℝ) * hk (k - unitIdx i) x : ℝ) : ℂ) • v k := by
    have h1 : ∑ k ∈ degLE m N, ((Real.sqrt (k i : ℝ) * hk (k - unitIdx i) x : ℝ) : ℂ) • v k =
        ∑ k ∈ degLE m (N + 1),
          ((Real.sqrt (k i : ℝ) * hk (k - unitIdx i) x : ℝ) : ℂ) • v k :=
      (sum_degLE_eq_of_vanish (Nat.le_succ N) _ fun k hk => by simp [hv k hk]).symm
    have h2 : ∑ k ∈ degLE m (N + 1),
          ((Real.sqrt (k i : ℝ) * hk (k - unitIdx i) x : ℝ) : ℂ) • v k =
        ∑ j ∈ degLE m N,
          ((Real.sqrt ((j + unitIdx i) i : ℝ) * hk (j + unitIdx i - unitIdx i) x : ℝ) : ℂ) •
            v (j + unitIdx i) :=
      sum_degLE_succ_eq i N (fun k => ((Real.sqrt (k i : ℝ) * hk (k - unitIdx i) x : ℝ) : ℂ) • v k)
        (fun k hk => by simp [hk])
    have h3 : ∑ k ∈ degLE m (N + 1), (hk k x : ℂ) • ann i v k =
        ∑ k ∈ degLE m N, (hk k x : ℂ) • ann i v k :=
      sum_degLE_eq_of_vanish (Nat.le_succ N) (fun k => (hk k x : ℂ) • ann i v k)
        fun k hk => by simp [ann, hv (k + unitIdx i) (by rw [deg_add_unitIdx]; omega)]
    rw [h1, h2, h3]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [ann, add_unitIdx_apply, add_sub_unitIdx, smul_smul]
    push_cast; congr 1; ring
  rw [hL, iota]
  simp only [gmul, smul_add, Finset.sum_add_distrib, hC, hA]

/-- **Field operator on the expansion**: for `v` supported in degrees `≤ N`,
`∑_i x_i H_i (iota N v x) = iota (N+1) (fieldOp H v) x`. -/
theorem sum_coord_smul_iota (N : ℕ) (H : Fin m → X →L[ℂ] X) {v : (Fin m → ℕ) → X}
    (hv : Supp N v) (x : Fin m → ℝ) :
    ∑ i, ((x i : ℝ) : ℂ) • H i (iota N v x) = iota (N + 1) (fieldOp H v) x := by
  have hHv : ∀ i, Supp N (fun l => H i (v l)) := fun i k hk => by simp [hv k hk]
  have e : ∀ i, H i (iota N v x) = iota N (fun l => H i (v l)) x := by
    intro i; simp [iota, map_sum]
  simp only [e, coord_smul_iota N _ (hHv _)]
  simp only [iota, fieldOp, Finset.smul_sum]
  rw [Finset.sum_comm]

/-- **Gaussian Fock bound, untruncated**: for symmetric `H_i` with
`∑_i ‖H_i u‖² ≤ c ‖u‖²`, `c ≥ 0`, and `v` supported in degrees `≤ N`,
`∫ ‖∑_i x_i H_i (iota N v x)‖² dγ_m ≤ (2√(N+1)√c)² ∫ ‖iota N v x‖² dγ_m`,
both integrands integrable. -/
theorem gaussian_field_bound (N : ℕ) (H : Fin m → X →L[ℂ] X)
    (hH : ∀ i u w, inner ℂ (H i u) w = inner ℂ u (H i w)) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ u, ∑ i, ‖H i u‖ ^ 2 ≤ c * ‖u‖ ^ 2) {v : (Fin m → ℕ) → X} (hv : Supp N v) :
    Integrable (fun x => ‖∑ i, ((x i : ℝ) : ℂ) • H i (iota N v x)‖ ^ 2)
        (GaussianIBP.stdPi m) ∧
      Integrable (fun x => ‖iota N v x‖ ^ 2) (GaussianIBP.stdPi m) ∧
      ∫ x, ‖∑ i, ((x i : ℝ) : ℂ) • H i (iota N v x)‖ ^ 2 ∂GaussianIBP.stdPi m ≤
        (2 * Real.sqrt ((N : ℝ) + 1) * Real.sqrt c) ^ 2 *
          ∫ x, ‖iota N v x‖ ^ 2 ∂GaussianIBP.stdPi m := by
  simp only [sum_coord_smul_iota N H hv]
  obtain ⟨h1, h2⟩ := integral_norm_sq_iota (N + 1) (fieldOp H v)
  obtain ⟨h3, h4⟩ := integral_norm_sq_iota N v
  exact ⟨h1, h3, by rw [h2, h4]; exact fieldOp_bound N H hH hc0 hc hv⟩

/-- **Gaussian Fock bound, truncated** (`P_N` on the output: the expansion of
the coefficients of degree `≤ N`):
`∫ ‖iota N (fieldOp H v) x‖² dγ_m ≤ (2√(N+1)√c)² ∫ ‖iota N v x‖² dγ_m`. -/
theorem gaussian_field_bound_trunc (N : ℕ) (H : Fin m → X →L[ℂ] X)
    (hH : ∀ i u w, inner ℂ (H i u) w = inner ℂ u (H i w)) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ u, ∑ i, ‖H i u‖ ^ 2 ≤ c * ‖u‖ ^ 2) {v : (Fin m → ℕ) → X} (hv : Supp N v) :
    Integrable (fun x => ‖iota N (fieldOp H v) x‖ ^ 2) (GaussianIBP.stdPi m) ∧
      ∫ x, ‖iota N (fieldOp H v) x‖ ^ 2 ∂GaussianIBP.stdPi m ≤
        (2 * Real.sqrt ((N : ℝ) + 1) * Real.sqrt c) ^ 2 *
          ∫ x, ‖iota N v x‖ ^ 2 ∂GaussianIBP.stdPi m := by
  obtain ⟨h1, h2⟩ := integral_norm_sq_iota N (fieldOp H v)
  obtain ⟨_, h4⟩ := integral_norm_sq_iota N v
  exact ⟨h1, by rw [h2, h4]; exact fieldOp_bound_trunc N H hH hc0 hc hv⟩

/-- **Vacuum insertion isometry**: `∫ ‖∑_i x_i w_i‖² dγ_m = ∑_i ‖w_i‖²`, with
integrability (the first-chaos isometry; with `w_i = K_i u` this is the phase
insertion `u ↦ ∑_i g_i K_i u` on a color in its vacuum). -/
theorem vacuum_insertion_isometry (w : Fin m → X) :
    Integrable (fun x => ‖∑ i, ((x i : ℝ) : ℂ) • w i‖ ^ 2) (GaussianIBP.stdPi m) ∧
      ∫ x, ‖∑ i, ((x i : ℝ) : ℂ) • w i‖ ^ 2 ∂GaussianIBP.stdPi m = ∑ i, ‖w i‖ ^ 2 := by
  have hx : ∀ i (x : Fin m → ℝ), x i = hk (unitIdx i) x := fun i x =>
    (GaussianHermite.hk_unitIdx i x).symm
  have := integral_norm_sq_sum_smul (GaussianIBP.stdPi m) univ (fun i x => x i) w
    (fun i _ j _ => by
      simpa [hx] using GaussianHermite.integrable_hk_mul_hk (unitIdx i) (unitIdx j))
    (fun i _ j _ => by
      simp only [hx, GaussianHermite.integral_hk_mul_hk]
      simp [unitIdx, Pi.single_left_inj (one_ne_zero (α := ℕ))])
  exact this

end StratonovichHAMSecondMoment.HermiteFock
