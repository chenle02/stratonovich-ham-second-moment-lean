module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L12 item F1: the supplied input `StaticInteractionCompleted.FockSandwich`
(`E:fock-sandwich` of `L:fock-form`) is discharged on a concrete model of the cutoff Hilbert
space, in `notes/notes_stratonovich_ham_second_moment.tex` (main TeX; line numbers at
revision 39f2597a).

`L:fock-form` (statement lines 2960-2977, proof 2979-3028) works "on the joint range" of
`P_N` (Hermite degrees at most `N`) and `S_b` (spatial Fourier band `|η| ≤ b`), where
`B_{N,m,b} = P_N S_b (∑_{i ≤ m} g_i M_{e_i}) S_b P_N` and `A_ρ = ρ² - Δ`, and claims
`‖A_ρ^{-1/2} B_{N,m,b} A_ρ^{-1/2}‖ ≤ d_N ρ^{α/2-2}` (lines 2972-2976).  The proof ends
(lines 3025-3026): "Boundedness of `-Δ` on `S_b` is explicit; no infinite-frequency operator
theorem was used."  `FockSandwich` states this bound with `A_ρ^{-1/2}` read as
`ComplexPhaseScalar.invSqrtShift A_0 ρ`, the `Ring.inverse` of the continuous functional
calculus square root of `A_0 + ρ²` for a bounded positive `A_0`.

Model choice (recorded as such; it is not the TeX's physical-space Hilbert space).
* Spatial `L²(ℝ³)` is K2's Fourier side `X = L²(ℝ³, dη)` (`FockColumnBound`), on which
  `S_b` is `bandProj b` (multiplication by `1_{|η| ≤ b}`), `A_ρ^{-1/2}` is `sqrtResolvent ρ`
  (multiplication by `(ρ² + |η|²)^{-1/2}`) and `M_{e_i}` is `modes … i` (convolution with
  `conj ψ_i μ_ε`).  The identification with physical-space operators (conjugation by the
  unitary Fourier transform) is not formalized, exactly as in K2; every conclusion here
  (operator norms, self-adjointness, positivity) is invariant under that unitary conjugation.
* The Gaussian factor truncated to degrees `≤ N` is `HermiteFock`'s coefficient model over the
  multi-indices `degLE m N`; the cutoff Hilbert space is the finite `ℓ²` sum
  `FockSp X m N = PiLp 2 (fun _ : degLE m N => X)` (`P_N` is built in).
* The band cutoff is not built into the space: we work on all of `FockSp X m N`, with
  `A_0 = diag M_{|η|² 1_{|η| ≤ b}}` (`opA0`), which is `-Δ` on the band range and `0` on its
  complement, and `B = B_{N,m,b}` (`fieldB`) the truncated field of the compressed
  `S_b M_{e_i} S_b`, which vanishes on the complement of the joint range and maps into it
  (`fieldB_band`).  On the joint range, `invSqrtShift A_0 ρ` is `A_ρ^{-1/2} = (ρ² - Δ)^{-1/2}`
  (`invSqrtShift_band`), so the operator bounded by `FockSandwich` is the TeX's operator
  extended by zero.

Formalized (nothing supplied):
* the diagonal extension `diagOp` of an operator on `X` to `PiLp 2`, with products, the unit,
  sums, `algebraMap`, adjoints, self-adjointness and positivity (`diagOp_nonneg`);
* the truncated field operator `fockOp H` as a continuous linear map on `FockSp X m N`, equal
  componentwise to `HermiteFock.fieldOp H` on degrees `≤ N` (`fockOp_apply`), self-adjoint for
  symmetric `H_i` (`fockOp_isSelfAdjoint`), with the norm identity `norm_sq_fockOp`;
* `0 ≤ M_a` for `a ≥ 0` (`mulOp_nonneg`), `M_1 = 1` (`mulOp_one`);
* the functional calculus on the model: `A_0 + ρ² = diag M_{ρ² + |η|² 1_b}` (`shiftOp_eq`),
  `CFC.sqrt (A_0 + ρ²) = diag M_{√(ρ² + |η|² 1_b)}` (`sqrt_shiftOp_eq`, by `CFC.sqrt_eq_iff`),
  `invSqrtShift A_0 ρ = diag M_{(ρ² + |η|² 1_b)^{-1/2}}` (`invSqrtShift_eq`, by an explicit
  two-sided inverse, so `Ring.inverse` is the genuine inverse);
* `E:fock-sandwich` on the model: `invSqrtShift A_0 ρ * B * invSqrtShift A_0 ρ` is the
  truncated field of `S_b H_i S_b` with K2's `H_i = A_ρ^{-1/2} M_{e_i} A_ρ^{-1/2}`
  (`sandwich_eq`), hence (`FockForm.fock_form` + `FockColumnBound.fock_column_completed`)
  `FockSandwich A_0 B d_N (α/2)` (`fockSandwich_model`, with `A_0 ≥ 0` and `B` self-adjoint);
  wrapper `fock_sandwich_paper` (`L:fock-form` in operator form, statement lines 2960-2977);
* the re-issued wrappers `static_phase_all_orders_model` (`E:all-static-phase-orders` of
  `P:static-phase-all-orders`, lines 3098-3192) and `static_interaction_model_paper`
  (`C:static-interaction`, lines 3216-3341), with `FockSandwich` discharged on this model.

Hypotheses beyond the manuscript's class (as in K2): finitely many modes `ψ_1, …, ψ_m`
orthonormal in `L²(μ_ε)` and real (`ψ_i(-ξ) = conj ψ_i(ξ)`), the band radius `b`, and the
Fourier-side model.  The TeX bound is "uniformly in `ε, m, b`": the constant `d_N` here does
not depend on `ε`, `m`, `b` or the modes.

Narrower than the TeX: the Fourier-to-physical identification is not formalized (above);
finitely many modes.  `C:static-interaction` and `P:static-phase-all-orders` remain narrower:
they still take `CPInputs`, `PropagatorBlock` (now at the concrete `A_0`, `B`), entireness,
the coefficient identification and cutoff removals of
`StaticPhaseCauchy.static_phase_all_orders_step`, the free estimate and norm comparisons,
Gaussian parity and the first-variance bounds (documented in `StaticInteractionCompleted`).

Junk values: `ρ > 0` throughout, so `(ρ² + |η|² 1_b)^{-1/2}` has a positive base and
`ρ^{α/2-2}` is a genuine power; `Ring.inverse` is applied only to an operator with an explicit
two-sided inverse (`invSqrtShift_eq`); `R_α ≥ 0` is proved.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.FockColumnBound
public import StratonovichHAMSecondMoment.StaticInteractionCompleted

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Real Finset Filter Topology Set
open scoped ComplexConjugate Nat

namespace StratonovichHAMSecondMoment.FockSandwichModel

open HomogHypothesis (Rd)
open HermiteFock (Supp degLE fieldOp mem_degLE deg gmul cre ann)
open GaussianHermite (unitIdx)
open FockColumnBound (mulOp mulOp_ae mulOp_comp mulOp_isSelfAdjoint op_ext band measurable_band
  abs_band_le bandProj wt measurable_wt sqrtResolvent nuEps nuEps_finite nuEps_even modes)
open ComplexPhaseScalar (invSqrtShift shiftOp)
open StaticInteractionCompleted (FockSandwich CPInputs PropagatorBlock InDisc)
open StaticPhaseCauchy (fockD taylorCoeff allOrdersA)
open SpectralMassIdentity (ralpha)
open PhaseContractions (PhaseCovariance dGam)
open IntervalScalar (staticE)

/-! ### Diagonal operators on a finite `ℓ²` sum -/

section Diag

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
variable {ι : Type*} [Fintype ι]

/-- Assemble a continuous linear map into `PiLp 2` from its components. -/
def piL {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (F : ι → E →L[ℂ] X) :
    E →L[ℂ] PiLp 2 (fun _ : ι => X) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => X)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi F

omit [Fintype ι] in
/-- Components of `piL F`. -/
theorem piL_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (F : ι → E →L[ℂ] X)
    (x : E) (i : ι) : piL F x i = F i x := rfl

/-- The diagonal operator `T ⊕ ⋯ ⊕ T` on `PiLp 2 (ι → X)`. -/
def diagOp (T : X →L[ℂ] X) : PiLp 2 (fun _ : ι => X) →L[ℂ] PiLp 2 (fun _ : ι => X) :=
  piL fun i => T ∘L PiLp.proj 2 (fun _ : ι => X) i

/-- Components of `diagOp T`. -/
theorem diagOp_apply (T : X →L[ℂ] X) (x : PiLp 2 (fun _ : ι => X)) (i : ι) :
    diagOp (ι := ι) T x i = T (x i) := rfl

/-- `diag (S T) = diag S · diag T`. -/
theorem diagOp_mul (S T : X →L[ℂ] X) :
    diagOp (ι := ι) (S * T) = diagOp S * diagOp T := by
  ext x i; rfl

/-- `diag 1 = 1`. -/
theorem diagOp_one : diagOp (ι := ι) (1 : X →L[ℂ] X) = 1 := by
  ext x i; rfl

/-- `diag (S + T) = diag S + diag T`. -/
theorem diagOp_add (S T : X →L[ℂ] X) :
    diagOp (ι := ι) (S + T) = diagOp S + diagOp T := by
  ext x i; rfl

/-- `diag (c T) = c diag T`. -/
theorem diagOp_smul (c : ℂ) (T : X →L[ℂ] X) :
    diagOp (ι := ι) (c • T) = c • diagOp T := by
  ext x i; rfl

variable [CompleteSpace X]

/-- `diag (T^*) = (diag T)^*`. -/
theorem diagOp_adjoint (T : X →L[ℂ] X) :
    diagOp (ι := ι) (ContinuousLinearMap.adjoint T) =
      ContinuousLinearMap.adjoint (diagOp (ι := ι) T) := by
  refine (ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y => ?_
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact ContinuousLinearMap.adjoint_inner_left T (y i) (x i)

/-- `diag` preserves self-adjointness. -/
theorem diagOp_isSelfAdjoint {T : X →L[ℂ] X} (hT : IsSelfAdjoint T) :
    IsSelfAdjoint (diagOp (ι := ι) T) := by
  show star (diagOp (ι := ι) T) = diagOp T
  rw [ContinuousLinearMap.star_eq_adjoint, ← diagOp_adjoint, ← ContinuousLinearMap.star_eq_adjoint,
    hT.star_eq]

/-- `diag` preserves positivity: `T = (√T)^* √T`. -/
theorem diagOp_nonneg {T : X →L[ℂ] X} (hT : 0 ≤ T) : 0 ≤ diagOp (ι := ι) T := by
  have hs : IsSelfAdjoint (CFC.sqrt T) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)
  have h : diagOp (ι := ι) T = star (diagOp (ι := ι) (CFC.sqrt T)) * diagOp (CFC.sqrt T) := by
    rw [(diagOp_isSelfAdjoint hs).star_eq, ← diagOp_mul, CFC.sqrt_mul_sqrt_self T hT]
  rw [h]
  exact star_mul_self_nonneg _

end Diag

/-! ### The truncated Fock space and the field operator -/

section Fock

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {m N : ℕ}

/-- The cutoff Fock space: coefficient vectors over the multi-indices of Hermite degree
`≤ N` in `m` Gaussian modes, with values in `X`, with the `ℓ²` norm (the range of `P_N`). -/
abbrev FockSp (X : Type*) [NormedAddCommGroup X] [InnerProductSpace ℂ X] (m N : ℕ) :=
  PiLp 2 (fun _ : degLE m N => X)

/-- The coefficient function of a vector of `FockSp X m N`, extended by zero above degree
`N`. -/
def coeffs (x : FockSp X m N) (k : Fin m → ℕ) : X :=
  if h : k ∈ degLE m N then x ⟨k, h⟩ else 0

/-- Auxiliary: the coefficient at an index of degree `≤ N`. -/
theorem coeffs_coe (x : FockSp X m N) (k : degLE m N) : coeffs x k.1 = x k := dite_eq_left k.2

/-- The coefficients are supported in degrees `≤ N`. -/
theorem coeffs_supp (x : FockSp X m N) : Supp N (coeffs x) := by
  intro k hk
  have : k ∉ degLE m N := fun h => by rw [mem_degLE] at h; omega
  simp [coeffs, this]

/-- Coefficients of a diagonal image. -/
theorem coeffs_diagOp (T : X →L[ℂ] X) (x : FockSp X m N) (k : Fin m → ℕ) :
    coeffs (diagOp T x) k = T (coeffs x k) := by
  unfold coeffs
  split_ifs with h
  · rfl
  · exact (map_zero T).symm

/-- `‖x‖² = ∑_{|k| ≤ N} ‖x_k‖²`. -/
theorem norm_sq_fock (x : FockSp X m N) : ‖x‖ ^ 2 = ∑ k ∈ degLE m N, ‖coeffs x k‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, ← Finset.sum_coe_sort (degLE m N)]
  exact Finset.sum_congr rfl fun k _ => by rw [coeffs_coe]

/-- `⟪x, y⟫ = ∑_{|k| ≤ N} ⟪x_k, y_k⟫`. -/
theorem inner_fock (x y : FockSp X m N) :
    inner ℂ x y = ∑ k ∈ degLE m N, inner ℂ (coeffs x k) (coeffs y k) := by
  rw [PiLp.inner_apply, ← Finset.sum_coe_sort (degLE m N)]
  exact Finset.sum_congr rfl fun k _ => by rw [coeffs_coe, coeffs_coe]

/-- Auxiliary: `|k - e_i| ≤ |k|`. -/
theorem deg_sub_unitIdx_le (k : Fin m → ℕ) (i : Fin m) : deg (k - unitIdx i) ≤ deg k :=
  Finset.sum_le_sum fun _ _ => Nat.sub_le _ _

/-- Auxiliary: `k - e_i` stays in degrees `≤ N`. -/
theorem sub_mem_degLE (k : degLE m N) (i : Fin m) : k.1 - unitIdx i ∈ degLE m N :=
  mem_degLE.2 ((deg_sub_unitIdx_le k.1 i).trans (mem_degLE.1 k.2))

/-- The creation component `k ↦ √k_i H x_{k-e_i}`. -/
def creTerm (H : X →L[ℂ] X) (i : Fin m) (k : degLE m N) : FockSp X m N →L[ℂ] X :=
  ((Real.sqrt (k.1 i : ℝ) : ℂ)) •
    (H ∘L PiLp.proj 2 (fun _ : degLE m N => X) ⟨k.1 - unitIdx i, sub_mem_degLE k i⟩)

/-- The annihilation component `k ↦ √(k_i+1) H x_{k+e_i}` (zero if `|k + e_i| > N`). -/
def annTerm (H : X →L[ℂ] X) (i : Fin m) (k : degLE m N) : FockSp X m N →L[ℂ] X :=
  if h : k.1 + unitIdx i ∈ degLE m N then
    ((Real.sqrt ((k.1 i : ℝ) + 1) : ℂ)) •
      (H ∘L PiLp.proj 2 (fun _ : degLE m N => X) ⟨k.1 + unitIdx i, h⟩)
  else 0

/-- The truncated field operator `P_N (∑_i (a_i^* + a_i) ⊗ H_i) P_N` on `FockSp X m N`. -/
def fockOp (H : Fin m → X →L[ℂ] X) : FockSp X m N →L[ℂ] FockSp X m N :=
  piL fun k => ∑ i, (creTerm (H i) i k + annTerm (H i) i k)

/-- `fockOp` is `HermiteFock.fieldOp` on the coefficients, in degrees `≤ N`. -/
theorem fockOp_apply (H : Fin m → X →L[ℂ] X) (x : FockSp X m N) (k : degLE m N) :
    fockOp H x k = fieldOp H (coeffs x) k.1 := by
  rw [fockOp, piL_apply, _root_.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_apply, gmul, cre, ann]
  congr 1
  · simp only [creTerm, smul_apply, ContinuousLinearMap.comp_apply]
    rw [coeffs, dite_eq_left (sub_mem_degLE k i)]
    rfl
  · by_cases h : k.1 + unitIdx i ∈ degLE m N
    · simp only [annTerm, dite_eq_left h, smul_apply,
        ContinuousLinearMap.comp_apply]
      rw [coeffs, dite_eq_left h]
      rfl
    · simp [annTerm, h, coeffs]

/-- Coefficients of `fockOp H x`. -/
theorem coeffs_fockOp (H : Fin m → X →L[ℂ] X) (x : FockSp X m N) (k : Fin m → ℕ) :
    coeffs (fockOp H x) k = if k ∈ degLE m N then fieldOp H (coeffs x) k else 0 := by
  unfold coeffs
  split_ifs with h
  · exact fockOp_apply H x ⟨k, h⟩
  · rfl

/-- `‖fockOp H x‖² = ∑_{|k| ≤ N} ‖(fieldOp H x)_k‖²`. -/
theorem norm_sq_fockOp (H : Fin m → X →L[ℂ] X) (x : FockSp X m N) :
    ‖fockOp H x‖ ^ 2 = ∑ k ∈ degLE m N, ‖fieldOp H (coeffs x) k‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, ← Finset.sum_coe_sort (degLE m N)]
  exact Finset.sum_congr rfl fun k _ => by rw [← fockOp_apply]

/-- Conjugating the field: `T (fieldOp H (S v))_k = (fieldOp (T H_i S) v)_k`. -/
theorem fieldOp_conj (T S : X →L[ℂ] X) (H : Fin m → X →L[ℂ] X) (v : (Fin m → ℕ) → X)
    (k : Fin m → ℕ) :
    T (fieldOp H (fun l => S (v l)) k) = fieldOp (fun i => T ∘L H i ∘L S) v k := by
  simp [fieldOp, gmul, cre, ann, map_sum, map_add]

/-- `diag T · fockOp H · diag S = fockOp (T H_i S)`. -/
theorem diagOp_fockOp_diagOp (T S : X →L[ℂ] X) (H : Fin m → X →L[ℂ] X) :
    diagOp T * fockOp (N := N) H * diagOp S = fockOp (fun i => T ∘L H i ∘L S) := by
  ext x k
  simp only [mul_apply_eq_comp]
  rw [diagOp_apply, fockOp_apply, fockOp_apply]
  have hc : coeffs (diagOp S x) = fun l => S (coeffs x l) := funext (coeffs_diagOp S x)
  rw [hc, fieldOp_conj]

/-- The Fock bound for `fockOp` from a column bound: for symmetric `H_i` with
`∑_i ‖H_i u‖² ≤ c ‖u‖²`, `c ≥ 0`, `‖fockOp H‖ ≤ 2√(N+1)√c`. -/
theorem fockOp_norm_le (H : Fin m → X →L[ℂ] X)
    (hH : ∀ i u w, inner ℂ (H i u) w = inner ℂ u (H i w)) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ u, ∑ i, ‖H i u‖ ^ 2 ≤ c * ‖u‖ ^ 2) :
    ‖fockOp (N := N) H‖ ≤ 2 * Real.sqrt ((N : ℝ) + 1) * Real.sqrt c := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
  rw [norm_sq_fockOp, mul_pow, norm_sq_fock]
  exact HermiteFock.fieldOp_bound_trunc N H hH hc0 hc (coeffs_supp x)

variable [CompleteSpace X]

/-- `fockOp H` is self-adjoint for symmetric `H_i` (the truncated field is symmetric). -/
theorem fockOp_isSelfAdjoint (H : Fin m → X →L[ℂ] X)
    (hH : ∀ i u w, inner ℂ (H i u) w = inner ℂ u (H i w)) :
    IsSelfAdjoint (fockOp (N := N) H) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  simp only [ContinuousLinearMap.coe_coe]
  rw [inner_fock, inner_fock]
  have hx : ∀ k ∈ degLE m N, inner ℂ (coeffs (fockOp H x) k) (coeffs y k) =
      inner ℂ (fieldOp H (coeffs x) k) (coeffs y k) := fun k hk => by
    rw [coeffs_fockOp, ite_eq_left hk]
  have hy : ∀ k ∈ degLE m N, inner ℂ (coeffs x k) (coeffs (fockOp H y) k) =
      inner ℂ (coeffs x k) (fieldOp H (coeffs y) k) := fun k hk => by
    rw [coeffs_fockOp, ite_eq_left hk]
  rw [Finset.sum_congr rfl hx, Finset.sum_congr rfl hy]
  exact HermiteFock.fieldOp_symm_trunc N H hH (coeffs_supp x) (coeffs_supp y)

end Fock

/-! ### Multiplication operators: unit, positivity, commuting products -/

section Mul

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- `M_1 = 1`. -/
theorem mulOp_one :
    mulOp (μ := μ) (fun _ => (1 : ℝ)) measurable_const 1 (fun _ => by simp) = 1 := by
  refine op_ext fun f => ?_
  filter_upwards [mulOp_ae (μ := μ) (fun _ => (1 : ℝ)) measurable_const 1 (fun _ => by simp) f]
    with x hx
  rw [hx]
  simp

/-- Two products of multiplication operators agree when the products of the functions do. -/
theorem mulOp_comp_comm (a b c e : α → ℝ) (ha : Measurable a) (hb : Measurable b)
    (hc : Measurable c) (he : Measurable e) (A B C D : ℝ) (hA : ∀ x, |a x| ≤ A)
    (hB : ∀ x, |b x| ≤ B) (hC : ∀ x, |c x| ≤ C) (hD : ∀ x, |e x| ≤ D)
    (h : ∀ x, a x * b x = c x * e x) :
    mulOp (μ := μ) a ha A hA ∘L mulOp b hb B hB = mulOp c hc C hC ∘L mulOp e he D hD := by
  have hAB : ∀ x, |a x * b x| ≤ A * B := fun x => by
    rw [abs_mul]; exact mul_le_mul (hA x) (hB x) (abs_nonneg _) ((abs_nonneg _).trans (hA x))
  have hAB' : ∀ x, |(fun y => a y * b y) x| ≤ A * B := hAB
  rw [mulOp_comp a b (fun y => a y * b y) ha hb (ha.mul hb) A B (A * B) hA hB hAB'
    fun _ => rfl, mulOp_comp c e (fun y => a y * b y) hc he (ha.mul hb) C D (A * B) hC hD hAB'
    fun x => (h x).symm]

/-- A nonnegative multiplication operator is positive: `M_a = M_{√a}^* M_{√a}`. -/
theorem mulOp_nonneg (a : α → ℝ) (ha : Measurable a) (B : ℝ) (hB : ∀ x, |a x| ≤ B)
    (ha0 : ∀ x, 0 ≤ a x) : 0 ≤ mulOp (μ := μ) a ha B hB := by
  have hs : ∀ x, |Real.sqrt (a x)| ≤ Real.sqrt B := fun x => by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt ((le_abs_self _).trans (hB x))
  have hsm : Measurable fun x => Real.sqrt (a x) := ha.sqrt
  have h : mulOp (μ := μ) a ha B hB =
      star (mulOp (μ := μ) (fun x => Real.sqrt (a x)) hsm _ hs) * mulOp _ hsm _ hs := by
    rw [(mulOp_isSelfAdjoint _ hsm _ hs).star_eq, ContinuousLinearMap.mul_def,
      mulOp_comp _ _ a hsm hsm ha _ _ B hs hs hB fun x => Real.mul_self_sqrt (ha0 x)]
  rw [h]
  exact star_mul_self_nonneg _

/-- `M_a + r = M_{r + a}` for a real constant `r` (acting as the complex scalar `r`). -/
theorem mulOp_add_smul_one (a : α → ℝ) (ha : Measurable a) (A : ℝ) (hA : ∀ x, |a x| ≤ A)
    (r : ℝ) (c : α → ℝ) (hc : Measurable c) (C : ℝ) (hC : ∀ x, |c x| ≤ C)
    (hac : ∀ x, c x = r + a x) :
    mulOp (μ := μ) a ha A hA + (r : ℂ) • (1 : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) = mulOp c hc C hC := by
  refine op_ext fun f => ?_
  rw [add_apply, smul_apply, one_apply_eq_self]
  filter_upwards [Lp.coeFn_add (mulOp (μ := μ) a ha A hA f) ((r : ℂ) • f),
    mulOp_ae (μ := μ) a ha A hA f, mulOp_ae (μ := μ) c hc C hC f, Lp.coeFn_smul (r : ℂ) f]
    with x h1 h2 h3 h4
  rw [h1, Pi.add_apply, h2, h3, h4, Pi.smul_apply, hac x, smul_eq_mul]
  push_cast
  ring

end Mul

/-! ### The concrete model: symbols -/

section Symbols

variable {d : ℕ}

/-- The symbol of `A_0` on the band: `|η|² 1_{|η| ≤ b}` (`-Δ` compressed to `S_b`, main TeX
lines 2969 and 3025-3026). -/
def symA (b : ℝ) (η : Rd d) : ℝ := ‖η‖ ^ 2 * band b η

/-- Auxiliary: `symA` is measurable. -/
theorem measurable_symA (b : ℝ) : Measurable (symA (d := d) b) :=
  (continuous_norm.measurable.pow_const 2).mul (measurable_band b)

/-- Auxiliary: `0 ≤ |η|² 1_{|η| ≤ b} ≤ b²`. -/
theorem symA_nonneg (b : ℝ) (η : Rd d) : 0 ≤ symA b η := by
  unfold symA band; by_cases h : η ∈ Metric.closedBall (0 : Rd d) b <;> simp [h]

/-- Auxiliary: `|η|² 1_{|η| ≤ b} ≤ b²` (bounded, as at main TeX line 3025). -/
theorem abs_symA_le (b : ℝ) (η : Rd d) : |symA b η| ≤ b ^ 2 := by
  rw [abs_of_nonneg (symA_nonneg b η)]
  unfold symA band
  by_cases h : η ∈ Metric.closedBall (0 : Rd d) b
  · simp only [h, Set.indicator_of_mem, mul_one]
    exact pow_le_pow_left₀ (norm_nonneg _) (mem_closedBall_zero_iff.1 h) 2
  · simp [h, sq_nonneg]

/-- The symbol of `A_0 + ρ²`: `ρ² + |η|² 1_{|η| ≤ b}`. -/
def symS (ρ b : ℝ) (η : Rd d) : ℝ := ρ ^ 2 + symA b η

/-- Auxiliary: `symS` is measurable. -/
theorem measurable_symS (ρ b : ℝ) : Measurable (symS (d := d) ρ b) :=
  measurable_const.add (measurable_symA b)

/-- Auxiliary: `ρ² ≤ symS`. -/
theorem sq_le_symS (ρ b : ℝ) (η : Rd d) : ρ ^ 2 ≤ symS ρ b η :=
  le_add_of_nonneg_right (symA_nonneg b η)

/-- Auxiliary: `|symS| ≤ ρ² + b²`. -/
theorem abs_symS_le (ρ b : ℝ) (η : Rd d) : |symS ρ b η| ≤ ρ ^ 2 + b ^ 2 := by
  rw [abs_of_nonneg ((sq_nonneg ρ).trans (sq_le_symS ρ b η)), symS]
  have := (le_abs_self _).trans (abs_symA_le b η)
  linarith

/-- The symbol of `(A_0 + ρ²)^{1/2}`. -/
def symR (ρ b : ℝ) (η : Rd d) : ℝ := Real.sqrt (symS ρ b η)

/-- Auxiliary: `symR` is measurable. -/
theorem measurable_symR (ρ b : ℝ) : Measurable (symR (d := d) ρ b) :=
  (measurable_symS ρ b).sqrt

/-- Auxiliary: `|symR| ≤ √(ρ² + b²)`. -/
theorem abs_symR_le (ρ b : ℝ) (η : Rd d) : |symR ρ b η| ≤ Real.sqrt (ρ ^ 2 + b ^ 2) := by
  rw [symR, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_sqrt ((le_abs_self _).trans (abs_symS_le ρ b η))

/-- The symbol of `(A_0 + ρ²)^{-1/2}`: `(ρ² + |η|² 1_{|η| ≤ b})^{-1/2}`. -/
def symI (ρ b : ℝ) (η : Rd d) : ℝ := 1 / Real.sqrt (symS ρ b η)

/-- Auxiliary: `symI` is measurable. -/
theorem measurable_symI (ρ b : ℝ) : Measurable (symI (d := d) ρ b) :=
  measurable_const.div (measurable_symS ρ b).sqrt

/-- Auxiliary: `|symI| ≤ ρ^{-1}` for `ρ > 0`. -/
theorem abs_symI_le {ρ : ℝ} (hρ : 0 < ρ) (b : ℝ) (η : Rd d) : |symI ρ b η| ≤ ρ⁻¹ := by
  have hs : ρ ≤ Real.sqrt (symS ρ b η) :=
    Real.le_sqrt_of_sq_le (sq_le_symS ρ b η)
  rw [symI, abs_of_nonneg (by positivity), one_div]
  exact inv_anti₀ hρ hs

/-- Auxiliary: on the band the shifted symbol is `ρ² + |η|²`, off it the band kills it:
`(ρ² + |η|² 1_b)^{-1/2} 1_b = 1_b (ρ² + |η|²)^{-1/2}`. -/
theorem symI_mul_band (ρ b : ℝ) (η : Rd d) : symI ρ b η * band b η = band b η * wt ρ η := by
  unfold symI symS symA wt band
  by_cases h : η ∈ Metric.closedBall (0 : Rd d) b <;> simp [h]

end Symbols

/-! ### The cutoff Hilbert space as a type -/

section Hilb

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {m N : ℕ}

/-- The cutoff Hilbert space (the joint range of `P_N`, before the band cutoff) as a type: a
synonym of `FockSp X m N` that carries only its complex Hilbert structure.  Mathlib's `PiLp`
also carries a componentwise real scalar action, which is propositionally but not
definitionally the restriction of the complex one, and blocks the instance
`NonUnitalContinuousFunctionalCalculus ℝ` for its operators; on the synonym the real action
is the restriction of the complex one, as for an abstract Hilbert space. -/
def FockH (X : Type*) [NormedAddCommGroup X] [InnerProductSpace ℂ X] (m N : ℕ) : Type _ :=
  FockSp X m N

instance instNormedAddCommGroupFockH : NormedAddCommGroup (FockH X m N) :=
  inferInstanceAs (NormedAddCommGroup (FockSp X m N))

instance instInnerProductSpaceFockH : InnerProductSpace ℂ (FockH X m N) :=
  inferInstanceAs (InnerProductSpace ℂ (FockSp X m N))

instance instCompleteSpaceFockH [CompleteSpace X] : CompleteSpace (FockH X m N) :=
  inferInstanceAs (CompleteSpace (FockSp X m N))

/-- An operator on `FockSp X m N` read on `FockH X m N` (the identity on the data). -/
def toH (T : FockSp X m N →L[ℂ] FockSp X m N) : FockH X m N →L[ℂ] FockH X m N := T

/-- `toH` is multiplicative. -/
theorem toH_mul (S T : FockSp X m N →L[ℂ] FockSp X m N) : toH (S * T) = toH S * toH T := rfl

/-- `toH 1 = 1`. -/
theorem toH_one : toH (1 : FockSp X m N →L[ℂ] FockSp X m N) = 1 := rfl

/-- `toH` is additive. -/
theorem toH_add (S T : FockSp X m N →L[ℂ] FockSp X m N) : toH (S + T) = toH S + toH T := rfl

/-- `toH` commutes with complex scalars. -/
theorem toH_smul (c : ℂ) (T : FockSp X m N →L[ℂ] FockSp X m N) : toH (c • T) = c • toH T := rfl

/-- `toH` preserves operator norms. -/
theorem norm_toH (T : FockSp X m N →L[ℂ] FockSp X m N) : ‖toH T‖ = ‖T‖ := rfl

variable [CompleteSpace X]

omit [CompleteSpace X] in
/-- `toH` preserves positivity. -/
theorem toH_nonneg {T : FockSp X m N →L[ℂ] FockSp X m N} (h : 0 ≤ T) : 0 ≤ toH T := h

/-- `toH` preserves self-adjointness. -/
theorem toH_isSelfAdjoint {T : FockSp X m N →L[ℂ] FockSp X m N} (h : IsSelfAdjoint T) :
    IsSelfAdjoint (toH T) := h

end Hilb

/-- Auxiliary: `algebraMap ℝ` on operators of a complex Hilbert space is the complex scalar. -/
theorem algebraMap_eq_smul_one {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (r : ℝ) : algebraMap ℝ (H →L[ℂ] H) r = (r : ℂ) • (1 : H →L[ℂ] H) := by
  ext x
  rw [Algebra.algebraMap_eq_smul_one, smul_apply, smul_apply, Complex.coe_smul]

/-! ### The concrete operators and the functional calculus -/

section Model

variable {d m N : ℕ}

/-- The Fourier side `L²(ℝ^d, dη)` of spatial `L²` (K2's model). -/
abbrev L2 (d : ℕ) := Lp ℂ 2 (volume : Measure (Rd d))

/-- The multiplication by `symA b` on `L²(dη)`. -/
def mulA (b : ℝ) : L2 d →L[ℂ] L2 d := mulOp (symA b) (measurable_symA b) (b ^ 2) (abs_symA_le b)

/-- The multiplication by `symS ρ b`. -/
def mulS (ρ b : ℝ) : L2 d →L[ℂ] L2 d :=
  mulOp (symS ρ b) (measurable_symS ρ b) (ρ ^ 2 + b ^ 2) (abs_symS_le ρ b)

/-- The multiplication by `symR ρ b`. -/
def mulR (ρ b : ℝ) : L2 d →L[ℂ] L2 d :=
  mulOp (symR ρ b) (measurable_symR ρ b) _ (abs_symR_le ρ b)

/-- The multiplication by `symI ρ b`, for `ρ > 0`. -/
def mulI {ρ : ℝ} (hρ : 0 < ρ) (b : ℝ) : L2 d →L[ℂ] L2 d :=
  mulOp (symI ρ b) (measurable_symI ρ b) ρ⁻¹ (abs_symI_le hρ b)

/-- **`A_0` on the model** (main TeX lines 2969 and 3025-3026): the diagonal multiplication by
`|η|² 1_{|η| ≤ b}` on the cutoff Hilbert space `FockH (L²(dη)) m N`, which is `-Δ` on the
joint range of `P_N`, `S_b`, and bounded (by `b²`). -/
def opA0 (b : ℝ) : FockH (L2 d) m N →L[ℂ] FockH (L2 d) m N := toH (diagOp (mulA b))

/-- `A_0 ≥ 0`. -/
theorem opA0_nonneg (b : ℝ) : 0 ≤ opA0 (d := d) (m := m) (N := N) b :=
  toH_nonneg (diagOp_nonneg (mulOp_nonneg _ _ _ _ (symA_nonneg b)))

/-- `A_0` is a positive operator. -/
theorem opA0_isPositive (b : ℝ) : (opA0 (d := d) (m := m) (N := N) b).IsPositive :=
  ContinuousLinearMap.nonneg_iff_isPositive.mp (opA0_nonneg b)

/-- `A_ρ = A_0 + ρ² = diag M_{ρ² + |η|² 1_b}` (main TeX line 2753 at the model). -/
theorem shiftOp_eq (ρ b : ℝ) :
    shiftOp (opA0 (d := d) (m := m) (N := N) b) ρ = toH (diagOp (mulS ρ b)) := by
  rw [shiftOp, algebraMap_eq_smul_one, opA0, ← toH_one, ← toH_smul, ← toH_add, ← diagOp_one,
    ← diagOp_smul, ← diagOp_add, mulA, mulS,
    mulOp_add_smul_one _ _ _ _ _ _ (measurable_symS ρ b) _ (abs_symS_le ρ b) fun _ => rfl]

/-- **The CFC square root on the model**: `CFC.sqrt (A_0 + ρ²) = diag M_{√(ρ² + |η|² 1_b)}`,
by uniqueness of the positive square root (`CFC.sqrt_eq_iff`). -/
theorem sqrt_shiftOp_eq (ρ b : ℝ) :
    CFC.sqrt (shiftOp (opA0 (d := d) (m := m) (N := N) b) ρ) = toH (diagOp (mulR ρ b)) := by
  have hS : 0 ≤ shiftOp (opA0 (d := d) (m := m) (N := N) b) ρ :=
    ComplexPhaseScalar.shiftOp_nonneg (opA0_isPositive b) ρ
  have hR : 0 ≤ toH (m := m) (N := N) (diagOp (mulR (d := d) ρ b)) :=
    toH_nonneg (diagOp_nonneg (mulOp_nonneg _ _ _ _ fun _ => Real.sqrt_nonneg _))
  refine (CFC.sqrt_eq_iff _ _ hS hR).2 ?_
  rw [shiftOp_eq, ← toH_mul, ← diagOp_mul, ContinuousLinearMap.mul_def, mulR, mulS,
    mulOp_comp _ _ _ (measurable_symR ρ b) (measurable_symR ρ b) (measurable_symS ρ b) _ _ _
      (abs_symR_le ρ b) (abs_symR_le ρ b) (abs_symS_le ρ b)
      fun η => Real.mul_self_sqrt ((sq_nonneg ρ).trans (sq_le_symS ρ b η))]

/-- Auxiliary: `M_{symR} M_{symI} = 1 = M_{symI} M_{symR}` for `ρ > 0`. -/
theorem mulR_mulI {ρ : ℝ} (hρ : 0 < ρ) (b : ℝ) :
    mulR (d := d) ρ b * mulI hρ b = 1 ∧ mulI (d := d) hρ b * mulR ρ b = 1 := by
  have hpos : ∀ η : Rd d, 0 < Real.sqrt (symS ρ b η) := fun η =>
    Real.sqrt_pos.2 (lt_of_lt_of_le (pow_pos hρ 2) (sq_le_symS ρ b η))
  have h1 : ∀ x, |(fun _ : Rd d => (1 : ℝ)) x| ≤ 1 := fun _ => by simp
  constructor
  · rw [ContinuousLinearMap.mul_def, mulR, mulI, mulOp_comp _ _ _ _ _ measurable_const _ _ 1 _ _ h1
      fun η => by rw [symR, symI, mul_one_div, div_self (hpos η).ne'], mulOp_one]
  · rw [ContinuousLinearMap.mul_def, mulR, mulI, mulOp_comp _ _ _ _ _ measurable_const _ _ 1 _ _ h1
      fun η => by rw [symR, symI, one_div_mul_eq_div, div_self (hpos η).ne'], mulOp_one]

/-- **`A_ρ^{-1/2}` on the model**: for `ρ > 0`,
`invSqrtShift A_0 ρ = diag M_{(ρ² + |η|² 1_b)^{-1/2}}`.  `invSqrtShift` is a `Ring.inverse`;
the square root is a unit with the explicit two-sided inverse `diag M_{symI}` (`hu`), so the
`Ring.inverse` is the genuine inverse (no junk value). -/
theorem invSqrtShift_eq {ρ : ℝ} (hρ : 0 < ρ) (b : ℝ) :
    invSqrtShift (opA0 (d := d) (m := m) (N := N) b) ρ = toH (diagOp (mulI hρ b)) := by
  obtain ⟨h1, h2⟩ := mulR_mulI (d := d) hρ b
  have e1 : toH (m := m) (N := N) (diagOp (mulR (d := d) ρ b)) * toH (diagOp (mulI hρ b)) = 1 := by
    rw [← toH_mul, ← diagOp_mul, h1, diagOp_one, toH_one]
  have e2 : toH (m := m) (N := N) (diagOp (mulI (d := d) hρ b)) * toH (diagOp (mulR ρ b)) = 1 := by
    rw [← toH_mul, ← diagOp_mul, h2, diagOp_one, toH_one]
  have hu : IsUnit (toH (m := m) (N := N) (diagOp (mulR (d := d) ρ b))) := ⟨⟨_, _, e1, e2⟩, rfl⟩
  rw [invSqrtShift, sqrt_shiftOp_eq]
  calc Ring.inverse (toH (diagOp (mulR ρ b)))
      = Ring.inverse (toH (diagOp (mulR ρ b))) * (toH (diagOp (mulR ρ b)) *
          toH (diagOp (mulI hρ b))) := by rw [e1, mul_one]
    _ = toH (diagOp (mulI hρ b)) := by rw [← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]

/-- `M_{symI} S_b = S_b A_ρ^{-1/2}` (`A_ρ^{-1/2} = sqrtResolvent ρ`, K2). -/
theorem mulI_comp_band {ρ : ℝ} (hρ : 0 < ρ) (b : ℝ) :
    mulI (d := d) hρ b ∘L bandProj b = bandProj b ∘L sqrtResolvent ρ hρ :=
  mulOp_comp_comm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (symI_mul_band ρ b)

/-- `S_b M_{symI} = A_ρ^{-1/2} S_b`. -/
theorem band_comp_mulI {ρ : ℝ} (hρ : 0 < ρ) (b : ℝ) :
    bandProj b ∘L mulI (d := d) hρ b = sqrtResolvent ρ hρ ∘L bandProj b :=
  mulOp_comp_comm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fun η => by
    rw [mul_comm, symI_mul_band, mul_comm]

/-- **On the joint range, `invSqrtShift A_0 ρ` is `A_ρ^{-1/2} = (ρ² - Δ)^{-1/2}`**:
`invSqrtShift A_0 ρ · diag S_b = diag A_ρ^{-1/2} · diag S_b`. -/
theorem invSqrtShift_band {ρ : ℝ} (hρ : 0 < ρ) (b : ℝ) :
    invSqrtShift (opA0 (d := d) (m := m) (N := N) b) ρ * toH (diagOp (bandProj b)) =
      toH (diagOp (sqrtResolvent ρ hρ)) * toH (diagOp (bandProj b)) := by
  rw [invSqrtShift_eq hρ, ← toH_mul, ← toH_mul, ← diagOp_mul, ← diagOp_mul,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def, mulI_comp_band,
    ← FockColumnBound.bandProj_comm hρ b]

variable {ν : Measure (Rd d)}

/-- **`B_{N,m,b}` on the model** (main TeX lines 2968-2970): the truncated field
`P_N S_b (∑_{i ≤ m} g_i M_{e_i}) S_b P_N` with K2's Fourier-side modes `M_{e_i}` of an
orthonormal family `ψ` in `L²(ν)`.  It does not depend on `ρ`. -/
def fieldB (b : ℝ) (hfin : IsFiniteMeasure ν) (ψ : Fin m → Lp ℂ 2 ν) (hψ : Orthonormal ℂ ψ) :
    FockH (L2 d) m N →L[ℂ] FockH (L2 d) m N :=
  toH (fockOp fun i => bandProj b ∘L modes hfin ψ hψ i ∘L bandProj b)

/-- `B_{N,m,b}` lives on the joint range: `diag S_b · B = B = B · diag S_b`. -/
theorem fieldB_band (b : ℝ) (hfin : IsFiniteMeasure ν) (ψ : Fin m → Lp ℂ 2 ν)
    (hψ : Orthonormal ℂ ψ) :
    toH (diagOp (bandProj b)) * fieldB (N := N) b hfin ψ hψ = fieldB b hfin ψ hψ ∧
      fieldB (N := N) b hfin ψ hψ * toH (diagOp (bandProj b)) = fieldB b hfin ψ hψ := by
  have hP : ∀ g, bandProj (d := d) b (bandProj b g) = bandProj b g := fun g =>
    DFunLike.congr_fun (FockColumnBound.bandProj_idem (d := d) b) g
  constructor
  · have h := diagOp_fockOp_diagOp (N := N) (bandProj (d := d) b) 1
      (fun i => bandProj b ∘L modes hfin ψ hψ i ∘L bandProj b)
    rw [diagOp_one, mul_one] at h
    rw [fieldB, ← toH_mul, h]
    congr 2
    funext i
    refine ContinuousLinearMap.ext fun f => ?_
    simp only [ContinuousLinearMap.comp_apply, one_apply_eq_self, hP]
  · have h := diagOp_fockOp_diagOp (N := N) 1 (bandProj (d := d) b)
      (fun i => bandProj b ∘L modes hfin ψ hψ i ∘L bandProj b)
    rw [diagOp_one, one_mul] at h
    rw [fieldB, ← toH_mul, h]
    congr 2
    funext i
    refine ContinuousLinearMap.ext fun f => ?_
    simp only [ContinuousLinearMap.comp_apply, one_apply_eq_self, hP]

/-- `B_{N,m,b}` is self-adjoint for real modes on an even `ν` (main TeX line 2971). -/
theorem fieldB_isSelfAdjoint (b : ℝ) (hfin : IsFiniteMeasure ν)
    (heven : ν.map (fun x => -x) = ν) (ψ : Fin m → Lp ℂ 2 ν) (hψ : Orthonormal ℂ ψ)
    (hreal : ∀ i, ∀ᵐ ξ ∂ν, ψ i (-ξ) = conj (ψ i ξ)) :
    IsSelfAdjoint (fieldB (N := N) b hfin ψ hψ) :=
  toH_isSelfAdjoint (fockOp_isSelfAdjoint _ fun i => FockForm.compress_symm
    (FockForm.symm_of_isSelfAdjoint (FockColumnBound.bandProj_isSelfAdjoint b))
    (FockForm.symm_of_isSelfAdjoint
      (FockColumnBound.modeOp_isSelfAdjoint hfin heven (ψ i) (hψ.1 i) (hreal i))))

/-- **The sandwich on the model**: `invSqrtShift A_0 ρ · B · invSqrtShift A_0 ρ` is the
truncated field of `S_b H_i S_b`, `H_i = A_ρ^{-1/2} M_{e_i} A_ρ^{-1/2}` (K2's operators). -/
theorem sandwich_eq {ρ : ℝ} (hρ : 0 < ρ) (b : ℝ) (hfin : IsFiniteMeasure ν)
    (ψ : Fin m → Lp ℂ 2 ν) (hψ : Orthonormal ℂ ψ) :
    invSqrtShift (opA0 (d := d) (m := m) (N := N) b) ρ * fieldB b hfin ψ hψ *
        invSqrtShift (opA0 b) ρ =
      toH (fockOp fun i => bandProj b ∘L
        (sqrtResolvent ρ hρ ∘L modes hfin ψ hψ i ∘L sqrtResolvent ρ hρ) ∘L bandProj b) := by
  rw [invSqrtShift_eq hρ, fieldB, ← toH_mul, ← toH_mul, diagOp_fockOp_diagOp]
  congr 2
  funext i
  refine ContinuousLinearMap.ext fun f => ?_
  have h1 : ∀ g, mulI (d := d) hρ b (bandProj b g) = bandProj b (sqrtResolvent ρ hρ g) :=
    fun g => DFunLike.congr_fun (mulI_comp_band hρ b) g
  have h2 : ∀ g, bandProj b (mulI (d := d) hρ b g) = sqrtResolvent ρ hρ (bandProj b g) :=
    fun g => DFunLike.congr_fun (band_comp_mulI hρ b) g
  simp only [ContinuousLinearMap.comp_apply]
  rw [h1, h2]

end Model

/-! ### `E:fock-sandwich` on the model -/

section Sandwich

variable {m : ℕ}

/-- **`E:fock-sandwich` on the model** (main TeX lines 2972-2976, proof 2979-3028): under the
class of `S:static-phase` (`PhaseCovariance`), for `ε > 0`, an orthonormal family
`ψ_1, …, ψ_m` of real modes in `L²(μ_ε)`, a band `b` and a degree `N`, on the cutoff Hilbert
space `FockH (L²(dη)) m N`: `A_0 = opA0 b ≥ 0`, `B = fieldB b … ψ` is self-adjoint, and
`FockSandwich A_0 B d_N (α/2)`, i.e. `‖A_ρ^{-1/2} B A_ρ^{-1/2}‖ ≤ d_N ρ^{α/2-2}` for every
`ρ > 0`, with `A_ρ^{-1/2} = invSqrtShift A_0 ρ`, `d_N = 2√(N+1)√R_α`. -/
theorem fockSandwich_model {alpha ε : ℝ} {Γ μ : Measure (Rd 3)}
    (hPC : PhaseCovariance alpha Γ μ) (hε : 0 < ε) (ψ : Fin m → Lp ℂ 2 (nuEps μ ε))
    (hψ : Orthonormal ℂ ψ) (hreal : ∀ i, ∀ᵐ ξ ∂(nuEps μ ε), ψ i (-ξ) = conj (ψ i ξ))
    (N : ℕ) (b : ℝ) :
    (opA0 (d := 3) (m := m) (N := N) b).IsPositive ∧
      IsSelfAdjoint (fieldB (N := N) b (nuEps_finite hPC.μ_tempered hε) ψ hψ) ∧
      FockSandwich (opA0 (d := 3) (m := m) (N := N) b)
        (fieldB b (nuEps_finite hPC.μ_tempered hε) ψ hψ) (fockD N (ralpha μ alpha))
        (alpha / 2) := by
  have := hPC.μ_radon
  refine ⟨opA0_isPositive b, fieldB_isSelfAdjoint b _ (nuEps_even hPC.μ_even ε) ψ hψ hreal,
    fun ρ hρ => ?_⟩
  have hR0 : 0 ≤ ralpha μ alpha := IntervalScalar.ralpha_nonneg μ hPC.alpha_pos hPC.alpha_lt_two
  obtain ⟨hHs, hcol⟩ := FockColumnBound.fock_column_completed hPC rfl hε hρ ψ hψ hreal
  have hc0 : 0 ≤ ralpha μ alpha * ρ ^ (alpha - 4) := mul_nonneg hR0 (Real.rpow_nonneg hρ.le _)
  have hPs := FockForm.symm_of_isSelfAdjoint (FockColumnBound.bandProj_isSelfAdjoint (d := 3) b)
  have hPP : ∀ u, bandProj (d := 3) b (bandProj b u) = bandProj b u := fun u =>
    DFunLike.congr_fun (FockColumnBound.bandProj_idem (d := 3) b) u
  have hcomp := FockForm.fockColumn_compress hc0 hcol hPs hPP
  rw [sandwich_eq hρ, norm_toH, ← FockForm.fock_const_eq N hR0 hρ]
  exact fockOp_norm_le _ (fun i => FockForm.compress_symm hPs
    (FockForm.symm_of_isSelfAdjoint (hHs i))) hc0 hcomp

/-- **`L:fock-form` in operator form** (main TeX lines 2960-2977, proof 2979-3028), with the
manuscript's hypotheses: the class of `S:static-phase` (lines 2490-2502), `R = R_α`
(`hRdef`), `ε > 0`, finitely many real orthonormal modes `ψ_i ∈ L²(μ_ε)` (the TeX's
orthonormal basis restricted to `m` modes), a band `b`, a degree `N`.  On the model of the
cutoff Hilbert space (`FockH (L²(dη)) m N`, Fourier side):
(i) `A_0 ≥ 0` and `B_{N,m,b}` is self-adjoint ("bounded selfadjoint operators", line 2971);
(ii) `B` lives on the joint range of `P_N`, `S_b`: `S_b B = B = B S_b`;
(iii) on that range `invSqrtShift A_0 ρ` is `A_ρ^{-1/2} = (ρ² - Δ)^{-1/2}`;
(iv) `E:fock-sandwich`: `FockSandwich A_0 B d_N (α/2)`, with `d_N` independent of `ε, m, b`.
Used from `hPC`: `0 < α < 2`, `μ` locally finite, even, tempered, the spectral relation and
the scaling (through `fock_column_completed`); carried and unused: `Γ_radon`, `Γ_even`,
`Γ_tempered`, `Γ_posdef`.  `hRdef` is used (to identify `R` with `ralpha μ α`). -/
theorem fock_sandwich_paper {alpha R ε : ℝ} {Γ μ : Measure (Rd 3)}
    (hPC : PhaseCovariance alpha Γ μ)
    (hRdef : R = alpha * π * (μ (Metric.ball 0 1)).toReal / (2 * Real.sin (π * alpha / 2)))
    (hε : 0 < ε) (ψ : Fin m → Lp ℂ 2 (nuEps μ ε)) (hψ : Orthonormal ℂ ψ)
    (hreal : ∀ i, ∀ᵐ ξ ∂(nuEps μ ε), ψ i (-ξ) = conj (ψ i ξ)) (N : ℕ) (b : ℝ) :
    let A0 := opA0 (d := 3) (m := m) (N := N) b
    let B := fieldB (N := N) b (nuEps_finite hPC.μ_tempered hε) ψ hψ
    let P := toH (m := m) (N := N) (diagOp (bandProj (d := 3) b))
    A0.IsPositive ∧ IsSelfAdjoint B ∧ (P * B = B ∧ B * P = B) ∧
      (∀ ρ (hρ : 0 < ρ), invSqrtShift A0 ρ * P = toH (diagOp (sqrtResolvent ρ hρ)) * P) ∧
      FockSandwich A0 B (fockD N R) (alpha / 2) := by
  intro A0 B P
  have hR : R = ralpha μ alpha := hRdef
  subst hR
  obtain ⟨h1, h2, h3⟩ := fockSandwich_model hPC hε ψ hψ hreal N b
  exact ⟨h1, h2, fieldB_band b _ ψ hψ, fun ρ hρ => invSqrtShift_band hρ b, h3⟩

end Sandwich

/-! ### The re-issued wrappers with `FockSandwich` discharged -/

/-- **`E:all-static-phase-orders` with `FockSandwich` discharged on the model** (main TeX
lines 3098-3105, proof 3127-3192): `StaticInteractionCompleted.static_phase_all_orders_cp` at
`R = R_α`, with the cutoff Hilbert spaces `Hs m b = FockH (L²(dη)) m n` (Hermite degree `n`),
`A_0 = opA0 b`, `B = fieldB b … (ψ m)` for each Gaussian cutoff `m` and band `b ∈ ℕ`, and
`FockSandwich`, `A_0 ≥ 0`, `B = B^*` proved (`fockSandwich_model`).  Still supplied:
`CPInputs`, `PropagatorBlock` (at these operators), and `hentire`, `hz`, `hv`, `hband`,
`hgauss` of `StaticPhaseCauchy.static_phase_all_orders_step`.  Used from `hcov`: as in
`fockSandwich_model`. -/
theorem static_phase_all_orders_model (Ec : ℕ → ℕ → Type*) [∀ m b, NormedAddCommGroup (Ec m b)]
    [∀ m b, NormedSpace ℂ (Ec m b)] [∀ m b, CompleteSpace (Ec m b)]
    {alpha ε h z N1 : ℝ} {Γ μ : Measure (Rd 3)} (hcov : PhaseCovariance alpha Γ μ) (hε : 0 < ε)
    (ψ : ∀ m, Fin m → Lp ℂ 2 (nuEps μ ε)) (hψ : ∀ m, Orthonormal ℂ (ψ m))
    (hreal : ∀ m i, ∀ᵐ ξ ∂(nuEps μ ε), ψ m i (-ξ) = conj (ψ m i ξ))
    (F : ∀ m b, ℂ → Ec m b →L[ℂ] Ec m b) (v : ∀ m b, Ec m b) (zc : ℕ → ℕ → ℝ) (zm : ℕ → ℝ)
    {n : ℕ} (hn : 1 ≤ n) (hh : 0 < h)
    (Cop Fop Hop Q' : ∀ m (_ : ℕ), ℂ → FockH (L2 3) m n →L[ℂ] FockH (L2 3) m n)
    (J : ∀ m (_ : ℕ), ℂ → ℝ → FockH (L2 3) m n →L[ℂ] FockH (L2 3) m n)
    (hcp : ∀ m (b : ℕ), CPInputs (opA0 (b : ℝ)) (fieldB (b : ℝ) (nuEps_finite hcov.μ_tempered hε)
      (ψ m) (hψ m)) n alpha h (ralpha μ alpha) (Cop m b) (Fop m b) (Hop m b) (Q' m b) (J m b))
    (hprop : ∀ m b z, InDisc n alpha h (ralpha μ alpha) z →
      PropagatorBlock (F m b z) (Cop m b z) (Fop m b z) (Hop m b z) (Q' m b z))
    (hentire : ∀ m b, Differentiable ℂ (F m b))
    (hz : ∀ m b, zc m b ≤ n * ‖taylorCoeff (F m b) n (v m b)‖) (hv : ∀ m b, ‖v m b‖ ≤ N1)
    (hband : ∀ m, Tendsto (zc m) atTop (𝓝 (zm m))) (hgauss : Tendsto zm atTop (𝓝 z)) :
    z ≤ (allOrdersA alpha * √(ralpha μ alpha)) ^ n * h ^ ((4 - alpha) * n / 2) /
      (n ! : ℝ) ^ ((3 - alpha) / 2) * N1 :=
  StaticInteractionCompleted.static_phase_all_orders_cp Ec (fun m _ => FockH (L2 3) m n) F v zc
    zm hn hcov.alpha_pos hcov.alpha_lt_two hh (fun _ b => opA0 (b : ℝ))
    (fun m b => fieldB (b : ℝ) (nuEps_finite hcov.μ_tempered hε) (ψ m) (hψ m))
    (fun m b => (fockSandwich_model hcov hε (ψ m) (hψ m) (hreal m) n b).1)
    (fun m b => (fockSandwich_model hcov hε (ψ m) (hψ m) (hreal m) n b).2.1)
    (fun m b => (fockSandwich_model hcov hε (ψ m) (hψ m) (hreal m) n b).2.2)
    Cop Fop Hop Q' J hcp hprop hentire hz hv hband hgauss

/-- **`C:static-interaction`, `E:static-interaction`, with `FockSandwich` discharged on the
model** (main TeX lines 3216-3240, proof 3264-3311; orders from lines 3098-3192).
`StaticInteractionCompleted.static_interaction_completed_paper` with, for every order `n`,
Gaussian cutoff `m` and band `b ∈ ℕ`, the cutoff Hilbert space `FockH (L²(dη)) m n`,
`A_0 = opA0 b`, `B = fieldB b … (ψ m)`, and the inputs `FockSandwich`, `A_0 ≥ 0`, `B = B^*`
proved (`fockSandwich_model`).  Under `PhaseCovariance α Γ μ`, `λ, h > 0`, `λh ≤ 1`:
`∑ σ^n Z_n` converges, `I_σ^ε(h)(f,g) = T (∑ σ^n Z_n) = ∑ σ^n T Z_n`, and
`‖I_σ^ε(h)(f,g)‖² ≤ (1 + 𝓔(h,σ,λ)) ‖(f,g)‖²`.  Still supplied (narrower than the TeX):
`CPInputs`, `PropagatorBlock`, entireness, the coefficient identification and cutoff
removals (`hz`, `hv`, `hband`, `hgauss`), the free estimate and group law (`hT`, `hS`, `hTS`,
`hZ0`), the norm comparisons (`hcmp`, `hN1`), Gaussian parity (`hodd`) and the first-variance
bounds (`hborn`, `hmean`).  Used from `hcov`: `0 < α < 2`, `μ` locally finite, even,
tempered, spectral, scaling; carried and unused: `Γ_radon`, `Γ_even`, `Γ_tempered`,
`Γ_posdef` (`D_Γ ≥ 0` needs only `α < 2`). -/
theorem static_interaction_model_paper {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (Ec : ℕ → ℕ → ℕ → Type*) [∀ n m b, NormedAddCommGroup (Ec n m b)]
    [∀ n m b, NormedSpace ℂ (Ec n m b)] [∀ n m b, CompleteSpace (Ec n m b)]
    {alpha ε h lam σ N1 : ℝ} {Γ μ : Measure (Rd 3)} (hcov : PhaseCovariance alpha Γ μ)
    (hε : 0 < ε) (ψ : ∀ m, Fin m → Lp ℂ 2 (nuEps μ ε)) (hψ : ∀ m, Orthonormal ℂ (ψ m))
    (hreal : ∀ m i, ∀ᵐ ξ ∂(nuEps μ ε), ψ m i (-ξ) = conj (ψ m i ξ))
    (hlam : 0 < lam) (hh : 0 < h) (hlh : lam * h ≤ 1)
    (T S : E →L[ℝ] E) (f0 : E) (Z : ℕ → E) (zn : ℕ → ℝ)
    (hT : ‖T‖ ≤ √(Real.exp 1)) (hS : ‖S‖ ≤ √(Real.exp 1)) (hTS : ∀ x, T (S x) = x)
    (hZ0 : Z 0 = S f0) (hcmp : ∀ n, 1 ≤ n → ‖Z n‖ ≤ (lam * h)⁻¹ * zn n) (hN1 : N1 ≤ ‖f0‖)
    (F : ∀ n m b, ℂ → Ec n m b →L[ℂ] Ec n m b) (v : ∀ n m b, Ec n m b)
    (zc : ℕ → ℕ → ℕ → ℝ) (zm : ℕ → ℕ → ℝ)
    (Cop Fop Hop Q' : ∀ n m (_ : ℕ), ℂ → FockH (L2 3) m n →L[ℂ] FockH (L2 3) m n)
    (J : ∀ n m (_ : ℕ), ℂ → ℝ → FockH (L2 3) m n →L[ℂ] FockH (L2 3) m n)
    (hcp : ∀ n, 1 ≤ n → ∀ m (b : ℕ), CPInputs (opA0 (b : ℝ))
      (fieldB (b : ℝ) (nuEps_finite hcov.μ_tempered hε) (ψ m) (hψ m)) n alpha h
      (ralpha μ alpha) (Cop n m b) (Fop n m b) (Hop n m b) (Q' n m b) (J n m b))
    (hprop : ∀ n, 1 ≤ n → ∀ m b z, InDisc n alpha h (ralpha μ alpha) z →
      PropagatorBlock (F n m b z) (Cop n m b z) (Fop n m b z) (Hop n m b z) (Q' n m b z))
    (hentire : ∀ n, 1 ≤ n → ∀ m b, Differentiable ℂ (F n m b))
    (hz : ∀ n, 1 ≤ n → ∀ m b, zc n m b ≤ n * ‖taylorCoeff (F n m b) n (v n m b)‖)
    (hv : ∀ n, 1 ≤ n → ∀ m b, ‖v n m b‖ ≤ N1)
    (hband : ∀ n, 1 ≤ n → ∀ m, Tendsto (zc n m) atTop (𝓝 (zm n m)))
    (hgauss : ∀ n, 1 ≤ n → Tendsto (zm n) atTop (𝓝 (zn n)))
    (hodd : ∀ r s, Odd (r + s) → inner ℝ (T (Z r)) (T (Z s)) = 0)
    (hborn : ‖T (Z 1)‖ ^ 2 ≤ Real.exp 1 * (ralpha μ alpha * h ^ 2 * lam ^ (alpha - 2) *
      (1 + lam ^ 2 * h ^ 2) ^ 2 * ‖f0‖ ^ 2))
    (hmean : |inner ℝ f0 (T (Z 2))| ≤ ‖f0‖ * (√(Real.exp 1) * (dGam Γ alpha *
      (1 + lam ^ 2 * h ^ 2) * h ^ (3 - alpha) / (lam * (2 - alpha) * (3 - alpha)) * ‖f0‖))) :
    Summable (fun n => σ ^ n • Z n) ∧
      T (∑' n, σ ^ n • Z n) = ∑' n, σ ^ n • T (Z n) ∧
      ‖T (∑' n, σ ^ n • Z n)‖ ^ 2 ≤
        (1 + staticE alpha (allOrdersA alpha) (ralpha μ alpha) (dGam Γ alpha) h σ lam) *
          ‖f0‖ ^ 2 :=
  StaticInteractionCompleted.static_interaction_completed_paper Ec
    (fun n m _ => FockH (L2 3) m n) hcov hlam hh hlh T S f0 Z zn hT hS hTS hZ0 hcmp hN1 F v zc
    zm (fun _ _ b => opA0 (b : ℝ))
    (fun _ m b => fieldB (b : ℝ) (nuEps_finite hcov.μ_tempered hε) (ψ m) (hψ m))
    (fun n m b => (fockSandwich_model hcov hε (ψ m) (hψ m) (hreal m) n b).1)
    (fun n m b => (fockSandwich_model hcov hε (ψ m) (hψ m) (hreal m) n b).2.1)
    (fun n _ m b => (fockSandwich_model hcov hε (ψ m) (hψ m) (hreal m) n b).2.2)
    Cop Fop Hop Q' J hcp hprop hentire hz hv hband hgauss hodd hborn hmean

end StratonovichHAMSecondMoment.FockSandwichModel
