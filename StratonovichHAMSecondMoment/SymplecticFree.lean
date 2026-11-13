module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

`L:symplectic-free` (Free wave form and compact Young baseline) of
`notes/integrated_symplectic_phase.tex` (revision a284420; statement lines 30-60,
proof lines 62-133): the abstract core (wave L8, item L8-g).  All line numbers below
refer to that file at a284420.

Formalized:
* Per-frequency free matrix (proof lines 70-86).  `freeMatrix t k br` is the TeX's
  `W_t(ξ)` with `k = |ξ|`, `br = ⟨ξ⟩`, and the continuous sine quotient
  `sineQuotient t k = t·sinc(tk)` (equal to `sin(tk)/k` for `k ≠ 0` and to `t` at
  `k = 0`); `freeMatrixAt t ξ` sets `k = ‖ξ‖`, `br = √(1+‖ξ‖²)`.  Proved:
  `freeMatrix_eq_forward` (for `k ≠ 0`, `br ≠ 0` it is the B22 matrix
  `StratonovichHAMAudit.DimensionalMatrix.forward (cos tk) (sin tk) (k/br)`),
  `freeMatrixAt_zero` (the matrix `(1 t; 0 1)` at `ξ = 0`, line 78),
  `continuous_freeMatrix` (continuity in `k`), `det_freeMatrix` (determinant one,
  lines 80-81), `freeMatrix_symplectic`/`freeMatrixAt_symplectic`
  (`W_tᵀ J_symp W_t = J_symp` at every frequency, zero included),
  `freeMatrix_preserves_omega2`, the per-frequency group law `freeMatrix_mul` and the
  reversal identity `reversal_freeMatrix` (`R W_t R = W_{-t}`, lines 120-121).
* Force skewness (statement lines 40-41, proof lines 88-91).  Abstract form
  `omega_force_skew` (for `ω(z,w) = P(z₁,w₂) - P(w₁,z₂)` and `B(u,v) = (0,Mu)` with
  `P(f,Mu) = P(u,Mf)`); `L²` form `omegaL2_force_skew`; integrability of the
  cancellation integrand `integrable_mul_force` (`u, f ∈ L²`, `b` bounded).
* Compactness: `isCompactOperator_of_tendsto` (closedness of the compact ideal, lines
  98-99, via Mathlib's `isClosed_setOfPred_isCompactOperator`),
  `isCompactOperator_youngSum` (each left Young sum is compact, lines 94-98),
  `isCompactOperator_orderedProd_sub` (telescoping, lines 125-128).
* Compact perturbations (lines 103-119): `tendsto_compact_of_weaklyNull` (a compact
  operator maps a bounded weakly null family, along any filter, to a norm-null one)
  and `norm_le_norm_add_compact` (`‖S‖ ≤ ‖S + K‖` for compact `K` when `S` commutes
  with isometries `τ_i` that are weakly null on every vector along a nontrivial
  filter); `norm_le_of_sub_compact`.
* `one_le_norm_of_reversal` and `FreeWaveData.one_le_norm`: `‖S_E(h)‖ ≥ 1` from the
  group law and the isometric reversal (lines 120-122), for `E ≠ 0`.
* General forms `compact_young_baseline`, `compact_product_baseline`, and the
  exact-hypothesis wrappers `symplectic_compact_young_baseline_paper`
  (`E:symplectic-compact-young-baseline`, lines 45-49),
  `symplectic_compact_product_baseline_paper`
  (`E:symplectic-compact-product-baseline`, lines 53-58), `symplectic_force_skew_paper`
  (lines 40-41) and `symplectic_free_paper` (their conjunction with the per-frequency
  identity).

Supplied inputs (named; not formalized):
* `FreeWaveData d E` (D8): the space `E = H^{1/2} × H^{-1/2}` is an abstract real
  Hilbert space; the structure carries the free group `S_E` (`S_E(0) = I`, group
  law), the velocity reversal `𝓡` (isometric, `S_E(-h) = 𝓡 S_E(h) 𝓡`) and the
  translations `τ_y`, `y ∈ ℝ^d` (isometric, commuting with every `S_E(h)`,
  `⟨τ_y z, w⟩_E → 0` as `|y| → ∞`).  Each field is a property that lines 103-122 state
  for the concrete objects (the weak nullity is proved there by a Riemann-Lebesgue
  argument, lines 105-110; the reversal identity from the free Fourier matrix, whose
  per-frequency form is `reversal_freeMatrix`; the group law per frequency is
  `freeMatrix_mul`).
* `LeftYoungSumsConverge X U s t` (D7; `P:constant-young-linear` on `𝓛(E)`, lines
  91-98): along some nontrivial filter of partitions of `[s,t]` the left Young sums
  converge in operator norm to `U(t,s) - I`.  The TeX's convergence as the mesh tends
  to zero implies it, so it is no stronger than its source.

Implicit hypotheses made explicit: `E ≠ 0` (`Nontrivial E`; on the zero space every
operator has norm `0` and `‖S_E(h)‖ ≥ 1` fails); `d ≥ 1` (from `H:homog`'s
`d ∈ {1,2,3}`; it makes the cocompact filter of `ℝ^d` nontrivial); the partition
points lie in `[s,t]`.

Narrower than the TeX: the operator `J_E`, the identity `ω = ⟨·, J_E ·⟩_E` with its
duality form (lines 32-39, 63-68) and the preservation of `ω` by `S_E` on all of `E`
(the Fourier integration of the per-frequency identity, lines 82-86) are not
formalized; the force claim is at the `L²` level, and the estimate
`‖bu‖_{H^{-1/2}} ≤ ‖b‖_∞‖u‖_{H^{1/2}}` (line 88) is not formalized.  The Young
evolution is not constructed: `U` is any operator family whose left Young sums
converge (the supplied input).  The wrappers state the norm bounds and compactness
claims exactly as displayed.

Proof route.  As in the TeX, except: the compact-maps-weakly-null step (lines 110-112)
is proved along an arbitrary filter through cluster points in the compact closure of
the image of a ball and the adjoint (not by subsequences), and the norm bound
(lines 114-119) is proved directly for every `z` by a limit along the filter; the
per-frequency symplecticity is proved through the auxiliary identity
`Mᵀ J_symp M = (det M) J_symp` for every `2 × 2` matrix.  Helpers labelled auxiliary
serve only this route.
-/

public import Mathlib
public import StratonovichHAMAudit.DimensionalMatrix
public import StratonovichHAMSecondMoment.HomogHypothesis

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace StratonovichHAMSecondMoment.SymplecticFree

open Filter Topology Matrix
open scoped NNReal

/-! ### Per-frequency free matrix -/

/-- The symplectic matrix `J_symp`, `J_symp(q,p) = (p,-q)` (TeX line 64). -/
def Jsymp : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

/-- The per-frequency symplectic form `ω₂(z,w) = z ⬝ J_symp w = z₀w₁ - z₁w₀`
(balanced coordinates `z = (q,p)`). -/
def omega2 (z w : Fin 2 → ℝ) : ℝ := z ⬝ᵥ (Jsymp *ᵥ w)

/-- Auxiliary: the coordinate form of `ω₂`. -/
theorem omega2_eq (z w : Fin 2 → ℝ) : omega2 z w = z 0 * w 1 - z 1 * w 0 := by
  simp [omega2, Jsymp, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- Auxiliary (Lean route): for every real `2 × 2` matrix,
`Mᵀ J_symp M = (det M) J_symp`. -/
theorem transpose_mul_Jsymp_mul (M : Matrix (Fin 2) (Fin 2) ℝ) :
    Mᵀ * Jsymp * M = M.det • Jsymp := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Jsymp, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

/-- Auxiliary (Lean route): `ω₂(Mz, Mw) = (det M) ω₂(z,w)`. -/
theorem omega2_mulVec (M : Matrix (Fin 2) (Fin 2) ℝ) (z w : Fin 2 → ℝ) :
    omega2 (M *ᵥ z) (M *ᵥ w) = M.det * omega2 z w := by
  simp only [omega2_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two]
  ring

/-- The continuous sine quotient `t ↦ sin(tk)/k`, with value `t` at `k = 0`:
`sineQuotient t k = t · sinc(tk)`. -/
def sineQuotient (t k : ℝ) : ℝ := t * Real.sinc (t * k)

/-- Auxiliary: `sineQuotient t k = sin(tk)/k` for `k ≠ 0`. -/
theorem sineQuotient_of_ne_zero (t : ℝ) {k : ℝ} (hk : k ≠ 0) :
    sineQuotient t k = Real.sin (t * k) / k := by
  unfold sineQuotient
  by_cases ht : t = 0
  · simp [ht]
  · rw [Real.sinc_of_ne_zero (mul_ne_zero ht hk)]
    field_simp

/-- Auxiliary: `sineQuotient t 0 = t`. -/
theorem sineQuotient_zero (t : ℝ) : sineQuotient t 0 = t := by
  simp [sineQuotient]

/-- Auxiliary: `sineQuotient t k · k = sin(tk)`, every `k`. -/
theorem sineQuotient_mul (t k : ℝ) : sineQuotient t k * k = Real.sin (t * k) := by
  by_cases hk : k = 0
  · simp [hk]
  · rw [sineQuotient_of_ne_zero t hk]
    field_simp

/-- The sine quotient is continuous in `k` (the "continuous sine quotient", line 79). -/
theorem continuous_sineQuotient (t : ℝ) : Continuous (fun k => sineQuotient t k) := by
  unfold sineQuotient
  fun_prop

/-- Auxiliary: `sineQuotient (-t) k = -sineQuotient t k`. -/
theorem sineQuotient_neg (t k : ℝ) : sineQuotient (-t) k = -sineQuotient t k := by
  simp [sineQuotient, neg_mul, Real.sinc_neg]

/-- The free matrix in balanced Fourier coordinates (TeX lines 70-77), with
frequency modulus `k = |ξ|` and weight `br = ⟨ξ⟩`; the `(0,1)` entry uses
the continuous sine quotient, so the matrix at `k = 0` is the TeX's limit. -/
def freeMatrix (t k br : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos (t * k), br * sineQuotient t k; -(k * Real.sin (t * k)) / br, Real.cos (t * k)]

/-- The free matrix at the frequency `ξ ∈ ℝ^d`: `k = |ξ|`, `⟨ξ⟩ = √(1+|ξ|²)`. -/
def freeMatrixAt {d : ℕ} (t : ℝ) (ξ : EuclideanSpace ℝ (Fin d)) : Matrix (Fin 2) (Fin 2) ℝ :=
  freeMatrix t ‖ξ‖ (Real.sqrt (1 + ‖ξ‖ ^ 2))

/-- Auxiliary: `⟨ξ⟩ = √(1+|ξ|²) > 0`. -/
theorem bracket_pos {d : ℕ} (ξ : EuclideanSpace ℝ (Fin d)) : 0 < Real.sqrt (1 + ‖ξ‖ ^ 2) :=
  Real.sqrt_pos.2 (by positivity)

/-- At nonzero frequency the free matrix is the B22 matrix
`DimensionalMatrix.forward (cos tk) (sin tk) (k/⟨ξ⟩)`. -/
theorem freeMatrix_eq_forward (t : ℝ) {k br : ℝ} (hk : k ≠ 0) (hbr : br ≠ 0) :
    freeMatrix t k br =
      StratonovichHAMAudit.DimensionalMatrix.forward (Real.cos (t * k)) (Real.sin (t * k))
        (k / br) := by
  rw [freeMatrix, StratonovichHAMAudit.DimensionalMatrix.forward,
    sineQuotient_of_ne_zero t hk]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp

/-- At frequency zero the free matrix is `!![1, br t; 0, 1]` (TeX line 78 with `⟨0⟩ = 1`). -/
theorem freeMatrix_zero_freq (t br : ℝ) : freeMatrix t 0 br = !![1, br * t; 0, 1] := by
  simp [freeMatrix, sineQuotient_zero]

/-- `W_t(0) = (1 t; 0 1)` (TeX line 78). -/
theorem freeMatrixAt_zero {d : ℕ} (t : ℝ) :
    freeMatrixAt t (0 : EuclideanSpace ℝ (Fin d)) = !![1, t; 0, 1] := by
  simp [freeMatrixAt, freeMatrix_zero_freq]

/-- The entries of the free matrix are continuous in the frequency modulus `k`
(fixed `t` and `br`), the frequency-zero value included. -/
theorem continuous_freeMatrix (t br : ℝ) :
    Continuous (fun k => freeMatrix t k br) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp [freeMatrix]
  · fun_prop
  · exact continuous_const.mul (continuous_sineQuotient t)
  · fun_prop
  · fun_prop

/-- Determinant one at every frequency, also at zero (TeX lines 80-81). -/
theorem det_freeMatrix (t k : ℝ) {br : ℝ} (hbr : br ≠ 0) : (freeMatrix t k br).det = 1 := by
  rw [Matrix.det_fin_two]
  simp only [freeMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  have h1 := sineQuotient_mul t k
  have h2 : br * sineQuotient t k * (-(k * Real.sin (t * k)) / br)
      = -(sineQuotient t k * k) * Real.sin (t * k) := by
    field_simp
  rw [h2, h1]
  nlinarith [Real.sin_sq_add_cos_sq (t * k)]

/-- Per-frequency symplecticity `W_tᵀ J_symp W_t = J_symp` (TeX lines 79-81), at
every frequency modulus `k`, zero included, for every weight `br ≠ 0`. -/
theorem freeMatrix_symplectic (t k : ℝ) {br : ℝ} (hbr : br ≠ 0) :
    (freeMatrix t k br)ᵀ * Jsymp * freeMatrix t k br = Jsymp := by
  rw [transpose_mul_Jsymp_mul, det_freeMatrix t k hbr, one_smul]

/-- `W_t(ξ)ᵀ J_symp W_t(ξ) = J_symp` at every `ξ ∈ ℝ^d`, `ξ = 0` included. -/
theorem freeMatrixAt_symplectic {d : ℕ} (t : ℝ) (ξ : EuclideanSpace ℝ (Fin d)) :
    (freeMatrixAt t ξ)ᵀ * Jsymp * freeMatrixAt t ξ = Jsymp :=
  freeMatrix_symplectic t ‖ξ‖ (bracket_pos ξ).ne'

/-- The free matrix preserves the per-frequency form: `ω₂(W_t z, W_t w) = ω₂(z,w)`. -/
theorem freeMatrix_preserves_omega2 (t k : ℝ) {br : ℝ} (hbr : br ≠ 0) (z w : Fin 2 → ℝ) :
    omega2 (freeMatrix t k br *ᵥ z) (freeMatrix t k br *ᵥ w) = omega2 z w := by
  rw [omega2_mulVec, det_freeMatrix t k hbr, one_mul]

/-- Per-frequency group law `W_s W_t = W_{s+t}` (the frequency form of the group law of
the free group used in TeX lines 101 and 121-122). -/
theorem freeMatrix_mul (s t k : ℝ) {br : ℝ} (hbr : br ≠ 0) :
    freeMatrix s k br * freeMatrix t k br = freeMatrix (s + t) k br := by
  by_cases hk : k = 0
  · subst hk
    simp only [freeMatrix_zero_freq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp only [freeMatrix, sineQuotient_of_ne_zero _ hk]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, add_mul, Real.cos_add, Real.sin_add] <;>
      field_simp <;> ring

/-- The velocity reversal `diag(1,-1)`. -/
def reversal : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

/-- Per-frequency reversal identity `R W_t R = W_{-t}` (TeX lines 120-121). -/
theorem reversal_freeMatrix (t k br : ℝ) :
    reversal * freeMatrix t k br * reversal = freeMatrix (-t) k br := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reversal, freeMatrix, Matrix.mul_apply, Fin.sum_univ_two, sineQuotient_neg,
      neg_mul, Real.cos_neg, Real.sin_neg, neg_div]

/-! ### Skewness of the force for the symplectic form -/

section Force

variable {U V : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]

/-- The symplectic form `ω((u,v),(f,g)) = P(u,g) - P(f,v)` for a pairing
`P : U × V → ℝ` (TeX line 36, with `P` the `H^{1/2}`-`H^{-1/2}` duality). -/
def omega (P : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (z w : U × V) : ℝ := P z.1 w.2 - P w.1 z.2

/-- The force `B(b)(u,v) = (0, M u)` for a map `M : U → V` (TeX line 41 with
`M u = b u`). -/
def force (M : U → V) (z : U × V) : U × V := (0, M z.1)

/-- Skewness of the force for `ω`: if the pairing is symmetric through `M`
(`P(f, Mu) = P(u, Mf)`), then `ω(B z, w) + ω(z, B w) = 0` (TeX lines 40-41 and
88-91). -/
theorem omega_force_skew (P : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (M : U → V)
    (hsymm : ∀ u f : U, P f (M u) = P u (M f)) (z w : U × V) :
    omega P (force M z) w + omega P z (force M w) = 0 := by
  simp [omega, force, hsymm z.1 w.1]

end Force

section ForceL2

variable {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)

/-- The `L²` form `ω((u,v),(f,g)) = ∫ u g - ∫ f v` on pairs of real functions
(the balanced `L²` pairing of TeX lines 67 and 89-90). -/
def omegaL2 (z w : (X → ℝ) × (X → ℝ)) : ℝ :=
  (∫ x, z.1 x * w.2 x ∂μ) - ∫ x, w.1 x * z.2 x ∂μ

/-- The force `B(b)(u,v) = (0, b u)` on pairs of real functions. -/
def forceL2 (b : X → ℝ) (z : (X → ℝ) × (X → ℝ)) : (X → ℝ) × (X → ℝ) :=
  (0, fun x => b x * z.1 x)

/-- Skewness at the `L²` level: `ω(B(b)z,w) + ω(z,B(b)w) = -∫ f b u + ∫ u b f = 0`
(TeX lines 89-91). -/
theorem omegaL2_force_skew (b : X → ℝ) (z w : (X → ℝ) × (X → ℝ)) :
    omegaL2 μ (forceL2 b z) w + omegaL2 μ z (forceL2 b w) = 0 := by
  simp only [omegaL2, forceL2, Pi.zero_apply, zero_mul, MeasureTheory.integral_zero, sub_zero,
    zero_sub]
  have : (fun x => w.1 x * (b x * z.1 x)) = fun x => z.1 x * (b x * w.1 x) := by
    funext x; ring
  rw [this]
  ring

/-- The cancellation of TeX lines 89-90 is absolutely integrable: for `u, f ∈ L²`
and a bounded a.e.-strongly measurable `b`, the integrand `f (b u)` is integrable. -/
theorem integrable_mul_force (b u f : X → ℝ) (C : ℝ) (hb : MeasureTheory.AEStronglyMeasurable b μ)
    (hbC : ∀ x, |b x| ≤ C) (hu : MeasureTheory.MemLp u 2 μ) (hf : MeasureTheory.MemLp f 2 μ) :
    MeasureTheory.Integrable (fun x => f x * (b x * u x)) μ := by
  have hbu : MeasureTheory.MemLp (fun x => b x * u x) 2 μ := by
    refine MeasureTheory.MemLp.of_le_mul (c := C) hu (hb.mul hu.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun x => ?_
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hbC x) (abs_nonneg _)
  exact hf.integrable_mul hbu

end ForceL2

/-! ### Compact operators -/

section Compact

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Auxiliary: a bounded operator after a compact one is compact. -/
theorem isCompactOperator_mul_left (A : E →L[ℝ] E) {K : E →L[ℝ] E}
    (hK : IsCompactOperator K) : IsCompactOperator (A * K) := by
  have : ⇑(A * K) = A ∘ K := rfl
  rw [this]
  exact hK.clm_comp A

/-- Auxiliary: a compact operator after a bounded one is compact. -/
theorem isCompactOperator_mul_right {K : E →L[ℝ] E} (hK : IsCompactOperator K)
    (A : E →L[ℝ] E) : IsCompactOperator (K * A) := by
  have : ⇑(K * A) = K ∘ A := rfl
  rw [this]
  exact hK.comp_clm A

/-- Auxiliary: differences of compact operators are compact (operator form). -/
theorem isCompactOperator_sub' {A B : E →L[ℝ] E} (hA : IsCompactOperator A)
    (hB : IsCompactOperator B) : IsCompactOperator (A - B) := by
  have : ⇑(A - B) = ⇑A - ⇑B := rfl
  rw [this]
  exact hA.sub hB

/-- Auxiliary: sums of compact operators are compact (operator form). -/
theorem isCompactOperator_add' {A B : E →L[ℝ] E} (hA : IsCompactOperator A)
    (hB : IsCompactOperator B) : IsCompactOperator (A + B) := by
  have : ⇑(A + B) = ⇑A + ⇑B := rfl
  rw [this]
  exact hA.add hB

/-- Closedness of the compact ideal: a norm limit, along a nontrivial filter, of
operators that are eventually compact is compact (TeX lines 98-99). -/
theorem isCompactOperator_of_tendsto [CompleteSpace E] {ι : Type*} {l : Filter ι} [l.NeBot]
    {A : ι → E →L[ℝ] E} {B : E →L[ℝ] E} (hlim : Tendsto A l (𝓝 B))
    (hA : ∀ᶠ i in l, IsCompactOperator (A i)) : IsCompactOperator B :=
  isClosed_setOfPred_isCompactOperator.mem_of_tendsto hlim hA

/-- The left Young sum `∑_{j<n} (X(p_{j+1}) - X(p_j)) U(p_j, s)` (TeX lines 95-97). -/
def youngSum (X : ℝ → E →L[ℝ] E) (U : ℝ → ℝ → E →L[ℝ] E) (s : ℝ) (p : ℕ → ℝ) (n : ℕ) :
    E →L[ℝ] E :=
  ∑ j ∈ Finset.range n, (X (p (j + 1)) - X (p j)) * U (p j) s

/-- Each left Young sum is compact when `X` is compact at the partition points
(TeX lines 94-98). -/
theorem isCompactOperator_youngSum (X : ℝ → E →L[ℝ] E) (U : ℝ → ℝ → E →L[ℝ] E) (s : ℝ)
    (p : ℕ → ℝ) (n : ℕ) (hX : ∀ j ≤ n, IsCompactOperator (X (p j))) :
    IsCompactOperator (youngSum X U s p n) := by
  unfold youngSum
  refine Finset.sum_induction _ (fun A : E →L[ℝ] E => IsCompactOperator A)
    (fun A B hA hB => isCompactOperator_add' hA hB) isCompactOperator_zero ?_
  intro j hj
  have hj' := Finset.mem_range.1 hj
  exact isCompactOperator_mul_right
    (isCompactOperator_sub' (hX (j + 1) (by omega)) (hX j (by omega))) _

/-- The ordered product `P_N ⋯ P_0`. -/
def orderedProd (P : ℕ → E →L[ℝ] E) : ℕ → E →L[ℝ] E
  | 0 => P 0
  | n + 1 => P (n + 1) * orderedProd P n

/-- Telescoping (TeX lines 125-128): if every `P_j - Q_j`, `j ≤ N`, is compact, then
`P_N ⋯ P_0 - Q_N ⋯ Q_0` is compact. -/
theorem isCompactOperator_orderedProd_sub (P Q : ℕ → E →L[ℝ] E) (N : ℕ)
    (h : ∀ j ≤ N, IsCompactOperator (P j - Q j)) :
    IsCompactOperator (orderedProd P N - orderedProd Q N) := by
  induction N with
  | zero => simpa [orderedProd] using h 0 le_rfl
  | succ n ih =>
    have hdecomp : orderedProd P (n + 1) - orderedProd Q (n + 1)
        = (P (n + 1) - Q (n + 1)) * orderedProd P n
          + Q (n + 1) * (orderedProd P n - orderedProd Q n) := by
      simp only [orderedProd, sub_mul, mul_sub]
      abel
    rw [hdecomp]
    exact isCompactOperator_add'
      (isCompactOperator_mul_right (h (n + 1) le_rfl) _)
      (isCompactOperator_mul_left _ (ih fun j hj => h j (by omega)))

end Compact

/-! ### Compact perturbations and translations -/

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Weak nullity of a family along a filter: `⟨x_i, w⟩ → 0` for every `w`. -/
def WeaklyNull {ι : Type*} (l : Filter ι) (x : ι → E) : Prop :=
  ∀ w : E, Tendsto (fun i => inner ℝ (x i) w) l (𝓝 0)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Auxiliary: a cluster point of `f` along `l` at which `g ∘ f → 0` for a continuous `g`
has `g = 0` there. -/
theorem eq_zero_of_mapClusterPt {ι : Type*} {l : Filter ι} {f : ι → E} {p : E}
    {g : E → ℝ} (hg : Continuous g) (hp : MapClusterPt p l f)
    (hlim : Tendsto (g ∘ f) l (𝓝 0)) : g p = 0 := by
  have hc : MapClusterPt (g p) l (g ∘ f) := hp.continuousAt_comp hg.continuousAt
  by_contra hne
  have hdis : Disjoint (𝓝 (g p)) (𝓝 (0 : ℝ)) := disjoint_nhds_nhds.2 hne
  have hle : 𝓝 (g p) ⊓ Filter.map (g ∘ f) l ≤ ⊥ :=
    (inf_le_inf_left _ hlim).trans hdis.le_bot
  exact (hc.neBot).ne (le_bot_iff.1 hle)

/-- A compact operator maps a bounded weakly null family (along any filter) to a norm
null family (TeX lines 110-112; the Lean route uses cluster points in the compact
closure of the image of a ball, not subsequences). -/
theorem tendsto_compact_of_weaklyNull {ι : Type*} {l : Filter ι} (K : E →L[ℝ] E)
    (hK : IsCompactOperator K) (x : ι → E) (C : ℝ) (hb : ∀ i, ‖x i‖ ≤ C)
    (hw : WeaklyNull l x) : Tendsto (fun i => K (x i)) l (𝓝 0) := by
  have hcpt : IsCompact (closure (K '' Metric.closedBall (0 : E) C)) :=
    hK.isCompact_closure_image_of_bounded Metric.isBounded_closedBall
  refine hcpt.tendsto_nhds_of_unique_mapClusterPt
    (Filter.Eventually.of_forall fun i => subset_closure ⟨x i, by simpa using hb i, rfl⟩) ?_
  intro p _ hp
  have hlim : Tendsto ((fun q : E => inner ℝ q p) ∘ fun i => K (x i)) l (𝓝 0) := by
    have := hw (ContinuousLinearMap.adjoint K p)
    refine this.congr fun i => ?_
    simp [ContinuousLinearMap.adjoint_inner_right]
  have h0 := eq_zero_of_mapClusterPt (continuous_id.inner continuous_const) hp hlim
  simpa using h0

/-- Abstract compact-perturbation bound (TeX lines 103-119): if `S` commutes with
isometries `τ_i` such that `τ_i z` is weakly null along a nontrivial filter for every
`z`, then `‖S‖ ≤ ‖S + K‖` for every compact `K`. -/
theorem norm_le_norm_add_compact {ι : Type*} (l : Filter ι) [l.NeBot] (S : E →L[ℝ] E)
    (τ : ι → E →L[ℝ] E) (hiso : ∀ i z, ‖τ i z‖ = ‖z‖) (hcomm : ∀ i, S * τ i = τ i * S)
    (hnull : ∀ z, WeaklyNull l (fun i => τ i z)) (K : E →L[ℝ] E) (hK : IsCompactOperator K) :
    ‖S‖ ≤ ‖S + K‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z => ?_
  have hKt : Tendsto (fun i => ‖K (τ i z)‖) l (𝓝 0) := by
    have := tendsto_compact_of_weaklyNull K hK (fun i => τ i z) ‖z‖
      (fun i => (hiso i z).le) (hnull z)
    simpa using this.norm
  have hpt : ∀ i, ‖S z‖ ≤ ‖S + K‖ * ‖z‖ + ‖K (τ i z)‖ := by
    intro i
    have h1 : ‖S z‖ = ‖S (τ i z)‖ := by
      have : S (τ i z) = τ i (S z) := by
        simpa using congrArg (fun A : E →L[ℝ] E => A z) (hcomm i)
      rw [this, hiso]
    have h2 : S (τ i z) = (S + K) (τ i z) - K (τ i z) := by simp
    rw [h1, h2]
    refine (norm_sub_le _ _).trans ?_
    gcongr
    calc ‖(S + K) (τ i z)‖ ≤ ‖S + K‖ * ‖τ i z‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖S + K‖ * ‖z‖ := by rw [hiso]
  have hlim : Tendsto (fun i => ‖S + K‖ * ‖z‖ + ‖K (τ i z)‖) l (𝓝 (‖S + K‖ * ‖z‖ + 0)) :=
    tendsto_const_nhds.add hKt
  rw [add_zero] at hlim
  exact ge_of_tendsto hlim (Filter.Eventually.of_forall hpt)

/-- Corollary: `‖S‖ ≤ ‖A‖` whenever `A - S` is compact (same hypotheses on `S`). -/
theorem norm_le_of_sub_compact {ι : Type*} (l : Filter ι) [l.NeBot] (S A : E →L[ℝ] E)
    (τ : ι → E →L[ℝ] E) (hiso : ∀ i z, ‖τ i z‖ = ‖z‖) (hcomm : ∀ i, S * τ i = τ i * S)
    (hnull : ∀ z, WeaklyNull l (fun i => τ i z)) (hK : IsCompactOperator (A - S)) :
    ‖S‖ ≤ ‖A‖ := by
  have := norm_le_norm_add_compact l S τ hiso hcomm hnull (A - S) hK
  simpa using this

end Hilbert

/-! ### Norm at least one from the group law and the reversal -/

section NormOne

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If `B A = I`, `B = R A R` and `R` is an isometry, then `1 ≤ ‖A‖` (TeX lines
120-122).  `Nontrivial E` is needed: on the zero space every operator has norm zero. -/
theorem one_le_norm_of_reversal [Nontrivial E] (A B R : E →L[ℝ] E) (hBA : B * A = 1)
    (hR : ∀ z, ‖R z‖ = ‖z‖) (hB : B = R * A * R) : 1 ≤ ‖A‖ := by
  have hRn : ‖R‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by rw [hR, one_mul]
  have hBn : ‖B‖ ≤ ‖A‖ := by
    rw [hB]
    calc ‖R * A * R‖ ≤ ‖R * A‖ * ‖R‖ := norm_mul_le _ _
      _ ≤ (‖R‖ * ‖A‖) * ‖R‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (1 * ‖A‖) * 1 := by gcongr
      _ = ‖A‖ := by ring
  have h1 : (1 : ℝ) ≤ ‖B‖ * ‖A‖ := by
    calc (1 : ℝ) = ‖(1 : E →L[ℝ] E)‖ := norm_one.symm
      _ = ‖B * A‖ := by rw [hBA]
      _ ≤ ‖B‖ * ‖A‖ := norm_mul_le _ _
  have hA0 : 0 ≤ ‖A‖ := norm_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hBn hA0]

end NormOne

/-! ### Supplied inputs and the wrappers -/

/-- Supplied input (D8; TeX lines 103-122): the free wave group `S_E` on
`E = H^{1/2} × H^{-1/2}`, the velocity reversal `𝓡(u,v) = (u,-v)` and the spatial
translations `τ_y`, `y ∈ ℝ^d`, with the properties the proof of `L:symplectic-free`
states for them: the group law, `S_E(-h) = 𝓡 S_E(h) 𝓡` with `𝓡` isometric,
translations isometric and commuting with `S_E(h)`, and `⟨τ_y z, w⟩_E → 0` as
`|y| → ∞` (cocompact filter on `ℝ^d`). -/
structure FreeWaveData (d : ℕ) (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  /-- The free group `S_E(t)`. -/
  S : ℝ → E →L[ℝ] E
  S_zero : S 0 = 1
  S_add : ∀ s t, S (s + t) = S s * S t
  /-- The velocity reversal. -/
  R : E →L[ℝ] E
  R_norm : ∀ z, ‖R z‖ = ‖z‖
  S_neg : ∀ h, S (-h) = R * S h * R
  /-- The translations `τ_y`. -/
  τ : EuclideanSpace ℝ (Fin d) → E →L[ℝ] E
  τ_norm : ∀ y z, ‖τ y z‖ = ‖z‖
  τ_comm : ∀ y h, S h * τ y = τ y * S h
  τ_weak : ∀ z w, Tendsto (fun y => inner ℝ (τ y z) w) (cocompact (EuclideanSpace ℝ (Fin d))) (𝓝 0)

/-- Supplied input (D7; `P:constant-young-linear` on `𝓛(E)`, TeX lines 91-98): the left
Young sums of `X` over partitions of `[s,t]` converge in operator norm to
`U(t,s) - I` along some nontrivial filter of partitions.  A partition is a pair
`(n, p)` with points `p 0, …, p n`; only the points `p j`, `j ≤ n`, enter, and they lie
in `[s,t]` eventually.  The TeX's convergence as the mesh tends to zero implies this
statement (the mesh filter is nontrivial). -/
def LeftYoungSumsConverge {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : ℝ → E →L[ℝ] E) (U : ℝ → ℝ → E →L[ℝ] E) (s t : ℝ) : Prop :=
  ∃ l : Filter (ℕ × (ℕ → ℝ)), l.NeBot ∧
    (∀ᶠ π in l, ∀ j ≤ π.1, π.2 j ∈ Set.Icc s t) ∧
    Tendsto (fun π => youngSum X U s π.2 π.1) l (𝓝 (U t s - 1))

section Wrappers

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Auxiliary: for `d ≥ 1` the cocompact filter of `ℝ^d` is nontrivial. -/
theorem FreeWaveData.cocompact_neBot (hd : 1 ≤ d) :
    (cocompact (EuclideanSpace ℝ (Fin d))).NeBot := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  infer_instance

omit [CompleteSpace E] in
/-- `‖S_E(h)‖ ≥ 1` (TeX lines 120-122), for a nonzero `E`. -/
theorem FreeWaveData.one_le_norm [Nontrivial E] (F : FreeWaveData d E) (h : ℝ) :
    1 ≤ ‖F.S h‖ :=
  one_le_norm_of_reversal (F.S h) (F.S (-h)) F.R
    (by rw [← F.S_add, neg_add_cancel, F.S_zero]) F.R_norm (F.S_neg h)

/-- `‖S_E(h)‖ ≤ ‖S_E(h) + K‖` for every compact `K` (TeX lines 103-119), `d ≥ 1`. -/
theorem FreeWaveData.norm_le_norm_add_compact (F : FreeWaveData d E) (hd : 1 ≤ d) (h : ℝ)
    (K : E →L[ℝ] E) (hK : IsCompactOperator K) : ‖F.S h‖ ≤ ‖F.S h + K‖ := by
  have := FreeWaveData.cocompact_neBot hd
  exact SymplecticFree.norm_le_norm_add_compact (cocompact _) (F.S h) F.τ F.τ_norm
    (fun y => F.τ_comm y h) (fun z w => F.τ_weak z w) K hK

/-- The compact Young baseline in general form: if the left Young sums of `X` over
partitions of `[s,t]` converge to `U(t,s) - I` (supplied, D7) and `X` is compact on
`[s,t]`, then `U(t,s) - I` and `S_E(t) U(t,s) S_E(-s) - S_E(t-s)` are compact, and
`‖S_E(t) U(t,s) S_E(-s)‖ ≥ ‖S_E(t-s)‖ ≥ 1`. -/
theorem compact_young_baseline [Nontrivial E] (F : FreeWaveData d E) (hd : 1 ≤ d)
    (X : ℝ → E →L[ℝ] E) (U : ℝ → ℝ → E →L[ℝ] E) (s t : ℝ)
    (hXK : ∀ r ∈ Set.Icc s t, IsCompactOperator (X r))
    (hY : LeftYoungSumsConverge X U s t) :
    IsCompactOperator ⇑(U t s - 1 : E →L[ℝ] E) ∧
      IsCompactOperator (F.S t * U t s * F.S (-s) - F.S (t - s)) ∧
      ‖F.S (t - s)‖ ≤ ‖F.S t * U t s * F.S (-s)‖ ∧ 1 ≤ ‖F.S (t - s)‖ := by
  obtain ⟨l, hl, hpts, hlim⟩ := hY
  have hU : IsCompactOperator ⇑(U t s - 1 : E →L[ℝ] E) := by
    refine isCompactOperator_of_tendsto hlim ?_
    filter_upwards [hpts] with π hπ
    exact isCompactOperator_youngSum X U s π.2 π.1 fun j hj => hXK _ (hπ j hj)
  have hdiff : F.S t * U t s * F.S (-s) - F.S (t - s) = F.S t * (U t s - 1) * F.S (-s) := by
    rw [sub_eq_add_neg t s, F.S_add, mul_sub, sub_mul, mul_one]
  have hK : IsCompactOperator (F.S t * U t s * F.S (-s) - F.S (t - s)) := by
    rw [hdiff]
    exact isCompactOperator_mul_right (isCompactOperator_mul_left _ hU) _
  have := FreeWaveData.cocompact_neBot hd
  refine ⟨hU, hK, ?_, F.one_le_norm _⟩
  exact norm_le_of_sub_compact (cocompact _) (F.S (t - s)) _ F.τ F.τ_norm
    (fun y => F.τ_comm y _) (fun z w => F.τ_weak z w) hK

omit [CompleteSpace E] in
/-- Auxiliary: the free product `S_E(ℓ_N) ⋯ S_E(ℓ_0) = S_E(∑_{j ≤ N} ℓ_j)` (group law). -/
theorem FreeWaveData.orderedProd_S (F : FreeWaveData d E) (ℓ : ℕ → ℝ) (N : ℕ) :
    orderedProd (fun j => F.S (ℓ j)) N = F.S (∑ j ∈ Finset.range (N + 1), ℓ j) := by
  induction N with
  | zero => simp [orderedProd]
  | succ n ih =>
    rw [orderedProd, ih, ← F.S_add]
    congr 1
    rw [Finset.sum_range_succ _ (n + 1)]
    ring

/-- The compact product baseline in general form: if each `U_j(ℓ_j,0) - I` is compact,
`P_j = S_E(ℓ_j) U_j(ℓ_j,0)`, then `P_N ⋯ P_0 - S_E(∑ ℓ_j)` is compact and
`‖P_N ⋯ P_0‖ ≥ ‖S_E(∑ ℓ_j)‖ ≥ 1`. -/
theorem compact_product_baseline [Nontrivial E] (F : FreeWaveData d E) (hd : 1 ≤ d)
    (U : ℕ → ℝ → ℝ → E →L[ℝ] E) (ℓ : ℕ → ℝ) (N : ℕ)
    (hU : ∀ j ≤ N, IsCompactOperator ⇑(U j (ℓ j) 0 - 1 : E →L[ℝ] E)) :
    IsCompactOperator (orderedProd (fun j => F.S (ℓ j) * U j (ℓ j) 0) N
        - F.S (∑ j ∈ Finset.range (N + 1), ℓ j)) ∧
      ‖F.S (∑ j ∈ Finset.range (N + 1), ℓ j)‖
        ≤ ‖orderedProd (fun j => F.S (ℓ j) * U j (ℓ j) 0) N‖ ∧
      1 ≤ ‖F.S (∑ j ∈ Finset.range (N + 1), ℓ j)‖ := by
  have hK : IsCompactOperator (orderedProd (fun j => F.S (ℓ j) * U j (ℓ j) 0) N
      - F.S (∑ j ∈ Finset.range (N + 1), ℓ j)) := by
    rw [← F.orderedProd_S ℓ N]
    refine isCompactOperator_orderedProd_sub _ _ N fun j hj => ?_
    have : F.S (ℓ j) * U j (ℓ j) 0 - F.S (ℓ j) = F.S (ℓ j) * (U j (ℓ j) 0 - 1) := by
      rw [mul_sub, mul_one]
    rw [this]
    exact isCompactOperator_mul_left _ (hU j hj)
  have := FreeWaveData.cocompact_neBot hd
  refine ⟨hK, ?_, F.one_le_norm _⟩
  exact norm_le_of_sub_compact (cocompact _) _ _ F.τ F.τ_norm
    (fun y => F.τ_comm y _) (fun z w => F.τ_weak z w) hK

end Wrappers

/-! ### Exact-hypothesis wrappers for `L:symplectic-free` -/

section Paper

open HomogHypothesis

variable {d : ℕ} {alpha alpha0 : ℝ} {Γ μ : MeasureTheory.Measure (Rd d)}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Auxiliary: `H:homog` gives `d ≥ 1`. -/
theorem one_le_dim (hH : HomogCovariance d alpha alpha0 Γ μ) : 1 ≤ d := by
  rcases hH.dim with h | h | h <;> omega

/-- `E:symplectic-compact-young-baseline` (TeX lines 43-49), with the lemma's own
hypotheses: `1/2 < θ < 1`, `X ∈ C^θ([0,T]; 𝒦(E))` with `X(0) = 0`, `U` the left Young
evolution of `X` (supplied, D7: `LeftYoungSumsConverge` for `0 ≤ s ≤ t ≤ T`), and the
section's standing `H:homog` and `T > 0`; the space `E`, its free group, reversal and
translations are supplied (`FreeWaveData`, D8), `E ≠ 0` is explicit.  Conclusion:
`U(t,s) - I` is compact, `‖S_E(t) U(t,s) S_E(-s)‖ ≥ ‖S_E(t-s)‖ ≥ 1`.
Used: `H:homog` only through `d ≥ 1`; `X` compact on `[0,T]`; the Young input.
Carried, unused by the Lean proof (they are the hypotheses of the supplied Young
input): `θ`, the Hölder bound, `X(0) = 0`, `T > 0`. -/
theorem symplectic_compact_young_baseline_paper [Nontrivial E]
    (hH : HomogCovariance d alpha alpha0 Γ μ) (F : FreeWaveData d E)
    (T : ℝ) (_hT : 0 < T) (θ : ℝ≥0) (_hθ : 1 / 2 < θ) (_hθ1 : θ < 1)
    (X : ℝ → E →L[ℝ] E) (CX : ℝ≥0) (_hXhol : HolderOnWith CX θ X (Set.Icc 0 T))
    (_hX0 : X 0 = 0) (hXK : ∀ r ∈ Set.Icc 0 T, IsCompactOperator (X r))
    (U : ℝ → ℝ → E →L[ℝ] E)
    (hU : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T → LeftYoungSumsConverge X U s t)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) :
    IsCompactOperator ⇑(U t s - 1 : E →L[ℝ] E) ∧
      ‖F.S (t - s)‖ ≤ ‖F.S t * U t s * F.S (-s)‖ ∧ 1 ≤ ‖F.S (t - s)‖ := by
  have h := compact_young_baseline F (one_le_dim hH) X U s t
    (fun r hr => hXK r ⟨hs.trans hr.1, hr.2.trans htT⟩) (hU s t hs hst htT)
  exact ⟨h.1, h.2.2⟩

/-- `E:symplectic-compact-product-baseline` (TeX lines 50-58), with the lemma's own
hypotheses: paths `X_j ∈ C^θ([0,B]; 𝒦(E))`, `1/2 < θ < 1`, `X_j(0) = 0`, with left
Young evolutions `U_j` (supplied, D7, on `[0, ℓ_j]`), lengths `0 ≤ ℓ_j ≤ B`,
`P_j = S_E(ℓ_j) U_j(ℓ_j,0)`, `j = 0, …, N`.  Conclusion:
`P_N ⋯ P_0 - S_E(∑ ℓ_j)` is compact and `‖P_N ⋯ P_0‖ ≥ ‖S_E(∑ ℓ_j)‖ ≥ 1`.
Used: `H:homog` only through `d ≥ 1`; `X_j` compact on `[0,B]`; `0 ≤ ℓ_j ≤ B`; the
Young inputs.  Carried, unused (hypotheses of the supplied Young input): `θ`, the
Hölder bounds, `X_j(0) = 0`. -/
theorem symplectic_compact_product_baseline_paper [Nontrivial E]
    (hH : HomogCovariance d alpha alpha0 Γ μ) (F : FreeWaveData d E)
    (B : ℝ) (θ : ℝ≥0) (_hθ : 1 / 2 < θ) (_hθ1 : θ < 1) (N : ℕ)
    (X : ℕ → ℝ → E →L[ℝ] E) (CX : ℕ → ℝ≥0)
    (_hXhol : ∀ j ≤ N, HolderOnWith (CX j) θ (X j) (Set.Icc 0 B))
    (_hX0 : ∀ j ≤ N, X j 0 = 0)
    (hXK : ∀ j ≤ N, ∀ r ∈ Set.Icc 0 B, IsCompactOperator (X j r))
    (U : ℕ → ℝ → ℝ → E →L[ℝ] E) (ℓ : ℕ → ℝ) (hℓ : ∀ j ≤ N, ℓ j ∈ Set.Icc 0 B)
    (hU : ∀ j ≤ N, LeftYoungSumsConverge (X j) (U j) 0 (ℓ j)) :
    IsCompactOperator ⇑(orderedProd (fun j => F.S (ℓ j) * U j (ℓ j) 0) N
        - F.S (∑ j ∈ Finset.range (N + 1), ℓ j)) ∧
      ‖F.S (∑ j ∈ Finset.range (N + 1), ℓ j)‖
        ≤ ‖orderedProd (fun j => F.S (ℓ j) * U j (ℓ j) 0) N‖ ∧
      1 ≤ ‖F.S (∑ j ∈ Finset.range (N + 1), ℓ j)‖ := by
  have hd := one_le_dim hH
  refine compact_product_baseline F hd U ℓ N fun j hj => ?_
  exact (compact_young_baseline F hd (X j) (U j) 0 (ℓ j)
    (fun r hr => hXK j hj r ⟨hr.1, hr.2.trans (hℓ j hj).2⟩) (hU j hj)).1

/-- The force claim of `L:symplectic-free` (TeX lines 40-41, proof lines 88-91) at the
`L²` level on `ℝ^d` with Lebesgue measure, for bounded real smooth `b`: the cancellation
integrand is integrable for `u, f ∈ L²`, and `ω(B(b)z,w) + ω(z,B(b)w) = 0` for the
`L²` form `omegaL2`.  The identification of the `H^{1/2}`-`H^{-1/2}` duality with the
`L²` integral for these functions is D8 and not formalized.
Used: continuity of `b` (measurability) and its bound.  Carried, unused: smoothness
beyond continuity, `H:homog`. -/
theorem symplectic_force_skew_paper (_hH : HomogCovariance d alpha alpha0 Γ μ)
    (b : Rd d → ℝ) (hb : ContDiff ℝ (⊤ : ℕ∞) b) (C : ℝ) (hbC : ∀ x, |b x| ≤ C) :
    (∀ u f : Rd d → ℝ, MeasureTheory.MemLp u 2 MeasureTheory.volume →
        MeasureTheory.MemLp f 2 MeasureTheory.volume →
        MeasureTheory.Integrable (fun x => f x * (b x * u x)) MeasureTheory.volume) ∧
      ∀ z w : (Rd d → ℝ) × (Rd d → ℝ),
        omegaL2 MeasureTheory.volume (forceL2 b z) w
          + omegaL2 MeasureTheory.volume z (forceL2 b w) = 0 := by
  refine ⟨fun u f hu hf => integrable_mul_force _ b u f C
    hb.continuous.aestronglyMeasurable hbC hu hf, fun z w => omegaL2_force_skew _ b z w⟩

/-- `L:symplectic-free` (TeX lines 30-60), the formalized parts together under the
lemma's hypotheses: (i) the per-frequency identity `W_t(ξ)ᵀ J_symp W_t(ξ) = J_symp` for
every `t` and every `ξ ∈ ℝ^d`, `ξ = 0` included; (ii) the force skewness of
`symplectic_force_skew_paper` (its identity half; the integrability half is in
`symplectic_force_skew_paper` itself); (iii) `E:symplectic-compact-young-baseline`;
(iv) `E:symplectic-compact-product-baseline`.  Narrower: the operator `J_E`, the identity
`ω = ⟨·, J_E ·⟩_E` and the preservation of `ω` by `S_E` on all of `E` (the Fourier
integration of (i)) are not formalized.  `b`'s smoothness and bound enter only
through `symplectic_force_skew_paper`, whose identity half (the part used here) does not
depend on them; they are carried for fidelity.  The other hypotheses are used as in the
two baseline wrappers. -/
theorem symplectic_free_paper [Nontrivial E]
    (hH : HomogCovariance d alpha alpha0 Γ μ) (F : FreeWaveData d E)
    (b : Rd d → ℝ) (hb : ContDiff ℝ (⊤ : ℕ∞) b) (Cb : ℝ) (hbC : ∀ x, |b x| ≤ Cb)
    (T : ℝ) (hT : 0 < T) (θ : ℝ≥0) (hθ : 1 / 2 < θ) (hθ1 : θ < 1)
    (X : ℝ → E →L[ℝ] E) (CX : ℝ≥0) (hXhol : HolderOnWith CX θ X (Set.Icc 0 T))
    (hX0 : X 0 = 0) (hXK : ∀ r ∈ Set.Icc 0 T, IsCompactOperator (X r))
    (U : ℝ → ℝ → E →L[ℝ] E)
    (hU : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T → LeftYoungSumsConverge X U s t)
    (B : ℝ) (N : ℕ) (Xs : ℕ → ℝ → E →L[ℝ] E) (CXs : ℕ → ℝ≥0)
    (hXshol : ∀ j ≤ N, HolderOnWith (CXs j) θ (Xs j) (Set.Icc 0 B))
    (hXs0 : ∀ j ≤ N, Xs j 0 = 0)
    (hXsK : ∀ j ≤ N, ∀ r ∈ Set.Icc 0 B, IsCompactOperator (Xs j r))
    (Us : ℕ → ℝ → ℝ → E →L[ℝ] E) (ℓ : ℕ → ℝ) (hℓ : ∀ j ≤ N, ℓ j ∈ Set.Icc 0 B)
    (hUs : ∀ j ≤ N, LeftYoungSumsConverge (Xs j) (Us j) 0 (ℓ j)) :
    (∀ (t : ℝ) (ξ : Rd d), (freeMatrixAt t ξ)ᵀ * Jsymp * freeMatrixAt t ξ = Jsymp) ∧
      (∀ z w : (Rd d → ℝ) × (Rd d → ℝ),
        omegaL2 MeasureTheory.volume (forceL2 b z) w
          + omegaL2 MeasureTheory.volume z (forceL2 b w) = 0) ∧
      (∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
        IsCompactOperator ⇑(U t s - 1 : E →L[ℝ] E) ∧
          ‖F.S (t - s)‖ ≤ ‖F.S t * U t s * F.S (-s)‖ ∧ 1 ≤ ‖F.S (t - s)‖) ∧
      (IsCompactOperator ⇑(orderedProd (fun j => F.S (ℓ j) * Us j (ℓ j) 0) N
          - F.S (∑ j ∈ Finset.range (N + 1), ℓ j)) ∧
        ‖F.S (∑ j ∈ Finset.range (N + 1), ℓ j)‖
          ≤ ‖orderedProd (fun j => F.S (ℓ j) * Us j (ℓ j) 0) N‖ ∧
        1 ≤ ‖F.S (∑ j ∈ Finset.range (N + 1), ℓ j)‖) :=
  ⟨fun t ξ => freeMatrixAt_symplectic t ξ,
    (symplectic_force_skew_paper hH b hb Cb hbC).2,
    fun s t hs hst htT => symplectic_compact_young_baseline_paper hH F T hT θ hθ hθ1 X CX
      hXhol hX0 hXK U hU s t hs hst htT,
    symplectic_compact_product_baseline_paper hH F B θ hθ hθ1 N Xs CXs hXshol hXs0 hXsK
      Us ℓ hℓ hUs⟩

end Paper

end StratonovichHAMSecondMoment.SymplecticFree
