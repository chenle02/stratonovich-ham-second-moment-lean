module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L16, item L16-C (part 3): the positive square root of a compact positive operator on a
real Hilbert space, from the compact spectral theorem (`integrated_cameron_mean.tex` line 265 at
revision edf7085f (book 1.1.3): "Its positive square root is compact by the compact
spectral theorem").  Mathlib has no continuous functional calculus for real operators, so
`CFC.sqrt` is not available; the root is built by hand.

* `exists_eigen_hilbertBasis`: a compact symmetric operator has a Hilbert basis of eigenvectors.
  Route: every eigenspace is closed, hence has a Hilbert basis (`exists_hilbertBasis`); the
  eigenspaces are mutually orthogonal (`orthogonalFamily_eigenspaces`), so the collected family
  is orthonormal (`orthonormal_sigma_orthonormal`); their span is dense because the orthogonal
  complement of the eigenspaces is trivial
  (`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`).
* `exists_isPositive_sqrt`: a compact positive operator `K` has a positive `S` with `S ∘ S = K`:
  `S` multiplies the coordinate along the eigenvector `b i` by `√μ_i`.
-/
public import Mathlib

@[expose] public section

noncomputable section

set_option autoImplicit false

open Filter Topology Set Module.End
open scoped RealInnerProductSpace

namespace StratonovichHAMSecondMoment.CameronTemporal

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Auxiliary: an eigenspace of a continuous operator is closed. -/
theorem isClosed_eigenspace (K : E →L[ℝ] E) (μ : ℝ) :
    IsClosed (eigenspace (K : E →ₗ[ℝ] E) μ : Set E) := by
  have : (eigenspace (K : E →ₗ[ℝ] E) μ : Set E) = {x | K x = μ • x} := by
    ext x
    simp only [SetLike.mem_coe, mem_eigenspace_iff, ContinuousLinearMap.coe_coe]
    rfl
  rw [this]
  exact isClosed_eq K.continuous (continuous_const_smul μ)

/-- **Compact spectral theorem, Hilbert-basis form**: a compact symmetric operator on a real
Hilbert space has a Hilbert basis of eigenvectors. -/
theorem exists_eigen_hilbertBasis (K : E →L[ℝ] E) (hK : IsCompactOperator K)
    (hs : K.IsSymmetric) :
    ∃ (ι : Type u) (b : HilbertBasis ι ℝ E) (μ : ι → ℝ), ∀ i, K (b i) = μ i • b i := by
  set V : ℝ → Submodule ℝ E := fun μ => eigenspace (K : E →ₗ[ℝ] E) μ with hV
  have hc : ∀ μ, CompleteSpace (V μ) := fun μ => (isClosed_eigenspace K μ).completeSpace_coe
  choose w b _ using fun μ => by haveI := hc μ; exact exists_hilbertBasis ℝ (V μ)
  set v : (Σ μ : ℝ, w μ) → E := fun x => ((b x.1 x.2 : V x.1) : E) with hv
  have hon : Orthonormal ℝ v :=
    (hs.orthogonalFamily_eigenspaces).orthonormal_sigma_orthonormal fun μ => (b μ).orthonormal
  have hsub : ∀ μ, V μ ≤ (Submodule.span ℝ (Set.range v)).topologicalClosure := by
    intro μ y hy
    have hsum := ((b μ).hasSum_repr ⟨y, hy⟩).mapL (V μ).subtypeL
    simp only [map_smul, Submodule.subtypeL_apply] at hsum
    refine (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hsum
      (Eventually.of_forall fun s => ?_)
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨⟨μ, i⟩, rfl⟩)
  have hbot := ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hK hs
  have htop : (⨆ μ, V μ).topologicalClosure = ⊤ :=
    Submodule.topologicalClosure_eq_top_iff.2 hbot
  have hsp : ⊤ ≤ (Submodule.span ℝ (Set.range v)).topologicalClosure := by
    rw [← htop]
    exact Submodule.topologicalClosure_minimal _ (iSup_le hsub)
      (Submodule.isClosed_topologicalClosure _)
  refine ⟨_, HilbertBasis.mk hon hsp, fun x => x.1, fun x => ?_⟩
  rw [HilbertBasis.coe_mk]
  exact mem_eigenspace_iff.1 (b x.1 x.2).2

section Diagonal

variable {ι : Type u}

/-- Auxiliary: multiplication of an `ℓ²` sequence by a bounded sequence stays in `ℓ²`. -/
theorem diag_memℓp (c : ι → ℝ) {C : ℝ} (hc : ∀ i, |c i| ≤ C) (f : lp (fun _ : ι => ℝ) 2) :
    Memℓp (fun i => c i * f i) 2 :=
  ((lp.memℓp f).norm.const_mul C).mono fun i => by
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hc i) (norm_nonneg _)

/-- Auxiliary: the diagonal operator `f ↦ (c_i f_i)` on `ℓ²`, as a linear map. -/
def diagL (c : ι → ℝ) {C : ℝ} (hc : ∀ i, |c i| ≤ C) : lp (fun _ : ι => ℝ) 2 →ₗ[ℝ] lp (fun _ : ι => ℝ) 2 where
  toFun f := ⟨fun i => c i * f i, diag_memℓp c hc f⟩
  map_add' f g := by
    apply lp.ext
    funext i
    simp [mul_add]
    rfl
  map_smul' r f := by
    apply lp.ext
    funext i
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    change c i * (r * f i) = r * (c i * f i)
    ring

/-- Auxiliary: `‖diag c f‖ ≤ C ‖f‖`. -/
theorem norm_diagL_le (c : ι → ℝ) {C : ℝ} (hC : 0 ≤ C) (hc : ∀ i, |c i| ≤ C) (f : lp (fun _ : ι => ℝ) 2) :
    ‖diagL c hc f‖ ≤ C * ‖f‖ := by
  calc ‖diagL c hc f‖ ≤ ‖C • f‖ := by
        refine lp.norm_mono (by norm_num) fun i => ?_
        change ‖c i * f i‖ ≤ ‖(C • f) i‖
        rw [lp.coeFn_smul, Pi.smul_apply, norm_mul, norm_smul, Real.norm_eq_abs,
          Real.norm_of_nonneg hC]
        exact mul_le_mul_of_nonneg_right (hc i) (norm_nonneg _)
    _ = C * ‖f‖ := by rw [lp.norm_const_smul (by norm_num), Real.norm_of_nonneg hC]

/-- Auxiliary: the diagonal operator as a continuous linear map. -/
def diagCLM (c : ι → ℝ) {C : ℝ} (hC : 0 ≤ C) (hc : ∀ i, |c i| ≤ C) :
    lp (fun _ : ι => ℝ) 2 →L[ℝ] lp (fun _ : ι => ℝ) 2 :=
  (diagL c hc).mkContinuous C (norm_diagL_le c hC hc)

/-- Auxiliary: the operator acting along a Hilbert basis by the bounded multipliers `c_i`. -/
def basisDiag (b : HilbertBasis ι ℝ E) (c : ι → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ i, |c i| ≤ C) : E →L[ℝ] E :=
  b.repr.symm.toLinearIsometry.toContinuousLinearMap ∘L diagCLM c hC hc ∘L
    b.repr.toLinearIsometry.toContinuousLinearMap

omit [CompleteSpace E] in
/-- Auxiliary: the coordinates of `basisDiag`: `⟪b i, D x⟫ = c_i ⟪b i, x⟫`. -/
theorem inner_basisDiag (b : HilbertBasis ι ℝ E) (c : ι → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ i, |c i| ≤ C) (x : E) (i : ι) :
    ⟪b i, basisDiag b c hC hc x⟫ = c i * ⟪b i, x⟫ := by
  rw [← b.repr_apply_apply, ← b.repr_apply_apply]
  simp only [basisDiag, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometryEquiv.apply_symm_apply]
  rfl

omit [CompleteSpace E] in
/-- Auxiliary: two vectors with the same coordinates along a Hilbert basis coincide. -/
theorem eq_of_inner_basis (b : HilbertBasis ι ℝ E) {x y : E} (h : ∀ i, ⟪b i, x⟫ = ⟪b i, y⟫) :
    x = y := by
  apply b.repr.injective
  apply lp.ext
  funext i
  rw [b.repr_apply_apply, b.repr_apply_apply, h i]

omit [CompleteSpace E] in
/-- Auxiliary: `⟪D x, y⟫ = ∑ c_i ⟪x, b i⟫ ⟪b i, y⟫`. -/
theorem inner_basisDiag_left (b : HilbertBasis ι ℝ E) (c : ι → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ i, |c i| ≤ C) (x y : E) :
    ⟪basisDiag b c hC hc x, y⟫ = ∑' i, c i * ⟪x, b i⟫ * ⟪b i, y⟫ := by
  rw [← b.tsum_inner_mul_inner]
  congr 1
  funext i
  rw [real_inner_comm (b i), inner_basisDiag, real_inner_comm (b i) x]

end Diagonal

/-- **The positive square root of a compact positive operator** (TeX line 265): there is a
positive `S` (symmetric, `⟪S x, x⟫ ≥ 0`) with `S ∘ S = K`.  Built along a Hilbert basis of
eigenvectors (`exists_eigen_hilbertBasis`): the eigenvalues lie in `[0, ‖K‖]` and `S` multiplies
the `i`-th coordinate by `√μ_i`. -/
theorem exists_isPositive_sqrt (K : E →L[ℝ] E) (hK : IsCompactOperator K) (hpos : K.IsPositive) :
    ∃ S : E →L[ℝ] E, S.IsPositive ∧ S ∘L S = K := by
  obtain ⟨ι, b, μ, hμ⟩ := exists_eigen_hilbertBasis K hK hpos.isSymmetric
  have hμi : ∀ i, μ i = ⟪K (b i), b i⟫ := by
    intro i
    rw [hμ i, real_inner_smul_left, real_inner_self_eq_norm_sq, b.orthonormal.1 i]
    ring
  have hμ0 : ∀ i, 0 ≤ μ i := fun i => by
    rw [hμi]
    have := hpos.re_inner_nonneg_left (b i)
    simpa using this
  have hμK : ∀ i, μ i ≤ ‖K‖ := fun i => by
    rw [hμi]
    calc ⟪K (b i), b i⟫ ≤ ‖K (b i)‖ * ‖b i‖ := real_inner_le_norm _ _
      _ ≤ ‖K‖ * ‖b i‖ * ‖b i‖ := by gcongr; exact K.le_opNorm _
      _ = ‖K‖ := by rw [b.orthonormal.1 i]; ring
  set c : ι → ℝ := fun i => Real.sqrt (μ i)
  have hC : 0 ≤ Real.sqrt ‖K‖ := Real.sqrt_nonneg _
  have hc : ∀ i, |c i| ≤ Real.sqrt ‖K‖ := fun i => by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (hμK i)
  set S := basisDiag b c hC hc
  have hcoord : ∀ x i, ⟪b i, S x⟫ = c i * ⟪b i, x⟫ := inner_basisDiag b c hC hc
  refine ⟨S, ⟨fun x y => ?_, fun x => ?_⟩, ?_⟩
  · change ⟪S x, y⟫ = ⟪x, S y⟫
    rw [inner_basisDiag_left, real_inner_comm, inner_basisDiag_left]
    congr 1
    funext i
    rw [real_inner_comm x, real_inner_comm (b i) y]
    ring
  · rw [ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real, inner_basisDiag_left]
    refine tsum_nonneg fun i => ?_
    rw [real_inner_comm x (b i), mul_assoc]
    exact mul_nonneg (Real.sqrt_nonneg _) (mul_self_nonneg _)
  · ext1 x
    refine eq_of_inner_basis b fun i => ?_
    have hsym : ⟪K (b i), x⟫ = ⟪b i, K x⟫ := hpos.isSymmetric (b i) x
    rw [ContinuousLinearMap.comp_apply, hcoord, hcoord, ← mul_assoc,
      Real.mul_self_sqrt (hμ0 i), ← hsym, hμ i, real_inner_smul_left]

end StratonovichHAMSecondMoment.CameronTemporal
