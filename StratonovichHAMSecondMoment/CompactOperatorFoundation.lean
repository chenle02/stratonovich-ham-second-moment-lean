module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L16, item L16-B1 (foundation part; approved by Le on 2026-11-20).  General compactness
lemmas for real (and `RCLike`) operators used by the Cameron-map chain: items B1, B2 and C.
The frozen signatures are those of `docs/l16/INTERFACE.md`, section B1 (interface commit
1e9c544).

TeX anchors (revision 0788ddee, book 1.1.0, read with `git show 0788ddee:notes/...`; the same
line numbers at edf7085f, book 1.1.3):
* `integrated_compact_gaussian.tex` lines 512-519 (`P:cutoff-singular-values`, Step 1: "finite
  dimensional images have finite nets of each positive radius, and norm approximation transfers
  those nets to the limiting image of the unit ball"): `isCompactOperator_of_tendsto_finiteRank`;
* `integrated_cameron_mean.tex` lines 225-237 and proof 239-314 (`P:cameron-temporal-map`: the
  kernel operator `K` with an `L²` truncation, `K^{1/2}` compact): `isCompactOperator_of_L2_kernel`,
  `isCompactOperator_of_adjoint_comp_self`;
* `integrated_cameron_mean.tex` lines 152-163 (`P:cameron-spatial-map`, Step 3: compact
  operator values): `isCompactOperator_adjoint`.

Main results:
* `isCompactOperator_of_finiteDimensional_range`, `isCompactOperator_of_tendsto_finiteRank`;
* `isCompactOperator_of_summable_sq` (Hilbert-Schmidt route over a Hilbert basis);
* `isCompactOperator_of_sq_le` (domination `‖S x‖² ≤ ‖K x‖ ‖x‖`),
  `isCompactOperator_of_adjoint_comp_self`, `isCompactOperator_adjoint`;
* the integral operator of an `L²(μ ⊗ μ)` kernel: `L2KernelOp` with
  `L2KernelOp_ae`, `norm_L2KernelOp_le` (`‖T_k‖ ≤ ‖k‖₂`), and
  `isCompactOperator_of_L2_kernel` (frozen signature; `μ` σ-finite).

Lean proof route of the `L²`-kernel lemma (the TeX uses it without proof): for a.e. `x` the
fibre `k(x,·)` lies in `L²(μ)` (Tonelli on `k²`); then `(T f)(x) = ⟪k(x,·), f⟫` a.e.; for a
Hilbert basis `(b_i)` and a finite set `s`,
`∑_{i∈s} ‖T b_i‖² = ∫ ∑_{i∈s} ⟪k(x,·), b_i⟫² dx ≤ ∫ ‖k(x,·)‖² dx = ‖k‖²` (Bessel pointwise,
Fubini), so the Hilbert-Schmidt sum is finite.

No `sorry`, no axiom; every theorem depends only on `propext`, `Classical.choice`, `Quot.sound`.
-/
public import Mathlib

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Filter Topology Set Metric
open scoped RealInnerProductSpace

namespace StratonovichHAMSecondMoment.CompactOperatorFoundation

/-! ### Finite-rank approximation -/

section FiniteRank

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A continuous linear map with finite-dimensional range is compact. -/
theorem isCompactOperator_of_finiteDimensional_range (f : E →L[ℝ] F)
    [FiniteDimensional ℝ (LinearMap.range (f : E →ₗ[ℝ] F))] : IsCompactOperator f := by
  have h1 : IsCompactOperator
      (f.codRestrict (LinearMap.range (f : E →ₗ[ℝ] F)) (fun x => LinearMap.mem_range_self _ x)) :=
    isCompactOperator_of_locallyCompactSpace_dom _
  exact h1.continuous_comp (LinearMap.range (f : E →ₗ[ℝ] F)).subtypeL.continuous

/-- **A norm limit of finite-rank continuous linear maps is compact**
(`integrated_compact_gaussian.tex` lines 516-519 at revision edf7085f (book 1.1.3)). -/
theorem isCompactOperator_of_tendsto_finiteRank [CompleteSpace F] {ι : Type*} {l : Filter ι}
    [l.NeBot] {A : ι → E →L[ℝ] F} {T : E →L[ℝ] F} (hA : Tendsto A l (𝓝 T))
    (hfin : ∀ i, FiniteDimensional ℝ (LinearMap.range (A i : E →ₗ[ℝ] F))) :
    IsCompactOperator T :=
  isCompactOperator_of_tendsto hA (Eventually.of_forall fun i => by
    have := hfin i
    exact isCompactOperator_of_finiteDimensional_range (A i))

end FiniteRank

/-! ### The Hilbert-Schmidt route -/

section HilbertSchmidt

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type*}

/-- The finite-section approximant `x ↦ ∑_{i ∈ s} ⟪b i, x⟫ T (b i)`. -/
def hsApprox (b : HilbertBasis ι ℝ E) (T : E →L[ℝ] F) (s : Finset ι) : E →L[ℝ] F :=
  ∑ i ∈ s, (innerSL ℝ (b i)).smulRight (T (b i))

/-- Auxiliary: the value of the finite-section approximant. -/
theorem hsApprox_apply (b : HilbertBasis ι ℝ E) (T : E →L[ℝ] F) (s : Finset ι) (x : E) :
    hsApprox b T s x = ∑ i ∈ s, (inner ℝ (b i) x) • T (b i) := by
  simp [hsApprox]

/-- Auxiliary: the finite-section approximant has finite rank. -/
theorem finiteDimensional_range_hsApprox (b : HilbertBasis ι ℝ E) (T : E →L[ℝ] F)
    (s : Finset ι) :
    FiniteDimensional ℝ (LinearMap.range (hsApprox b T s : E →ₗ[ℝ] F)) := by
  classical
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℝ
    ((s.image fun i => T (b i) : Finset F) : Set F)) ?_
  rintro _ ⟨x, rfl⟩
  change hsApprox b T s x ∈ _
  rw [hsApprox_apply]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  simp only [Finset.coe_image]
  exact ⟨i, hi, rfl⟩

/-- Auxiliary (tail estimate): `‖T - approx s‖ ≤ ε` once `s` contains a set `s₀` outside which
the Hilbert-Schmidt sum is at most `ε²`. -/
theorem norm_sub_hsApprox_le [CompleteSpace E] (b : HilbertBasis ι ℝ E) (T : E →L[ℝ] F) {s₀ : Finset ι} {ε : ℝ}
    (hε : 0 ≤ ε) (htail : ∀ t : Finset ι, Disjoint t s₀ → ∑ i ∈ t, ‖T (b i)‖ ^ 2 ≤ ε ^ 2)
    {s : Finset ι} (hs : s₀ ⊆ s) : ‖T - hsApprox b T s‖ ≤ ε := by
  classical
  refine ContinuousLinearMap.opNorm_le_bound _ hε fun x => ?_
  have hsum : HasSum (fun i => (inner ℝ (b i) x) • T (b i)) (T x) := by
    have := (b.hasSum_repr x).mapL T
    simpa [b.repr_apply_apply, map_smul] using this
  have h0 : Tendsto (fun t : Finset ι => ∑ i ∈ t, (inner ℝ (b i) x) • T (b i)) atTop
      (𝓝 (T x)) := hsum
  have hlim : Tendsto
      (fun t : Finset ι => ‖∑ i ∈ t, (inner ℝ (b i) x) • T (b i) - hsApprox b T s x‖) atTop
      (𝓝 ‖(T - hsApprox b T s) x‖) := by
    rw [sub_apply]
    exact (h0.sub_const _).norm
  refine le_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop s] with t ht
  rw [hsApprox_apply, ← Finset.sum_sdiff ht, add_sub_cancel_right]
  set u := t \ s
  have hu : Disjoint u s₀ := Finset.sdiff_disjoint.mono_right hs
  calc ‖∑ i ∈ u, (inner ℝ (b i) x) • T (b i)‖
      ≤ ∑ i ∈ u, ‖inner ℝ (b i) x‖ * ‖T (b i)‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun i _ => norm_smul _ _
    _ ≤ √(∑ i ∈ u, ‖inner ℝ (b i) x‖ ^ 2) * √(∑ i ∈ u, ‖T (b i)‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ √(‖x‖ ^ 2) * √(ε ^ 2) := by
        gcongr
        · exact b.orthonormal.sum_inner_products_le x
        · exact htail u hu
    _ = ε * ‖x‖ := by
        rw [Real.sqrt_sq (norm_nonneg x), Real.sqrt_sq hε, mul_comm]

/-- **Hilbert-Schmidt route**: if `∑ ‖T (b i)‖²` is finite over a Hilbert basis, `T` is
compact (it is the norm limit of its finite sections). -/
theorem isCompactOperator_of_summable_sq [CompleteSpace E] [CompleteSpace F] (b : HilbertBasis ι ℝ E)
    (T : E →L[ℝ] F) (hT : Summable fun i => ‖T (b i)‖ ^ 2) : IsCompactOperator T := by
  have hA : Tendsto (hsApprox b T) atTop (𝓝 T) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨s₀, hs₀⟩ := hT.vanishing (Iio_mem_nhds (by positivity : (0 : ℝ) < (ε / 2) ^ 2))
    filter_upwards [eventually_ge_atTop s₀] with s hs
    rw [dist_comm, dist_eq_norm]
    have := norm_sub_hsApprox_le b T (by positivity : (0 : ℝ) ≤ ε / 2)
      (fun t ht => le_of_lt (hs₀ t ht)) hs
    linarith
  exact isCompactOperator_of_tendsto_finiteRank hA (finiteDimensional_range_hsApprox b T)

end HilbertSchmidt

/-! ### Domination, `S† S` and adjoints -/

section Domination

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- **Domination lemma**: `‖S x‖² ≤ ‖K x‖ ‖x‖` and `K` compact imply `S` compact. -/
theorem isCompactOperator_of_sq_le [CompleteSpace G] (S : E →L[𝕜] F) (K : E →L[𝕜] G) (hK : IsCompactOperator K)
    (hS : ∀ x, ‖S x‖ ^ 2 ≤ ‖K x‖ * ‖x‖) : IsCompactOperator S := by
  classical
  refine (isCompactOperator_iff_isCompact_closure_image_closedBall
    (S : E →ₛₗ[RingHom.id 𝕜] F) zero_lt_one).mpr ?_
  have hKtb : TotallyBounded (K '' closedBall 0 1) :=
    ((hK.isCompact_closure_image_closedBall 1).totallyBounded).subset subset_closure
  suffices htb : TotallyBounded (S '' closedBall 0 1) from
    htb.closure.isCompact_of_isClosed isClosed_closure
  rw [Metric.totallyBounded_iff]
  intro ε hε
  have hδ : (0 : ℝ) < ε ^ 2 / 4 := by positivity
  obtain ⟨t, htK, htf, hcov⟩ := Metric.finite_approx_of_totallyBounded hKtb _ hδ
  let pre : G → E := fun y => if h : y ∈ K '' closedBall (0 : E) 1 then h.choose else 0
  have hpre : ∀ y ∈ t, pre y ∈ closedBall (0 : E) 1 ∧ K (pre y) = y := by
    intro y hy
    have h : y ∈ K '' closedBall (0 : E) 1 := htK hy
    simp only [pre, h, dite_true]
    exact h.choose_spec
  refine ⟨(fun y => S (pre y)) '' t, htf.image _, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hyt, hy⟩ := mem_iUnion₂.mp (hcov (mem_image_of_mem K hx))
  obtain ⟨hpb, hKp⟩ := hpre y hyt
  refine mem_iUnion₂.mpr ⟨S (pre y), mem_image_of_mem _ hyt, ?_⟩
  rw [mem_ball, dist_eq_norm, ← map_sub]
  have hx1 : ‖x‖ ≤ 1 := by simpa using hx
  have hp1 : ‖pre y‖ ≤ 1 := by simpa using hpb
  have hKd : ‖K (x - pre y)‖ < ε ^ 2 / 4 := by
    rw [map_sub, hKp, ← dist_eq_norm]
    exact hy
  have hd : ‖x - pre y‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
  have hsq : ‖S (x - pre y)‖ ^ 2 < ε ^ 2 := by
    calc ‖S (x - pre y)‖ ^ 2 ≤ ‖K (x - pre y)‖ * ‖x - pre y‖ := hS _
      _ ≤ ε ^ 2 / 4 * 2 := by gcongr
      _ < ε ^ 2 := by linarith
  exact abs_lt_of_sq_lt_sq' hsq hε.le |>.2 |> fun h => by
    simpa [abs_of_nonneg (norm_nonneg _)] using
      (abs_lt.mpr ⟨by linarith [norm_nonneg (S (x - pre y))], h⟩)

end Domination

section Adjoint

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **`S† S` compact implies `S` compact** (over `ℝ` as well): `‖S x‖² = ⟪S† S x, x⟫`. -/
theorem isCompactOperator_of_adjoint_comp_self (S : E →L[𝕜] F)
    (h : IsCompactOperator (ContinuousLinearMap.adjoint S ∘L S)) : IsCompactOperator S := by
  refine isCompactOperator_of_sq_le S _ h fun x => ?_
  have h1 : (‖S x‖ : 𝕜) ^ 2 = inner 𝕜 (ContinuousLinearMap.adjoint S (S x)) x := by
    rw [ContinuousLinearMap.adjoint_inner_left, inner_self_eq_norm_sq_to_K]
  have h2 : ‖S x‖ ^ 2 = ‖inner 𝕜 ((ContinuousLinearMap.adjoint S ∘L S) x) x‖ := by
    rw [ContinuousLinearMap.comp_apply, ← h1]
    simp
  rw [h2]
  exact norm_inner_le_norm _ _

/-- **Schauder for Hilbert spaces**: the adjoint of a compact operator is compact. -/
theorem isCompactOperator_adjoint (T : E →L[𝕜] F) (hT : IsCompactOperator T) :
    IsCompactOperator (ContinuousLinearMap.adjoint T) := by
  apply isCompactOperator_of_adjoint_comp_self
  rw [ContinuousLinearMap.adjoint_adjoint]
  exact hT.comp_clm (ContinuousLinearMap.adjoint T)

end Adjoint

/-! ### Integral operators with an `L²(μ ⊗ μ)` kernel -/

section L2Kernel

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Auxiliary: `‖v‖² = ∫ v²` in real `L²(μ)`. -/
theorem norm_sq_eq_integral (v : Lp ℝ 2 μ) : ‖v‖ ^ 2 = ∫ x, (v : α → ℝ) x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [sq]

/-- Auxiliary: `⟪v, f⟫ = ∫ v f` in real `L²(μ)`. -/
theorem inner_eq_integral (v f : Lp ℝ 2 μ) :
    ⟪v, f⟫ = ∫ x, (v : α → ℝ) x * (f : α → ℝ) x ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [mul_comm]

/-- The fibre `k(x,·)` as an element of `L²(μ)` (`0` where it is not square integrable). -/
def kFibre (k : α × α → ℝ) (x : α) : Lp ℝ 2 μ :=
  open Classical in
  if h : MemLp (fun y => k (x, y)) 2 μ then h.toLp _ else 0

/-- Auxiliary: on the good fibres, `kFibre` is `k(x,·)` a.e. -/
theorem kFibre_coe {k : α × α → ℝ} {x : α} (hx : MemLp (fun y => k (x, y)) 2 μ) :
    (kFibre (μ := μ) k x : α → ℝ) =ᵐ[μ] fun y => k (x, y) := by
  simp only [kFibre, hx, ↓reduceDIte]
  exact hx.coeFn_toLp

variable [SigmaFinite μ]

/-- Auxiliary: almost every fibre of an `L²(μ ⊗ μ)` kernel is in `L²(μ)`. -/
theorem ae_memLp_fibre {k : α × α → ℝ} (hk : MemLp k 2 (μ.prod μ)) :
    ∀ᵐ x ∂μ, MemLp (fun y => k (x, y)) 2 μ := by
  have hsq : Integrable (fun p => k p ^ 2) (μ.prod μ) :=
    (memLp_two_iff_integrable_sq hk.aestronglyMeasurable).1 hk
  filter_upwards [hsq.prod_right_ae, hk.aestronglyMeasurable.prodMk_left] with x hx hm
  exact (memLp_two_iff_integrable_sq hm).2 hx

/-- Auxiliary: `‖k(x,·)‖² = ∫ k(x,y)² dy` for a.e. `x`. -/
theorem ae_norm_kFibre_sq {k : α × α → ℝ} (hk : MemLp k 2 (μ.prod μ)) :
    ∀ᵐ x ∂μ, ‖kFibre (μ := μ) k x‖ ^ 2 = ∫ y, k (x, y) ^ 2 ∂μ := by
  filter_upwards [ae_memLp_fibre hk] with x hx
  rw [norm_sq_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [kFibre_coe hx] with y hy
  rw [hy]

/-- Auxiliary: `⟪k(x,·), f⟫ = ∫ k(x,y) f(y) dy` for a.e. `x`. -/
theorem ae_inner_kFibre {k : α × α → ℝ} (hk : MemLp k 2 (μ.prod μ)) (f : Lp ℝ 2 μ) :
    ∀ᵐ x ∂μ, ⟪kFibre (μ := μ) k x, f⟫ = ∫ y, k (x, y) * (f : α → ℝ) y ∂μ := by
  filter_upwards [ae_memLp_fibre hk] with x hx
  rw [inner_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [kFibre_coe hx] with y hy
  rw [hy]

/-- Auxiliary: `x ↦ ∫ k(x,·)²` is integrable, with integral `‖k‖²`. -/
theorem integrable_fibre_sq {k : α × α → ℝ} (hk : MemLp k 2 (μ.prod μ)) :
    Integrable (fun x => ∫ y, k (x, y) ^ 2 ∂μ) μ ∧
      ∫ x, (∫ y, k (x, y) ^ 2 ∂μ) ∂μ = ‖hk.toLp k‖ ^ 2 := by
  have hsq : Integrable (fun p => k p ^ 2) (μ.prod μ) :=
    (memLp_two_iff_integrable_sq hk.aestronglyMeasurable).1 hk
  refine ⟨hsq.integral_prod_left, ?_⟩
  rw [← integral_prod _ hsq, norm_sq_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [hk.coeFn_toLp] with p hp
  rw [hp]

/-- Auxiliary: `x ↦ ∫ k(x,y) f(y) dy` is a.e. strongly measurable. -/
theorem aestronglyMeasurable_kernel_integral {k : α × α → ℝ} (hk : MemLp k 2 (μ.prod μ))
    (f : Lp ℝ 2 μ) :
    AEStronglyMeasurable (fun x => ∫ y, k (x, y) * (f : α → ℝ) y ∂μ) μ := by
  have h : AEStronglyMeasurable (fun p : α × α => k p * (f : α → ℝ) p.2) (μ.prod μ) :=
    hk.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f).comp_snd
  exact h.integral_prod_right'

/-- The kernel function `x ↦ ⟪k(x,·), f⟫` (equal a.e. to `∫ k(x,y) f(y) dy`). -/
def kernelFun (k : α × α → ℝ) (f : Lp ℝ 2 μ) (x : α) : ℝ := ⟪kFibre (μ := μ) k x, f⟫

/-- Auxiliary: `kernelFun` is in `L²(μ)`, with `∫ (kernelFun f)² ≤ ‖k‖² ‖f‖²`. -/
theorem memLp_kernelFun {k : α × α → ℝ} (hk : MemLp k 2 (μ.prod μ)) (f : Lp ℝ 2 μ) :
    MemLp (kernelFun (μ := μ) k f) 2 μ ∧
      ∫ x, kernelFun (μ := μ) k f x ^ 2 ∂μ ≤ ‖hk.toLp k‖ ^ 2 * ‖f‖ ^ 2 := by
  obtain ⟨hint, heq⟩ := integrable_fibre_sq hk
  have hm : AEStronglyMeasurable (kernelFun (μ := μ) k f) μ :=
    (aestronglyMeasurable_kernel_integral hk f).congr
      ((ae_inner_kFibre hk f).mono fun x hx => hx.symm)
  have hbd : ∀ᵐ x ∂μ, kernelFun (μ := μ) k f x ^ 2 ≤ (∫ y, k (x, y) ^ 2 ∂μ) * ‖f‖ ^ 2 := by
    filter_upwards [ae_norm_kFibre_sq hk] with x hx
    rw [← hx, ← mul_pow]
    have := abs_real_inner_le_norm (kFibre (μ := μ) k x) f
    rw [kernelFun, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have hsq : Integrable (fun x => kernelFun (μ := μ) k f x ^ 2) μ :=
    (hint.mul_const (‖f‖ ^ 2)).mono' (hm.pow 2)
      (hbd.mono fun x hx => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hx)
  refine ⟨(memLp_two_iff_integrable_sq hm).2 hsq, ?_⟩
  calc ∫ x, kernelFun (μ := μ) k f x ^ 2 ∂μ ≤ ∫ x, (∫ y, k (x, y) ^ 2 ∂μ) * ‖f‖ ^ 2 ∂μ :=
        integral_mono_ae hsq (hint.mul_const _) hbd
    _ = ‖hk.toLp k‖ ^ 2 * ‖f‖ ^ 2 := by rw [integral_mul_const, heq]

/-- The integral operator `T_k`, linear part. -/
def L2KernelLin {k : α × α → ℝ} (hk : MemLp k 2 (μ.prod μ)) : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ where
  toFun f := (memLp_kernelFun hk f).1.toLp _
  map_add' f g := by
    have e : kernelFun (μ := μ) k (f + g) = kernelFun k f + kernelFun k g := by
      funext x; simp [kernelFun, inner_add_right]
    simp_rw [e]
    exact MemLp.toLp_add _ _
  map_smul' c f := by
    have e : kernelFun (μ := μ) k (c • f) = c • kernelFun k f := by
      funext x; simp [kernelFun, inner_smul_right]
    simp_rw [e]
    exact MemLp.toLp_const_smul _ _

/-- **The integral operator `T_k f(x) = ∫ k(x,y) f(y) μ(dy)` of an `L²(μ ⊗ μ)` kernel** on
`L²(μ)`, with `‖T_k‖ ≤ ‖k‖₂` (`norm_L2KernelOp_le`). -/
def L2KernelOp {k : α × α → ℝ} (hk : MemLp k 2 (μ.prod μ)) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (L2KernelLin hk).mkContinuous ‖hk.toLp k‖ fun f => by
    have h := (memLp_kernelFun hk f).2
    have h1 : ‖L2KernelLin hk f‖ ^ 2 ≤ (‖hk.toLp k‖ * ‖f‖) ^ 2 := by
      rw [mul_pow, norm_sq_eq_integral]
      refine le_trans (le_of_eq ?_) h
      refine integral_congr_ae ?_
      filter_upwards [(memLp_kernelFun hk f).1.coeFn_toLp] with x hx
      simp only [L2KernelLin, LinearMap.coe_mk, AddHom.coe_mk]
      rw [hx]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h1

/-- **The kernel formula**: `T_k f = ∫ k(·,y) f(y) dy` a.e. -/
theorem L2KernelOp_ae {k : α × α → ℝ} (hk : MemLp k 2 (μ.prod μ)) (f : Lp ℝ 2 μ) :
    (L2KernelOp hk f : α → ℝ) =ᵐ[μ] fun x => ∫ y, k (x, y) * (f : α → ℝ) y ∂μ := by
  filter_upwards [(memLp_kernelFun hk f).1.coeFn_toLp, ae_inner_kFibre hk f] with x hx hx'
  simp only [L2KernelOp, LinearMap.mkContinuous_apply, L2KernelLin, LinearMap.coe_mk,
    AddHom.coe_mk]
  rw [hx, kernelFun, hx']

/-- **`‖T_k‖ ≤ ‖k‖_{L²(μ⊗μ)}`.** -/
theorem norm_L2KernelOp_le {k : α × α → ℝ} (hk : MemLp k 2 (μ.prod μ)) :
    ‖L2KernelOp hk‖ ≤ ‖hk.toLp k‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

/-- **An integral operator with an `L²(μ ⊗ μ)` kernel is compact** (Hilbert-Schmidt), on a
σ-finite space: Bessel on the fibres `k(x,·)` and Fubini give `∑ ‖T b_i‖² ≤ ‖k‖₂²` over a Hilbert
basis.  (Used for the truncations `K_ε` of `P:cameron-temporal-map`,
`integrated_cameron_mean.tex` lines 239-298 at revision edf7085f (book 1.1.3).) -/
theorem isCompactOperator_of_L2_kernel (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (k : α × α → ℝ)
    (hk : MemLp k 2 (μ.prod μ))
    (hT : ∀ f : Lp ℝ 2 μ, (T f : α → ℝ) =ᵐ[μ] fun x => ∫ y, k (x, y) * f y ∂μ) :
    IsCompactOperator T := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℝ (Lp ℝ 2 μ)
  refine isCompactOperator_of_summable_sq b T ?_
  obtain ⟨hint, heq⟩ := integrable_fibre_sq hk
  refine summable_of_sum_le (fun i => sq_nonneg _) (c := ‖hk.toLp k‖ ^ 2) fun s => ?_
  have hTi : ∀ i, ‖T (b i)‖ ^ 2 = ∫ x, kernelFun (μ := μ) k (b i) x ^ 2 ∂μ := by
    intro i
    rw [norm_sq_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [hT (b i), ae_inner_kFibre hk (b i)] with x hx hx'
    rw [hx, kernelFun, hx']
  have hint_i : ∀ i, Integrable (fun x => kernelFun (μ := μ) k (b i) x ^ 2) μ := fun i =>
    (memLp_two_iff_integrable_sq (memLp_kernelFun hk (b i)).1.aestronglyMeasurable).1 (memLp_kernelFun hk (b i)).1
  simp_rw [hTi]
  rw [← integral_finsetSum s fun i _ => hint_i i, ← heq]
  refine integral_mono_ae (integrable_finsetSum s fun i _ => hint_i i) hint ?_
  filter_upwards [ae_norm_kFibre_sq hk] with x hx
  rw [← hx]
  have hb := b.orthonormal.sum_inner_products_le (kFibre (μ := μ) k x) (s := s)
  refine le_trans (le_of_eq ?_) hb
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [kernelFun, real_inner_comm, Real.norm_eq_abs, sq_abs]

end L2Kernel

end StratonovichHAMSecondMoment.CompactOperatorFoundation
