module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

The finite Gaussian comparison used in the proof of
`P:masked-noise-completion` (Completion on the same noise) of
`notes/integrated_covariance_foundation.tex` (revision a284420; statement
lines 188-206, the comparison sentence lines 201-205; proof lines 208-247, the
comparison argument lines 239-246).

Formalized (a standalone finite result supporting the label, not the label):
* `gaussian_seminorm_moment_le` (and `gaussian_seminorm_moment_le_paper`): for
  a finite index type `ι`, real `ι × ι` matrices `A`, `B` with `A` positive
  semidefinite and `B - A` positive semidefinite (`A ≤ B` in the Loewner
  order, TeX lines 240-241: `bᵀAb ≤ bᵀBb` for every real `b`), every seminorm `N`
  on `ℝ^ι` (`EuclideanSpace ℝ ι`) and every real `p ≥ 1`, the functions
  `x ↦ N(x)^p` are integrable against the centered Gaussian laws
  `N(0,A)` and `N(0,B)` (`ProbabilityTheory.multivariateGaussian`), and
  `∫ N(x)^p dN(0,A) ≤ ∫ N(x)^p dN(0,B)` (TeX line 244:
  `E‖X‖^p ≤ E‖X+Z‖^p`, with finiteness of both sides, lines 245-246).

Outside this module (a D1 boundary, stated here and in the wrapper): the
identification of `A` with the covariance matrix of the masked noise
evaluations `W(ζ_R F_i)` and of `B` with the auxiliary Gram matrix of
`N_R` (TeX lines 201-203 and 239-240), the noise identity
`E:masked-actual-noise-norm`, the contraction extension and its joint
Gaussianity (lines 199-201, 230-237).  None of these is formalized; the
theorem below is the finite comparison those steps feed into.

Supplied inputs: none.

Implicit hypotheses made explicit: the moments are Bochner integrals, so both
integrability statements are conclusions; `N` is an arbitrary seminorm (its
continuity in finite dimension is proved, `seminorm_continuous`), which
contains every norm of the TeX.

Proof route.  As in the TeX (lines 241-246), with the coupling expressed by
measures: `N(0,B) = N(0,A) ∗ N(0,B-A)` (`multivariateGaussian_conv`, by
characteristic functions, `Measure.ext_of_charFun`) replaces "diagonalizing
`B - A` constructs `Z` ... on a product space", and the integral against the
convolution is the iterated integral over the product.  For fixed `x`,
`y ↦ N(x+y)^p` is convex and `N(0,B-A)` is centered, so Jensen's inequality
(`ConvexOn.map_integral_le`) gives `N(x)^p ≤ ∫ N(x+y)^p dN(0,B-A)(y)`; this is
the TeX's conditional Jensen step.  Finite moments come from
`IsGaussian.memLp_id` and the bound `N(x) ≤ C‖x‖`.
-/

public import Mathlib

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set

namespace StratonovichHAMSecondMoment.GaussianComparison

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Auxiliary to the Lean proof route (the coupling of TeX lines 242-244 as an
identity of laws): for `A` and `B - A` positive semidefinite,
`N(0,B) = N(0,A) ∗ N(0,B-A)`. -/
theorem multivariateGaussian_conv {A B : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hBA : (B - A).PosSemidef) :
    multivariateGaussian (0 : EuclideanSpace ℝ ι) B =
      (multivariateGaussian 0 A) ∗ (multivariateGaussian 0 (B - A)) := by
  have hB : B.PosSemidef := by simpa using hA.add hBA
  apply Measure.ext_of_charFun
  funext x
  rw [charFun_conv, charFun_multivariateGaussian hB, charFun_multivariateGaussian hA,
    charFun_multivariateGaussian hBA]
  rw [← Complex.exp_add]
  congr 1
  simp [Matrix.sub_mulVec]
  ring

/-- Auxiliary: a seminorm on `ℝ^ι` is bounded by a multiple of the Euclidean norm,
`N(x) ≤ (∑ᵢ N(eᵢ)) ‖x‖`. -/
theorem seminorm_le_mul_norm (N : Seminorm ℝ (EuclideanSpace ℝ ι))
    (x : EuclideanSpace ℝ ι) :
    N x ≤ (∑ i, N (EuclideanSpace.single i (1 : ℝ))) * ‖x‖ := by
  have hx : x = ∑ i, x i • EuclideanSpace.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  calc N x = N (∑ i, x i • EuclideanSpace.single i (1 : ℝ)) := by rw [← hx]
    _ ≤ ∑ i, N (x i • EuclideanSpace.single i (1 : ℝ)) := Finset.map_sum_le_sum N Finset.univ _
    _ = ∑ i, ‖x i‖ * N (EuclideanSpace.single i (1 : ℝ)) := by
        simp only [map_smul_eq_mul]
    _ ≤ ∑ i, ‖x‖ * N (EuclideanSpace.single i (1 : ℝ)) :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (PiLp.norm_apply_le x i) (apply_nonneg N _)
    _ = _ := by rw [← Finset.mul_sum, mul_comm]

/-- Auxiliary: every seminorm on `ℝ^ι` is continuous. -/
theorem seminorm_continuous (N : Seminorm ℝ (EuclideanSpace ℝ ι)) : Continuous N := by
  set C := ∑ i, N (EuclideanSpace.single i (1 : ℝ))
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ => apply_nonneg N _
  refine (LipschitzWith.of_dist_le_mul (K := ⟨C, hC⟩) fun x y => ?_).continuous
  simp only [dist_eq_norm]
  exact (abs_sub_map_le_sub N x y).trans (seminorm_le_mul_norm N _)

/-- Auxiliary: for a Gaussian law `μ` on `ℝ^ι`, a seminorm `N` and `p ≥ 0`, the
moment function `x ↦ N(x)^p` is `μ`-integrable. -/
theorem integrable_seminorm_rpow (μ : Measure (EuclideanSpace ℝ ι)) [IsGaussian μ]
    (N : Seminorm ℝ (EuclideanSpace ℝ ι)) {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun x => N x ^ p) μ := by
  set C := ∑ i, N (EuclideanSpace.single i (1 : ℝ))
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ => apply_nonneg N _
  have hI : Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖ ^ p) μ := by
    rcases hp.eq_or_lt with hp0 | hp0
    · simp only [← hp0, Real.rpow_zero]
      exact integrable_const _
    have hm := IsGaussian.memLp_id μ (ENNReal.ofReal p) ENNReal.ofReal_ne_top
    have := hm.integrable_norm_rpow (by simpa using hp0) ENNReal.ofReal_ne_top
    simpa [ENNReal.toReal_ofReal hp] using this
  have hmeas : AEStronglyMeasurable (fun x => N x ^ p) μ :=
    ((seminorm_continuous N).rpow_const fun _ => Or.inr hp).aestronglyMeasurable
  refine (hI.const_mul (C ^ p)).mono' hmeas (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (apply_nonneg N x) p), ← Real.mul_rpow hC
    (norm_nonneg x)]
  exact Real.rpow_le_rpow (apply_nonneg N x) (seminorm_le_mul_norm N x) hp

omit [Fintype ι] [DecidableEq ι] in
/-- Auxiliary: for fixed `x`, `y ↦ N(x+y)^p` is convex when `p ≥ 1`. -/
theorem convexOn_seminorm_rpow (N : Seminorm ℝ (EuclideanSpace ℝ ι))
    (x : EuclideanSpace ℝ ι) {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ univ (fun y => N (x + y) ^ p) := by
  refine ⟨convex_univ, fun y _ z _ a b ha hb hab => ?_⟩
  have hxyz : x + (a • y + b • z) = a • (x + y) + b • (x + z) := by
    rw [smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul]
  have h1 : N (x + (a • y + b • z)) ≤ a * N (x + y) + b * N (x + z) := by
    rw [hxyz]
    refine (map_add_le_add N _ _).trans ?_
    rw [map_smul_eq_mul, map_smul_eq_mul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
  have h2 := (convexOn_rpow hp).2 (mem_Ici.2 (apply_nonneg N (x + y)))
    (mem_Ici.2 (apply_nonneg N (x + z))) ha hb hab
  simp only [smul_eq_mul] at h2 ⊢
  exact (Real.rpow_le_rpow (apply_nonneg N _) h1 (by linarith)).trans h2

/-- The finite Gaussian comparison in the proof of `P:masked-noise-completion`
(`notes/integrated_covariance_foundation.tex`, a284420, lines 239-246; stated in
lines 201-205).  For real `ι × ι` matrices with `A` and `B - A` positive
semidefinite, every seminorm `N` on `ℝ^ι` and every real `p ≥ 1`: `N(x)^p` is
integrable against `N(0,A)` and `N(0,B)`, and
`∫ N(x)^p dN(0,A) ≤ ∫ N(x)^p dN(0,B)`. -/
theorem gaussian_seminorm_moment_le {A B : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hBA : (B - A).PosSemidef) (N : Seminorm ℝ (EuclideanSpace ℝ ι)) {p : ℝ}
    (hp : 1 ≤ p) :
    Integrable (fun x => N x ^ p) (multivariateGaussian (0 : EuclideanSpace ℝ ι) A) ∧
      Integrable (fun x => N x ^ p) (multivariateGaussian (0 : EuclideanSpace ℝ ι) B) ∧
      ∫ x, N x ^ p ∂(multivariateGaussian (0 : EuclideanSpace ℝ ι) A) ≤
        ∫ x, N x ^ p ∂(multivariateGaussian (0 : EuclideanSpace ℝ ι) B) := by
  set f : EuclideanSpace ℝ ι → ℝ := fun x => N x ^ p with hf
  set μA := multivariateGaussian (0 : EuclideanSpace ℝ ι) A
  set ν := multivariateGaussian (0 : EuclideanSpace ℝ ι) (B - A)
  have hiA : Integrable f μA := integrable_seminorm_rpow μA N (by linarith)
  have hiB : Integrable f (multivariateGaussian (0 : EuclideanSpace ℝ ι) B) :=
    integrable_seminorm_rpow _ N (by linarith)
  refine ⟨hiA, hiB, ?_⟩
  have hconv := multivariateGaussian_conv hA hBA
  have hiC : Integrable f (μA ∗ ν) := hconv ▸ hiB
  rw [hconv, integral_conv hiC]
  have hprod : Integrable (fun q : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => f (q.1 + q.2))
      (μA.prod ν) :=
    hiC.comp_measurable (f := fun q : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => q.1 + q.2)
      measurable_add
  have hae := hprod.prod_right_ae
  have hout := hprod.integral_prod_left
  refine integral_mono_ae hiA hout ?_
  filter_upwards [hae] with x hx
  have hcont : Continuous fun y => f (x + y) :=
    ((seminorm_continuous N).comp (continuous_const.add continuous_id)).rpow_const
      fun _ => Or.inr (by linarith)
  have hJ := (convexOn_seminorm_rpow N x hp).map_integral_le hcont.continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun _ => mem_univ _) (IsGaussian.integrable_id (μ := ν)) hx
  have h0 : ∫ y, id y ∂ν = 0 := integral_id_multivariateGaussian
  rw [h0, add_zero] at hJ
  exact hJ

/-- `P:masked-noise-completion`, finite comparison step
(`notes/integrated_covariance_foundation.tex`, a284420, statement lines 201-205,
proof lines 239-246), with the hypotheses of that step: `A` is a covariance
matrix (positive semidefinite) and `A ≤ B` in positive semidefinite order
(`(B - A).PosSemidef`, i.e. `bᵀAb ≤ bᵀBb` for every real `b`, lines 240-241).  For
`X ~ N(0,A)`, `X + Z ~ N(0,B)`, every seminorm (in particular every norm) `N`
and `p ≥ 1`, both moments `E N(X)^p`, `E N(X+Z)^p` are finite and
`E N(X)^p ≤ E N(X+Z)^p`.  Narrower than the label: the identification of `A`
and `B` with the masked covariance matrix and the auxiliary Gram matrix, and the
noise statements of the proposition, are outside Lean (D1). -/
theorem gaussian_seminorm_moment_le_paper {A B : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hAB : (B - A).PosSemidef) (N : Seminorm ℝ (EuclideanSpace ℝ ι)) (p : ℝ)
    (hp : 1 ≤ p) :
    Integrable (fun x => N x ^ p) (multivariateGaussian (0 : EuclideanSpace ℝ ι) A) ∧
      Integrable (fun x => N x ^ p) (multivariateGaussian (0 : EuclideanSpace ℝ ι) B) ∧
      ∫ x, N x ^ p ∂(multivariateGaussian (0 : EuclideanSpace ℝ ι) A) ≤
        ∫ x, N x ^ p ∂(multivariateGaussian (0 : EuclideanSpace ℝ ι) B) :=
  gaussian_seminorm_moment_le hA hAB N hp

/-- Auxiliary (calibration, used by the refutations): the coordinate seminorm
`x ↦ |xᵢ|` on `ℝ^ι`. -/
def coordSeminorm (i : ι) : Seminorm ℝ (EuclideanSpace ℝ ι) :=
  (normSeminorm ℝ ℝ).comp (EuclideanSpace.proj i : EuclideanSpace ℝ ι →L[ℝ] ℝ).toLinearMap

omit [Fintype ι] [DecidableEq ι] in
/-- Auxiliary (calibration). -/
theorem coordSeminorm_apply (i : ι) (x : EuclideanSpace ℝ ι) : coordSeminorm i x = |x i| := by
  simp [coordSeminorm]

/-- Auxiliary (calibration, used by the refutations): for positive semidefinite `S`,
`∫ |xᵢ|² dN(0,S)(x) = Sᵢᵢ`. -/
theorem integral_coord_sq {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (i : ι) :
    ∫ x, coordSeminorm i x ^ (2 : ℝ) ∂(multivariateGaussian (0 : EuclideanSpace ℝ ι) S) =
      S i i := by
  have hv := variance_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ ι)) hS i
  have hmean : ∫ x, x i ∂(multivariateGaussian (0 : EuclideanSpace ℝ ι) S) = 0 := by
    have h := (EuclideanSpace.proj i : EuclideanSpace ℝ ι →L[ℝ] ℝ).integral_comp_comm
      (IsGaussian.integrable_id (μ := multivariateGaussian (0 : EuclideanSpace ℝ ι) S))
    simpa using h
  rw [variance_of_integral_eq_zero (by fun_prop) hmean] at hv
  rw [← hv]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [coordSeminorm_apply]

end StratonovichHAMSecondMoment.GaussianComparison
