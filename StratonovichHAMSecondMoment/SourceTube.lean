module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Three labelled results at manuscript revision 39f2597a.

1. `L:source-finite-comparison` (Finite Gaussian linear images) of
   `notes/integrated_source_convergence.tex` (statement lines 21-29, proof
   lines 31-45).  Whole result: `source_finite_comparison_paper`.
2. `L:tube-half-action` (Supremum with the Gaussian quadratic cost) of
   `notes/integrated_gaussian_tubes.tex` (statement lines 581-588, proof
   lines 590-597).  Whole result: `tube_half_action_paper`.
3. `P:tube-rayleigh-transfer` (Comparison with the Rayleigh integral,
   including jumps and zero law) of `notes/integrated_gaussian_tubes.tex`
   (statement lines 225-237, proof lines 239-271).  Whole result with two
   supplied inputs: `tube_rayleigh_transfer_paper` (nonzero law) and
   `tube_rayleigh_transfer_zero_paper` (zero law, no input).

Supplied inputs (item 3 only; both are conclusions of `L:tube-closed-geometry`,
gaussian_tubes.tex lines 150-215, which the manuscript proves from the
imported Gaussian isoperimetric theorem of Borell and Sudakov-Tsirelson,
Friz-Hairer Theorem 11.6, lines 134-148):
* `TubeAttained`: every tube `T_r` is closed and `{d_δ ≤ r} = T_r`
  (lines 158-161, first half of `E:tube-attained-radius`; proof lines
  167-193, compactness of `M_δ`).
* `TubeTail`: `P(d_δ(X) > r) ≤ e^{-r²/(2δ)}` for `r ≥ 0` (second half of
  `E:tube-attained-radius`; proof lines 199-214, the Borell input, D3).

Implicit hypotheses made explicit:
* item 1: "centered Gaussian vector with covariance bounded by `CI`" is
  `HasGaussianLaw` of the vector `ξ` in `ℝ^N`, `E ξ_j = 0`, and the Loewner
  bound `CI - Cov ξ ⪰ 0` for the covariance matrix `cov[ξ_i, ξ_j]`;
  "independent standard real `g_j`" is `iIndepFun` with each law `N(0,1)`.
  The moments are Bochner integrals, so integrability of both sides is a
  conclusion (TeX lines 33-34: "finite by the finite-sum bound").
* item 2: `g_J(r)` is the real supremum `sSup (J '' closedBall 0 r)`, which
  is the true supremum by the hypothesis "bounded above on every ball".
* item 3: expectations and the Rayleigh integral are lower Lebesgue integrals
  in `[0, ∞]` (the TeX allows infinite expectations, lines 263-265).
-/

public import Mathlib
public import StratonovichHAMSecondMoment.GaussianComparison
public import StratonovichHAMSecondMoment.RayleighTail

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Pointwise Matrix

namespace StratonovichHAMSecondMoment.SourceTube

/-! ### `L:source-finite-comparison` -/

section Source

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Auxiliary: the linear image `x ↦ ∑ⱼ xⱼ vⱼ` of `ℝ^N` in `E`. -/
def linImage (v : ι → E) : EuclideanSpace ℝ ι →ₗ[ℝ] E where
  toFun x := ∑ j, x j • v j
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum, smul_smul]

/-- Auxiliary: the seminorm `x ↦ ‖∑ⱼ xⱼ vⱼ‖` on `ℝ^N` (TeX lines 32-33: "the linear
image gives only a seminorm on `ℝ^N`"). -/
def imageSeminorm (v : ι → E) : Seminorm ℝ (EuclideanSpace ℝ ι) :=
  (normSeminorm ℝ E).comp (linImage v)

omit [DecidableEq ι] in
/-- Auxiliary. -/
theorem imageSeminorm_apply (v : ι → E) (x : EuclideanSpace ℝ ι) :
    imageSeminorm v x = ‖∑ j, x j • v j‖ := rfl

/-- Auxiliary (the law of `√C g`, TeX line 41): `N(0, C I)` is the image of
`N(0, I)` under `x ↦ √C x`. -/
theorem multivariateGaussian_smul_one {C : ℝ} (hC : 0 ≤ C) :
    multivariateGaussian (0 : EuclideanSpace ℝ ι) (C • (1 : Matrix ι ι ℝ)) =
      (multivariateGaussian (0 : EuclideanSpace ℝ ι) 1).map (fun x => Real.sqrt C • x) := by
  have hS : (C • (1 : Matrix ι ι ℝ)).PosSemidef := Matrix.PosSemidef.one.smul hC
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_map_smul, charFun_multivariateGaussian hS,
    charFun_multivariateGaussian Matrix.PosSemidef.one]
  congr 1
  have h2 : Real.sqrt C * Real.sqrt C = C := Real.mul_self_sqrt hC
  simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub, neg_inj]
  congr 2
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec, WithLp.ofLp_smul, dotProduct_smul,
    smul_dotProduct, smul_eq_mul]
  rw [← mul_assoc, h2]

/-- Auxiliary: the `p`-th moment of a seminorm under `N(0, C I)` is
`(√C)^p` times its moment under `N(0, I)`. -/
theorem integral_seminorm_rpow_smul_one (N : Seminorm ℝ (EuclideanSpace ℝ ι)) {C : ℝ}
    (hC : 0 ≤ C) {p : ℝ} (hp : 0 ≤ p) :
    ∫ x, N x ^ p ∂(multivariateGaussian (0 : EuclideanSpace ℝ ι) (C • (1 : Matrix ι ι ℝ))) =
      Real.sqrt C ^ p * ∫ x, N x ^ p ∂(multivariateGaussian (0 : EuclideanSpace ℝ ι) 1) := by
  rw [multivariateGaussian_smul_one hC, integral_map (by fun_prop)
    ((GaussianComparison.seminorm_continuous N).rpow_const
      fun _ => Or.inr hp).aestronglyMeasurable, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [map_smul_eq_mul, Real.norm_of_nonneg (Real.sqrt_nonneg C)]
  exact Real.mul_rpow (Real.sqrt_nonneg C) (apply_nonneg N x)

/-- `L:source-finite-comparison` in law form: for a positive semidefinite
covariance `S` with `S ≤ C I` (Loewner), `C ≥ 0`, vectors `vⱼ` and `p ≥ 1`,
both moments are finite and
`(∫ ‖∑ xⱼ vⱼ‖^p dN(0,S))^{1/p} ≤ √C (∫ ‖∑ xⱼ vⱼ‖^p dN(0,I))^{1/p}`. -/
theorem source_finite_comparison_law {S : Matrix ι ι ℝ} (hS : S.PosSemidef) {C : ℝ}
    (hC : 0 ≤ C) (hSC : (C • (1 : Matrix ι ι ℝ) - S).PosSemidef) (v : ι → E) {p : ℝ}
    (hp : 1 ≤ p) :
    Integrable (fun x => ‖∑ j, x j • v j‖ ^ p)
        (multivariateGaussian (0 : EuclideanSpace ℝ ι) S) ∧
      Integrable (fun x => ‖∑ j, x j • v j‖ ^ p)
        (multivariateGaussian (0 : EuclideanSpace ℝ ι) 1) ∧
      (∫ x, ‖∑ j, x j • v j‖ ^ p ∂(multivariateGaussian (0 : EuclideanSpace ℝ ι) S)) ^ (1 / p)
        ≤ Real.sqrt C *
          (∫ x, ‖∑ j, x j • v j‖ ^ p
            ∂(multivariateGaussian (0 : EuclideanSpace ℝ ι) 1)) ^ (1 / p) := by
  set N := imageSeminorm v
  have hp0 : 0 ≤ p := by linarith
  obtain ⟨hiS, -, hle⟩ :=
    GaussianComparison.gaussian_seminorm_moment_le_paper hS hSC N p hp
  have hi1 : Integrable (fun x => N x ^ p) (multivariateGaussian (0 : EuclideanSpace ℝ ι) 1) :=
    GaussianComparison.integrable_seminorm_rpow _ N hp0
  refine ⟨hiS, hi1, ?_⟩
  change (∫ x, N x ^ p ∂_) ^ (1 / p) ≤ Real.sqrt C * (∫ x, N x ^ p ∂_) ^ (1 / p)
  rw [integral_seminorm_rpow_smul_one N hC hp0] at hle
  have hI0 : 0 ≤ ∫ x, N x ^ p ∂(multivariateGaussian (0 : EuclideanSpace ℝ ι) S) :=
    integral_nonneg fun x => Real.rpow_nonneg (apply_nonneg N x) p
  have hJ0 : 0 ≤ ∫ x, N x ^ p ∂(multivariateGaussian (0 : EuclideanSpace ℝ ι) 1) :=
    integral_nonneg fun x => Real.rpow_nonneg (apply_nonneg N x) p
  have hq : 0 ≤ 1 / p := by positivity
  calc (∫ x, N x ^ p ∂(multivariateGaussian (0 : EuclideanSpace ℝ ι) S)) ^ (1 / p)
      ≤ (Real.sqrt C ^ p *
          ∫ x, N x ^ p ∂(multivariateGaussian (0 : EuclideanSpace ℝ ι) 1)) ^ (1 / p) :=
        Real.rpow_le_rpow hI0 hle hq
    _ = (Real.sqrt C ^ p) ^ (1 / p) *
          (∫ x, N x ^ p ∂(multivariateGaussian (0 : EuclideanSpace ℝ ι) 1)) ^ (1 / p) :=
        Real.mul_rpow (Real.rpow_nonneg (Real.sqrt_nonneg C) p) hJ0
    _ = _ := by
        rw [one_div, Real.rpow_rpow_inv (Real.sqrt_nonneg C) (by linarith)]

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- Auxiliary: the joint law of independent standard real `gⱼ`, as a vector of
`ℝ^N`, is `N(0, I)`. -/
theorem map_indep_std_eq {Q : Measure Ω'} [IsProbabilityMeasure Q] (g : ι → Ω' → ℝ)
    (hgm : ∀ j, AEMeasurable (g j) Q) (hind : iIndepFun g Q)
    (hgl : ∀ j, Q.map (g j) = gaussianReal 0 1) :
    Q.map (fun ω => WithLp.toLp 2 (fun j => g j ω)) =
      multivariateGaussian (0 : EuclideanSpace ℝ ι) 1 := by
  have hpi := (iIndepFun_iff_map_fun_eq_pi_map hgm).1 hind
  simp_rw [hgl] at hpi
  have hm : AEMeasurable (fun ω j => g j ω) Q := AEMeasurable.of_eval hgm
  have hc : (fun ω => WithLp.toLp 2 (fun j => g j ω)) =
      (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) ∘ (fun ω j => g j ω) := rfl
  rw [hc, ← AEMeasurable.map_map_of_aemeasurable (by fun_prop) hm, hpi,
    map_pi_eq_stdGaussian, multivariateGaussian_zero_one]

/-- Auxiliary: the covariance matrix `cov[ξᵢ, ξⱼ]` of a random vector `ξ`. -/
def covMatrix (P : Measure Ω) (ξ : ι → Ω → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => cov[ξ i, ξ j; P]

/-- Auxiliary: a centered Gaussian vector with covariance matrix `S` has law
`N(0, S)`, and `S` is positive semidefinite. -/
theorem map_gaussian_eq {P : Measure Ω} (ξ : ι → Ω → ℝ)
    (hξ : HasGaussianLaw (fun ω => WithLp.toLp 2 (fun j => ξ j ω)) P)
    (hcent : ∀ j, ∫ ω, ξ j ω ∂P = 0) :
    (covMatrix P ξ).PosSemidef ∧
      P.map (fun ω => WithLp.toLp 2 (fun j => ξ j ω)) =
        multivariateGaussian (0 : EuclideanSpace ℝ ι) (covMatrix P ξ) := by
  have := hξ.isProbabilityMeasure
  set X : Ω → EuclideanSpace ℝ ι := fun ω => WithLp.toLp 2 (fun j => ξ j ω) with hXdef
  set μ := P.map X
  have : IsGaussian μ := hξ.isGaussian_map
  have hXm : AEMeasurable X P := hξ.aemeasurable
  have hL2 : MemLp X 2 P := hξ.memLp_two
  have hcoord : ∀ i, MemLp (ξ i) 2 P := fun i => by
    have := (EuclideanSpace.proj i : EuclideanSpace ℝ ι →L[ℝ] ℝ).comp_memLp' hL2
    simpa [Function.comp_def, hXdef] using this
  have hquad : ∀ t : EuclideanSpace ℝ ι,
      covarianceBilin μ t t = t ⬝ᵥ covMatrix P ξ *ᵥ t := by
    intro t
    rw [covarianceBilin_apply_pi hcoord]
    simp only [covMatrix, dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hsymm : (covMatrix P ξ).IsHermitian := by
    ext i j
    simp [covMatrix, covariance_comm]
  have hS : (covMatrix P ξ).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hsymm fun x => ?_
    have h := hquad (WithLp.toLp 2 x)
    simp only [star_trivial] at h ⊢
    rw [← h, covarianceBilin_self IsGaussian.memLp_two_id]
    exact variance_nonneg _ _
  refine ⟨hS, ?_⟩
  have hmean : ∫ x, x ∂μ = 0 := by
    ext i
    have h1 : ∫ x, x i ∂μ = (∫ x, x ∂μ) i := by
      have := (EuclideanSpace.proj i : EuclideanSpace ℝ ι →L[ℝ] ℝ).integral_comp_comm
        (IsGaussian.integrable_id (μ := μ))
      simpa [EuclideanSpace.coe_proj] using this
    rw [PiLp.zero_apply, ← h1, integral_map hXm (Continuous.aestronglyMeasurable (by fun_prop))]
    simpa [hXdef] using hcent i
  apply Measure.ext_of_charFun
  funext t
  rw [IsGaussian.charFun_eq', charFun_multivariateGaussian hS, hquad]
  simp [hmean]

/-- `L:source-finite-comparison` (`notes/integrated_source_convergence.tex`,
39f2597a, lines 21-45), random-variable form.  `ξ = (ξⱼ)` is a centered Gaussian
vector of `ℝ^N` on `(Ω, P)` whose covariance matrix is bounded by `C I`
(Loewner order), `C ≥ 0`; `g = (gⱼ)` are independent standard real Gaussians on
`(Ω', Q)`; `vⱼ` lie in a real normed space; `p ≥ 1`.  Then both moments are
finite and
`(E‖∑ ξⱼ vⱼ‖^p)^{1/p} ≤ √C (E‖∑ gⱼ vⱼ‖^p)^{1/p}`. -/
theorem source_finite_comparison {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure Q]
    (ξ : ι → Ω → ℝ) (hξ : HasGaussianLaw (fun ω => WithLp.toLp 2 (fun j => ξ j ω)) P)
    (hcent : ∀ j, ∫ ω, ξ j ω ∂P = 0) {C : ℝ} (hC : 0 ≤ C)
    (hcov : (C • (1 : Matrix ι ι ℝ) - covMatrix P ξ).PosSemidef)
    (g : ι → Ω' → ℝ) (hgm : ∀ j, AEMeasurable (g j) Q) (hind : iIndepFun g Q)
    (hgl : ∀ j, Q.map (g j) = gaussianReal 0 1) (v : ι → E) {p : ℝ} (hp : 1 ≤ p) :
    Integrable (fun ω => ‖∑ j, ξ j ω • v j‖ ^ p) P ∧
      Integrable (fun ω => ‖∑ j, g j ω • v j‖ ^ p) Q ∧
      (∫ ω, ‖∑ j, ξ j ω • v j‖ ^ p ∂P) ^ (1 / p) ≤
        Real.sqrt C * (∫ ω, ‖∑ j, g j ω • v j‖ ^ p ∂Q) ^ (1 / p) := by
  obtain ⟨hS, hlawξ⟩ := map_gaussian_eq ξ hξ hcent
  have hlawg := map_indep_std_eq g hgm hind hgl
  obtain ⟨hiS, hi1, hle⟩ := source_finite_comparison_law hS hC hcov v hp
  have hXm : AEMeasurable (fun ω => WithLp.toLp 2 (fun j => ξ j ω)) P := hξ.aemeasurable
  have hGm : AEMeasurable (fun ω => WithLp.toLp 2 (fun j => g j ω)) Q := by
    have : AEMeasurable (fun ω j => g j ω) Q := AEMeasurable.of_eval hgm
    exact (WithLp.measurable_toLp 2 _).comp_aemeasurable this
  have hcont : Continuous fun x : EuclideanSpace ℝ ι => ‖∑ j, x j • v j‖ ^ p :=
    ((GaussianComparison.seminorm_continuous (imageSeminorm v)).rpow_const
      fun _ => Or.inr (by linarith))
  rw [← hlawξ] at hiS hle
  rw [← hlawg] at hi1 hle
  rw [integral_map hXm hcont.aestronglyMeasurable,
    integral_map hGm hcont.aestronglyMeasurable] at hle
  refine ⟨?_, ?_, by simpa using hle⟩
  · simpa [Function.comp_def] using
      (integrable_map_measure hcont.aestronglyMeasurable hXm).1 hiS
  · simpa [Function.comp_def] using
      (integrable_map_measure hcont.aestronglyMeasurable hGm).1 hi1

/-- `L:source-finite-comparison` with the manuscript's hypotheses (whole result).
The TeX's real Banach space is a real normed space here (completeness is not
used); the two Gaussian families may live on different probability spaces
(the TeX takes `g` "independent standard real", on any space). -/
theorem source_finite_comparison_paper {P : Measure Ω} {Q : Measure Ω'}
    [IsProbabilityMeasure Q] [CompleteSpace E] (v : ι → E)
    (ξ : ι → Ω → ℝ) (hξ : HasGaussianLaw (fun ω => WithLp.toLp 2 (fun j => ξ j ω)) P)
    (hcent : ∀ j, ∫ ω, ξ j ω ∂P = 0) (C : ℝ) (hC : 0 ≤ C)
    (hcov : (C • (1 : Matrix ι ι ℝ) - covMatrix P ξ).PosSemidef)
    (g : ι → Ω' → ℝ) (hgm : ∀ j, AEMeasurable (g j) Q) (hind : iIndepFun g Q)
    (hgl : ∀ j, Q.map (g j) = gaussianReal 0 1) (p : ℝ) (hp : 1 ≤ p) :
    Integrable (fun ω => ‖∑ j, ξ j ω • v j‖ ^ p) P ∧
      Integrable (fun ω => ‖∑ j, g j ω • v j‖ ^ p) Q ∧
      (∫ ω, ‖∑ j, ξ j ω • v j‖ ^ p ∂P) ^ (1 / p) ≤
        Real.sqrt C * (∫ ω, ‖∑ j, g j ω • v j‖ ^ p ∂Q) ^ (1 / p) :=
  source_finite_comparison ξ hξ hcent hC hcov g hgm hind hgl v hp

end Source

/-! ### `L:tube-half-action` -/

section HalfAction

variable {H : Type*} [SeminormedAddCommGroup H]

/-- `g_J(r) = sup_{‖h‖ ≤ r} J(h)` (TeX line 583), as the real supremum of the
image of the closed ball. -/
def ballSup (J : H → ℝ) (r : ℝ) : ℝ := sSup (J '' Metric.closedBall (0 : H) r)

/-- Auxiliary: `J h ≤ g_J(r)` for `‖h‖ ≤ r` when `J` is bounded above on the ball. -/
theorem le_ballSup (J : H → ℝ) {r : ℝ} (hJ : BddAbove (J '' Metric.closedBall (0 : H) r))
    {h : H} (hh : ‖h‖ ≤ r) : J h ≤ ballSup J r :=
  le_csSup hJ ⟨h, mem_closedBall_zero_iff.2 hh, rfl⟩

/-- Auxiliary: `g_J(r) ≤ B` when `J h ≤ B` for every `‖h‖ ≤ r`, `r ≥ 0`. -/
theorem ballSup_le (J : H → ℝ) {r B : ℝ} (hr : 0 ≤ r) (hB : ∀ h : H, ‖h‖ ≤ r → J h ≤ B) :
    ballSup J r ≤ B :=
  csSup_le ⟨J 0, 0, by simpa using hr, rfl⟩ fun _ ⟨h, hh, he⟩ =>
    he ▸ hB h (mem_closedBall_zero_iff.1 hh)

/-- `L:tube-half-action` (`notes/integrated_gaussian_tubes.tex`, 39f2597a, lines
581-597): for `J : H → ℝ` bounded above on every closed ball about `0`, in the
extended reals
`sup_{r ≥ 0} {g_J(r) - r²/2} = sup_{h ∈ H} {J(h) - ‖h‖²/2}`.
Every term is real (`g_J(r)` is finite), so no `∞ - ∞` occurs (TeX lines 593-594). -/
theorem tube_half_action (J : H → ℝ)
    (hJ : ∀ r, 0 ≤ r → BddAbove (J '' Metric.closedBall (0 : H) r)) :
    (⨆ (r : ℝ) (_ : 0 ≤ r), ((ballSup J r - r ^ 2 / 2 : ℝ) : EReal)) =
      ⨆ h : H, ((J h - ‖h‖ ^ 2 / 2 : ℝ) : EReal) := by
  apply le_antisymm
  · refine iSup₂_le fun r hr => ?_
    set R := ⨆ h : H, ((J h - ‖h‖ ^ 2 / 2 : ℝ) : EReal) with hRdef
    by_cases htop : R = ⊤
    · rw [htop]; exact le_top
    have hbot : R ≠ ⊥ := by
      intro hb
      have : ((J 0 - ‖(0 : H)‖ ^ 2 / 2 : ℝ) : EReal) ≤ R :=
        le_iSup (fun h : H => ((J h - ‖h‖ ^ 2 / 2 : ℝ) : EReal)) 0
      rw [hb] at this
      exact EReal.coe_ne_bot _ (le_bot_iff.1 this)
    rw [← EReal.coe_toReal htop hbot, EReal.coe_le_coe_iff]
    have hb : ballSup J r ≤ R.toReal + r ^ 2 / 2 := by
      refine ballSup_le J hr fun h hh => ?_
      have h1 : ((J h - ‖h‖ ^ 2 / 2 : ℝ) : EReal) ≤ R :=
        le_iSup (fun h : H => ((J h - ‖h‖ ^ 2 / 2 : ℝ) : EReal)) h
      rw [← EReal.coe_toReal htop hbot, EReal.coe_le_coe_iff] at h1
      have h2 : ‖h‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg h) hh 2
      linarith
    linarith
  · refine iSup_le fun h => ?_
    refine le_iSup₂_of_le (f := fun (r : ℝ) (_ : 0 ≤ r) =>
      ((ballSup J r - r ^ 2 / 2 : ℝ) : EReal)) ‖h‖ (norm_nonneg h) ?_
    rw [EReal.coe_le_coe_iff]
    have := le_ballSup J (hJ ‖h‖ (norm_nonneg h)) (le_refl ‖h‖)
    linarith

/-- `L:tube-half-action` with the manuscript's hypotheses (whole result): `H` is the
section's real Hilbert space (TeX lines 4-5; completeness and the inner product
are carried and not used: the identity holds in every seminormed group), `J` is
finite (real valued) and bounded above on every original (closed) ball. -/
theorem tube_half_action_paper {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (J : H → ℝ)
    (hJ : ∀ r, 0 ≤ r → BddAbove (J '' Metric.closedBall (0 : H) r)) :
    (⨆ (r : ℝ) (_ : 0 ≤ r), ((ballSup J r - r ^ 2 / 2 : ℝ) : EReal)) =
      ⨆ h : H, ((J h - ‖h‖ ^ 2 / 2 : ℝ) : EReal) :=
  tube_half_action J hJ

end HalfAction

/-! ### `P:tube-rayleigh-transfer` -/

section Transfer

/-- The Rayleigh density `(r/δ) e^{-r²/(2δ)}` (TeX line 246). -/
def rayleighDensity (δ r : ℝ) : ℝ := r / δ * Real.exp (-(r ^ 2) / (2 * δ))

/-- The Rayleigh survival function, from `RayleighTail.gaussian_weight_tail` at
`δ/4` (TeX lines 246-247, "by direct integration"): for `c ≥ 0`,
`∫_c^∞ (r/δ) e^{-r²/(2δ)} dr = e^{-c²/(2δ)}`, with integrability. -/
theorem rayleigh_survival {δ c : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) :
    IntegrableOn (rayleighDensity δ) (Ioi c) ∧
      ∫ r in Ioi c, rayleighDensity δ r = Real.exp (-(c ^ 2) / (2 * δ)) := by
  obtain ⟨hi, hv⟩ := RayleighTail.gaussian_weight_tail (δ / 4) c (by positivity) hc
  have hfun : rayleighDensity δ =
      fun r => (1 / 4 : ℝ) * (r / (δ / 4) * Real.exp (-(r ^ 2) / (8 * (δ / 4)))) := by
    funext r
    have h8 : 8 * (δ / 4) = 2 * δ := by ring
    rw [rayleighDensity, h8]
    field_simp
  rw [hfun]
  refine ⟨hi.const_mul _, ?_⟩
  rw [integral_const_mul, hv]
  have h8 : 8 * (δ / 4) = 2 * δ := by ring
  rw [h8]
  ring

/-- Auxiliary: the survival function as a lower integral. -/
theorem lintegral_rayleigh_Ioi {δ c : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) :
    ∫⁻ r in Ioi c, ENNReal.ofReal (rayleighDensity δ r) =
      ENNReal.ofReal (Real.exp (-(c ^ 2) / (2 * δ))) := by
  obtain ⟨hi, hv⟩ := rayleigh_survival hδ hc
  rw [← hv, ofReal_integral_eq_lintegral_ofReal hi]
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r hr => ?_)
  have : 0 ≤ r := hc.trans (le_of_lt hr)
  simp only [Pi.zero_apply, rayleighDensity]
  positivity

/-- The law of the auxiliary Rayleigh variable `𝓡_δ` (TeX lines 245-248): the
density `(r/δ) e^{-r²/(2δ)}` on `r > 0`. -/
def rayleighMeasure (δ : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity fun r => ENNReal.ofReal (rayleighDensity δ r)

/-- `P(𝓡_δ > c) = e^{-c²/(2δ)}` for `c ≥ 0`; at `c = 0` this is mass one. -/
theorem rayleighMeasure_Ioi {δ c : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) :
    rayleighMeasure δ (Ioi c) = ENNReal.ofReal (Real.exp (-(c ^ 2) / (2 * δ))) := by
  rw [rayleighMeasure, withDensity_apply _ measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.2 (Ioi_subset_Ioi hc), lintegral_rayleigh_Ioi hδ hc]

/-- Stochastic domination by the Rayleigh law and layer cake (TeX lines 249-265): if
`Y ≥ 0` a.e. and `P(Y ≥ c) ≤ e^{-c²/(2δ)}` for every `c ≥ 0`, then for every
nondecreasing `φ ≥ 0`, `E φ(Y) ≤ E φ(𝓡_δ)` in `[0, ∞]`; no continuity of `φ`
(jumps of `G`) and no finiteness of the expectations is needed. -/
theorem lintegral_monotone_le_rayleigh {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {δ : ℝ} (Y : Ω → ℝ) (hY : AEMeasurable Y P) (hY0 : ∀ᵐ ω ∂P, 0 ≤ Y ω)
    (htail : ∀ c, 0 ≤ c → P {ω | c ≤ Y ω} ≤ ENNReal.ofReal (Real.exp (-(c ^ 2) / (2 * δ))))
    (hδ : 0 < δ) (φ : ℝ → ℝ) (hφ : Monotone φ) (hφ0 : ∀ r, 0 ≤ φ r) :
    ∫⁻ ω, ENNReal.ofReal (φ (Y ω)) ∂P ≤ ∫⁻ r, ENNReal.ofReal (φ r) ∂(rayleighMeasure δ) := by
  rw [lintegral_eq_lintegral_meas_lt P (Eventually.of_forall fun ω => hφ0 _)
      (hφ.measurable.comp_aemeasurable hY),
    lintegral_eq_lintegral_meas_lt _ (Eventually.of_forall fun r => hφ0 r)
      hφ.measurable.aemeasurable]
  refine lintegral_mono fun t => ?_
  set U : Set ℝ := {u | 0 ≤ u ∧ t < φ u} with hU
  by_cases hne : U.Nonempty
  · have hbdd : BddBelow U := ⟨0, fun u hu => hu.1⟩
    set c := sInf U
    have hc0 : 0 ≤ c := le_csInf hne fun u hu => hu.1
    have h1 : P {ω | t < φ (Y ω)} ≤ P {ω | c ≤ Y ω} := by
      refine measure_mono_ae ?_
      filter_upwards [hY0] with ω hω h
      exact csInf_le hbdd ⟨hω, h⟩
    have h2 : Ioi c ⊆ {r | t < φ r} := by
      intro r hr
      obtain ⟨u, hu, hur⟩ := exists_lt_of_csInf_lt hne hr
      exact lt_of_lt_of_le hu.2 (hφ hur.le)
    calc P {ω | t < φ (Y ω)} ≤ P {ω | c ≤ Y ω} := h1
      _ ≤ ENNReal.ofReal (Real.exp (-(c ^ 2) / (2 * δ))) := htail c hc0
      _ = rayleighMeasure δ (Ioi c) := (rayleighMeasure_Ioi hδ hc0).symm
      _ ≤ rayleighMeasure δ {r | t < φ r} := measure_mono h2
  · have h0 : P {ω | t < φ (Y ω)} = 0 := by
      refine measure_mono_null_ae ?_ measure_empty
      filter_upwards [hY0] with ω hω h
      exact hne ⟨Y ω, hω, h⟩
    rw [h0]
    exact zero_le

/-- Auxiliary: the Rayleigh density is measurable. -/
theorem measurable_rayleighDensity (δ : ℝ) : Measurable (rayleighDensity δ) := by
  unfold rayleighDensity
  fun_prop

/-- Auxiliary: the Rayleigh expectation of `e^{G/δ}` is the Rayleigh integral of
`E:tube-rayleigh-transfer` (TeX lines 232-233). -/
theorem lintegral_rayleigh_exp {δ : ℝ} (hδ : 0 < δ) {G : ℝ → ℝ} (hG : Measurable G) :
    ∫⁻ r, ENNReal.ofReal (Real.exp (G r / δ)) ∂(rayleighMeasure δ) =
      ∫⁻ r in Ioi 0, ENNReal.ofReal (r / δ * Real.exp ((G r - r ^ 2 / 2) / δ)) := by
  rw [rayleighMeasure, lintegral_withDensity_eq_lintegral_mul₀
    (measurable_rayleighDensity δ).ennreal_ofReal.aemeasurable
    (by fun_prop : Measurable fun r => ENNReal.ofReal (Real.exp (G r / δ))).aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hr0 : 0 ≤ r := le_of_lt hr
  simp only [Pi.mul_apply, rayleighDensity]
  rw [← ENNReal.ofReal_mul (by positivity), mul_assoc, ← Real.exp_add]
  congr 3
  field_simp
  ring

/-- Auxiliary: the Rayleigh law has mass one (`P(𝓡_δ > 0) = 1`, TeX line 246). -/
theorem lintegral_rayleigh_one {δ : ℝ} (hδ : 0 < δ) :
    ∫⁻ r in Ioi 0, ENNReal.ofReal (rayleighDensity δ r) = 1 := by
  rw [lintegral_rayleigh_Ioi hδ le_rfl]
  simp

variable {B : Type*}

/-- The extended tube radius `d(x) = inf {r ≥ 0 : x ∈ T_r}` in `[0, ∞]`, with
`inf ∅ = ∞` (TeX line 158-159, `d_δ`). -/
def tubeRadius (T : ℝ → Set B) (x : B) : ℝ≥0∞ :=
  ⨅ (r : ℝ) (_ : 0 ≤ r) (_ : x ∈ T r), ENNReal.ofReal r

/-- Supplied input (closed tubes and least-radius attainment, the first sentence
and the first identity of `E:tube-attained-radius` in `L:tube-closed-geometry`,
gaussian_tubes.tex lines 158-161, proved there in lines 167-193 from the
compactness of `M_δ` and the closedness of `A_δ`): every `T_r`, `r ≥ 0`, is
closed and `{d ≤ r} = T_r`.  True for the manuscript's tubes
`T_r = A_δ + M_δ(B̄_H(r))` under the section's standing hypotheses. -/
def TubeAttained [TopologicalSpace B] (T : ℝ → Set B) : Prop :=
  ∀ r : ℝ, 0 ≤ r → IsClosed (T r) ∧ {x | tubeRadius T x ≤ ENNReal.ofReal r} = T r

/-- Supplied input (the Gaussian tail of `L:tube-closed-geometry`, second part of
`E:tube-attained-radius`, gaussian_tubes.tex lines 161-162, proved there in
lines 199-214 from the imported Gaussian isoperimetric inequality of Borell and
Sudakov-Tsirelson in the form of Friz-Hairer Theorem 11.6, lines 134-148; D3):
`P(d(X) > r) ≤ e^{-r²/(2δ)}` for every `r ≥ 0`.  True for the manuscript's `X`,
`δ` and tubes when the law of `X` is nonzero. -/
def TubeTail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → B)
    (T : ℝ → Set B) (δ : ℝ) : Prop :=
  ∀ r : ℝ, 0 ≤ r →
    P {ω | ENNReal.ofReal r < tubeRadius T (X ω)} ≤
      ENNReal.ofReal (Real.exp (-(r ^ 2) / (2 * δ)))

/-- Auxiliary (TeX lines 192-193, "closed sublevels give lower semicontinuity and
Borel measurability"): under `TubeAttained`, the radius is measurable. -/
theorem measurable_tubeRadius [TopologicalSpace B] [MeasurableSpace B] [OpensMeasurableSpace B]
    {T : ℝ → Set B} (hT : TubeAttained T) : Measurable (tubeRadius T) := by
  refine LowerSemicontinuous.measurable (lowerSemicontinuous_iff_isClosed_preimage.2 ?_)
  intro y
  induction y using ENNReal.recTopCoe with
  | top => simp
  | coe q =>
    have h := hT q q.2
    have hq : ((q : ℝ≥0∞)) = ENNReal.ofReal (q : ℝ) := (ENNReal.ofReal_coe_nnreal).symm
    rw [hq]
    change IsClosed {x | tubeRadius T x ≤ ENNReal.ofReal q}
    rw [h.2]
    exact h.1

/-- Auxiliary: the tail of the radius at a closed endpoint (TeX lines 251-258):
`P(d(X) ≥ c) ≤ e^{-c²/(2δ)}` for `c ≥ 0`, for the real radius `d(X).toReal`. -/
theorem tail_toReal_ge {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → B} {T : ℝ → Set B} {δ : ℝ}
    (htail : TubeTail P X T δ) {c : ℝ} (hc : 0 ≤ c) :
    P {ω | c ≤ (tubeRadius T (X ω)).toReal} ≤
      ENNReal.ofReal (Real.exp (-(c ^ 2) / (2 * δ))) := by
  rcases hc.eq_or_lt with h0 | hpos
  · subst h0
    simp
  have hcont : Continuous fun s : ℝ => ENNReal.ofReal (Real.exp (-(s ^ 2) / (2 * δ))) :=
    ENNReal.continuous_ofReal.comp (by fun_prop)
  refine ge_of_tendsto (hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (x := 𝓝[<] c) ?_
  filter_upwards [Ioo_mem_nhdsLT hpos] with s hs
  refine (measure_mono fun ω (hω : c ≤ _) => ?_).trans (htail s hs.1.le)
  have hne : tubeRadius T (X ω) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.toReal_top] at hω
    linarith
  change ENNReal.ofReal s < tubeRadius T (X ω)
  rw [← ENNReal.ofReal_toReal hne]
  exact (ENNReal.ofReal_lt_ofReal_iff (hpos.trans_le hω)).2 (hs.2.trans_le hω)

/-- Auxiliary (TeX lines 260-262): the radius is finite almost surely. -/
theorem ae_tubeRadius_lt_top {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → B} {T : ℝ → Set B} {δ : ℝ} (hδ : 0 < δ) (htail : TubeTail P X T δ) :
    ∀ᵐ ω ∂P, tubeRadius T (X ω) < ⊤ := by
  refine ae_iff.2 (le_antisymm ?_ zero_le)
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (-((n : ℝ) ^ 2) / (2 * δ))))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) ^ 2 / (2 * δ)) atTop atTop :=
      ((tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop).atTop_div_const
        (by positivity)
    have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1)
    have h3 := ENNReal.tendsto_ofReal h2
    rw [ENNReal.ofReal_zero] at h3
    refine h3.congr fun n => ?_
    simp [neg_div]
  refine ge_of_tendsto' hlim fun n => ?_
  refine (measure_mono fun ω (hω : ¬ _ < ⊤) => ?_).trans (htail n n.cast_nonneg)
  change ENNReal.ofReal n < _
  rw [not_lt_top_iff.1 hω]
  exact ENNReal.ofReal_lt_top

/-- `P:tube-rayleigh-transfer`, nonzero-law case, for an abstract tube family:
with the supplied inputs `TubeAttained T` and `TubeTail P X T δ`, for every
`F : B → ℝ` and every `G` nondecreasing on `[0, ∞)` with `F x ≤ G r` on `T_r`,
`E e^{F(X)/δ} ≤ ∫_0^∞ (r/δ) exp((G(r) - r²/2)/δ) dr` in `[0, ∞]`. -/
theorem tube_rayleigh_transfer [TopologicalSpace B] [MeasurableSpace B] [OpensMeasurableSpace B]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : Ω → B) (hX : AEMeasurable X P) (T : ℝ → Set B) (δ : ℝ) (hδ : 0 < δ)
    (hT : TubeAttained T) (htail : TubeTail P X T δ)
    (F : B → ℝ) (G : ℝ → ℝ) (hG : MonotoneOn G (Ici 0))
    (hFG : ∀ r : ℝ, 0 ≤ r → ∀ x ∈ T r, F x ≤ G r) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (F (X ω) / δ)) ∂P ≤
      ∫⁻ r in Ioi 0, ENNReal.ofReal (r / δ * Real.exp ((G r - r ^ 2 / 2) / δ)) := by
  set D : Ω → ℝ≥0∞ := fun ω => tubeRadius T (X ω) with hD
  set Y : Ω → ℝ := fun ω => (D ω).toReal with hYdef
  have hDm : AEMeasurable D P := (measurable_tubeRadius hT).comp_aemeasurable hX
  have hYm : AEMeasurable Y P := ENNReal.measurable_toReal.comp_aemeasurable hDm
  set G' : ℝ → ℝ := fun r => G (max r 0) with hG'
  have hG'm : Monotone G' := fun a b hab =>
    hG (le_max_right a 0) (le_max_right b 0) (max_le_max hab le_rfl)
  set φ : ℝ → ℝ := fun r => Real.exp (G' r / δ)
  have hφ : Monotone φ := fun a b hab =>
    Real.exp_le_exp.2 (div_le_div_of_nonneg_right (hG'm hab) hδ.le)
  have hdom := lintegral_monotone_le_rayleigh Y hYm
    (Eventually.of_forall fun ω => ENNReal.toReal_nonneg)
    (fun c hc => tail_toReal_ge htail hc) hδ φ hφ fun r => (Real.exp_pos _).le
  have hlhs : ∫⁻ ω, ENNReal.ofReal (Real.exp (F (X ω) / δ)) ∂P ≤
      ∫⁻ ω, ENNReal.ofReal (φ (Y ω)) ∂P := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_tubeRadius_lt_top hδ htail] with ω hω
    have hY0 : 0 ≤ Y ω := ENNReal.toReal_nonneg
    have hmem : X ω ∈ T (Y ω) := by
      rw [← (hT (Y ω) hY0).2]
      change D ω ≤ ENNReal.ofReal (D ω).toReal
      rw [ENNReal.ofReal_toReal hω.ne]
    have hF := hFG (Y ω) hY0 (X ω) hmem
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    refine div_le_div_of_nonneg_right ?_ hδ.le
    simpa [hG', max_eq_left hY0] using hF
  have hrhs : ∫⁻ r, ENNReal.ofReal (φ r) ∂(rayleighMeasure δ) =
      ∫⁻ r in Ioi 0, ENNReal.ofReal (r / δ * Real.exp ((G r - r ^ 2 / 2) / δ)) := by
    rw [lintegral_rayleigh_exp hδ hG'm.measurable]
    refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    simp [hG', max_eq_left (le_of_lt (mem_Ioi.1 hr))]
  exact hlhs.trans (hdom.trans hrhs.le)

/-- `P:tube-rayleigh-transfer`, zero-law case (TeX lines 235-236 and 267-269): if
`X = 0` almost surely, `G` is nondecreasing on `[0, ∞)` and `F(0) ≤ G(0)`, then
`E e^{F(X)/δ} ≤ ∫_0^∞ (r/δ) exp((G(r) - r²/2)/δ) dr`.  No input is used. -/
theorem tube_rayleigh_transfer_zero [Zero B] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (X : Ω → B) (hX0 : ∀ᵐ ω ∂P, X ω = 0)
    (δ : ℝ) (hδ : 0 < δ) (F : B → ℝ) (G : ℝ → ℝ) (hG : MonotoneOn G (Ici 0))
    (hF0 : F 0 ≤ G 0) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (F (X ω) / δ)) ∂P ≤
      ∫⁻ r in Ioi 0, ENNReal.ofReal (r / δ * Real.exp ((G r - r ^ 2 / 2) / δ)) := by
  have hl : ∫⁻ ω, ENNReal.ofReal (Real.exp (F (X ω) / δ)) ∂P =
      ENNReal.ofReal (Real.exp (F 0 / δ)) := by
    rw [lintegral_congr_ae (g := fun _ => ENNReal.ofReal (Real.exp (F 0 / δ)))
      (hX0.mono fun ω hω => by simp only [hω]), lintegral_const,
      measure_univ, mul_one]
  rw [hl]
  calc ENNReal.ofReal (Real.exp (F 0 / δ))
      ≤ ENNReal.ofReal (Real.exp (G 0 / δ)) :=
        ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (div_le_div_of_nonneg_right hF0 hδ.le))
    _ = ∫⁻ r in Ioi 0, ENNReal.ofReal (Real.exp (G 0 / δ)) *
          ENNReal.ofReal (rayleighDensity δ r) := by
        rw [lintegral_const_mul _ (measurable_rayleighDensity δ).ennreal_ofReal,
          lintegral_rayleigh_one hδ, mul_one]
    _ ≤ _ := by
        refine setLIntegral_mono' measurableSet_Ioi fun r hr => ?_
        have hr0 : 0 ≤ r := le_of_lt hr
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
        refine ENNReal.ofReal_le_ofReal ?_
        have hGr : G 0 ≤ G r := hG (mem_Ici.2 le_rfl) hr0 hr0
        have he : Real.exp (G 0 / δ) * Real.exp (-(r ^ 2) / (2 * δ)) ≤
            Real.exp ((G r - r ^ 2 / 2) / δ) := by
          rw [← Real.exp_add]
          refine Real.exp_le_exp.2 ?_
          have : (G r - r ^ 2 / 2) / δ = G r / δ + -(r ^ 2) / (2 * δ) := by
            field_simp
            ring
          rw [this]
          have := div_le_div_of_nonneg_right hGr hδ.le
          linarith
        simp only [rayleighDensity]
        have hrd : 0 ≤ r / δ := div_nonneg hr0 hδ.le
        calc Real.exp (G 0 / δ) * (r / δ * Real.exp (-(r ^ 2) / (2 * δ)))
            = r / δ * (Real.exp (G 0 / δ) * Real.exp (-(r ^ 2) / (2 * δ))) := by ring
          _ ≤ r / δ * Real.exp ((G r - r ^ 2 / 2) / δ) := mul_le_mul_of_nonneg_left he hrd

end Transfer

/-! ### The manuscript's tubes and the paper wrappers of `P:tube-rayleigh-transfer` -/

section TransferPaper

variable {𝔅 : Type*} [NormedAddCommGroup 𝔅] [NormedSpace ℝ 𝔅]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The manuscript's tubes (TeX lines 152-157 and 12-13): with
`b_δ = 2 E‖X‖`, `E₀ = closure (range M_δ)` (equal to `closure C(H)`, since
`C = √δ M_δ` with `δ > 0`), `A_δ = {x ∈ E₀ : ‖x‖ ≤ b_δ}` and
`T_r = A_δ + M_δ(B̄_H(r))`. -/
def paperTube {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → 𝔅)
    (M : H →L[ℝ] 𝔅) (r : ℝ) : Set 𝔅 :=
  {x ∈ closure (Set.range M) | ‖x‖ ≤ 2 * ∫ ω, ‖X ω‖ ∂P} + M '' Metric.closedBall 0 r

/-- `P:tube-rayleigh-transfer` (`notes/integrated_gaussian_tubes.tex`, 39f2597a,
lines 225-271), nonzero law, with the manuscript's hypotheses and the two supplied
inputs of `L:tube-closed-geometry` at the manuscript's tubes (whole result,
inputs supplied).  `𝔅` real separable Banach with its Borel sets, `H` real
separable Hilbert, `M_δ` compact, `0 < δ < 1`, `X` measurable with
`E‖X‖² < ∞` and nonzero law; `F` Borel; `G` Borel and nondecreasing on
`[0, ∞)`; `F ≤ G(r)` on every `T_r`.  Then
`E e^{F(X)/δ} ≤ ∫_0^∞ (r/δ) exp((G(r) - r²/2)/δ) dr` in `[0, ∞]`.
`F` is taken on all of `𝔅` (only its values on the tubes and at `X` enter). -/
theorem tube_rayleigh_transfer_paper [CompleteSpace 𝔅] [MeasurableSpace 𝔅] [BorelSpace 𝔅]
    [TopologicalSpace.SeparableSpace 𝔅] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (M : H →L[ℝ] 𝔅) (_hM : IsCompactOperator M) (δ : ℝ) (hδ : 0 < δ) (_hδ1 : δ < 1)
    (X : Ω → 𝔅) (hX : AEMeasurable X P) (_hX2 : MemLp X 2 P)
    (_hlaw : ¬ ∀ᵐ ω ∂P, X ω = 0)
    (hAtt : TubeAttained (paperTube P X M)) (hTail : TubeTail P X (paperTube P X M) δ)
    (F : 𝔅 → ℝ) (_hF : Measurable F) (G : ℝ → ℝ) (_hGm : Measurable G)
    (hG : MonotoneOn G (Ici 0))
    (hFG : ∀ r : ℝ, 0 ≤ r → ∀ x ∈ paperTube P X M r, F x ≤ G r) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (F (X ω) / δ)) ∂P ≤
      ∫⁻ r in Ioi 0, ENNReal.ofReal (r / δ * Real.exp ((G r - r ^ 2 / 2) / δ)) :=
  tube_rayleigh_transfer X hX (paperTube P X M) δ hδ hAtt hTail F G hG hFG

omit [NormedSpace ℝ 𝔅] in
/-- `P:tube-rayleigh-transfer`, zero law (TeX lines 235-236, 267-269), with the
manuscript's hypotheses (whole result, no input): `X = 0` almost surely
(`E₀ = {0}`, `C = M_δ = 0`), `0 < δ < 1`, `F` Borel with `F(0) ≤ G(0)`, `G`
Borel and nondecreasing on `[0, ∞)`. -/
theorem tube_rayleigh_transfer_zero_paper [MeasurableSpace 𝔅] [BorelSpace 𝔅]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : Ω → 𝔅) (hX0 : ∀ᵐ ω ∂P, X ω = 0) (δ : ℝ) (hδ : 0 < δ) (_hδ1 : δ < 1)
    (F : 𝔅 → ℝ) (_hF : Measurable F) (G : ℝ → ℝ) (_hGm : Measurable G)
    (hG : MonotoneOn G (Ici 0)) (hF0 : F 0 ≤ G 0) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (F (X ω) / δ)) ∂P ≤
      ∫⁻ r in Ioi 0, ENNReal.ofReal (r / δ * Real.exp ((G r - r ^ 2 / 2) / δ)) :=
  tube_rayleigh_transfer_zero X hX0 δ hδ F G hG hF0

end TransferPaper

end StratonovichHAMSecondMoment.SourceTube
