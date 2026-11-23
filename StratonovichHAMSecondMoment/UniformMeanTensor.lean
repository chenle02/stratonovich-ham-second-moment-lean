module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L16, item L16-D, part 3: `L:uniform-mean-tensor` (dimension-free Hilbert tensor extension)
on finite tensors with orthonormal second factors, by the book's **Gaussian route** (decision 5
of L16), and the non-compactness sentence.

TeX anchors (revision edf7085f, book 1.1.3): `integrated_uniform_mean.tex`,
`L:uniform-mean-tensor` statement lines 198-206, proof 208-255 (Step 1 lines 214-230, Step 2
lines 233-247, non-compactness lines 249-253).

Statement (frozen, `CameronInterface.TensorExtensionTarget`): for real Hilbert spaces `H₀, G`,
`2 ≤ r < ∞`, a bounded `A : H₀ → L^r(I)`, finitely many `f_j ∈ H₀` and orthonormal `e_j ∈ G`,
the field `t ↦ ∑_j (A f_j)(t) e_j` has `L^r(I; G)` norm at most `‖A‖ (∑_j ‖f_j‖²)^{1/2}`.

Proof (the TeX's, with one change in Step 1).  Let `γ` be a standard Gaussian vector of
`ℝ^n` (`ProbabilityTheory.stdGaussian` on `EuclideanSpace ℝ (Fin n)`) and
`m_r = E|γ₁|^r ∈ (0, ∞)` (`gaussMoment`).
* Scalar moments (`lintegral_sum_gauss`): `E|∑_j γ_j a_j|^r = m_r (∑_j a_j²)^{r/2}`, since
  `⟪c, γ⟫` is `N(0, ‖c‖²)` (`IsGaussian.map_eq_gaussianReal`, `variance_dual_stdGaussian`).
* Step 1 (`lintegral_norm_sum_gauss_le`): `E‖∑_j γ_j f_j‖^r ≤ m_r (∑_j ‖f_j‖²)^{r/2}`.  The TeX
  diagonalizes the covariance and uses convexity; here an orthonormal basis `(b_l)` of
  `span{f_j}` writes `‖∑ γ_j f_j‖² = ∑_l Z_l²` with `Z_l = ⟪b_l, ∑ γ_j f_j⟫` Gaussian of variance
  `λ_l`, and Minkowski's inequality in `L^{r/2}` (`eLpNorm_sum_le`) gives
  `(E‖∑ γ_j f_j‖^r)^{2/r} ≤ ∑_l (E|Z_l|^r)^{2/r} = m_r^{2/r} ∑_l λ_l = m_r^{2/r} ∑_j ‖f_j‖²`
  (no independence of the `Z_l` and no division by `λ_l` is needed).
* Step 2 (`tensor_extension_bound`): Tonelli in `(t, γ)` and the scalar moments give
  `m_r ∫_I (∑_j |A f_j(t)|²)^{r/2} = E‖A(∑ γ_j f_j)‖_r^r ≤ ‖A‖^r m_r (∑ ‖f_j‖²)^{r/2}`; cancel
  `m_r`.  Orthonormality gives `‖∑_j c_j e_j‖ = (∑ c_j²)^{1/2}`.

Headline: `uniform_mean_tensor : TensorExtensionTarget ∧ TensorNoncompactTarget`.

Lemmas whose doc comments say "Auxiliary" have no manuscript label.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.CameronInterface

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace StratonovichHAMSecondMoment.UniformMeanTensor

open SpaceTimePositivity (timeMeasure)
open CameronInterface

/-! ### Auxiliary real/extended-real identities -/

/-- Auxiliary: `∫⁻ ‖f‖ₑ^q = ‖f‖_{L^q}^q` for `0 < q`. -/
theorem lintegral_enorm_rpow_eq {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {f : α → E} (hf : AEStronglyMeasurable f μ) {q : ℝ} (hq : 0 < q) :
    ∫⁻ x, ‖f x‖ₑ ^ q ∂μ = eLpNorm f (ENNReal.ofReal q) μ ^ q := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hq) ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hq.le, ← ENNReal.rpow_mul, one_div_mul_cancel hq.ne',
    ENNReal.rpow_one]

/-- Auxiliary: `(√Φ)^r = Φ^{r/2}` in `ℝ≥0∞`, `Φ ≥ 0`. -/
theorem ofReal_sqrt_rpow {Φ r : ℝ} (hΦ : 0 ≤ Φ) (hr : 0 ≤ r) :
    ENNReal.ofReal √Φ ^ r = ENNReal.ofReal Φ ^ (r / 2) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) hr,
    ENNReal.ofReal_rpow_of_nonneg hΦ (by positivity), Real.sqrt_eq_rpow, ← Real.rpow_mul hΦ]
  congr 2
  ring

/-- Auxiliary: for orthonormal `e_j`, `‖∑_j c_j e_j‖ = (∑_j c_j²)^{1/2}`. -/
theorem norm_sum_orthonormal {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    {n : ℕ} {e : Fin n → G} (he : Orthonormal ℝ e) (c : Fin n → ℝ) :
    ‖∑ j, c j • e j‖ = √(∑ j, c j ^ 2) := by
  have h2 : ‖∑ j, c j • e j‖ ^ 2 = ∑ j, c j ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_left, he.inner_right_fintype c j, sq]
  rw [← h2, Real.sqrt_sq (norm_nonneg _)]

/-! ### Gaussian moments -/

/-- **The Gaussian moment `m_r = E|γ₁|^r`** (`integrated_uniform_mean.tex` lines 218-219 at
revision edf7085f (book 1.1.3)), as an extended real. -/
def gaussMoment (r : ℝ) : ℝ≥0∞ := ∫⁻ x, ‖x‖ₑ ^ r ∂(gaussianReal 0 1)

/-- Auxiliary: `m_r < ∞` (`r > 0`). -/
theorem gaussMoment_ne_top {r : ℝ} (hr : 0 < r) : gaussMoment r ≠ ⊤ := by
  have h := lintegral_enorm_rpow_eq (f := id) (μ := gaussianReal 0 1)
    aestronglyMeasurable_id hr
  rw [gaussMoment]
  simp only [id] at h
  rw [h]
  exact ENNReal.rpow_ne_top_of_nonneg hr.le
    (memLp_id_gaussianReal' _ ENNReal.ofReal_ne_top).eLpNorm_ne_top

/-- Auxiliary: `m_r > 0` (`r > 0`): `γ₁ ≠ 0` almost surely. -/
theorem gaussMoment_ne_zero {r : ℝ} (hr : 0 < r) : gaussMoment r ≠ 0 := by
  intro h
  rw [gaussMoment, lintegral_eq_zero_iff (by fun_prop)] at h
  have h0 : ∀ᵐ x ∂(gaussianReal 0 1), x = 0 := by
    filter_upwards [h] with x hx
    have hx' : ‖x‖ₑ ^ r = 0 := hx
    rw [ENNReal.rpow_eq_zero_iff] at hx'
    rcases hx' with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact enorm_eq_zero.1 h1
    · exact absurd h2 (not_lt.2 hr.le)
  have hc : gaussianReal 0 1 {x : ℝ | ¬ x = 0} = 0 := ae_iff.1 h0
  have hs : gaussianReal 0 1 ({0} : Set ℝ) = 0 :=
    gaussianReal_absolutelyContinuous 0 one_ne_zero Real.volume_singleton
  have hu := measure_univ_le_add_compl (μ := gaussianReal 0 1) ({0} : Set ℝ)
  rw [measure_univ, hs, zero_add] at hu
  have hcomp : ({0} : Set ℝ)ᶜ = {x : ℝ | ¬ x = 0} := by ext x; simp
  rw [hcomp, hc] at hu
  exact absurd hu (by norm_num)

variable {n : ℕ}

/-- Auxiliary: `E|σ γ₁|^r = |σ|^r m_r`: `∫ |x|^r d N(0, σ²) = |σ|^r m_r`. -/
theorem lintegral_gaussianReal_sq {r : ℝ} (hr : 0 < r) (σ : ℝ) :
    ∫⁻ x, ‖x‖ₑ ^ r ∂(gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩) = ‖σ‖ₑ ^ r * gaussMoment r := by
  have h2 : gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩ = (gaussianReal 0 1).map (σ * ·) := by
    rw [gaussianReal_map_const_mul, mul_zero, mul_one]
    rfl
  rw [h2, lintegral_map (by fun_prop) (by fun_prop)]
  simp_rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ hr.le]
  rw [lintegral_const_mul _ (by fun_prop), gaussMoment]

/-- **The one-dimensional marginals of the standard Gaussian vector** (`integrated_uniform_mean.tex`
lines 236-240 at revision edf7085f (book 1.1.3)): for `c ∈ ℝ^n`,
`E|⟪c, γ⟫|^r = ‖c‖^r m_r` (`⟪c, γ⟫` is `N(0, ‖c‖²)`). -/
theorem lintegral_inner_stdGaussian {r : ℝ} (hr : 0 < r) (c : EuclideanSpace ℝ (Fin n)) :
    ∫⁻ γ, ‖⟪c, γ⟫‖ₑ ^ r ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) =
      ‖c‖ₑ ^ r * gaussMoment r := by
  set L : StrongDual ℝ (EuclideanSpace ℝ (Fin n)) := innerSL ℝ c with hL
  have hmap : (stdGaussian (EuclideanSpace ℝ (Fin n))).map L =
      gaussianReal 0 ⟨‖c‖ ^ 2, sq_nonneg _⟩ := by
    rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian, hL, innerSL_apply_norm]
    congr 1
    ext
    exact Real.coe_toNNReal _ (sq_nonneg _)
  have h1 : ∫⁻ γ, ‖⟪c, γ⟫‖ₑ ^ r ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) =
      ∫⁻ x, ‖x‖ₑ ^ r ∂((stdGaussian (EuclideanSpace ℝ (Fin n))).map L) := by
    rw [lintegral_map (by fun_prop) L.continuous.measurable]
    rfl
  rw [h1, hmap, lintegral_gaussianReal_sq hr, enorm_norm]

/-- Auxiliary: `⟪c, γ⟫ = ∑_j c_j γ_j` on `ℝ^n`. -/
theorem inner_euclidean (c γ : EuclideanSpace ℝ (Fin n)) : ⟪c, γ⟫ = ∑ j, c j * γ j := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- **Scalar Gaussian moments** (`integrated_uniform_mean.tex` lines 243-245, after the display
238-242, at revision edf7085f (book 1.1.3): "For each fixed `t`, the scalar sum ... has variance
`∑_j |Af_j(t)|²`. Its
`r`th absolute moment is that variance to the power `r/2` times `m_r`"):
`E|∑_j γ_j a_j|^r = (∑_j a_j²)^{r/2} m_r`. -/
theorem lintegral_sum_gauss {r : ℝ} (hr : 0 < r) (a : Fin n → ℝ) :
    ∫⁻ γ, ‖∑ j, γ j * a j‖ₑ ^ r ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) =
      ENNReal.ofReal (∑ j, a j ^ 2) ^ (r / 2) * gaussMoment r := by
  set c : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 a with hc
  have hci : ∀ γ : EuclideanSpace ℝ (Fin n), ∑ j, γ j * a j = ⟪c, γ⟫ := by
    intro γ
    rw [inner_euclidean]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hc, PiLp.toLp_apply, mul_comm]
  simp_rw [hci]
  rw [lintegral_inner_stdGaussian hr c]
  congr 1
  have hn : ‖c‖ = √(∑ j, a j ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg c), EuclideanSpace.real_norm_sq_eq]
  rw [← ofReal_norm, hn, ofReal_sqrt_rpow (Finset.sum_nonneg fun j _ => sq_nonneg _) hr.le]

/-! ### Step 1: the Gaussian norm moment of a finite Hilbert sum -/

/-- **Step 1 of `L:uniform-mean-tensor`** (`integrated_uniform_mean.tex` lines 214-230 at
revision edf7085f (book 1.1.3)): for `f_j ∈ H₀` and `2 ≤ r`,
`E‖∑_j γ_j f_j‖^r ≤ m_r (∑_j ‖f_j‖²)^{r/2}`.  Route (differs from the TeX's diagonalization
and convexity, disclosed): an orthonormal basis `(b_l)` of `span{f_j}`, Parseval and
Minkowski's inequality in `L^{r/2}`. -/
theorem lintegral_norm_sum_gauss_le {H0 : Type*} [NormedAddCommGroup H0] [InnerProductSpace ℝ H0]
    {r : ℝ} (hr : 2 ≤ r) (f : Fin n → H0) :
    ∫⁻ γ, ‖∑ j, γ j • f j‖ₑ ^ r ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) ≤
      gaussMoment r * ENNReal.ofReal (∑ j, ‖f j‖ ^ 2) ^ (r / 2) := by
  have hr0 : 0 < r := by linarith
  set q : ℝ := r / 2 with hq
  have hq0 : 0 < q := by rw [hq]; linarith
  have hq1 : 1 ≤ q := by rw [hq]; linarith
  set μγ := stdGaussian (EuclideanSpace ℝ (Fin n)) with hμγ
  set W : Submodule ℝ H0 := Submodule.span ℝ (Set.range f) with hW
  have : FiniteDimensional ℝ W := FiniteDimensional.span_of_finite ℝ (Set.finite_range f)
  set b := stdOrthonormalBasis ℝ W with hb
  set k := Module.finrank ℝ W with hk
  -- the coefficient vectors `c_l = (⟪b_l, f_j⟫)_j`
  set c : Fin k → EuclideanSpace ℝ (Fin n) :=
    fun l => WithLp.toLp 2 fun j => ⟪((b l : W) : H0), f j⟫ with hc
  set Z : Fin k → EuclideanSpace ℝ (Fin n) → ℝ := fun l γ => ⟪c l, γ⟫ with hZ
  have hfW : ∀ j, f j ∈ W := fun j => Submodule.subset_span ⟨j, rfl⟩
  have hvW : ∀ γ : EuclideanSpace ℝ (Fin n), ∑ j, γ j • f j ∈ W := fun γ =>
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hfW j)
  -- Parseval in `W`
  have hpars : ∀ v : H0, v ∈ W → ‖v‖ ^ 2 = ∑ l, ⟪((b l : W) : H0), v⟫ ^ 2 := by
    intro v hv
    have h := b.sum_sq_inner_right (⟨v, hv⟩ : W)
    exact h.symm
  have hZv : ∀ γ l, Z l γ = ⟪((b l : W) : H0), ∑ j, γ j • f j⟫ := by
    intro γ l
    show ⟪c l, γ⟫ = _
    rw [inner_euclidean, inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hc, PiLp.toLp_apply, real_inner_smul_right, mul_comm]
  set Q : EuclideanSpace ℝ (Fin n) → ℝ := ∑ l, fun γ => Z l γ ^ 2 with hQ
  have hQapp : ∀ γ, Q γ = ∑ l, Z l γ ^ 2 := fun γ => by rw [hQ, Finset.sum_apply]
  have hQ0 : ∀ γ, 0 ≤ Q γ := fun γ => by
    rw [hQapp]; exact Finset.sum_nonneg fun l _ => sq_nonneg _
  have hZm : ∀ l, Continuous (Z l) := fun l => continuous_const.inner continuous_id
  have hQm : Continuous Q := by
    have hQf : Q = fun γ => ∑ l, Z l γ ^ 2 := funext hQapp
    rw [hQf]
    exact continuous_finsetSum _ fun l _ => (hZm l).pow 2
  -- `‖∑ γ_j f_j‖ₑ^r = ‖Q γ‖ₑ^q`
  have hpt : ∀ γ, ‖∑ j, γ j • f j‖ₑ ^ r = ‖Q γ‖ₑ ^ q := by
    intro γ
    have hsq : ‖∑ j, γ j • f j‖ = √(Q γ) := by
      rw [hQapp, ← Real.sqrt_sq (norm_nonneg _), hpars _ (hvW γ)]
      simp_rw [hZv]
    rw [← ofReal_norm, hsq, ofReal_sqrt_rpow (hQ0 γ) hr0.le, ← ofReal_norm,
      Real.norm_of_nonneg (hQ0 γ)]
  -- Minkowski in `L^q`
  have hmink : eLpNorm Q (ENNReal.ofReal q) μγ ≤
      ∑ l, eLpNorm (fun γ => Z l γ ^ 2) (ENNReal.ofReal q) μγ := by
    rw [hQ]
    exact eLpNorm_sum_le (by simpa using hq1)
  have hterm : ∀ l, eLpNorm (fun γ => Z l γ ^ 2) (ENNReal.ofReal q) μγ =
      ‖c l‖ₑ ^ (2 : ℝ) * gaussMoment r ^ (1 / q) := by
    intro l
    have h1 := lintegral_enorm_rpow_eq (f := fun γ => Z l γ ^ 2) (μ := μγ)
      ((hZm l).pow 2).aestronglyMeasurable hq0
    have h2 : ∫⁻ γ, ‖Z l γ ^ 2‖ₑ ^ q ∂μγ = ‖c l‖ₑ ^ r * gaussMoment r := by
      rw [← lintegral_inner_stdGaussian hr0 (c l)]
      refine lintegral_congr fun γ => ?_
      have e : ((2 : ℕ) : ℝ) * (r / 2) = r := by push_cast; ring
      rw [enorm_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, hq, e]
    rw [h2] at h1
    have h3 := congrArg (fun x : ℝ≥0∞ => x ^ (1 / q)) h1
    rw [← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one] at h3
    rw [← h3, ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, hq]
    congr 2
    field_simp
  -- `∑_l ‖c_l‖² = ∑_j ‖f_j‖²`
  have hcsum : ∑ l, ‖c l‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (∑ j, ‖f j‖ ^ 2) := by
    have hreal : ∑ l, ‖c l‖ ^ 2 = ∑ j, ‖f j‖ ^ 2 := by
      simp only [EuclideanSpace.real_norm_sq_eq, hc]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hpars _ (hfW j)]
    rw [← hreal, ENNReal.ofReal_sum_of_nonneg (fun l _ => sq_nonneg _)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
    norm_cast
  have hnorm : eLpNorm Q (ENNReal.ofReal q) μγ ≤
      gaussMoment r ^ (1 / q) * ENNReal.ofReal (∑ j, ‖f j‖ ^ 2) := by
    refine hmink.trans (le_of_eq ?_)
    simp_rw [hterm]
    rw [← Finset.sum_mul, hcsum, mul_comm]
  calc ∫⁻ γ, ‖∑ j, γ j • f j‖ₑ ^ r ∂μγ = ∫⁻ γ, ‖Q γ‖ₑ ^ q ∂μγ := lintegral_congr hpt
    _ = eLpNorm Q (ENNReal.ofReal q) μγ ^ q := lintegral_enorm_rpow_eq hQm.aestronglyMeasurable hq0
    _ ≤ (gaussMoment r ^ (1 / q) * ENNReal.ofReal (∑ j, ‖f j‖ ^ 2)) ^ q :=
        ENNReal.rpow_le_rpow hnorm hq0.le
    _ = gaussMoment r * ENNReal.ofReal (∑ j, ‖f j‖ ^ 2) ^ q := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne',
          ENNReal.rpow_one]

/-! ### Step 2 and the lemma -/

/-- **`L:uniform-mean-tensor`, the bound on finite tensors** (`integrated_uniform_mean.tex`
lines 198-204, proof Steps 1-2 lines 214-248, at revision edf7085f (book 1.1.3)), by
the Gaussian route: for `A : H₀ → L^r(I)` bounded, `2 ≤ r < ∞`, `f_j ∈ H₀` and orthonormal
`e_j ∈ G`, `‖∑_j (A f_j) e_j‖_{L^r(I;G)} ≤ ‖A‖ (∑_j ‖f_j‖²)^{1/2}`. -/
theorem tensor_extension_bound {H0 G : Type} [NormedAddCommGroup H0] [InnerProductSpace ℝ H0]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr : 2 ≤ r)
    (hrt : r ≠ ⊤) (A : H0 →L[ℝ] Lp ℝ r timeMeasure) (f : Fin n → H0) (e : Fin n → G)
    (he : Orthonormal ℝ e) (F : Lp G r timeMeasure)
    (hF : (F : ℝ → G) =ᵐ[timeMeasure] fun t => ∑ j, (A (f j) : ℝ → ℝ) t • e j) :
    ‖F‖ ≤ ‖A‖ * √(∑ j, ‖f j‖ ^ 2) := by
  set r0 := r.toReal with hr0def
  have hr0 : 2 ≤ r0 := by
    have h := ENNReal.toReal_mono hrt hr
    simpa using h
  have hr0p : 0 < r0 := by linarith
  have hrr : ENNReal.ofReal r0 = r := ENNReal.ofReal_toReal hrt
  set μγ := stdGaussian (EuclideanSpace ℝ (Fin n)) with hμγ
  set m := gaussMoment r0 with hm
  set a : Fin n → ℝ → ℝ := fun j => (A (f j) : ℝ → ℝ) with ha
  have ham : ∀ j, StronglyMeasurable (a j) := fun j => Lp.stronglyMeasurable _
  set Φ : ℝ → ℝ := fun t => ∑ j, a j t ^ 2 with hΦ
  have hΦ0 : ∀ t, 0 ≤ Φ t := fun t => Finset.sum_nonneg fun j _ => sq_nonneg _
  set S : ℝ := ∑ j, ‖f j‖ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => sq_nonneg _
  set X : ℝ≥0∞ := ∫⁻ t, ENNReal.ofReal (Φ t) ^ (r0 / 2) ∂timeMeasure with hX
  -- the `L^r` norm of `F` through `X`
  have hFX : eLpNorm (F : ℝ → G) r timeMeasure = X ^ (1 / r0) := by
    have h1 := lintegral_enorm_rpow_eq (Lp.aestronglyMeasurable F) hr0p
    rw [hrr] at h1
    have h2 : ∫⁻ t, ‖(F : ℝ → G) t‖ₑ ^ r0 ∂timeMeasure = X := by
      rw [hX]
      refine lintegral_congr_ae ?_
      filter_upwards [hF] with t ht
      rw [ht, ← ofReal_norm, norm_sum_orthonormal he, ofReal_sqrt_rpow (hΦ0 t) hr0p.le]
    rw [h2] at h1
    rw [h1, ← ENNReal.rpow_mul, mul_one_div_cancel hr0p.ne', ENNReal.rpow_one]
  -- joint measurability in `(t, γ)`
  have hjoint : Measurable (Function.uncurry fun (t : ℝ) (γ : EuclideanSpace ℝ (Fin n)) =>
      ‖∑ j, γ j * a j t‖ₑ ^ r0) := by
    have hc : ∀ j, Measurable fun p : ℝ × EuclideanSpace ℝ (Fin n) => p.2 j * a j p.1 := by
      intro j
      exact ((EuclideanSpace.proj j : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).continuous.measurable.comp
        measurable_snd).mul ((ham j).measurable.comp measurable_fst)
    have hs : Measurable fun p : ℝ × EuclideanSpace ℝ (Fin n) => ∑ j, p.2 j * a j p.1 :=
      Finset.measurable_sum _ fun j _ => hc j
    exact (hs.enorm.pow_const r0)
  -- `m X = ∫_t ∫_γ`
  have hstep1 : X * m = ∫⁻ t, ∫⁻ γ, ‖∑ j, γ j * a j t‖ₑ ^ r0 ∂μγ ∂timeMeasure := by
    rw [hX, ← lintegral_mul_const _ ?_]
    · refine lintegral_congr fun t => ?_
      rw [lintegral_sum_gauss hr0p]
    · have hΦm : Measurable Φ := by
        rw [hΦ]
        exact Finset.measurable_sum _ fun j _ => ((ham j).measurable.pow_const 2)
      exact hΦm.ennreal_ofReal.pow_const _
  -- Tonelli and the operator bound for each `γ`
  have hγ : ∀ γ : EuclideanSpace ℝ (Fin n), ∫⁻ t, ‖∑ j, γ j * a j t‖ₑ ^ r0 ∂timeMeasure ≤
      ENNReal.ofReal ‖A‖ ^ r0 * ‖∑ j, γ j • f j‖ₑ ^ r0 := by
    intro γ
    set v := ∑ j, γ j • f j with hv
    have hAv : (A v : ℝ → ℝ) =ᵐ[timeMeasure] fun t => ∑ j, γ j * a j t := by
      have h1 : A v = ∑ j, γ j • A (f j) := by rw [hv, map_sum]; simp_rw [map_smul]
      rw [h1]
      filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ fun j => γ j • A (f j),
        eventually_all.2 fun j => Lp.coeFn_smul (γ j) (A (f j))] with t h2 h3
      rw [h2]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [h3 j, Pi.smul_apply, smul_eq_mul]
    have h1 : ∫⁻ t, ‖∑ j, γ j * a j t‖ₑ ^ r0 ∂timeMeasure =
        ∫⁻ t, ‖(A v : ℝ → ℝ) t‖ₑ ^ r0 ∂timeMeasure :=
      lintegral_congr_ae (hAv.mono fun t ht => by simp only [ht])
    rw [h1, lintegral_enorm_rpow_eq (Lp.aestronglyMeasurable _) hr0p, hrr]
    have h2 : eLpNorm (A v : ℝ → ℝ) r timeMeasure = ENNReal.ofReal ‖A v‖ := by
      rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
    rw [h2, ← ENNReal.mul_rpow_of_nonneg _ _ hr0p.le]
    refine ENNReal.rpow_le_rpow ?_ hr0p.le
    rw [← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (A.le_opNorm v)
  have hstep2 : ∫⁻ t, ∫⁻ γ, ‖∑ j, γ j * a j t‖ₑ ^ r0 ∂μγ ∂timeMeasure ≤
      ENNReal.ofReal ‖A‖ ^ r0 * (m * ENNReal.ofReal S ^ (r0 / 2)) := by
    rw [lintegral_lintegral_swap hjoint.aemeasurable]
    calc ∫⁻ γ, ∫⁻ t, ‖∑ j, γ j * a j t‖ₑ ^ r0 ∂timeMeasure ∂μγ
        ≤ ∫⁻ γ, ENNReal.ofReal ‖A‖ ^ r0 * ‖∑ j, γ j • f j‖ₑ ^ r0 ∂μγ := lintegral_mono hγ
      _ = ENNReal.ofReal ‖A‖ ^ r0 * ∫⁻ γ, ‖∑ j, γ j • f j‖ₑ ^ r0 ∂μγ :=
          lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hr0p.le ENNReal.ofReal_ne_top)
      _ ≤ ENNReal.ofReal ‖A‖ ^ r0 * (m * ENNReal.ofReal S ^ (r0 / 2)) :=
          mul_le_mul_right (lintegral_norm_sum_gauss_le hr0 f) _
  -- cancel `m`
  have hX' : X ≤ ENNReal.ofReal ‖A‖ ^ r0 * ENNReal.ofReal S ^ (r0 / 2) := by
    have h := (hstep1.trans_le hstep2)
    rw [mul_comm X m, mul_left_comm] at h
    exact (ENNReal.mul_le_mul_iff_right (gaussMoment_ne_zero hr0p) (gaussMoment_ne_top hr0p)).1 h
  have hfin : eLpNorm (F : ℝ → G) r timeMeasure ≤ ENNReal.ofReal (‖A‖ * √S) := by
    rw [hFX]
    calc X ^ (1 / r0) ≤ (ENNReal.ofReal ‖A‖ ^ r0 * ENNReal.ofReal S ^ (r0 / 2)) ^ (1 / r0) :=
          ENNReal.rpow_le_rpow hX' (by positivity)
      _ = ENNReal.ofReal (‖A‖ * √S) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
            ← ENNReal.rpow_mul, mul_one_div_cancel hr0p.ne', ENNReal.rpow_one,
            ENNReal.ofReal_mul (norm_nonneg _), Real.sqrt_eq_rpow,
            ENNReal.ofReal_rpow_of_nonneg hS0
              (mul_nonneg (by linarith) (one_div_nonneg.2 hr0p.le))]
          congr 2
          field_simp
  rw [Lp.norm_def]
  calc (eLpNorm (F : ℝ → G) r timeMeasure).toReal ≤ (ENNReal.ofReal (‖A‖ * √S)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hfin
    _ = ‖A‖ * √S := ENNReal.toReal_ofReal (mul_nonneg A.opNorm_nonneg (Real.sqrt_nonneg _))

/-- **`L:uniform-mean-tensor`, the non-compactness sentence** (`integrated_uniform_mean.tex`
lines 205 and 250-253 at revision edf7085f (book 1.1.3)): for orthonormal `e_j`, the
images `t ↦ (A f)(t) e_j` of `f ⊗ e_j` have pairwise distance `√2 ‖A f‖_{L^r}`. -/
theorem tensor_noncompact {H0 G : Type} [NormedAddCommGroup H0] [InnerProductSpace ℝ H0]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (A : H0 →L[ℝ] Lp ℝ r timeMeasure) (f : H0) (e : ℕ → G) (he : Orthonormal ℝ e)
    (F : ℕ → Lp G r timeMeasure)
    (hF : ∀ j, (F j : ℝ → G) =ᵐ[timeMeasure] fun t => (A f : ℝ → ℝ) t • e j) (i j : ℕ)
    (hij : i ≠ j) : ‖F i - F j‖ = √2 * ‖A f‖ := by
  have hd : ‖e i - e j‖ = √2 := by
    have h2 : ‖e i - e j‖ ^ 2 = 2 := by
      rw [@norm_sub_sq_real, he.1 i, he.1 j, he.2 hij]
      norm_num
    rw [← h2, Real.sqrt_sq (norm_nonneg _)]
  have hae : ∀ᵐ t ∂timeMeasure, ‖((F i - F j : Lp G r timeMeasure) : ℝ → G) t‖ =
      ‖(((√2 : ℝ) • A f : Lp ℝ r timeMeasure) : ℝ → ℝ) t‖ := by
    filter_upwards [Lp.coeFn_sub (F i) (F j), hF i, hF j, Lp.coeFn_smul (√2 : ℝ) (A f)]
      with t h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h2, h3, h4, Pi.smul_apply, ← smul_sub, norm_smul, norm_smul, hd,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_comm]
  have hnorm : ‖F i - F j‖ = ‖(√2 : ℝ) • A f‖ := by
    rw [Lp.norm_def, Lp.norm_def,
      eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _) hae]
  rw [hnorm, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]

/-- **D target 1, `L:uniform-mean-tensor`** (`integrated_uniform_mean.tex` lines 198-206, proof
208-255, at revision edf7085f (book 1.1.3)), by the Gaussian route (decision 5 of
L16): the dimension-free tensor bound on finite tensors with orthonormal second factors, and the
non-compactness sentence. -/
theorem uniform_mean_tensor : TensorExtensionTarget ∧ TensorNoncompactTarget := by
  refine ⟨?_, ?_⟩
  · intro H0 G _ _ _ _ _ _ r _ hr hrt A n f e he F hF
    exact tensor_extension_bound hr hrt A f e he F hF
  · intro H0 G _ _ _ _ _ _ r _ _ A f e he F hF i j hij
    exact tensor_noncompact A f e he F hF i j hij

end StratonovichHAMSecondMoment.UniformMeanTensor
