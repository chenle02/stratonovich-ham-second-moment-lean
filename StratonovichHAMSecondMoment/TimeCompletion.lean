module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Lemma `L:masked-time-completion` (Temporal covariance completion) of
`notes/integrated_covariance_foundation.tex` at revision a284420 (statement TeX lines
141-156, display `E:masked-time-schur` 150-152, proof 158-181), with the completion
`H_a` constructed, and Lemma `L:masked-trig-products` (TeX lines 347-374) re-issued
with nothing supplied.

Standing hypotheses.  `T > 0` and `0 < a < 1` (the section's `a = α₀`; TeX lines 4-7).
The section also assumes `H:homog` and `Γ ≠ 0`, but states that "the purely temporal
estimates remain valid independently of `Γ`" (lines 5-8); this lemma is purely
temporal, so neither `H:homog` nor `Γ ≠ 0` is assumed here.

What is constructed and proved (`masked_time_completion_paper`):
* the form `⟨f,g⟩_a = ∬_{[0,T]²} f(t) conj g(s) |t-s|^{-a}` (`TimeSchur.timeForm`) is a
  Hermitian positive semidefinite sesquilinear form on complex `L²(0,T)`
  (`timeForm_add_right`, `timeForm_smul_right`, `conj_timeForm`, `timeForm_re_nonneg`);
  this contains the TeX's positivity on real compact smooth tests (lines 143-147);
* `H_a` (`Ha p`) is Mathlib's `UniformSpace.Completion` of `L²(0,T)` with this
  pre-inner product: a separable complex Hilbert space (`separableSpace_Ha`), in which
  functions at seminorm distance zero are identified (the null quotient);
* the inclusion `emb p : L²(0,T) → H_a` satisfies `‖emb f‖² = Re⟨f,f⟩_a`
  (`emb_norm_sq`), the Schur bound `E:masked-time-schur` (`emb_norm_sq_le`), and
  factors through a continuous linear map on a.e.-classes `extL2 p` with
  `‖extL2 p w‖² ≤ (2T^{1-a}/(1-a))‖w‖²` (lines 148-149, 177-179);
* complexification (lines 153-154, 175-177): `‖emb f‖²` equals the complex double
  integral with `f(t) conj f(s)` (`emb_norm_sq_eq_timeForm`), it is the sum of the
  squared norms of the real and imaginary parts (`emb_norm_sq_re_im`), and for real `g`
  it is the real double integral `∬ g(t) g(s) |t-s|^{-a}` (`emb_norm_sq_real`);
* interval amplitudes (lines 154-155): `indicator_mem_L2fun`;
* the complex compact smooth tests supported in `(0,T)` have dense image in `H_a`
  (`dense_emb_testSet`), and the complex span of the real ones is dense
  (`dense_span_realTestSet`); hence `H_a` is the complexified null-quotient completion
  of the real tests, as in the TeX (Le's decision 3 stretch: done).

Re-issued `L:masked-trig-products` (`masked_trig_products_completed_paper`):
`MaskedModulation.masked_trig_products_bridged_paper` instantiated with `E = H_a`,
`V = L²(0,T)` and `emb`; its two supplied inputs `hmem` and `hnorm` now hold by
construction (`MaskedModulation.memLp_modeFn`, `emb_norm_sq`).  No supplied input
remains.  The existing modules are not modified.

Proof route and differences from the TeX.
* Positivity follows the TeX (lines 159-172): Gamma subordination
  (`TimeFractional.rpow_neg_eq_subordination`) and the exponential-kernel identity
  (`exp_abs_eq`) give, off the null diagonal, `|t-s|^{-a}` as a mixture
  `∫ ρ(λ,u) φ_{λ,u}(t) φ_{λ,u}(s)` with `ρ = Γ(a)⁻¹2λ^a ≥ 0`,
  `φ_{λ,u}(t) = 1_{u≤t} e^{-λ(t-u)}` (`kern_eq_mixture`).  The TeX treats each `λ`
  separately; here one Fubini over `[0,T]² × (0,∞) × ℝ` (absolute integrability from
  the Schur bound, as in the TeX) gives `Re⟨f,f⟩_a = ∫ ρ |∫ f φ|² ≥ 0`
  (`re_form_nonneg_of_mixture`).  It is proved for all complex `f ∈ L²(0,T)`, not only
  real tests.
* Separability: the TeX uses a countable `L²`-dense family of tests; here the
  separability of `L²(0,T)` (Mathlib) and the Lipschitz map `w ↦ ⇑w` into the
  pre-Hilbert space (`lipschitz_ofLp`, from the Schur bound).
* Extension: the TeX extends the inclusion from tests to `L²` by density; here `H_a`
  is built over `L²(0,T)` directly, so the inclusion is defined on `L²` and the density
  of tests is proved afterwards (`exists_test_approx`: Mathlib's smooth approximation
  `MemLp.exist_eLpNorm_sub_le`, a smooth bump equal to one on `[η, T-η]`, and uniform
  integrability `MemLp.eLpNorm_indicator_le` for the boundary layer).
* `H_a` is built directly over `ℂ`; the TeX's real completion is represented by the
  real functions (items 1, 5 of the wrapper), not by a separate real Hilbert space.

Conventions and side conditions made explicit here:
* `L²(0,T)` is `L2fun T = {f : ℝ → ℂ | MemLp f 2 (volume.restrict (Icc 0 T))}`, a space
  of functions; `[0,T]` versus `(0,T)` is immaterial.  `Lp ℂ 2 …` (a.e.-classes) is used
  only for `extL2` and separability.
* The kernel is `TimeSchur.kern a x = |x|^{-a}`; on the diagonal it takes Lean's value
  `0^{-a} = 0`.  The diagonal is null for the product measure (`ae_ne_diag`), and the
  mixture identity is used only off it.
* The form is an iterated Bochner integral; its integrand is integrable on `[0,T]²` for
  `f, g ∈ L²(0,T)` (`cross_integrable`), and integrability is part of the wrapper's
  integral conclusions (items 1 and 5), so no integral is Lean's junk `0`.
* `mixWeight` uses `|λ|^a` (equal to `λ^a` on `λ > 0`, the only values charged by
  `mixMeasure`) so that no `rpow` of a negative base occurs.
* The suprema `M`, `D` of `L:masked-trig-products` are finite (`I` compact, `A ∈ C¹`;
  `MaskedModulation.envelope_of_contDiffOn`), so `sSup` is not Lean's junk value.
* Hypotheses carried but not used: `tsupport f ⊆ (0,T)` in item 1 of the wrapper
  (positivity holds on all of `L²(0,T)`); `h ≤ 1` in the trig-products wrapper.

Auxiliary to the Lean proof route (no direct manuscript label): every declaration whose
doc string says "Auxiliary", `TimeParams`, `Pre`, `core`, the instances, `L2fun`,
`schurConst`, `testSet`, `realTestSet`, `extL2Lin`.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.TimeSchur
public import StratonovichHAMSecondMoment.TimeFractional
public import StratonovichHAMSecondMoment.MaskedModulation

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set
open scoped ComplexConjugate ENNReal

namespace StratonovichHAMSecondMoment.TimeCompletion

open StratonovichHAMSecondMoment.TimeSchur

/-! ### The exponential kernel and Gamma subordination (TeX lines 159-169) -/

/-- The exponential-kernel identity of the proof (TeX lines 164-169): for `λ > 0`,
`e^{-λ|t-s|} = 2λ ∫_{-∞}^{min(t,s)} e^{-λ(t-u)} e^{-λ(s-u)} du`. -/
theorem exp_abs_eq (l t s : ℝ) (hl : 0 < l) :
    Real.exp (-(l * |t - s|)) =
      2 * l * ∫ u in Iic (min t s), Real.exp (-(l * (t - u))) * Real.exp (-(l * (s - u))) := by
  have h : ∀ u, Real.exp (-(l * (t - u))) * Real.exp (-(l * (s - u))) =
      Real.exp (-(l * (t + s))) * Real.exp ((2 * l) * u) := by
    intro u; rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  simp_rw [h]
  rw [integral_const_mul, integral_exp_mul_Iic (by linarith) (min t s)]
  have hl2 : (2 * l) ≠ 0 := by positivity
  rw [mul_comm (2 * l) _, mul_assoc, div_mul_cancel₀ _ hl2, ← Real.exp_add]
  congr 1
  rcases le_total t s with h | h
  · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
  · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring

/-- Auxiliary: for `λ > 0` the product `e^{-λ(t-u)} e^{-λ(s-u)}` is integrable in `u`
on every half-line `(-∞, c]`. -/
theorem integrableOn_exp_pair (l t s c : ℝ) (hl : 0 < l) :
    IntegrableOn (fun u => Real.exp (-(l * (t - u))) * Real.exp (-(l * (s - u)))) (Iic c) := by
  have h : ∀ u, Real.exp (-(l * (t - u))) * Real.exp (-(l * (s - u))) =
      Real.exp (-(l * (t + s))) * Real.exp ((2 * l) * u) := by
    intro u; rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  simp_rw [h]
  exact (integrableOn_exp_mul_Iic (by linarith) c).const_mul _

/-- Auxiliary to the Lean proof route: the mixing weight `Γ(a)⁻¹ · 2|λ|^a` on the
parameter pair `w = (λ, u)` (only `λ > 0` is charged by `mixMeasure`; the absolute
value keeps the weight nonnegative everywhere). -/
def mixWeight (a : ℝ) (w : ℝ × ℝ) : ℝ := (Real.Gamma a)⁻¹ * (2 * |w.1| ^ a)

/-- Auxiliary to the Lean proof route: the profile `t ↦ 1_{u ≤ t} e^{-λ(t-u)}` of the
parameter pair `w = (λ, u)`. -/
def mixProfile (w : ℝ × ℝ) (t : ℝ) : ℝ :=
  if w.2 ≤ t then Real.exp (-(w.1 * (t - w.2))) else 0

/-- Auxiliary to the Lean proof route: Lebesgue measure on `(0,∞) × ℝ` (the pairs
`(λ, u)`), an s-finite product measure. -/
abbrev mixMeasure : Measure (ℝ × ℝ) := (volume.restrict (Ioi (0 : ℝ))).prod volume

/-- Auxiliary: the mixing weight is measurable. -/
theorem measurable_mixWeight (a : ℝ) : Measurable (mixWeight a) := by
  unfold mixWeight; fun_prop

/-- Auxiliary: the profile is jointly measurable. -/
theorem measurable_mixProfile : Measurable (Function.uncurry mixProfile) := by
  have : Function.uncurry mixProfile = fun q : (ℝ × ℝ) × ℝ =>
      if q.1.2 ≤ q.2 then Real.exp (-(q.1.1 * (q.2 - q.1.2))) else 0 := rfl
  rw [this]
  exact Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) (by fun_prop) (by fun_prop)

/-- Auxiliary: the mixing weight is nonnegative (`a > 0`, so `Γ(a) > 0`). -/
theorem mixWeight_nonneg (a : ℝ) (ha : 0 < a) (w : ℝ × ℝ) : 0 ≤ mixWeight a w :=
  mul_nonneg (inv_nonneg.2 (Real.Gamma_pos_of_pos ha).le)
    (mul_nonneg zero_le_two (Real.rpow_nonneg (abs_nonneg _) _))

/-- Auxiliary: the profile is nonnegative. -/
theorem mixProfile_nonneg (w : ℝ × ℝ) (t : ℝ) : 0 ≤ mixProfile w t := by
  unfold mixProfile; split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

/-- The kernel as a mixture of products (TeX lines 159-169, combined): for `a > 0` and
`t ≠ s` (off the null diagonal),
`|t-s|^{-a} = ∫_{(0,∞)×ℝ} Γ(a)⁻¹ 2λ^a 1_{u≤t} e^{-λ(t-u)} 1_{u≤s} e^{-λ(s-u)} dλ du`,
as an identity in `[0,∞]` (Tonelli).  It combines the subordination formula
`TimeFractional.rpow_neg_eq_subordination` with `exp_abs_eq`. -/
theorem kern_eq_mixture (a : ℝ) (ha : 0 < a) (t s : ℝ) (hts : t ≠ s) :
    ENNReal.ofReal (kern a (t - s)) =
      ∫⁻ w, ENNReal.ofReal (mixWeight a w * mixProfile w t * mixProfile w s) ∂mixMeasure := by
  have hm : Measurable fun w : ℝ × ℝ =>
      ENNReal.ofReal (mixWeight a w * mixProfile w t * mixProfile w s) := by
    refine ENNReal.measurable_ofReal.comp (((measurable_mixWeight a).mul ?_).mul ?_)
    · exact measurable_mixProfile.comp (measurable_id.prodMk measurable_const)
    · exact measurable_mixProfile.comp (measurable_id.prodMk measurable_const)
  rw [lintegral_prod _ hm.aemeasurable]
  set r := |t - s|
  have hr : 0 < r := abs_pos.2 (sub_ne_zero.2 hts)
  have hG : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have hinner : ∀ l ∈ Ioi (0 : ℝ),
      ∫⁻ u, ENNReal.ofReal (mixWeight a (l, u) * mixProfile (l, u) t * mixProfile (l, u) s) =
        ENNReal.ofReal ((Real.Gamma a)⁻¹ * TimeFractional.subKernel a r l) := by
    intro l hl
    have hl : 0 < l := hl
    have hpt : ∀ u, mixWeight a (l, u) * mixProfile (l, u) t * mixProfile (l, u) s =
        (Iic (min t s)).indicator (fun u => ((Real.Gamma a)⁻¹ * (2 * |l| ^ a)) *
          (Real.exp (-(l * (t - u))) * Real.exp (-(l * (s - u))))) u := by
      intro u
      by_cases hu : u ≤ min t s
      · rw [indicator_of_mem (show u ∈ Iic (min t s) from hu)]
        have hu1 : u ≤ t := hu.trans (min_le_left _ _)
        have hu2 : u ≤ s := hu.trans (min_le_right _ _)
        simp only [mixProfile, mixWeight, hu1, hu2, ↓reduceIte]
        ring
      · rw [indicator_of_notMem (show u ∉ Iic (min t s) from hu)]
        rcases min_lt_iff.1 (not_le.1 hu) with h | h
        · simp [mixProfile, not_le.2 h]
        · simp [mixProfile, not_le.2 h]
    simp_rw [hpt]
    have hint : Integrable ((Iic (min t s)).indicator (fun u => ((Real.Gamma a)⁻¹ * (2 * |l| ^ a)) *
          (Real.exp (-(l * (t - u))) * Real.exp (-(l * (s - u)))))) := by
      refine (integrable_indicator_iff measurableSet_Iic).2 ?_
      exact (integrableOn_exp_pair l t s _ hl).const_mul _
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ fun u => ?_), integral_indicator measurableSet_Iic, integral_const_mul]
    · congr 1
      have he := exp_abs_eq l t s hl
      have hI : ∫ u in Iic (min t s), Real.exp (-(l * (t - u))) * Real.exp (-(l * (s - u))) =
          Real.exp (-(l * r)) / (2 * l) := by
        rw [he]; field_simp
      rw [hI, abs_of_pos hl]
      simp only [TimeFractional.subKernel]
      rw [Real.rpow_sub_one hl.ne']
      field_simp
    · by_cases hu : u ∈ Iic (min t s)
      · rw [indicator_of_mem hu]
        exact mul_nonneg (mixWeight_nonneg a ha (l, 0)) (by positivity)
      · rw [indicator_of_notMem hu]; rfl
  rw [setLIntegral_congr_fun measurableSet_Ioi hinner]
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((TimeFractional.subKernel_integrable a r ha hr).const_mul _) ?_]
  · rw [integral_const_mul, ← TimeFractional.rpow_neg_eq_subordination a r ha hr]
    rfl
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with l hl
    exact mul_nonneg (inv_nonneg.2 hG.le) (TimeFractional.subKernel_nonneg a r l (le_of_lt hl))

/-- Auxiliary: the diagonal `{t = s}` is null for the product of Lebesgue measure on
`[0,T]` with itself. -/
theorem ae_ne_diag (T : ℝ) :
    ∀ᵐ q ∂((volume.restrict (Icc (0 : ℝ) T)).prod (volume.restrict (Icc (0 : ℝ) T))),
      q.1 ≠ q.2 := by
  have hD : ((volume.restrict (Icc (0 : ℝ) T)).prod (volume.restrict (Icc (0 : ℝ) T)))
      {q : ℝ × ℝ | q.1 = q.2} = 0 := by
    rw [Measure.measure_prod_null (measurableSet_eq_fun measurable_fst measurable_snd)]
    refine Filter.Eventually.of_forall fun x => ?_
    have : Prod.mk x ⁻¹' {q : ℝ × ℝ | q.1 = q.2} = {x} := by
      ext y; simp [eq_comm]
    simp only [this, Pi.zero_apply]
    exact le_antisymm ((Measure.restrict_apply_le _ _).trans (by simp)) bot_le
  rw [ae_iff]
  simpa using hD

/-! ### A positivity criterion for mixtures of product kernels -/

/-- Auxiliary to the Lean proof route (the abstract form of TeX lines 170-171, "its
quadratic form is an integral of a square"): let `μ` on `ℝ` and `ν` on `W` be
s-finite, `ρ ≥ 0` measurable on `W`, `φ ≥ 0` jointly measurable on `W × ℝ`, and
`K ≥ 0` a kernel with `K(t,s) = ∫ ρ(w) φ_w(t) φ_w(s) dν(w)` (in `[0,∞]`) for
`μ⊗μ`-a.e. `(t,s)`.  If `f` is a.e.-strongly measurable and
`f(t) conj f(s) K(t,s)` is `μ⊗μ`-integrable, then
`Re ∬ f(t) conj f(s) K(t,s) ≥ 0`; indeed the integral equals
`∫ ρ(w) |∫ f φ_w dμ|² dν(w)` (Fubini on the triple product). -/
theorem re_form_nonneg_of_mixture {W : Type*} [MeasurableSpace W]
    (μ : Measure ℝ) [SFinite μ] (ν : Measure W) [SFinite ν]
    (ρ : W → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ w, 0 ≤ ρ w)
    (φ : W → ℝ → ℝ) (hφ : Measurable (Function.uncurry φ)) (hφ0 : ∀ w t, 0 ≤ φ w t)
    (K : ℝ × ℝ → ℝ) (hK0 : ∀ p, 0 ≤ K p)
    (hK : ∀ᵐ p ∂(μ.prod μ),
      ENNReal.ofReal (K p) = ∫⁻ w, ENNReal.ofReal (ρ w * φ w p.1 * φ w p.2) ∂ν)
    (f : ℝ → ℂ) (hf : AEStronglyMeasurable f μ)
    (hint : Integrable (fun p : ℝ × ℝ => f p.1 * conj (f p.2) * (K p : ℂ)) (μ.prod μ)) :
    0 ≤ (∫ p, f p.1 * conj (f p.2) * (K p : ℂ) ∂(μ.prod μ)).re := by
  set m := μ.prod μ
  set F : (ℝ × ℝ) × W → ℂ := fun q =>
    f q.1.1 * conj (f q.1.2) * ((ρ q.2 * φ q.2 q.1.1 * φ q.2 q.1.2 : ℝ) : ℂ) with hFdef
  have hkm : Measurable fun q : (ℝ × ℝ) × W => ρ q.2 * φ q.2 q.1.1 * φ q.2 q.1.2 := by
    have h1 : Measurable fun q : (ℝ × ℝ) × W => φ q.2 q.1.1 :=
      hφ.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))
    have h2 : Measurable fun q : (ℝ × ℝ) × W => φ q.2 q.1.2 :=
      hφ.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
    exact ((hρ.comp measurable_snd).mul h1).mul h2
  have hknn : ∀ q : (ℝ × ℝ) × W, 0 ≤ ρ q.2 * φ q.2 q.1.1 * φ q.2 q.1.2 := fun q =>
    mul_nonneg (mul_nonneg (hρ0 _) (hφ0 _ _)) (hφ0 _ _)
  have hFm : AEStronglyMeasurable F (m.prod ν) := by
    refine ((hf.comp_fst.comp_fst).mul ?_).mul ?_
    · exact (Complex.continuous_conj.comp_aestronglyMeasurable hf.comp_snd).comp_fst
    · exact (Complex.continuous_ofReal.measurable.comp hkm).aestronglyMeasurable
  -- the a.e. section identity
  have hsec : ∀ᵐ p ∂m, ∫ w, F (p, w) ∂ν = f p.1 * conj (f p.2) * (K p : ℂ) := by
    filter_upwards [hK] with p hp
    have hmw : Measurable fun w => ρ w * φ w p.1 * φ w p.2 :=
      hkm.comp (measurable_const.prodMk measurable_id)
    have hKr : ∫ w, ρ w * φ w p.1 * φ w p.2 ∂ν = K p := by
      rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun w => hknn (p, w))
        hmw.aestronglyMeasurable, ← hp, ENNReal.toReal_ofReal (hK0 p)]
    simp only [hFdef]
    rw [integral_const_mul, integral_complex_ofReal, hKr]
  -- integrability on the triple product
  have hFi : Integrable F (m.prod ν) := by
    refine ⟨hFm, ?_⟩
    have hen : ∀ q : (ℝ × ℝ) × W, ‖F q‖ₑ = ‖f q.1.1‖ₑ * ‖f q.1.2‖ₑ *
        ENNReal.ofReal (ρ q.2 * φ q.2 q.1.1 * φ q.2 q.1.2) := by
      intro q
      simp only [hFdef, enorm_mul, RCLike.enorm_conj]
      rw [← ofReal_norm (((ρ q.2 * φ q.2 q.1.1 * φ q.2 q.1.2 : ℝ) : ℂ)), Complex.norm_real,
        Real.norm_of_nonneg (hknn q)]
    have hm2 : AEMeasurable (fun q : (ℝ × ℝ) × W => ‖F q‖ₑ) (m.prod ν) :=
      hFm.enorm
    show ∫⁻ q, ‖F q‖ₑ ∂(m.prod ν) < ∞
    rw [lintegral_prod _ hm2]
    have heq : ∀ᵐ p ∂m, ∫⁻ w, ‖F (p, w)‖ₑ ∂ν =
        ‖f p.1 * conj (f p.2) * (K p : ℂ)‖ₑ := by
      filter_upwards [hK] with p hp
      simp_rw [hen]
      have hmw : Measurable fun w => ENNReal.ofReal (ρ w * φ w p.1 * φ w p.2) :=
        ENNReal.measurable_ofReal.comp (hkm.comp (measurable_const.prodMk measurable_id))
      rw [lintegral_const_mul _ hmw, ← hp]
      simp only [enorm_mul, RCLike.enorm_conj]
      rw [← ofReal_norm (K p : ℂ), Complex.norm_real, Real.norm_of_nonneg (hK0 p)]
    rw [lintegral_congr_ae heq]
    exact hint.2
  -- assemble
  have hswap : ∫ p, ∫ w, F (p, w) ∂ν ∂m = ∫ w, ∫ p, F (p, w) ∂m ∂ν :=
    integral_integral_swap (f := fun p w => F (p, w)) hFi
  have hinner : ∀ w, ∫ p, F (p, w) ∂m =
      ((ρ w * Complex.normSq (∫ t, f t * (φ w t : ℂ) ∂μ) : ℝ) : ℂ) := by
    intro w
    have hpt : ∀ p : ℝ × ℝ, F (p, w) = (ρ w : ℂ) * ((f p.1 * (φ w p.1 : ℂ)) *
        conj (f p.2 * (φ w p.2 : ℂ))) := by
      intro p
      simp only [hFdef, map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
      ring
    simp_rw [hpt]
    rw [integral_const_mul]
    erw [integral_prod_mul (μ := μ) (ν := μ) (fun t => f t * (φ w t : ℂ))
      (fun s => conj (f s * (φ w s : ℂ)))]
    rw [integral_conj, Complex.mul_conj]
    push_cast
    ring
  rw [integral_congr_ae (Filter.EventuallyEq.symm hsec), hswap]
  simp_rw [hinner]
  rw [integral_complex_ofReal, Complex.ofReal_re]
  exact integral_nonneg fun w => mul_nonneg (hρ0 w) (Complex.normSq_nonneg _)

/-! ### The form on `L²(0,T)` -/

/-- `L²(0,T)` as a complex subspace of functions `ℝ → ℂ`: the functions `f` with
`MemLp f 2 (volume.restrict (Icc 0 T))` (`[0,T]` versus `(0,T)` is immaterial).
Its elements are functions, not a.e.-classes; the completion below identifies
functions at seminorm distance zero. -/
def L2fun (T : ℝ) : Submodule ℂ (ℝ → ℂ) where
  carrier := {f | MemLp f 2 (volume.restrict (Icc 0 T))}
  add_mem' := fun hf hg => hf.add hg
  zero_mem' := MemLp.zero
  smul_mem' := fun c _ hf => hf.const_smul c

/-- Auxiliary: for `f, g ∈ L²(0,T)` and `a < 1`, the integrand
`f(t) conj g(s) |t-s|^{-a}` is integrable on `[0,T]²` (Schur bound applied to
`|f| + |g|`). -/
theorem cross_integrable {a T : ℝ} (ha1 : a < 1) (hT : 0 ≤ T) (f g : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Icc 0 T))) (hg : MemLp g 2 (volume.restrict (Icc 0 T))) :
    Integrable (fun p : ℝ × ℝ => f p.1 * conj (g p.2) * ((kern a (p.1 - p.2) : ℝ) : ℂ))
      ((volume.restrict (Icc 0 T)).prod (volume.restrict (Icc 0 T))) := by
  set F : ℝ → ℝ := fun t => ‖f t‖ + ‖g t‖
  have hF : MemLp F 2 (volume.restrict (Icc 0 T)) := hf.norm.add hg.norm
  obtain ⟨hi, -⟩ := time_schur_rclike (𝕜 := ℝ) ha1 hT F hF
  refine hi.mono ?_ (Filter.Eventually.of_forall fun p => ?_)
  · exact ((hf.aestronglyMeasurable.comp_fst).mul
      (Complex.continuous_conj.comp_aestronglyMeasurable hg.aestronglyMeasurable.comp_snd)).mul
      (Complex.continuous_ofReal.measurable.comp ((measurable_kern a).comp
        (measurable_fst.sub measurable_snd))).aestronglyMeasurable
  · simp only [integrand, F, norm_mul, Complex.norm_conj, Complex.norm_real,
      Real.norm_eq_abs, RCLike.conj_to_real, RCLike.ofReal_real_eq_id, id]
    rw [abs_of_nonneg (kern_nonneg a _)]
    have h1 : 0 ≤ ‖f p.1‖ + ‖g p.1‖ := by positivity
    have h2 : 0 ≤ ‖f p.2‖ + ‖g p.2‖ := by positivity
    rw [abs_of_nonneg h1, abs_of_nonneg h2]
    have hk := kern_nonneg a (p.1 - p.2)
    have e1 : ‖f p.1‖ ≤ ‖f p.1‖ + ‖g p.1‖ := by linarith [norm_nonneg (g p.1)]
    have e2 : ‖g p.2‖ ≤ ‖f p.2‖ + ‖g p.2‖ := by linarith [norm_nonneg (f p.2)]
    exact mul_le_mul_of_nonneg_right (mul_le_mul e1 e2 (norm_nonneg _) h1) hk

/-- Auxiliary: for `f, g ∈ L²(0,T)`, `a < 1`, the iterated integral `timeForm` equals the
integral over the product `[0,T]²` (Fubini). -/
theorem timeForm_eq_prod {a T : ℝ} (ha1 : a < 1) (hT : 0 ≤ T) {f g : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Icc 0 T))) (hg : MemLp g 2 (volume.restrict (Icc 0 T))) :
    timeForm a T f g = ∫ p, f p.1 * conj (g p.2) * ((kern a (p.1 - p.2) : ℝ) : ℂ)
      ∂((volume.restrict (Icc 0 T)).prod (volume.restrict (Icc 0 T))) := by
  rw [timeForm, integral_prod _ (cross_integrable ha1 hT f g hf hg)]

/-- The form is additive in its (conjugate-linear) second slot on `L²(0,T)`. -/
theorem timeForm_add_right {a T : ℝ} (ha1 : a < 1) (hT : 0 ≤ T) {f g h : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Icc 0 T))) (hg : MemLp g 2 (volume.restrict (Icc 0 T)))
    (hh : MemLp h 2 (volume.restrict (Icc 0 T))) :
    timeForm a T h (f + g) = timeForm a T h f + timeForm a T h g := by
  rw [timeForm_eq_prod ha1 hT hh (hf.add hg), timeForm_eq_prod ha1 hT hh hf,
    timeForm_eq_prod ha1 hT hh hg, ← integral_add (cross_integrable ha1 hT h f hh hf)
      (cross_integrable ha1 hT h g hh hg)]
  congr 1
  funext p
  simp only [Pi.add_apply, map_add]
  ring

/-- The form is conjugate-homogeneous in its second slot (no integrability needed). -/
theorem timeForm_smul_right (a T : ℝ) (c : ℂ) (f g : ℝ → ℂ) :
    timeForm a T g (c • f) = conj c * timeForm a T g f := by
  unfold timeForm
  rw [← integral_const_mul]
  congr 1
  funext t
  rw [← integral_const_mul]
  congr 1
  funext s
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

/-- Hermitian symmetry of the form on `L²(0,T)`: `conj ⟨f,g⟩ = ⟨g,f⟩` (Fubini swap and
the evenness of `|x|^{-a}`). -/
theorem conj_timeForm {a T : ℝ} (ha1 : a < 1) (hT : 0 ≤ T) {f g : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Icc 0 T))) (hg : MemLp g 2 (volume.restrict (Icc 0 T))) :
    conj (timeForm a T f g) = timeForm a T g f := by
  rw [timeForm_eq_prod ha1 hT hf hg, timeForm_eq_prod ha1 hT hg hf, ← integral_conj]
  have h := integral_prod_swap (μ := volume.restrict (Icc (0 : ℝ) T))
    (ν := volume.restrict (Icc (0 : ℝ) T))
    (fun p : ℝ × ℝ => g p.1 * conj (f p.2) * ((kern a (p.1 - p.2) : ℝ) : ℂ))
  rw [← h]
  congr 1
  funext p
  simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal, Prod.fst_swap, Prod.snd_swap,
    kern_sub_comm a p.2 p.1]
  ring

/-- Positive semidefiniteness of the form on all of complex `L²(0,T)` (TeX lines 143-147
assert it on real compact smooth tests; this is stronger): for `0 < a < 1`, `T ≥ 0`
and `f ∈ L²(0,T)`, `Re ∬_{[0,T]²} f(t) conj f(s) |t-s|^{-a} ≥ 0`.  Route as in the
TeX proof (lines 159-172): Gamma subordination and the exponential-kernel identity
(`kern_eq_mixture`) write the kernel, off the null diagonal, as a mixture of products
`φ_w(t) φ_w(s)` with nonnegative weight; Fubini on `[0,T]² × (0,∞) × ℝ`, justified by
the Schur bound, turns the form into `∫ ρ(w) |∫ f φ_w|² ≥ 0`
(`re_form_nonneg_of_mixture`). -/
theorem timeForm_re_nonneg {a T : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hT : 0 ≤ T) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Icc 0 T))) :
    0 ≤ (timeForm a T f f).re := by
  rw [timeForm_eq_prod ha1 hT hf hf]
  refine re_form_nonneg_of_mixture _ mixMeasure (mixWeight a) (measurable_mixWeight a)
    (mixWeight_nonneg a ha0) mixProfile measurable_mixProfile mixProfile_nonneg
    (fun p => kern a (p.1 - p.2)) (fun p => kern_nonneg _ _) ?_ f hf.aestronglyMeasurable
    (cross_integrable ha1 hT f f hf hf)
  filter_upwards [ae_ne_diag T] with p hp
  exact kern_eq_mixture a ha0 p.1 p.2 hp

/-- The form of real functions is the real double integral:
`⟨g, h⟩_a = ∬ g(t) h(s) |t-s|^{-a}` for `g, h : ℝ → ℝ` (no integrability needed: both
sides are iterated Bochner integrals of the same real integrand). -/
theorem timeForm_ofReal (a T : ℝ) (g h : ℝ → ℝ) :
    timeForm a T (fun t => (g t : ℂ)) (fun t => (h t : ℂ)) =
      ((∫ t in Icc 0 T, ∫ s in Icc 0 T, g t * h s * kern a (t - s) : ℝ) : ℂ) := by
  unfold timeForm
  simp_rw [Complex.conj_ofReal, ← Complex.ofReal_mul, integral_complex_ofReal]

/-- Auxiliary (calibration, used by the refutations): the form at `f = g = 1` is
`⟨1,1⟩_a = 2T^{2-a}/((1-a)(2-a))` for `a < 1`, `T ≥ 0`. -/
theorem timeForm_one {a T : ℝ} (ha1 : a < 1) (hT : 0 ≤ T) :
    timeForm a T (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ)) =
      ((2 * T ^ (2 - a) / ((1 - a) * (2 - a)) : ℝ) : ℂ) := by
  have h := timeForm_ofReal a T (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
  simp only [Complex.ofReal_one] at h
  rw [h]
  congr 1
  simp only [one_mul]
  rw [setIntegral_congr_fun measurableSet_Icc (fun t ht => (integral_row ha1 ht).2),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT, intervalIntegral.integral_div]
  have hr : -1 < 1 - a := by linarith
  have h1 : IntervalIntegrable (fun t : ℝ => t ^ (1 - a)) volume 0 T :=
    intervalIntegral.intervalIntegrable_rpow' hr
  have h2 : IntervalIntegrable (fun t : ℝ => (T - t) ^ (1 - a)) volume 0 T := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := T - T) (b := T - 0) hr).comp_sub_left T
    simpa using this.symm
  rw [intervalIntegral.integral_add h1 h2, intervalIntegral.integral_comp_sub_left
    (fun x : ℝ => x ^ (1 - a)) T, sub_self, sub_zero,
    integral_rpow (Or.inl hr), Real.zero_rpow (by linarith), sub_zero]
  have e : 1 - a + 1 = 2 - a := by ring
  rw [e]
  have h2a : (2 - a) ≠ 0 := by linarith
  have h1a : (1 - a) ≠ 0 := by linarith
  field_simp
  ring

/-! ### The completion `H_a` -/

/-- The standing parameters of `L:masked-time-completion` (TeX lines 141-142 and
the section's standing assumptions): `0 < a < 1` and `T > 0`. -/
structure TimeParams where
  /-- the exponent `a` (`= α₀` in the section). -/
  a : ℝ
  /-- the time horizon. -/
  T : ℝ
  ha0 : 0 < a
  ha1 : a < 1
  hT : 0 < T

variable (p : TimeParams)

/-- The pre-Hilbert space: `L²(0,T)` with the (degenerate) inner product
`⟪f, g⟫ = ⟨g, f⟩_a = ∬ g(t) conj f(s) |t-s|^{-a}` (the arguments are swapped because
Mathlib's inner product is conjugate-linear in the first slot). -/
def Pre : Type := L2fun p.T

instance instAddCommGroupPre : AddCommGroup (Pre p) := inferInstanceAs (AddCommGroup (L2fun p.T))
instance instModulePre : Module ℂ (Pre p) := inferInstanceAs (Module ℂ (L2fun p.T))

variable {p}

/-- Auxiliary: the function underlying an element of `Pre p`. -/
def Pre.toFun (f : Pre p) : ℝ → ℂ := ((show L2fun p.T from f) : ℝ → ℂ)

/-- Auxiliary: the underlying function is in `L²(0,T)`. -/
theorem Pre.memLp (f : Pre p) : MemLp f.toFun 2 (volume.restrict (Icc 0 p.T)) :=
  (show L2fun p.T from f).2

variable (p)

/-- The inner-product core of `Pre p`; its positivity is `timeForm_re_nonneg`. -/
@[instance_reducible] def core : PreInnerProductSpace.Core ℂ (Pre p) where
  inner f g := timeForm p.a p.T g.toFun f.toFun
  conj_inner_symm f g := conj_timeForm p.ha1 p.hT.le f.memLp g.memLp
  re_inner_nonneg f := timeForm_re_nonneg p.ha0 p.ha1 p.hT.le f.memLp
  add_left f g h := timeForm_add_right p.ha1 p.hT.le f.memLp g.memLp h.memLp
  smul_left f g c := timeForm_smul_right p.a p.T c f.toFun g.toFun

instance instSeminormedPre : SeminormedAddCommGroup (Pre p) :=
  @InnerProductSpace.Core.toSeminormedAddCommGroup ℂ _ _ _ _ (core p)

instance instInnerPre : InnerProductSpace ℂ (Pre p) :=
  InnerProductSpace.ofCore (core p)

/-- The temporal completion `H_a`: the (Hausdorff) completion of `L²(0,T)` for the
seminorm `‖f‖_a = (Re⟨f,f⟩_a)^{1/2}`.  It is a complex Hilbert space (Mathlib
instances), and its construction identifies functions at seminorm distance zero
(the manuscript's null quotient). -/
abbrev Ha := UniformSpace.Completion (Pre p)

/-- The inclusion `L²(0,T) → H_a`, a linear isometry for the seminorm `‖·‖_a`. -/
def emb : L2fun p.T →ₗ[ℂ] Ha p :=
  (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ) (E := Pre p)).toLinearMap

variable {p}

/-- Auxiliary: an element of `L²(0,T)` viewed in `Pre p`. -/
def toPre (f : L2fun p.T) : Pre p := f

/-- Auxiliary: `emb p f` is the image of `f` in the completion. -/
theorem emb_apply (f : L2fun p.T) : emb p f = ((toPre f : Pre p) : Ha p) := rfl

/-- Auxiliary: the inner product of `Pre p` is the form with swapped arguments. -/
theorem inner_pre (f g : Pre p) : inner ℂ f g = timeForm p.a p.T g.toFun f.toFun := rfl

/-- Auxiliary: `‖f‖_a² = Re⟨f,f⟩_a` in `Pre p`. -/
theorem norm_pre_sq (f : Pre p) : ‖f‖ ^ 2 = (timeForm p.a p.T f.toFun f.toFun).re := by
  rw [@norm_sq_eq_re_inner ℂ]
  rfl

/-- The norm identity: for `f ∈ L²(0,T)`, `‖emb f‖² = Re ∬ f(t) conj f(s) |t-s|^{-a}`. -/
theorem emb_norm_sq (f : L2fun p.T) :
    ‖emb p f‖ ^ 2 = (timeForm p.a p.T f f).re := by
  rw [emb_apply, UniformSpace.Completion.norm_coe, norm_pre_sq]
  rfl

/-- The Schur constant `2T^{1-a}/(1-a)` of `E:masked-time-schur`. -/
def schurConst (p : TimeParams) : ℝ := 2 * p.T ^ (1 - p.a) / (1 - p.a)

/-- Auxiliary: `‖f‖_a² ≤ C ∫_0^T |f|²` in `Pre p` (from `TimeSchur.time_schur_complex`). -/
theorem norm_pre_sq_le (f : Pre p) :
    ‖f‖ ^ 2 ≤ schurConst p * ∫ t in Icc 0 p.T, ‖f.toFun t‖ ^ 2 := by
  rw [norm_pre_sq]
  exact (Complex.re_le_norm _).trans (time_schur_complex p.ha0 p.ha1 p.hT f.toFun f.memLp).2

/-! ### Separability and the continuous extension from `L²(0,T)` -/

/-- Auxiliary: `∫ |g|² = (‖g‖_{L²})²` for `g ∈ L²`, with the `eLpNorm`. -/
theorem integral_norm_sq_eq {μ : Measure ℝ} {g : ℝ → ℂ} (hg : MemLp g 2 μ) :
    ∫ t, ‖g t‖ ^ 2 ∂μ = ((eLpNorm g 2 μ).toReal) ^ 2 := by
  rw [hg.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  have hnn : 0 ≤ ∫ t, ‖g t‖ ^ (2 : ℝ) ∂μ := integral_nonneg fun t => by positivity
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofNat]
  have h2 : (2 : ℝ)⁻¹ = ((2 : ℕ) : ℝ)⁻¹ := by norm_num
  rw [h2, Real.rpow_inv_natCast_pow hnn two_ne_zero]
  congr 1
  funext t
  exact (Real.rpow_two _).symm

/-- Auxiliary: if the function of `f : Pre p` is a.e. equal to a representative of
`w ∈ L²`, then `‖f‖_a² ≤ C ‖w‖²`. -/
theorem norm_pre_sq_le_Lp (f : Pre p) (w : Lp ℂ 2 (volume.restrict (Icc (0 : ℝ) p.T)))
    (h : f.toFun =ᵐ[volume.restrict (Icc (0 : ℝ) p.T)] w) :
    ‖f‖ ^ 2 ≤ schurConst p * ‖w‖ ^ 2 := by
  refine (norm_pre_sq_le f).trans_eq ?_
  have h2 : (fun t => ‖f.toFun t‖ ^ 2) =ᵐ[volume.restrict (Icc (0 : ℝ) p.T)]
      fun t => ‖(w : ℝ → ℂ) t‖ ^ 2 := h.mono fun t ht => by simp only; rw [ht]
  rw [integral_congr_ae h2, integral_norm_sq_eq (Lp.memLp w), Lp.norm_def]

/-- Auxiliary: elements of `Pre p` whose functions agree a.e. on `[0,T]` are at
seminorm distance zero. -/
theorem dist_pre_eq_zero (f g : Pre p)
    (h : f.toFun =ᵐ[volume.restrict (Icc (0 : ℝ) p.T)] g.toFun) : dist f g = 0 := by
  rw [dist_eq_norm]
  have h0 : (f - g).toFun =ᵐ[volume.restrict (Icc (0 : ℝ) p.T)]
      (0 : Lp ℂ 2 (volume.restrict (Icc (0 : ℝ) p.T))) := by
    filter_upwards [h, Lp.coeFn_zero ℂ 2 (volume.restrict (Icc (0 : ℝ) p.T))] with t ht h0
    rw [h0]
    change f.toFun t - g.toFun t = 0
    rw [ht, sub_self]
  have := norm_pre_sq_le_Lp (f - g) 0 h0
  rw [norm_zero, zero_pow two_ne_zero, mul_zero] at this
  exact pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm this (by positivity)) |> fun h => by
    simpa using h

/-- Auxiliary: elements of `Pre p` whose functions agree a.e. on `[0,T]` have the same
image in `H_a`. -/
theorem coe_eq_of_ae (f g : Pre p)
    (h : f.toFun =ᵐ[volume.restrict (Icc (0 : ℝ) p.T)] g.toFun) :
    (f : Ha p) = (g : Ha p) :=
  dist_eq_zero.1 (by rw [UniformSpace.Completion.dist_eq]; exact dist_pre_eq_zero f g h)

/-- Auxiliary to the Lean proof route: the representative map `L²` (a.e.-classes) `→ Pre p`,
`w ↦ ⇑w`. -/
def ofLp (p : TimeParams) (w : Lp ℂ 2 (volume.restrict (Icc (0 : ℝ) p.T))) : Pre p :=
  (⟨(w : ℝ → ℂ), Lp.memLp w⟩ : L2fun p.T)

/-- Auxiliary: `ofLp` is Lipschitz with constant `√C`. -/
theorem lipschitz_ofLp :
    LipschitzWith (Real.toNNReal (Real.sqrt (schurConst p))) (ofLp p) := by
  refine LipschitzWith.of_dist_le_mul fun u v => ?_
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
  have hae : (ofLp p u - ofLp p v).toFun =ᵐ[volume.restrict (Icc (0 : ℝ) p.T)] (u - v :
      Lp ℂ 2 (volume.restrict (Icc (0 : ℝ) p.T))) := by
    filter_upwards [Lp.coeFn_sub u v] with t ht
    rw [ht]
    rfl
  have h := norm_pre_sq_le_Lp _ _ hae
  calc ‖ofLp p u - ofLp p v‖ = Real.sqrt (‖ofLp p u - ofLp p v‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (schurConst p * ‖u - v‖ ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt (schurConst p) * ‖u - v‖ := by
        rw [Real.sqrt_mul' _ (by positivity), Real.sqrt_sq (norm_nonneg _)]

/-- Auxiliary: every `f : Pre p` is at seminorm distance zero from `ofLp` of its class. -/
theorem dist_ofLp_toLp (f : Pre p) : dist f (ofLp p (f.memLp.toLp f.toFun)) = 0 :=
  dist_pre_eq_zero _ _ (f.memLp.coeFn_toLp.symm)

/-- `Pre p` is separable (the separable `L²(0,T)` maps onto a dense subset). -/
instance separableSpace_pre : TopologicalSpace.SeparableSpace (Pre p) := by
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  have hs := TopologicalSpace.isSeparable_range (lipschitz_ofLp (p := p)).continuous
  have hcl : closure (range (ofLp p)) = univ := by
    refine eq_univ_of_forall fun f => Metric.mem_closure_iff.2 fun ε hε => ?_
    exact ⟨_, mem_range_self _, by rw [dist_ofLp_toLp]; exact hε⟩
  exact TopologicalSpace.isSeparable_univ_iff.1 (hcl ▸ hs.closure)

/-- `H_a` is separable (TeX lines 147-148 and 173-174). -/
theorem separableSpace_Ha : TopologicalSpace.SeparableSpace (Ha p) := inferInstance

variable (p)

/-- Auxiliary: the linear map `L²(0,T) → H_a` on a.e.-classes, `w ↦ [⇑w]`. -/
def extL2Lin : Lp ℂ 2 (volume.restrict (Icc (0 : ℝ) p.T)) →ₗ[ℂ] Ha p where
  toFun w := ((ofLp p w : Pre p) : Ha p)
  map_add' u v := by
    rw [← UniformSpace.Completion.coe_add]
    refine coe_eq_of_ae _ _ ?_
    filter_upwards [Lp.coeFn_add u v] with t ht
    exact ht
  map_smul' c u := by
    rw [RingHom.id_apply, ← UniformSpace.Completion.coe_smul]
    refine coe_eq_of_ae _ _ ?_
    filter_upwards [Lp.coeFn_smul c u] with t ht
    exact ht

variable {p}

/-- Auxiliary: `extL2Lin p w` is the image of the representative `⇑w`. -/
theorem extL2Lin_apply (w : Lp ℂ 2 (volume.restrict (Icc (0 : ℝ) p.T))) :
    extL2Lin p w = ((ofLp p w : Pre p) : Ha p) := rfl

/-- Auxiliary: `‖extL2Lin p w‖² ≤ C ‖w‖²`. -/
theorem extL2Lin_norm_sq_le (w : Lp ℂ 2 (volume.restrict (Icc (0 : ℝ) p.T))) :
    ‖extL2Lin p w‖ ^ 2 ≤ schurConst p * ‖w‖ ^ 2 := by
  rw [extL2Lin_apply, UniformSpace.Completion.norm_coe]
  exact norm_pre_sq_le_Lp (ofLp p w) w (Filter.EventuallyEq.refl _ _)

/-- Auxiliary: `‖extL2Lin p w‖ ≤ √C ‖w‖`. -/
theorem extL2Lin_norm_le (w : Lp ℂ 2 (volume.restrict (Icc (0 : ℝ) p.T))) :
    ‖extL2Lin p w‖ ≤ Real.sqrt (schurConst p) * ‖w‖ := by
  calc ‖extL2Lin p w‖ = Real.sqrt (‖extL2Lin p w‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (schurConst p * ‖w‖ ^ 2) := Real.sqrt_le_sqrt (extL2Lin_norm_sq_le w)
    _ = Real.sqrt (schurConst p) * ‖w‖ := by
        rw [Real.sqrt_mul' _ (by positivity), Real.sqrt_sq (norm_nonneg _)]

variable (p)

/-- The continuous linear extension `L²(0,T) → H_a` of the inclusion (TeX lines 148-149
and 177-179), defined on a.e.-classes: `extL2 p w` is the image of any representative. -/
def extL2 : Lp ℂ 2 (volume.restrict (Icc (0 : ℝ) p.T)) →L[ℂ] Ha p :=
  (extL2Lin p).mkContinuous (Real.sqrt (schurConst p)) extL2Lin_norm_le

variable {p}

/-- The extension agrees with the inclusion: `extL2 p [f] = emb p f` for `f ∈ L²(0,T)`. -/
theorem extL2_toLp (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Icc (0 : ℝ) p.T))) :
    extL2 p (hf.toLp f) = emb p ⟨f, hf⟩ :=
  coe_eq_of_ae (ofLp p (hf.toLp f)) (toPre ⟨f, hf⟩) hf.coeFn_toLp

/-- The extension bound (`E:masked-time-schur`, TeX lines 150-152, for classes):
`‖extL2 p w‖² ≤ (2T^{1-a}/(1-a)) ‖w‖²`. -/
theorem extL2_norm_sq_le (w : Lp ℂ 2 (volume.restrict (Icc (0 : ℝ) p.T))) :
    ‖extL2 p w‖ ^ 2 ≤ schurConst p * ‖w‖ ^ 2 :=
  extL2Lin_norm_sq_le w

/-- `E:masked-time-schur` (TeX lines 150-152) in `H_a`: for `f ∈ L²(0,T)`,
`‖f‖_a² ≤ (2T^{1-a}/(1-a)) ∫_0^T |f|²`. -/
theorem emb_norm_sq_le (f : L2fun p.T) :
    ‖emb p f‖ ^ 2 ≤ schurConst p * ∫ t in Icc 0 p.T, ‖(f : ℝ → ℂ) t‖ ^ 2 := by
  rw [emb_apply, UniformSpace.Completion.norm_coe]
  exact norm_pre_sq_le _

/-! ### The complexified norm (TeX lines 153-154 and 175-177) -/

/-- The form at `f ∈ L²(0,T)` is real: `Im⟨f,f⟩_a = 0`. -/
theorem timeForm_self_im (f : L2fun p.T) : (timeForm p.a p.T f f).im = 0 := by
  have h := conj_timeForm p.ha1 p.hT.le f.2 f.2
  exact Complex.conj_eq_iff_im.1 h

/-- The complexified norm is the double integral with `f(t) conj f(s)`:
`‖emb f‖² = ∬_{[0,T]²} f(t) conj f(s) |t-s|^{-a} dt ds` as a complex number. -/
theorem emb_norm_sq_eq_timeForm (f : L2fun p.T) :
    ((‖emb p f‖ ^ 2 : ℝ) : ℂ) = timeForm p.a p.T f f := by
  rw [emb_norm_sq]
  exact Complex.ext (by simp) (by simp [timeForm_self_im])

/-- For a real function `g ∈ L²(0,T)`, `‖emb g‖² = ∬ g(t) g(s) |t-s|^{-a} dt ds`, the
manuscript's original real form. -/
theorem emb_norm_sq_real (g : ℝ → ℝ) (hg : MemLp g 2 (volume.restrict (Icc (0 : ℝ) p.T))) :
    ‖emb p ⟨fun t => (g t : ℂ), hg.ofReal⟩‖ ^ 2 =
      ∫ t in Icc 0 p.T, ∫ s in Icc 0 p.T, g t * g s * |t - s| ^ (-p.a) := by
  rw [emb_norm_sq]
  change (timeForm p.a p.T (fun t => (g t : ℂ)) (fun t => (g t : ℂ))).re = _
  rw [timeForm_ofReal, Complex.ofReal_re]
  rfl

/-- Auxiliary: the real part `t ↦ Re f(t)` of `f ∈ L²(0,T)`, as an element of `L²(0,T)`. -/
def reL2 (f : L2fun p.T) : L2fun p.T :=
  ⟨fun t => (((f : ℝ → ℂ) t).re : ℂ), (f.2.re).ofReal⟩

/-- Auxiliary: the imaginary part `t ↦ Im f(t)` of `f ∈ L²(0,T)`, as an element of
`L²(0,T)`. -/
def imL2 (f : L2fun p.T) : L2fun p.T :=
  ⟨fun t => (((f : ℝ → ℂ) t).im : ℂ), (f.2.im).ofReal⟩

/-- Auxiliary: `f = Re f + i Im f` in `L²(0,T)`. -/
theorem eq_reL2_add_imL2 (f : L2fun p.T) : f = reL2 f + Complex.I • imL2 f := by
  apply Subtype.ext
  funext t
  change (f : ℝ → ℂ) t = (((f : ℝ → ℂ) t).re : ℂ) + Complex.I * (((f : ℝ → ℂ) t).im : ℂ)
  rw [mul_comm]
  exact (Complex.re_add_im _).symm

/-- The complex quadratic form is the sum of those of the real and imaginary parts
(TeX lines 175-177: "symmetry cancels the imaginary cross term"):
`‖emb f‖² = ‖emb (Re f)‖² + ‖emb (Im f)‖²`. -/
theorem emb_norm_sq_re_im (f : L2fun p.T) :
    ‖emb p f‖ ^ 2 = ‖emb p (reL2 f)‖ ^ 2 + ‖emb p (imL2 f)‖ ^ 2 := by
  have hf := eq_reL2_add_imL2 f
  have hinner : inner ℂ (emb p (reL2 f)) (emb p (imL2 f)) =
      timeForm p.a p.T (imL2 f : ℝ → ℂ) (reL2 f : ℝ → ℂ) := by
    rw [emb_apply, emb_apply, UniformSpace.Completion.inner_coe, inner_pre]
    rfl
  have hreal : (timeForm p.a p.T (imL2 f : ℝ → ℂ) (reL2 f : ℝ → ℂ)).im = 0 := by
    change (timeForm p.a p.T (fun t => (((f : ℝ → ℂ) t).im : ℂ))
      (fun t => (((f : ℝ → ℂ) t).re : ℂ))).im = 0
    rw [timeForm_ofReal, Complex.ofReal_im]
  conv_lhs => rw [hf]
  rw [map_add, map_smul, @norm_add_sq ℂ, inner_smul_right, hinner, norm_smul, Complex.norm_I,
    one_mul]
  simp [hreal]

/-! ### Interval amplitudes (TeX lines 154-155 and 179-180) -/

/-- Bounded measurable amplitudes on an interval `[c,d]`, extended by zero, belong to
`L²(0,T)`, hence (through `emb`) to `H_a`. -/
theorem indicator_mem_L2fun (T c d M : ℝ) (A : ℝ → ℂ)
    (hA : AEStronglyMeasurable A (volume.restrict (Icc c d)))
    (hM : ∀ t ∈ Icc c d, ‖A t‖ ≤ M) :
    (Icc c d).indicator A ∈ L2fun T := by
  change MemLp ((Icc c d).indicator A) 2 (volume.restrict (Icc 0 T))
  rw [memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet]
  have hle : (volume.restrict (Icc (0 : ℝ) T)).restrict (Icc c d) ≤ volume.restrict (Icc c d) :=
    Measure.restrict_mono le_rfl Measure.restrict_le_self
  refine MemLp.of_bound (hA.mono_measure hle) M ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact hM t ht

/-! ### Compact smooth tests inside `(0,T)` are dense (TeX lines 141-147, 173-179) -/

/-- Auxiliary: the boundary layer `[0,T] \ [η, T-η]` has measure at most `2η`. -/
theorem measure_compl_Icc_le (T η : ℝ) (hη : 0 ≤ η) :
    volume.restrict (Icc (0 : ℝ) T) (Icc η (T - η))ᶜ ≤ ENNReal.ofReal (2 * η) := by
  rw [Measure.restrict_apply measurableSet_Icc.compl]
  have hsub : (Icc η (T - η))ᶜ ∩ Icc 0 T ⊆ Ico 0 η ∪ Ioc (T - η) T := by
    intro t ⟨h1, h2⟩
    simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at h1
    rcases h1 with h | h
    · exact Or.inl ⟨h2.1, h⟩
    · exact Or.inr ⟨h, h2.2⟩
  calc volume ((Icc η (T - η))ᶜ ∩ Icc 0 T) ≤ volume (Ico 0 η ∪ Ioc (T - η) T) :=
        measure_mono hsub
    _ ≤ volume (Ico 0 η) + volume (Ioc (T - η) T) := measure_union_le _ _
    _ = ENNReal.ofReal (2 * η) := by
        rw [Real.volume_Ico, Real.volume_Ioc, ← ENNReal.ofReal_add (by linarith) (by linarith)]
        congr 1; ring

/-- Density of compact smooth tests supported inside `(0,T)` in `L²(0,T)` (the TeX's
"smooth density in `L²`", line 177): for `T > 0`, `f ∈ L²(0,T)` and `ε > 0` there is a
smooth compactly supported `g` with `tsupport g ⊆ (0,T)` and `‖f - g‖_{L²(0,T)} ≤ ε`.
Route: Mathlib's density of smooth compactly supported functions
(`MemLp.exist_eLpNorm_sub_le`), multiplied by a smooth bump equal to one on
`[η, T-η]` and supported in `[η/2, T-η/2]`; the boundary layer is controlled by uniform
integrability (`MemLp.eLpNorm_indicator_le`). -/
theorem exists_test_approx {T : ℝ} (hT : 0 < T) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Icc 0 T))) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧ tsupport g ⊆ Ioo 0 T ∧
      eLpNorm (f - g) 2 (volume.restrict (Icc 0 T)) ≤ ENNReal.ofReal ε := by
  set μ := volume.restrict (Icc (0 : ℝ) T)
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨δ, hδ, hδs⟩ := hf.eLpNorm_indicator_le one_le_two ENNReal.ofNat_ne_top
    (ENNReal.ofReal_pos.2 hε2)
  obtain ⟨r, hr0, hrpos, hrδ⟩ := ENNReal.lt_iff_exists_real_btwn.1 hδ
  have hr : 0 < r := ENNReal.ofReal_pos.1 hrpos
  set η := min (T / 4) (r / 2)
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hηT : η ≤ T / 4 := min_le_left _ _
  have hηr : 2 * η ≤ r := by have := min_le_right (T / 4) (r / 2); linarith
  obtain ⟨g0, hg0s, hg0c, hg0⟩ := hf.exist_eLpNorm_sub_le ENNReal.ofNat_ne_top one_le_two hε2
  let χ : ContDiffBump (T / 2) := ⟨T / 2 - η, T / 2 - η / 2, by linarith, by linarith⟩
  set g : ℝ → ℂ := fun t => (χ t : ℂ) * g0 t
  have hχ1 : ∀ t ∈ Icc η (T - η), χ t = 1 := by
    intro t ht
    refine χ.one_of_mem_closedBall ?_
    rw [Real.closedBall_eq_Icc]
    exact ⟨by simp only [χ]; linarith [ht.1], by simp only [χ]; linarith [ht.2]⟩
  have hχs : tsupport (χ : ℝ → ℝ) ⊆ Ioo 0 T := by
    rw [χ.tsupport_eq, Real.closedBall_eq_Icc]
    intro t ht
    simp only [χ] at ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hgs : tsupport g ⊆ Ioo 0 T := by
    refine (tsupport_mul_subset_left (f := fun t => (χ t : ℂ))).trans ?_
    refine (closure_mono fun t ht => ?_).trans hχs
    simp only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero] at ht ⊢
    exact ht
  have hχc : ContDiff ℝ (⊤ : ℕ∞) (fun t => (χ t : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp χ.contDiff
  refine ⟨g, hχc.mul hg0c, ?_, hgs, ?_⟩
  · exact hg0s.mul_left
  have hsplit : f - g = (fun t => (χ t : ℂ) * (f t - g0 t)) + fun t => (1 - (χ t : ℂ)) * f t := by
    funext t; simp only [Pi.sub_apply, Pi.add_apply, g]; ring
  have hχm : AEStronglyMeasurable (fun t => (χ t : ℂ)) μ := hχc.continuous.aestronglyMeasurable
  have hA : AEStronglyMeasurable (fun t => (χ t : ℂ) * (f t - g0 t)) μ :=
    hχm.mul (hf.aestronglyMeasurable.sub hg0c.continuous.aestronglyMeasurable)
  have hB : AEStronglyMeasurable (fun t => (1 - (χ t : ℂ)) * f t) μ :=
    (aestronglyMeasurable_const.sub hχm).mul hf.aestronglyMeasurable
  have h01 : ∀ t, ‖(1 - (χ t : ℂ))‖ ≤ 1 := by
    intro t
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_le]
    constructor <;> linarith [χ.nonneg (x := t), χ.le_one (x := t)]
  have hAle : eLpNorm (fun t => (χ t : ℂ) * (f t - g0 t)) 2 μ ≤ ENNReal.ofReal (ε / 2) := by
    refine (eLpNorm_mono hA fun t => ?_).trans hg0
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg χ.nonneg, Pi.sub_apply]
    exact mul_le_of_le_one_left (norm_nonneg _) χ.le_one
  have hBle : eLpNorm (fun t => (1 - (χ t : ℂ)) * f t) 2 μ ≤ ENNReal.ofReal (ε / 2) := by
    refine (eLpNorm_mono hB fun t => ?_).trans (hδs (Icc η (T - η))ᶜ measurableSet_Icc.compl.nullMeasurableSet ?_)
    · by_cases ht : t ∈ Icc η (T - η)
      · rw [hχ1 t ht, Complex.ofReal_one, sub_self, zero_mul, norm_zero]
        exact norm_nonneg _
      · rw [indicator_of_mem (show t ∈ (Icc η (T - η))ᶜ from ht), norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (h01 t)
    · exact (measure_compl_Icc_le T η hη.le).trans
        ((ENNReal.ofReal_le_ofReal hηr).trans hrδ.le)
  rw [hsplit]
  refine (eLpNorm_add_le one_le_two).trans ?_
  calc _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hAle hBle
    _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add hε2.le hε2.le, add_halves]

/-- The complex compact smooth tests supported inside `(0,T)`, as elements of
`L²(0,T)`. -/
def testSet (T : ℝ) : Set (L2fun T) :=
  {f | ContDiff ℝ (⊤ : ℕ∞) (f : ℝ → ℂ) ∧ HasCompactSupport (f : ℝ → ℂ) ∧
    tsupport (f : ℝ → ℂ) ⊆ Ioo 0 T}

/-- The real compact smooth tests supported inside `(0,T)` (the TeX's "real compact
smooth tests"), as (real-valued) elements of `L²(0,T)`. -/
def realTestSet (T : ℝ) : Set (L2fun T) :=
  {f | ∃ g : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧ tsupport g ⊆ Ioo 0 T ∧
    (f : ℝ → ℂ) = fun t => (g t : ℂ)}

/-- The images of the complex compact smooth tests on `(0,T)` are dense in `H_a`. -/
theorem dense_emb_testSet : Dense (emb p '' testSet p.T) := by
  have key : ∀ f : L2fun p.T, emb p f ∈ closure (emb p '' testSet p.T) := by
    intro f
    refine Metric.mem_closure_iff.2 fun ε hε => ?_
    set C := schurConst p
    have hC : 0 ≤ C := by
      have := Real.rpow_nonneg p.hT.le (1 - p.a)
      exact div_nonneg (by linarith) (by linarith [p.ha1])
    have hden : 0 < Real.sqrt C + 1 := by positivity
    obtain ⟨g, hgc, hgs, hgt, hg⟩ := exists_test_approx p.hT f.2 (div_pos hε hden)
    have hgm : MemLp g 2 (volume.restrict (Icc 0 p.T)) :=
      (hgc.continuous.memLp_of_hasCompactSupport hgs).restrict _
    refine ⟨emb p ⟨g, hgm⟩, ⟨⟨g, hgm⟩, ⟨hgc, hgs, hgt⟩, rfl⟩, ?_⟩
    rw [dist_eq_norm, ← map_sub]
    have hfg : MemLp ((f : ℝ → ℂ) - g) 2 (volume.restrict (Icc 0 p.T)) := f.2.sub hgm
    have h1 := emb_norm_sq_le (p := p) (f - ⟨g, hgm⟩)
    change ‖emb p (f - ⟨g, hgm⟩)‖ ^ 2 ≤ C * ∫ t in Icc 0 p.T, ‖((f : ℝ → ℂ) - g) t‖ ^ 2 at h1
    rw [integral_norm_sq_eq hfg] at h1
    have h2 : (eLpNorm ((f : ℝ → ℂ) - g) 2 (volume.restrict (Icc 0 p.T))).toReal ≤
        ε / (Real.sqrt C + 1) :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hg
    have h3 : ‖emb p (f - ⟨g, hgm⟩)‖ ≤ Real.sqrt C * (ε / (Real.sqrt C + 1)) := by
      calc ‖emb p (f - ⟨g, hgm⟩)‖ = Real.sqrt (‖emb p (f - ⟨g, hgm⟩)‖ ^ 2) :=
            (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt (C * (eLpNorm ((f : ℝ → ℂ) - g) 2
              (volume.restrict (Icc 0 p.T))).toReal ^ 2) := Real.sqrt_le_sqrt h1
        _ = Real.sqrt C * (eLpNorm ((f : ℝ → ℂ) - g) 2
              (volume.restrict (Icc 0 p.T))).toReal := by
            rw [Real.sqrt_mul' _ (by positivity), Real.sqrt_sq ENNReal.toReal_nonneg]
        _ ≤ Real.sqrt C * (ε / (Real.sqrt C + 1)) :=
            mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
    refine h3.trans_lt ?_
    rw [mul_div_assoc', div_lt_iff₀ hden]
    nlinarith
  refine dense_iff_closure_eq.2 (eq_univ_of_forall fun x => ?_)
  have hsub : range ((↑) : Pre p → Ha p) ⊆ closure (emb p '' testSet p.T) := by
    rintro _ ⟨y, rfl⟩
    exact key y
  have hx : x ∈ closure (range ((↑) : Pre p → Ha p)) := by
    rw [(UniformSpace.Completion.denseRange_coe (α := Pre p)).closure_range]
    exact mem_univ _
  exact closure_minimal hsub isClosed_closure hx

/-- `H_a` is the complexified completion of the real compact smooth tests on `(0,T)`:
the complex span of their images is dense in `H_a` (TeX lines 141-147 and 173-177). -/
theorem dense_span_realTestSet :
    Dense (Submodule.span ℂ (emb p '' realTestSet p.T) : Set (Ha p)) := by
  refine dense_emb_testSet.mono ?_
  rintro _ ⟨f, ⟨hfc, hfs, hft⟩, rfl⟩
  have hre : reL2 f ∈ realTestSet p.T := by
    refine ⟨fun t => ((f : ℝ → ℂ) t).re, Complex.reCLM.contDiff.comp hfc,
      hfs.comp_left Complex.zero_re, ?_, rfl⟩
    exact (tsupport_comp_subset Complex.zero_re _).trans hft
  have him : imL2 f ∈ realTestSet p.T := by
    refine ⟨fun t => ((f : ℝ → ℂ) t).im, Complex.imCLM.contDiff.comp hfc,
      hfs.comp_left Complex.zero_im, ?_, rfl⟩
    exact (tsupport_comp_subset Complex.zero_im _).trans hft
  rw [eq_reL2_add_imL2 f, map_add, map_smul]
  exact Submodule.add_mem _ (Submodule.subset_span ⟨_, hre, rfl⟩)
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, him, rfl⟩))

/-! ### The paper statement -/

/-- Auxiliary: a real compact smooth test lies in `L²(0,T)`. -/
theorem memLp_of_test (T : ℝ) (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) : MemLp f 2 (volume.restrict (Icc 0 T)) :=
  (hf.continuous.memLp_of_hasCompactSupport hc).restrict _

/-- `L:masked-time-completion` (TeX lines 141-156, proof 158-181), exact standing
hypotheses `T > 0`, `0 < a < 1` (no `Γ ≠ 0`: the TeX says the purely temporal
estimates hold for any `Γ`, lines 5-7).  With `p = ⟨a, T, …⟩`, `H_a = Ha p` the
completion of `L²(0,T)` for `‖f‖_a = (Re⟨f,f⟩_a)^{1/2}` and `emb p` the inclusion:

1. (positive semidefinite, TeX lines 143-147) for every real compact smooth test `f`
   the integrand `f(t) f(s) |t-s|^{-a}` is integrable on `[0,T]²` and
   `∬ f(t) f(s) |t-s|^{-a} ≥ 0` (the hypothesis `tsupport f ⊆ (0,T)` is carried but
   not used: positivity holds for every real, indeed every complex, `f ∈ L²(0,T)`,
   `timeForm_re_nonneg`);
2. (separable, line 147) `H_a` is separable;
3. (`E:masked-time-schur`, lines 148-152) `‖emb f‖² ≤ (2T^{1-a}/(1-a)) ∫_0^T |f|²` for
   `f ∈ L²(0,T)`;
4. (continuous extension from `L²`, lines 148-149 and 177-179) the continuous linear
   map `extL2 p` on a.e.-classes agrees with `emb` on every `f ∈ L²(0,T)` and satisfies
   `‖extL2 p w‖² ≤ (2T^{1-a}/(1-a)) ‖w‖²`;
5. (complexification, lines 153-154 and 175-177) for complex `f ∈ L²(0,T)` the
   integrand `f(t) conj f(s) |t-s|^{-a}` is integrable, `‖emb f‖²` equals the double
   integral `∬ f(t) conj f(s) |t-s|^{-a}` (as a complex number), and
   `‖emb f‖² = ‖emb (Re f)‖² + ‖emb (Im f)‖²`; for real `g ∈ L²(0,T)`,
   `‖emb g‖² = ∬ g(t) g(s) |t-s|^{-a}`;
6. (interval amplitudes, lines 154-155) a bounded a.e.-strongly measurable amplitude on
   an interval `[c,d]`, extended by zero, lies in `L²(0,T)`, hence has an image under
   `emb`;
7. (identification with the TeX's completion, lines 141-147 and 177) the complex span
   of the images of the real compact smooth tests supported in `(0,T)` is dense in
   `H_a`.

Representation (not a narrowing of the conclusion): `H_a` is built as the completion of
complex `L²(0,T)` for `‖·‖_a`, directly over `ℂ`.  By item 7 it is the closure of the
complex span of the real tests, so it is the complexified null-quotient completion of
the real tests, as in the TeX; the TeX's real `H_a` is represented through the real
functions in items 1 and 5 (no separate real Hilbert space is constructed). -/
theorem masked_time_completion_paper (a T : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hT : 0 < T) :
    (∀ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → tsupport f ⊆ Ioo 0 T →
        Integrable (fun q : ℝ × ℝ => f q.1 * f q.2 * |q.1 - q.2| ^ (-a))
          ((volume.restrict (Icc 0 T)).prod (volume.restrict (Icc 0 T))) ∧
        0 ≤ ∫ t in Icc 0 T, ∫ s in Icc 0 T, f t * f s * |t - s| ^ (-a)) ∧
      TopologicalSpace.SeparableSpace (Ha ⟨a, T, ha0, ha1, hT⟩) ∧
      (∀ (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Icc 0 T))),
        ‖emb ⟨a, T, ha0, ha1, hT⟩ ⟨f, hf⟩‖ ^ 2 ≤
          2 * T ^ (1 - a) / (1 - a) * ∫ t in Icc 0 T, ‖f t‖ ^ 2) ∧
      ((∀ (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Icc 0 T))),
          extL2 ⟨a, T, ha0, ha1, hT⟩ (hf.toLp f) = emb ⟨a, T, ha0, ha1, hT⟩ ⟨f, hf⟩) ∧
        ∀ w : Lp ℂ 2 (volume.restrict (Icc (0 : ℝ) T)),
          ‖extL2 ⟨a, T, ha0, ha1, hT⟩ w‖ ^ 2 ≤ 2 * T ^ (1 - a) / (1 - a) * ‖w‖ ^ 2) ∧
      (∀ (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Icc 0 T))),
        Integrable (fun q : ℝ × ℝ => f q.1 * conj (f q.2) * ((kern a (q.1 - q.2) : ℝ) : ℂ))
            ((volume.restrict (Icc 0 T)).prod (volume.restrict (Icc 0 T))) ∧
          ((‖emb ⟨a, T, ha0, ha1, hT⟩ ⟨f, hf⟩‖ ^ 2 : ℝ) : ℂ) = timeForm a T f f ∧
          ‖emb ⟨a, T, ha0, ha1, hT⟩ ⟨f, hf⟩‖ ^ 2 =
            ‖emb ⟨a, T, ha0, ha1, hT⟩ (reL2 ⟨f, hf⟩)‖ ^ 2 +
              ‖emb ⟨a, T, ha0, ha1, hT⟩ (imL2 ⟨f, hf⟩)‖ ^ 2) ∧
      (∀ (g : ℝ → ℝ) (hg : MemLp g 2 (volume.restrict (Icc 0 T))),
        ‖emb ⟨a, T, ha0, ha1, hT⟩ ⟨fun t => (g t : ℂ), hg.ofReal⟩‖ ^ 2 =
          ∫ t in Icc 0 T, ∫ s in Icc 0 T, g t * g s * |t - s| ^ (-a)) ∧
      (∀ (c d M : ℝ) (A : ℝ → ℂ), AEStronglyMeasurable A (volume.restrict (Icc c d)) →
        (∀ t ∈ Icc c d, ‖A t‖ ≤ M) → (Icc c d).indicator A ∈ L2fun T) ∧
      Dense (Submodule.span ℂ (emb ⟨a, T, ha0, ha1, hT⟩ '' realTestSet T) :
        Set (Ha ⟨a, T, ha0, ha1, hT⟩)) := by
  set p : TimeParams := ⟨a, T, ha0, ha1, hT⟩
  refine ⟨fun f hf hc _ => ?_, separableSpace_Ha, fun f hf => emb_norm_sq_le (p := p) ⟨f, hf⟩,
    ⟨fun f hf => extL2_toLp (p := p) f hf, fun w => extL2_norm_sq_le (p := p) w⟩,
    fun f hf => ⟨time_schur_complex ha0 ha1 hT f hf |>.1, emb_norm_sq_eq_timeForm (p := p) ⟨f, hf⟩,
      emb_norm_sq_re_im (p := p) ⟨f, hf⟩⟩,
    fun g hg => emb_norm_sq_real (p := p) g hg,
    fun c d M A hA hM => indicator_mem_L2fun T c d M A hA hM, dense_span_realTestSet (p := p)⟩
  have hm := memLp_of_test T f hf hc
  refine ⟨(time_schur_paper ha0 ha1 hT f hm).1, ?_⟩
  rw [← emb_norm_sq_real (p := p) f hm]
  positivity

/-! ### `L:masked-trig-products` with nothing supplied -/

/-- `L:masked-trig-products` (TeX lines 347-374, display 352-360), re-issued with NO
supplied input: `MaskedModulation.masked_trig_products_bridged_paper` instantiated with
`E = H_a`, `V = L²(0,T)` and `emb`, so that its inputs `hmem` (the modes
`1_I A e^{iωt}` lie in `L²(0,T)`, by `MaskedModulation.memLp_modeFn`) and `hnorm`
(`‖emb f‖² = Re⟨f,f⟩_a`, `emb_norm_sq`) hold by construction.  Hypotheses: exactly the
manuscript's (TeX lines 296-298 and 347-351, with `T > 0`, `0 < a < 1` from
`L:masked-time-completion`); `T > 0` and `h ≤ 1` are carried but not used by the
proof.  Conclusion: `1_I A P_r Q_ρ ∈ L²(0,T)` and
`‖1_I A P_r Q_ρ‖_a² ≤ C₀(a) h^{2-a} (M+hD)² 𝒬_h(r,ρ)`, the norm being that of `H_a` as
built here (`masked_time_completion_paper`). -/
theorem masked_trig_products_completed_paper
    (a T s h : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hT : 0 < T)
    (hh0 : 0 < h) (hh1 : h ≤ 1) (hs : 0 ≤ s) (hsT : s + h ≤ T)
    (A : ℝ → ℂ) (hA : ContDiffOn ℝ 1 A (Icc s (s + h)))
    (M D : ℝ)
    (hM : M = sSup ((fun t => ‖A t‖) '' Icc s (s + h)))
    (hD : D = sSup ((fun t => ‖derivWithin A (Icc s (s + h)) t‖) '' Icc s (s + h)))
    (r ρ : ℝ) (hr : 0 ≤ r) (hρ : 0 ≤ ρ) (P Q : MaskedTrigProducts.Trig) :
    MaskedTrigProducts.prodFn (Icc s (s + h)) A P Q r ρ ∈ L2fun T ∧
      ∀ hp : MaskedTrigProducts.prodFn (Icc s (s + h)) A P Q r ρ ∈ L2fun T,
        ‖emb ⟨a, T, ha0, ha1, hT⟩ ⟨MaskedTrigProducts.prodFn (Icc s (s + h)) A P Q r ρ, hp⟩‖ ^ 2 ≤
          MaskedTrigProducts.C₀ a * h ^ (2 - a) * (M + h * D) ^ 2 *
            MaskedTrigProducts.frequencyPair a h r ρ := by
  obtain ⟨hc, hMb, -⟩ := MaskedModulation.envelope_of_contDiffOn hh0 A hA M D hM hD
  exact MaskedModulation.masked_trig_products_bridged_paper a T s h ha0 ha1 hT hh0 hh1 hs hsT
    A hA M D hM hD r ρ hr hρ P Q (L2fun T) (emb ⟨a, T, ha0, ha1, hT⟩)
    (fun ω => MaskedModulation.memLp_modeFn (T := T) A hc M hMb ω)
    (fun f _ => emb_norm_sq (p := ⟨a, T, ha0, ha1, hT⟩) f)

end StratonovichHAMSecondMoment.TimeCompletion
