module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Finite Gaussian integration by parts (a reusable foundation; no direct
manuscript label of its own).

Source: `notes/integrated_compact_gaussian.tex` at commit `a284420`, proof of
Proposition `P:finite-gaussian-matrix` (lines 121--126: "Componentwise
integration by parts against the product Gaussian density gives
`E[g_k P(g)] = E[∂_k P(g)]`, with zero boundary terms ... absolute polynomial
integrability justifies Fubini") and Remark `R:gaussian-one-variance-test`
(lines 182--183: "Gaussian integration by parts gives `E g^2 = 1`,
`E g^4 = 3`").  This module proves that step in the generality used there.

Contents:
* `hasDerivAt_stdPDF`: `φ' = -x φ` for the standard Gaussian density.
* `integral_mul_eq_integral_deriv`: one-dimensional Gaussian integration by
  parts `∫ x f(x) dγ = ∫ f'(x) dγ` for a differentiable `f` with `f`, `x f`,
  `f'` integrable (from Mathlib's whole-line integration by parts
  `integral_mul_deriv_eq_deriv_mul_of_integrable`; no boundary hypothesis is
  needed).
* `stdPi N`: the law of `N` independent standard Gaussians,
  `Measure.pi (fun _ => gaussianReal 0 1)` on `Fin N → ℝ`.
* `integral_coord_mul_eq_integral_partial`: `N`-dimensional integration by
  parts in coordinate `k`, by Fubini along `Fin.insertNth k`.
* `integrable_one_add_norm_pow`, `integrable_of_growth`,
  `integrable_coord_mul_of_growth`, `integral_coord_mul_eq_of_growth`:
  polynomial-growth integrability and the polynomial-growth form of the
  identity ("absolute polynomial integrability justifies Fubini").
* `moment_recursion`, `moment_two`, `moment_four`: `E g^(j+2) = (j+1) E g^j`,
  hence `E g^2 = 1` and `E g^4 = 3`, from the integration by parts.
* `map_eq_stdPi`, `integral_comp_eq_stdPi`, `integrable_comp_iff_stdPi`,
  `integral_coord_mul_eq_of_growth_paper`: transfer to an arbitrary
  probability space carrying `iIndepFun` standard Gaussians (`HasLaw`).

Side conditions made explicit: the derivative is a hypothesis on every
coordinate slice (`HasDerivAt` of `s ↦ f (update x k s)`); integrability of
`f`, `x_k f` and `∂_k f` is a hypothesis of the general form and is derived from
measurability and polynomial growth in the growth form (the Bochner integral of
a non-integrable function is `0` in Lean, so integrability is never left
implicit).
-/
public import Mathlib

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace StratonovichHAMSecondMoment.GaussianIBP

/-! ### One dimension -/

/-- The standard Gaussian density satisfies `φ'(x) = -x φ(x)`. -/
theorem hasDerivAt_stdPDF (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have h : gaussianPDFReal 0 1 = fun y => (√(2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2) := by
    rw [gaussianPDFReal_def]; funext y; simp
  rw [h]
  have h1 : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-x) x := by
    have := ((hasDerivAt_pow 2 x).neg).div_const 2
    convert this using 1; push_cast; ring
  have := (h1.exp).const_mul (√(2 * Real.pi))⁻¹
  convert this using 1; ring

/-- Integrability against `N(0,1)` is Lebesgue integrability of `φ h`. -/
theorem integrable_gaussian_iff (h : ℝ → ℝ) :
    Integrable h (gaussianReal 0 1) ↔
      Integrable (fun x => gaussianPDFReal 0 1 x * h x) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (Filter.Eventually.of_forall fun _ => gaussianPDF_lt_top)]
  simp [toReal_gaussianPDF, smul_eq_mul]

/-- The `N(0,1)` integral is the Lebesgue integral of `φ h`. -/
theorem integral_gaussian_eq (h : ℝ → ℝ) :
    ∫ x, h x ∂gaussianReal 0 1 = ∫ x, gaussianPDFReal 0 1 x * h x := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]; rfl

/-- One-dimensional Gaussian integration by parts: `E[g f(g)] = E[f'(g)]` for
`g ~ N(0,1)`, `f` differentiable with derivative `f'`, and `f`, `x f(x)`, `f'`
integrable against `N(0,1)`. -/
theorem integral_mul_eq_integral_deriv (f f' : ℝ → ℝ) (hf : ∀ x, HasDerivAt f (f' x) x)
    (hi0 : Integrable f (gaussianReal 0 1))
    (hi1 : Integrable (fun x => x * f x) (gaussianReal 0 1))
    (hi2 : Integrable f' (gaussianReal 0 1)) :
    ∫ x, x * f x ∂gaussianReal 0 1 = ∫ x, f' x ∂gaussianReal 0 1 := by
  rw [integrable_gaussian_iff] at hi0 hi1 hi2
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (u := f)
    (v := gaussianPDFReal 0 1) (u' := f') (v' := fun x => -x * gaussianPDFReal 0 1 x)
    (fun x _ => hf x) (fun x _ => hasDerivAt_stdPDF x)
    (by
      refine hi1.neg.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.neg_apply, Pi.mul_apply]; ring)
    (by
      refine hi2.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.mul_apply]; ring)
    (by
      refine hi0.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.mul_apply]; ring)
  rw [integral_gaussian_eq, integral_gaussian_eq]
  have e1 : ∫ x, gaussianPDFReal 0 1 x * (x * f x) =
      -∫ x, f x * (-x * gaussianPDFReal 0 1 x) := by
    rw [← integral_neg]; congr 1; funext x; ring
  rw [e1, key, neg_neg]; congr 1; funext x; ring

/-! ### `N` independent standard Gaussians -/

/-- The law of `N` independent standard Gaussians on `Fin N → ℝ`. -/
def stdPi (N : ℕ) : Measure (Fin N → ℝ) := Measure.pi fun _ => gaussianReal 0 1

/-- `stdPi N` is a probability measure. -/
instance isProbabilityMeasure_stdPi (N : ℕ) : IsProbabilityMeasure (stdPi N) := by
  unfold stdPi; infer_instance

/-- `N`-dimensional Gaussian integration by parts in coordinate `k`:
`E[g_k f(g)] = E[∂_k f(g)]`, where `∂_k f` is given on every slice
`s ↦ f (update x k s)` by `HasDerivAt`, and `f`, `x_k f(x)`, `∂_k f` are
integrable.  Proof: Fubini along `Fin.insertNth k` and the one-dimensional
identity on almost every slice. -/
theorem integral_coord_mul_eq_integral_partial {N : ℕ} (k : Fin N)
    (f f' : (Fin N → ℝ) → ℝ)
    (hf : ∀ x t, HasDerivAt (fun s => f (Function.update x k s)) (f' (Function.update x k t)) t)
    (hi0 : Integrable f (stdPi N)) (hi1 : Integrable (fun x => x k * f x) (stdPi N))
    (hi2 : Integrable f' (stdPi N)) :
    ∫ x, x k * f x ∂stdPi N = ∫ x, f' x ∂stdPi N := by
  cases N with
  | zero => exact k.elim0
  | succ n =>
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) k
    have hmp : MeasurePreserving e.symm ((gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin n => gaussianReal 0 1)) (stdPi (n + 1)) :=
      (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gaussianReal 0 1) k).symm
    have hint : ∀ h : (Fin (n + 1) → ℝ) → ℝ, Integrable h (stdPi (n + 1)) →
        Integrable (fun z : ℝ × (Fin n → ℝ) => h (Fin.insertNth k z.1 z.2))
          ((gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)) :=
      fun h hh => (hmp.integrable_comp_emb e.symm.measurableEmbedding).2 hh
    have hrw : ∀ h : (Fin (n + 1) → ℝ) → ℝ, Integrable h (stdPi (n + 1)) →
        ∫ x, h x ∂stdPi (n + 1) = ∫ y, ∫ t, h (Fin.insertNth k t y) ∂gaussianReal 0 1
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
      intro h hh
      rw [← hmp.integral_comp' h]
      exact integral_prod_symm (fun z : ℝ × (Fin n → ℝ) => h (e.symm z)) (hint h hh)
    rw [hrw _ hi1, hrw _ hi2]
    refine integral_congr_ae ?_
    filter_upwards [(hint _ hi0).prod_left_ae, (hint _ hi1).prod_left_ae,
      (hint _ hi2).prod_left_ae] with y h0 h1 h2
    simp only [Fin.insertNth_apply_same] at h1 ⊢
    refine integral_mul_eq_integral_deriv (fun t => f (Fin.insertNth k t y))
      (fun t => f' (Fin.insertNth k t y)) (fun t => ?_) h0 h1 h2
    have := hf (Fin.insertNth k t y) t
    simp only [Fin.update_insertNth] at this
    exact this

/-! ### Polynomial growth -/

/-- `(1 + |x|)^d` is integrable against `N(0,1)`. -/
theorem integrable_one_add_abs_pow (d : ℕ) :
    Integrable (fun x : ℝ => (1 + |x|) ^ d) (gaussianReal 0 1) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  have h : MemLp (fun x : ℝ => 1 + |x|) d (gaussianReal 0 1) :=
    (memLp_const 1).add (memLp_id_gaussianReal (d : NNReal)).norm
  refine (h.integrable_norm_pow hd.ne').congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity)]

/-- `1 + ‖x‖ ≤ ∏ i, (1 + |x i|)` for the sup norm on `Fin N → ℝ` (auxiliary to
the Lean proof route). -/
theorem one_add_norm_le_prod {N : ℕ} (x : Fin N → ℝ) :
    1 + ‖x‖ ≤ ∏ i, (1 + |x i|) := by
  have hP : 1 ≤ ∏ i, (1 + |x i|) := Finset.one_le_prod₀ fun i _ => by simp
  have : ‖x‖ ≤ ∏ i, (1 + |x i|) - 1 := by
    refine (pi_norm_le_iff_of_nonneg (by linarith)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    have h2 : ∏ j, (1 + |x j|) = (1 + |x i|) * ∏ j ∈ Finset.univ.erase i, (1 + |x j|) :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
    have h3 : 1 ≤ ∏ j ∈ Finset.univ.erase i, (1 + |x j|) :=
      Finset.one_le_prod₀ fun j _ => by simp
    have h4 : (1 + |x i|) * 1 ≤ (1 + |x i|) * ∏ j ∈ Finset.univ.erase i, (1 + |x j|) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    linarith
  linarith

/-- `(1 + ‖x‖)^d` is integrable against `stdPi N`. -/
theorem integrable_one_add_norm_pow (N d : ℕ) :
    Integrable (fun x : Fin N → ℝ => (1 + ‖x‖) ^ d) (stdPi N) := by
  have hprod : Integrable (fun x : Fin N → ℝ => ∏ i, (1 + |x i|) ^ d) (stdPi N) :=
    Integrable.fintype_prod (f := fun _ (t : ℝ) => (1 + |t|) ^ d)
      (fun _ => integrable_one_add_abs_pow d)
  refine hprod.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Finset.prod_pow]
  exact pow_le_pow_left₀ (by positivity) (one_add_norm_le_prod x) d

/-- A measurable function of polynomial growth is integrable against `stdPi N`. -/
theorem integrable_of_growth {N : ℕ} {f : (Fin N → ℝ) → ℝ}
    (hm : AEStronglyMeasurable f (stdPi N)) {C : ℝ} {d : ℕ}
    (hb : ∀ x, |f x| ≤ C * (1 + ‖x‖) ^ d) : Integrable f (stdPi N) :=
  ((integrable_one_add_norm_pow N d).const_mul C).mono' hm
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb x)

/-- If `f` has polynomial growth, so has `x_k f(x)`; it is integrable. -/
theorem integrable_coord_mul_of_growth {N : ℕ} (k : Fin N) {f : (Fin N → ℝ) → ℝ}
    (hm : AEStronglyMeasurable f (stdPi N)) {C : ℝ} {d : ℕ}
    (hb : ∀ x, |f x| ≤ C * (1 + ‖x‖) ^ d) :
    Integrable (fun x => x k * f x) (stdPi N) := by
  refine integrable_of_growth (C := C) (d := d + 1)
    ((continuous_apply k).aestronglyMeasurable.mul hm) fun x => ?_
  have hC : 0 ≤ C := by
    have h0 := (abs_nonneg _).trans (hb 0)
    have : (0 : ℝ) < (1 + ‖(0 : Fin N → ℝ)‖) ^ d := by positivity
    exact nonneg_of_mul_nonneg_left h0 this
  rw [abs_mul, pow_succ]
  have hk : |x k| ≤ 1 + ‖x‖ := by
    have := norm_le_pi_norm x k; rw [Real.norm_eq_abs] at this; linarith
  calc |x k| * |f x| ≤ (1 + ‖x‖) * (C * (1 + ‖x‖) ^ d) :=
        mul_le_mul hk (hb x) (abs_nonneg _) (by positivity)
    _ = C * ((1 + ‖x‖) ^ d * (1 + ‖x‖)) := by ring

/-- Gaussian integration by parts for measurable `f`, `∂_k f` of polynomial
growth: `E[g_k f(g)] = E[∂_k f(g)]`, with both integrands integrable. -/
theorem integral_coord_mul_eq_of_growth {N : ℕ} (k : Fin N) (f f' : (Fin N → ℝ) → ℝ)
    (hf : ∀ x t, HasDerivAt (fun s => f (Function.update x k s)) (f' (Function.update x k t)) t)
    (hm : AEStronglyMeasurable f (stdPi N)) (hm' : AEStronglyMeasurable f' (stdPi N))
    {C C' : ℝ} {d d' : ℕ} (hb : ∀ x, |f x| ≤ C * (1 + ‖x‖) ^ d)
    (hb' : ∀ x, |f' x| ≤ C' * (1 + ‖x‖) ^ d') :
    Integrable (fun x => x k * f x) (stdPi N) ∧ Integrable f' (stdPi N) ∧
      ∫ x, x k * f x ∂stdPi N = ∫ x, f' x ∂stdPi N :=
  ⟨integrable_coord_mul_of_growth k hm hb, integrable_of_growth hm' hb',
    integral_coord_mul_eq_integral_partial k f f' hf (integrable_of_growth hm hb)
      (integrable_coord_mul_of_growth k hm hb) (integrable_of_growth hm' hb')⟩

/-! ### Gaussian moments -/

/-- Every power `x^j` is integrable against `N(0,1)`. -/
theorem integrable_pow_gaussian (j : ℕ) :
    Integrable (fun x : ℝ => x ^ j) (gaussianReal 0 1) :=
  (integrable_one_add_abs_pow j).mono' (by fun_prop) (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (by linarith) j)

/-- Moment recursion from integration by parts: `E g^(j+2) = (j+1) E g^j`. -/
theorem moment_recursion (j : ℕ) :
    ∫ x, x ^ (j + 2) ∂gaussianReal 0 1 = (j + 1) * ∫ x, x ^ j ∂gaussianReal 0 1 := by
  have h := integral_mul_eq_integral_deriv (fun x => x ^ (j + 1))
    (fun x => ((j + 1 : ℕ) : ℝ) * x ^ j)
    (fun x => by simpa using hasDerivAt_pow (j + 1) x)
    (integrable_pow_gaussian _)
    (by simpa [← pow_succ'] using integrable_pow_gaussian (j + 2))
    ((integrable_pow_gaussian j).const_mul _)
  rw [integral_const_mul] at h
  simp only [← pow_succ'] at h
  rw [h]; push_cast; ring

/-- `E g^2 = 1` (manuscript `R:gaussian-one-variance-test`, line 183). -/
theorem moment_two : ∫ x, x ^ 2 ∂gaussianReal 0 1 = 1 := by
  rw [moment_recursion 0]; simp

/-- `E g^4 = 3` (manuscript `R:gaussian-one-variance-test`, line 183). -/
theorem moment_four : ∫ x, x ^ 4 ∂gaussianReal 0 1 = 3 := by
  rw [moment_recursion 2, moment_two]; norm_num

/-! ### Transfer to a probability space with independent standard Gaussians -/

section Transfer

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {N : ℕ}

/-- The joint law of independent standard Gaussians `g_1, …, g_N` is `stdPi N`. -/
theorem map_eq_stdPi (g : Fin N → Ω → ℝ) (hind : iIndepFun g P)
    (hlaw : ∀ k, HasLaw (g k) (gaussianReal 0 1) P) :
    P.map (fun ω k => g k ω) = stdPi N := by
  rw [(iIndepFun_iff_map_fun_eq_pi_map (fun k => (hlaw k).aemeasurable)).1 hind]
  unfold stdPi
  congr 1; funext k; exact (hlaw k).map_eq

/-- Expectations of measurable functionals of `(g_1, …, g_N)` are integrals
against `stdPi N`. -/
theorem integral_comp_eq_stdPi (g : Fin N → Ω → ℝ) (hind : iIndepFun g P)
    (hlaw : ∀ k, HasLaw (g k) (gaussianReal 0 1) P) {h : (Fin N → ℝ) → ℝ}
    (hh : AEStronglyMeasurable h (stdPi N)) :
    ∫ ω, h (fun k => g k ω) ∂P = ∫ x, h x ∂stdPi N := by
  have hmeas : AEMeasurable (fun ω k => g k ω) P :=
    AEMeasurable.of_eval fun k => (hlaw k).aemeasurable
  rw [← map_eq_stdPi g hind hlaw] at hh ⊢
  rw [integral_map hmeas hh]

/-- Integrability transfers between `P` and `stdPi N`. -/
theorem integrable_comp_iff_stdPi (g : Fin N → Ω → ℝ) (hind : iIndepFun g P)
    (hlaw : ∀ k, HasLaw (g k) (gaussianReal 0 1) P) {h : (Fin N → ℝ) → ℝ}
    (hh : AEStronglyMeasurable h (stdPi N)) :
    Integrable (fun ω => h (fun k => g k ω)) P ↔ Integrable h (stdPi N) := by
  have hmeas : AEMeasurable (fun ω k => g k ω) P :=
    AEMeasurable.of_eval fun k => (hlaw k).aemeasurable
  rw [← map_eq_stdPi g hind hlaw] at hh ⊢
  exact (integrable_map_measure hh hmeas).symm

/-- Gaussian integration by parts on a probability space: for independent
standard Gaussians `g_1, …, g_N` and continuous `f`, `∂_k f` of polynomial
growth, `E[g_k f(g)] = E[∂_k f(g)]`, with both integrands integrable. -/
theorem integral_coord_mul_eq_of_growth_paper (g : Fin N → Ω → ℝ) (hind : iIndepFun g P)
    (hlaw : ∀ k, HasLaw (g k) (gaussianReal 0 1) P) (k : Fin N)
    (f f' : (Fin N → ℝ) → ℝ)
    (hf : ∀ x t, HasDerivAt (fun s => f (Function.update x k s)) (f' (Function.update x k t)) t)
    (hc : Continuous f) (hc' : Continuous f')
    {C C' : ℝ} {d d' : ℕ} (hb : ∀ x, |f x| ≤ C * (1 + ‖x‖) ^ d)
    (hb' : ∀ x, |f' x| ≤ C' * (1 + ‖x‖) ^ d') :
    Integrable (fun ω => g k ω * f (fun i => g i ω)) P ∧
      Integrable (fun ω => f' (fun i => g i ω)) P ∧
      ∫ ω, g k ω * f (fun i => g i ω) ∂P = ∫ ω, f' (fun i => g i ω) ∂P := by
  obtain ⟨h1, h2, h3⟩ := integral_coord_mul_eq_of_growth k f f' hf hc.aestronglyMeasurable
    hc'.aestronglyMeasurable hb hb'
  have hm1 : AEStronglyMeasurable (fun x : Fin N → ℝ => x k * f x) (stdPi N) :=
    ((continuous_apply k).mul hc).aestronglyMeasurable
  refine ⟨(integrable_comp_iff_stdPi g hind hlaw hm1).2 h1,
    (integrable_comp_iff_stdPi g hind hlaw hc'.aestronglyMeasurable).2 h2, ?_⟩
  rw [integral_comp_eq_stdPi g hind hlaw hm1 (h := fun x => x k * f x),
    integral_comp_eq_stdPi g hind hlaw hc'.aestronglyMeasurable, h3]

end Transfer

end StratonovichHAMSecondMoment.GaussianIBP
