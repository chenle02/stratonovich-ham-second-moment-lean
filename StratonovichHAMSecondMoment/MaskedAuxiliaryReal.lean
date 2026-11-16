module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

The real-Hilbert-space clause of `P:masked-auxiliary-norm` (Auxiliary mask
norm) of `notes/integrated_covariance_foundation.tex` (revision 39f2597a):
statement lines 106-118, the clause being line 117, "For a real `H`, the same
assertion holds after complexification".

Why complexification and not a statement over `RCLike 𝕜`.  The transform of
the section (lines 10-14) has the complex kernel `e^{-iξ·x}`, so the transform
of an `H`-valued function has values in a complex space even when `H` is
real; a version "over `ℝ`" of `E:masked-hilbert-fourier` has no meaning.  The
clause therefore says: complexify `H`, regard the real Schwartz map `F` as a
map into the complexification, and apply the complex assertion.  This module
proves exactly that.

Mathlib (at the companion's pin) has no complexification of a real inner
product space, so it is built here:
* `Cx H`, pairs `x = (x.re, x.im)` of vectors of `H`, read as `x.re + i x.im`;
  `(a + ib)(u, v) = (au - bv, av + bu)`;
* the inner product
  `⟪x, y⟫ = ⟪x.re, y.re⟫ + ⟪x.im, y.im⟫ + i(⟪x.re, y.im⟫ - ⟪x.im, y.re⟫)`,
  conjugate linear in the first argument as in Mathlib, so that
  `‖x‖² = ‖x.re‖² + ‖x.im‖²` (`norm_sq_eq`);
* `Cx H` is a complex Hilbert space (`InnerProductSpace ℂ`, `CompleteSpace`),
  and separable when `H` is (`SeparableSpace`);
* the real embedding `ofRealCLM : H →L[ℝ] Cx H`, `v ↦ (v, 0)`, an isometry
  (`norm_ofReal`), and the real and imaginary parts `reCLM`, `imCLM`.

Formalized:
* `masked_auxiliary_norm_real_paper`: under the manuscript's hypotheses
  (`H:homog`, `Γ ≠ 0`, `ζ` a real nonzero Schwartz function, `H` a separable
  real Hilbert space, `F` an `H`-valued Schwartz map), with `F_ℂ = ι ∘ F` the
  complexified map (`cxS F`): `H_ℂ = Cx H` is a separable complex Hilbert space
  (instances), `ι` is isometric, the masked function `ζ_R F_ℂ` is the
  complexification of the real masked function `ζ_R F`, and every conclusion of
  `MaskedAuxiliaryNorm.masked_auxiliary_norm_paper` holds for `F_ℂ`.  It also
  states the transform in real terms:
  `(F_ℂ)^(ξ) = c_d (∫ cos(ξ·x) F(x) dx, -∫ sin(ξ·x) F(x) dx)`, hence
  `‖(F_ℂ)^(ξ)‖² = c_d² (‖∫ cos(ξ·x) F(x) dx‖² + ‖∫ sin(ξ·x) F(x) dx‖²)`
  (`norm_sq_paperHat_cx`), so both sides of `E:masked-hilbert-fourier` after
  complexification are explicit integrals of norms in `H`.

Whole: with `MaskedAuxiliaryNorm.masked_auxiliary_norm_paper` (complex `H`)
and this module (real `H`), every conclusion of `P:masked-auxiliary-norm` is a
Lean conclusion under the TeX hypotheses, except the proof-internal claims on
`ρ_R` (finite everywhere, continuous; lines 131-134) that are not part of the
statement (as recorded in `MaskedAuxiliaryNorm`).

Hypotheses of the wrapper: `Γ ≠ 0` is carried, unused (it is unused in the
complex wrapper too).  The inner product of `H` defines the Hilbert norm of
`Cx H`; the completeness of `H` gives the completeness of `Cx H`, needed by the
complex statement (Bochner integrals, Fourier inversion); the separability of
`H` gives the separability of `Cx H`, a hypothesis of the complex wrapper that
the complex proof does not use.  The general form `masked_auxiliary_norm_real`
drops `Γ ≠ 0` and the separability.

Implicit hypotheses made explicit: the complexification is the standard one,
`‖x + iy‖² = ‖x‖² + ‖y‖²` with the inner product above (the TeX does not
define it); `F_ℂ = ι ∘ F`.

Proof route.  `Cx H` is built from an `InnerProductSpace.Core`; completeness
and separability transfer along the real continuous linear equivalence
`Cx H ≃ H × H`; the transform identities use `integral_comp_comm` for the real
and imaginary parts; the measure-theoretic conclusions and the inequality are
`MaskedAuxiliaryNorm.masked_auxiliary_norm_paper` applied to `Cx H`.

Supplied inputs: none.
-/

public import Mathlib
public import StratonovichHAMSecondMoment.MaskedAuxiliaryNorm

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Real Metric
open scoped ENNReal NNReal ComplexConjugate

namespace StratonovichHAMSecondMoment.MaskedAuxiliaryReal

open HomogHypothesis SpectralHomog MaskedSpectralGrowth MaskedAuxiliaryNorm

/-! ### The complexification `Cx H` of a real space -/

/-- The complexification of a real vector space `H`: pairs `(re, im)`, read as
`re + i im` (line 117, "after complexification"). -/
@[ext] structure Cx (H : Type*) where
  /-- The real part. -/
  re : H
  /-- The imaginary part. -/
  im : H

namespace Cx

variable {H : Type*}

/-- Auxiliary to the Lean proof route. `Cx H` as a set is `H × H`. -/
def equivProd : Cx H ≃ H × H where
  toFun x := (x.re, x.im)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

section Group

variable [AddCommGroup H]

instance instAddCommGroup : AddCommGroup (Cx H) := equivProd.addCommGroup

/-- Auxiliary to the Lean proof route. -/
@[simp] theorem add_re (x y : Cx H) : (x + y).re = x.re + y.re := rfl
/-- Auxiliary to the Lean proof route. -/
@[simp] theorem add_im (x y : Cx H) : (x + y).im = x.im + y.im := rfl
/-- Auxiliary to the Lean proof route. -/
@[simp] theorem zero_re : (0 : Cx H).re = 0 := rfl
/-- Auxiliary to the Lean proof route. -/
@[simp] theorem zero_im : (0 : Cx H).im = 0 := rfl
/-- Auxiliary to the Lean proof route. -/
@[simp] theorem neg_re (x : Cx H) : (-x).re = -x.re := rfl
/-- Auxiliary to the Lean proof route. -/
@[simp] theorem neg_im (x : Cx H) : (-x).im = -x.im := rfl
/-- Auxiliary to the Lean proof route. -/
@[simp] theorem sub_re (x y : Cx H) : (x - y).re = x.re - y.re := rfl
/-- Auxiliary to the Lean proof route. -/
@[simp] theorem sub_im (x y : Cx H) : (x - y).im = x.im - y.im := rfl

end Group

section Algebra

variable [AddCommGroup H] [Module ℝ H]

/-- The complex scalar action `(a + ib)(u, v) = (au - bv, av + bu)`. -/
instance instSMul : SMul ℂ (Cx H) where
  smul c x := ⟨c.re • x.re - c.im • x.im, c.re • x.im + c.im • x.re⟩

/-- Auxiliary to the Lean proof route. -/
@[simp] theorem smul_re (c : ℂ) (x : Cx H) : (c • x).re = c.re • x.re - c.im • x.im := rfl
/-- Auxiliary to the Lean proof route. -/
@[simp] theorem smul_im (c : ℂ) (x : Cx H) : (c • x).im = c.re • x.im + c.im • x.re := rfl

instance instModule : Module ℂ (Cx H) where
  one_smul x := by ext <;> simp
  mul_smul a b x := by ext <;> simp <;> module
  smul_zero a := by ext <;> simp
  smul_add a x y := by ext <;> simp <;> module
  add_smul a b x := by ext <;> simp <;> module
  zero_smul x := by ext <;> simp

end Algebra

section Inner

variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The complex inner product of the complexification:
`⟪x, y⟫ = ⟪x.re, y.re⟫ + ⟪x.im, y.im⟫ + i(⟪x.re, y.im⟫ - ⟪x.im, y.re⟫)`. -/
def cxInner (x y : Cx H) : ℂ :=
  ((inner ℝ x.re y.re + inner ℝ x.im y.im : ℝ) : ℂ) +
    ((inner ℝ x.re y.im - inner ℝ x.im y.re : ℝ) : ℂ) * Complex.I

/-- Auxiliary to the Lean proof route. -/
theorem cxInner_re (x y : Cx H) :
    (cxInner x y).re = inner ℝ x.re y.re + inner ℝ x.im y.im := by
  simp [cxInner]

/-- Auxiliary to the Lean proof route. -/
theorem cxInner_im (x y : Cx H) :
    (cxInner x y).im = inner ℝ x.re y.im - inner ℝ x.im y.re := by
  simp [cxInner]

/-- Auxiliary to the Lean proof route. The inner product core of `Cx H`. -/
@[instance_reducible]
def core : InnerProductSpace.Core ℂ (Cx H) where
  inner := cxInner
  conj_inner_symm x y := by
    apply Complex.ext
    · simp only [Complex.conj_re, cxInner_re, real_inner_comm]
    · simp only [Complex.conj_im, cxInner_im, real_inner_comm]; ring
  re_inner_nonneg x := by
    change 0 ≤ (cxInner x x).re
    rw [cxInner_re]
    exact add_nonneg real_inner_self_nonneg real_inner_self_nonneg
  add_left x y z := by
    apply Complex.ext
    · simp only [Complex.add_re, cxInner_re, add_re, add_im, inner_add_left]; ring
    · simp only [Complex.add_im, cxInner_im, add_re, add_im, inner_add_left]; ring
  smul_left x y c := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, cxInner_re, cxInner_im,
        smul_re, smul_im, inner_sub_left, inner_add_left, real_inner_smul_left]
      ring
    · simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, cxInner_re, cxInner_im,
        smul_re, smul_im, inner_sub_left, inner_add_left, real_inner_smul_left]
      ring
  definite x hx := by
    have h0 : inner ℝ x.re x.re + inner ℝ x.im x.im = 0 := by
      rw [← cxInner_re]; exact congrArg Complex.re hx
    have h1 := real_inner_self_nonneg (x := x.re)
    have h2 := real_inner_self_nonneg (x := x.im)
    ext
    · exact (inner_self_eq_zero (𝕜 := ℝ)).1 (by linarith)
    · exact (inner_self_eq_zero (𝕜 := ℝ)).1 (by linarith)

instance instNormedAddCommGroup : NormedAddCommGroup (Cx H) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ (Cx H) _ _ _ core

instance instInnerProductSpace : InnerProductSpace ℂ (Cx H) := InnerProductSpace.ofCore core.toCore

/-- Auxiliary to the Lean proof route. -/
theorem inner_eq (x y : Cx H) : inner ℂ x y = cxInner x y := rfl

/-- The norm of the complexification:
`‖x‖² = ‖x.re‖² + ‖x.im‖²`. -/
theorem norm_sq_eq (x : Cx H) : ‖x‖ ^ 2 = ‖x.re‖ ^ 2 + ‖x.im‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ, inner_eq, RCLike.re_to_complex, cxInner_re,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

/-- Auxiliary to the Lean proof route. -/
theorem norm_re_le (x : Cx H) : ‖x.re‖ ≤ ‖x‖ := by
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero, norm_sq_eq]
  nlinarith [sq_nonneg ‖x.im‖]

/-- Auxiliary to the Lean proof route. -/
theorem norm_im_le (x : Cx H) : ‖x.im‖ ≤ ‖x‖ := by
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero, norm_sq_eq]
  nlinarith [sq_nonneg ‖x.re‖]

/-- Auxiliary to the Lean proof route. -/
theorem norm_mk_le (u v : H) : ‖(⟨u, v⟩ : Cx H)‖ ≤ ‖u‖ + ‖v‖ := by
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, norm_sq_eq]
  nlinarith [norm_nonneg u, norm_nonneg v]

/-- Auxiliary to the Lean proof route. The real scalar action of `Cx H`
(restricted from `ℂ`) acts componentwise. -/
@[simp] theorem real_smul_re (r : ℝ) (x : Cx H) : (r • x).re = r • x.re := by
  have h : ((r : ℂ) • x).re = r • x.re := by
    rw [smul_re]; simp only [Complex.ofReal_re, Complex.ofReal_im, zero_smul]; abel
  exact h

/-- Auxiliary to the Lean proof route. -/
@[simp] theorem real_smul_im (r : ℝ) (x : Cx H) : (r • x).im = r • x.im := by
  have h : ((r : ℂ) • x).im = r • x.im := by
    rw [smul_im]; simp only [Complex.ofReal_re, Complex.ofReal_im, zero_smul]; abel
  exact h

/-- The real embedding `ι : H → Cx H`, `v ↦ (v, 0)`, as a real continuous linear
map. -/
def ofRealCLM : H →L[ℝ] Cx H :=
  LinearMap.mkContinuous
    { toFun := fun v => ⟨v, 0⟩
      map_add' := fun u v => by ext <;> simp
      map_smul' := fun r v => by ext <;> simp } 1
    (fun v => by rw [one_mul]; simpa using norm_mk_le v (0 : H))

/-- Auxiliary to the Lean proof route. -/
@[simp] theorem ofRealCLM_re (v : H) : (ofRealCLM v).re = v := rfl

/-- Auxiliary to the Lean proof route. -/
@[simp] theorem ofRealCLM_im (v : H) : (ofRealCLM v).im = 0 := rfl

/-- The embedding `ι` is isometric: `‖ι v‖ = ‖v‖`. -/
theorem norm_ofReal (v : H) : ‖ofRealCLM v‖ = ‖v‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_eq]
  simp

/-- The real part as a real continuous linear map. -/
def reCLM : Cx H →L[ℝ] H :=
  LinearMap.mkContinuous
    { toFun := Cx.re
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by simp } 1
    (fun x => by rw [one_mul]; exact norm_re_le x)

/-- Auxiliary to the Lean proof route. -/
@[simp] theorem reCLM_apply (x : Cx H) : reCLM x = x.re := rfl

/-- The imaginary part as a real continuous linear map. -/
def imCLM : Cx H →L[ℝ] H :=
  LinearMap.mkContinuous
    { toFun := Cx.im
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by simp } 1
    (fun x => by rw [one_mul]; exact norm_im_le x)

/-- Auxiliary to the Lean proof route. -/
@[simp] theorem imCLM_apply (x : Cx H) : imCLM x = x.im := rfl

/-- Auxiliary to the Lean proof route. `Cx H ≃ H × H` as a real continuous
linear equivalence (`H × H` with the sup norm). -/
def equivProdL : Cx H ≃L[ℝ] H × H :=
  LinearEquiv.toContinuousLinearEquivOfBounds
    { equivProd with
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        simp only [equivProd, Equiv.toFun_as_coe, Equiv.coe_fn_mk, RingHom.id_apply,
          Prod.smul_mk, real_smul_re, real_smul_im] } 1 2
    (fun x => by
      simp only [one_mul, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, equivProd,
        Equiv.toFun_as_coe, Equiv.coe_fn_mk, Prod.norm_mk]
      exact max_le (norm_re_le x) (norm_im_le x))
    (fun p => by
      simp only [LinearEquiv.coe_symm_mk', equivProd, Equiv.invFun_as_coe, Equiv.coe_fn_symm_mk]
      refine (norm_mk_le p.1 p.2).trans ?_
      have h1 : ‖p.1‖ ≤ ‖p‖ := norm_fst_le p
      have h2 : ‖p.2‖ ≤ ‖p‖ := norm_snd_le p
      linarith)

/-- Auxiliary to the Lean proof route. -/
@[simp] theorem equivProdL_apply (x : Cx H) : equivProdL x = (x.re, x.im) := rfl

instance instCompleteSpace [CompleteSpace H] : CompleteSpace (Cx H) := by
  have he : IsUniformEmbedding (equivProdL (H := H)).toEquiv :=
    Equiv.isUniformEmbedding _ (equivProdL (H := H) : Cx H →L[ℝ] H × H).uniformContinuous
      (equivProdL (H := H)).symm.toContinuousLinearMap.uniformContinuous
  exact (completeSpace_congr he).2 inferInstance

instance instSeparableSpace [TopologicalSpace.SeparableSpace H] :
    TopologicalSpace.SeparableSpace (Cx H) :=
  (equivProdL (H := H)).symm.surjective.denseRange.separableSpace
    (equivProdL (H := H)).symm.continuous

end Inner

end Cx

open Cx

/-! ### The complexified Schwartz map and its transform -/

section Transform

variable {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The complexification `F_ℂ = ι ∘ F` of a real-Hilbert-valued Schwartz map
(line 117), as a `Cx H`-valued Schwartz map. -/
def cxS (F : SchwartzMap (Rd d) H) : SchwartzMap (Rd d) (Cx H) :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) ofRealCLM F

/-- Auxiliary to the Lean proof route. -/
@[simp] theorem cxS_apply (F : SchwartzMap (Rd d) H) (x : Rd d) : cxS F x = ofRealCLM (F x) :=
  rfl

/-- The masked complexified map is the complexification of the real masked map
`ζ_R F`: `ζ_R(x) F_ℂ(x) = ι(ζ_R(x) F(x))`. -/
theorem mask_cxS (ζ : SchwartzMap (Rd d) ℝ) (R : ℝ) (F : SchwartzMap (Rd d) H) :
    (fun x => (zetaR ζ R x : ℂ) • cxS F x) = fun x => ofRealCLM (zetaR ζ R x • F x) := by
  funext x
  ext <;> simp

variable [CompleteSpace H]

/-- The real part of the transform of a complexified Schwartz map:
`Re (F_ℂ)^(ξ) = c_d ∫ cos(ξ·x) F(x) dx`. -/
theorem paperHat_cxS_re (F : SchwartzMap (Rd d) H) (ξ : Rd d) :
    (paperHat (cxS F : Rd d → Cx H) ξ).re = cd d • ∫ x, Real.cos (inner ℝ ξ x) • F x := by
  have hi := integrable_paperHat_integrand (cxS F) ξ
  rw [paperHat, smul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_smul, sub_zero]
  congr 1
  rw [← reCLM_apply, ← ContinuousLinearMap.integral_comp_comm _ hi]
  congr 1
  funext x
  simp [Complex.exp_re, Complex.exp_im]

/-- The imaginary part of the transform of a complexified Schwartz map:
`Im (F_ℂ)^(ξ) = -c_d ∫ sin(ξ·x) F(x) dx`. -/
theorem paperHat_cxS_im (F : SchwartzMap (Rd d) H) (ξ : Rd d) :
    (paperHat (cxS F : Rd d → Cx H) ξ).im = -(cd d • ∫ x, Real.sin (inner ℝ ξ x) • F x) := by
  have hi := integrable_paperHat_integrand (cxS F) ξ
  rw [paperHat, smul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_smul, add_zero]
  rw [← imCLM_apply, ← ContinuousLinearMap.integral_comp_comm _ hi, ← smul_neg,
    ← integral_neg]
  congr 2
  funext x
  simp [Complex.exp_re, Complex.exp_im]

/-- The norm of the complexified transform in real terms:
`‖(F_ℂ)^(ξ)‖² = c_d² (‖∫ cos(ξ·x) F(x) dx‖² + ‖∫ sin(ξ·x) F(x) dx‖²)`. -/
theorem norm_sq_paperHat_cx (F : SchwartzMap (Rd d) H) (ξ : Rd d) :
    ‖paperHat (cxS F : Rd d → Cx H) ξ‖ ^ 2 =
      cd d ^ 2 * (‖∫ x, Real.cos (inner ℝ ξ x) • F x‖ ^ 2 +
        ‖∫ x, Real.sin (inner ℝ ξ x) • F x‖ ^ 2) := by
  rw [norm_sq_eq, paperHat_cxS_re, paperHat_cxS_im, norm_neg, norm_smul, norm_smul,
    Real.norm_of_nonneg (cd_pos d).le]
  ring

end Transform

/-! ### `P:masked-auxiliary-norm` for a real `H` (line 117) -/

/-- **`P:masked-auxiliary-norm`, real `H`, general form** (line 117).
Hypotheses as in `MaskedAuxiliaryNorm.masked_auxiliary_norm` (`μ` s-finite,
tempered, even; `IsSpectralMeasure Γ μ`; the scaling of `Γ`; `ζ ≠ 0` real
Schwartz), with `H` a real Hilbert space (inner product, complete) and `F` an
`H`-valued Schwartz map.  Conclusions: the complexification `Cx H` is complete;
`ι` is isometric and `‖z‖² = ‖Re z‖² + ‖Im z‖²`; the transform of `F_ℂ` in real
terms; `ζ_R F_ℂ = ι(ζ_R F)`; and every conclusion of
`masked_auxiliary_norm` for `F_ℂ = cxS F`. -/
theorem masked_auxiliary_norm_real {d : ℕ} {Γ μ : Measure (Rd d)} {alpha : ℝ} [SFinite μ]
    (hμt : IsTempered μ) (hμe : IsEven μ) (hsp : IsSpectralMeasure Γ μ)
    (hΓs : SpectralHomogeneous Γ ((d : ℝ) - alpha)) (ζ : SchwartzMap (Rd d) ℝ) (hζ : ζ ≠ 0)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (F : SchwartzMap (Rd d) H) :
    CompleteSpace (Cx H) ∧ (∀ v : H, ‖ofRealCLM v‖ = ‖v‖) ∧
      (∀ z : Cx H, ‖z‖ ^ 2 = ‖z.re‖ ^ 2 + ‖z.im‖ ^ 2) ∧
      (∀ ξ : Rd d, ‖paperHat (cxS F : Rd d → Cx H) ξ‖ ^ 2 =
        cd d ^ 2 * (‖∫ x, Real.cos (inner ℝ ξ x) • F x‖ ^ 2 +
          ‖∫ x, Real.sin (inner ℝ ξ x) • F x‖ ^ 2)) ∧
      (∀ R : ℝ, (fun x => (zetaR ζ R x : ℂ) • cxS F x) =
        fun x => ofRealCLM (zetaR ζ R x • F x)) ∧
      (Integrable (paperHat (fun x => (ζ x : ℂ))) ∧ 0 < Lz ζ) ∧
      ∀ R : ℝ, 0 < R →
        (Integrable (kR ζ R) ∧ ∫ u, ‖kR ζ R u‖ = Lz ζ) ∧
        IsEven (nu μ ζ R) ∧ IsTempered (nu μ ζ R) ∧ IsLocallyFiniteMeasure (nu μ ζ R) ∧
        (∀ y : Rd d, ∀ r : ℝ, 0 < r →
          nu μ ζ R (ball y r) ≤ ENNReal.ofReal (cd d ^ 2 * Lz ζ ^ 2 * CGamma Γ * r ^ alpha) ∧
          nu μ ζ R (closedBall y r) ≤
            ENNReal.ofReal (cd d ^ 2 * Lz ζ ^ 2 * CGamma Γ * r ^ alpha)) ∧
        (Integrable (fun ξ => ‖paperHat (fun x => (zetaR ζ R x : ℂ) • cxS F x) ξ‖ ^ 2) μ ∧
          Integrable (fun η => ‖paperHat (cxS F : Rd d → Cx H) η‖ ^ 2) (nu μ ζ R) ∧
          ∫⁻ ξ, ‖paperHat (fun x => (zetaR ζ R x : ℂ) • cxS F x) ξ‖ₑ ^ 2 ∂μ ≤
            ∫⁻ η, ‖paperHat (cxS F : Rd d → Cx H) η‖ₑ ^ 2 ∂nu μ ζ R ∧
          ∫⁻ η, ‖paperHat (cxS F : Rd d → Cx H) η‖ₑ ^ 2 ∂nu μ ζ R < ⊤ ∧
          ∫ ξ, ‖paperHat (fun x => (zetaR ζ R x : ℂ) • cxS F x) ξ‖ ^ 2 ∂μ ≤
            ∫ η, ‖paperHat (cxS F : Rd d → Cx H) η‖ ^ 2 ∂nu μ ζ R) :=
  ⟨inferInstance, norm_ofReal, norm_sq_eq, norm_sq_paperHat_cx F, fun R => mask_cxS ζ R F,
    masked_auxiliary_norm hμt hμe hsp hΓs ζ hζ (cxS F)⟩

/-- **`P:masked-auxiliary-norm` for a real `H`, with the manuscript's
hypotheses** (line 117, "For a real `H`, the same assertion holds after
complexification"): the section's standing assumptions `H:homog`
(`HomogCovariance`) and `Γ ≠ 0` (lines 7-8), `ζ` a real nonzero Schwartz
function (line 96), `H` a separable real Hilbert space and `F` an `H`-valued
Schwartz map.  Conclusions: the complexification `Cx H` is a separable complex
Hilbert space (its `InnerProductSpace ℂ` instance, `CompleteSpace` and
`SeparableSpace` stated); `ι` is isometric and `‖z‖² = ‖Re z‖² + ‖Im z‖²`; the
transform of `F_ℂ` in real terms; `ζ_R F_ℂ = ι(ζ_R F)`; and every conclusion
of `MaskedAuxiliaryNorm.masked_auxiliary_norm_paper` for `F_ℂ = cxS F`, which
is that proposition applied to the separable complex Hilbert space `Cx H`.
`Γ ≠ 0` is carried, unused (as in the complex wrapper). -/
theorem masked_auxiliary_norm_real_paper {d : ℕ} {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (h : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) (ζ : SchwartzMap (Rd d) ℝ)
    (hζ : ζ ≠ 0) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (F : SchwartzMap (Rd d) H) :
    CompleteSpace (Cx H) ∧ TopologicalSpace.SeparableSpace (Cx H) ∧
      (∀ v : H, ‖ofRealCLM v‖ = ‖v‖) ∧
      (∀ z : Cx H, ‖z‖ ^ 2 = ‖z.re‖ ^ 2 + ‖z.im‖ ^ 2) ∧
      (∀ ξ : Rd d, ‖paperHat (cxS F : Rd d → Cx H) ξ‖ ^ 2 =
        cd d ^ 2 * (‖∫ x, Real.cos (inner ℝ ξ x) • F x‖ ^ 2 +
          ‖∫ x, Real.sin (inner ℝ ξ x) • F x‖ ^ 2)) ∧
      (∀ R : ℝ, (fun x => (zetaR ζ R x : ℂ) • cxS F x) =
        fun x => ofRealCLM (zetaR ζ R x • F x)) ∧
      (Integrable (paperHat (fun x => (ζ x : ℂ))) ∧ 0 < Lz ζ) ∧
      ∀ R : ℝ, 0 < R →
        (Integrable (kR ζ R) ∧ ∫ u, ‖kR ζ R u‖ = Lz ζ) ∧
        IsEven (nu μ ζ R) ∧ IsTempered (nu μ ζ R) ∧ IsLocallyFiniteMeasure (nu μ ζ R) ∧
        (∀ y : Rd d, ∀ r : ℝ, 0 < r →
          nu μ ζ R (ball y r) ≤ ENNReal.ofReal (cd d ^ 2 * Lz ζ ^ 2 * CGamma Γ * r ^ alpha) ∧
          nu μ ζ R (closedBall y r) ≤
            ENNReal.ofReal (cd d ^ 2 * Lz ζ ^ 2 * CGamma Γ * r ^ alpha)) ∧
        (Integrable (fun ξ => ‖paperHat (fun x => (zetaR ζ R x : ℂ) • cxS F x) ξ‖ ^ 2) μ ∧
          Integrable (fun η => ‖paperHat (cxS F : Rd d → Cx H) η‖ ^ 2) (nu μ ζ R) ∧
          ∫⁻ ξ, ‖paperHat (fun x => (zetaR ζ R x : ℂ) • cxS F x) ξ‖ₑ ^ 2 ∂μ ≤
            ∫⁻ η, ‖paperHat (cxS F : Rd d → Cx H) η‖ₑ ^ 2 ∂nu μ ζ R ∧
          ∫⁻ η, ‖paperHat (cxS F : Rd d → Cx H) η‖ₑ ^ 2 ∂nu μ ζ R < ⊤ ∧
          ∫ ξ, ‖paperHat (fun x => (zetaR ζ R x : ℂ) • cxS F x) ξ‖ ^ 2 ∂μ ≤
            ∫ η, ‖paperHat (cxS F : Rd d → Cx H) η‖ ^ 2 ∂nu μ ζ R) :=
  ⟨inferInstance, inferInstance, norm_ofReal, norm_sq_eq, norm_sq_paperHat_cx F,
    fun R => mask_cxS ζ R F, masked_auxiliary_norm_paper h hΓ ζ hζ (cxS F)⟩

end StratonovichHAMSecondMoment.MaskedAuxiliaryReal
