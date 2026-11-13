module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Lemma `L:masked-trig-products` (Correlated trigonometric products) of
`notes/integrated_covariance_foundation.tex`.

Statement (TeX lines 347-360).  Let `r, ρ ≥ 0`, `P_r ∈ {cos(rt), sin(rt)}`,
`Q_ρ ∈ {cos(ρt), sin(ρt)}`.  With `I = [s, s+h] ⊂ [0, T]`, `0 < h ≤ 1`,
`A ∈ C¹(I; ℂ)`, `M = sup_I |A|`, `D = sup_I |A'|`, `C₀(a) = 16/(1-a)`,
`‖1_I A P_r Q_ρ‖_a² ≤ C₀(a) h^{2-a} (M+hD)² 𝒬_h(r,ρ)`, where
`𝒬_h(r,ρ) = ⟨h(r-ρ)⟩^{a-1} + ⟨h(r+ρ)⟩^{a-1}` and `⟨x⟩ = √(1+x²)` (TeX l. 296).

Abstraction (the norm `‖·‖_a`).  The manuscript's norm is that of the
complexified temporal completion `H_a^ℂ` of Lemma `L:masked-time-completion`;
functions enter it through the continuous linear inclusion of `L²(0,T)`
(TeX l. 148-155), and "bounded measurable amplitudes on a subinterval,
extended by zero, belong to this completion" (l. 154-155).  We model exactly
this and nothing more:
* `E` is the target space of the norm (a complex normed space in the general
  theorem; a complex inner product space in the `_paper` wrapper, as in TeX);
* `V : Submodule ℂ (ℝ → ℂ)` is the class of functions accepted into the
  completion, and `emb : V →ₗ[ℂ] E` is the (linear) inclusion; `‖emb f‖` is
  `‖f‖_a`.  Only linearity of `emb` is used (TeX l. 365-368 combines modes
  linearly; nothing about the completion beyond linearity enters the proof);
* membership of the four modes `1_I A e^{iωt}` in `V` is the supplied input
  from `L:masked-time-completion` (`hmem`);
* the modulation bound `‖1_I A e^{iωt}‖_a² ≤ C₀ h^{2-a}(M+hD)²⟨hω⟩^{a-1}` for
  every real `ω` is the supplied input from `L:masked-temporal-modulation`
  (`hmod`), stated in exactly the manuscript's form (TeX l. 303-307).
The product `1_I A P_r Q_ρ` is *not* assumed to be in `V` or to satisfy any
bound: its membership and its bound are derived from the four-mode expansion.

Manuscript hypotheses made explicit / implicit side conditions:
* `A` is a function `ℝ → ℂ` (Lean convention); only its values on `I` matter
  because every function is multiplied by the indicator of `I`.
* `C¹(I;ℂ)` is `ContDiffOn ℝ 1 A I`; `M` and `D` are `sSup` of `‖A‖` and of
  `‖derivWithin A I‖` over `I`.  These, `0 < a < 1`, `T > 0`, `0 < h ≤ 1`,
  `0 ≤ s`, `s + h ≤ T` and `r, ρ ≥ 0` appear in the `_paper` wrapper only;
  the proof of this lemma uses none of them (they are needed for the supplied
  modulation input, which is a hypothesis here).
* The general theorems hold for arbitrary real `C, a, h, M, D, r, ρ` and any
  set `I`: the four-mode reduction needs no sign conditions, because `⟨·⟩` is
  even.  The general theorem also proves the sharper bound with an extra
  factor `1/2` (the manuscript's "one half of the asserted right side",
  TeX l. 373).
-/
public import Mathlib

@[expose] public section

noncomputable section

set_option autoImplicit false

open Complex Finset

namespace StratonovichHAMSecondMoment.MaskedTrigProducts

/-! ### (1) The Hilbert-space inequality (TeX l. 365-368) -/

/-- `‖Σ c_j v_j‖² ≤ (Σ |c_j|) Σ |c_j| ‖v_j‖²` for a finite family in a complex
seminormed space (in particular in any complex inner product space). -/
theorem norm_sq_sum_le {ι E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (s : Finset ι) (c : ι → ℂ) (v : ι → E) :
    ‖∑ j ∈ s, c j • v j‖ ^ 2 ≤
      (∑ j ∈ s, ‖c j‖) * ∑ j ∈ s, ‖c j‖ * ‖v j‖ ^ 2 := by
  have htri : ‖∑ j ∈ s, c j • v j‖ ≤ ∑ j ∈ s, ‖c j‖ * ‖v j‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun j _ => norm_smul _ _
  have hcs : (∑ j ∈ s, ‖c j‖ * ‖v j‖) ^ 2 ≤
      (∑ j ∈ s, ‖c j‖) * ∑ j ∈ s, ‖c j‖ * ‖v j‖ ^ 2 := by
    have key := Finset.sum_mul_sq_le_sq_mul_sq s (fun j => Real.sqrt ‖c j‖)
      (fun j => Real.sqrt ‖c j‖ * ‖v j‖)
    have e1 : ∀ j, Real.sqrt ‖c j‖ * (Real.sqrt ‖c j‖ * ‖v j‖) = ‖c j‖ * ‖v j‖ :=
      fun j => by rw [← mul_assoc, Real.mul_self_sqrt (norm_nonneg _)]
    have e2 : ∀ j, Real.sqrt ‖c j‖ ^ 2 = ‖c j‖ :=
      fun j => Real.sq_sqrt (norm_nonneg _)
    have e3 : ∀ j, (Real.sqrt ‖c j‖ * ‖v j‖) ^ 2 = ‖c j‖ * ‖v j‖ ^ 2 :=
      fun j => by rw [mul_pow, e2]
    simp only [e1, e2, e3] at key
    exact key
  have h0 : 0 ≤ ‖∑ j ∈ s, c j • v j‖ := norm_nonneg _
  calc ‖∑ j ∈ s, c j • v j‖ ^ 2 ≤ (∑ j ∈ s, ‖c j‖ * ‖v j‖) ^ 2 :=
        pow_le_pow_left₀ h0 htri 2
    _ ≤ _ := hcs

/-- The same inequality, stated in a complex inner product space (the
manuscript's "In a Hilbert space"). -/
theorem norm_sq_sum_le_inner {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (s : Finset ι) (c : ι → ℂ) (v : ι → E) :
    ‖∑ j ∈ s, c j • v j‖ ^ 2 ≤
      (∑ j ∈ s, ‖c j‖) * ∑ j ∈ s, ‖c j‖ * ‖v j‖ ^ 2 :=
  norm_sq_sum_le s c v

/-! ### Definitions -/

/-- Japanese bracket `⟨x⟩ = √(1+x²)` (TeX l. 296). -/
def bracket (x : ℝ) : ℝ := Real.sqrt (1 + x ^ 2)

theorem bracket_neg (x : ℝ) : bracket (-x) = bracket x := by
  simp [bracket]

/-- `𝒬_h(r,ρ) = ⟨h(r-ρ)⟩^{a-1} + ⟨h(r+ρ)⟩^{a-1}` (TeX l. 355-358). -/
def frequencyPair (a h r ρ : ℝ) : ℝ :=
  bracket (h * (r - ρ)) ^ (a - 1) + bracket (h * (r + ρ)) ^ (a - 1)

/-- The two trigonometric factor shapes `cos` and `sin`. -/
inductive Trig
  | cos
  | sin
  deriving DecidableEq

/-- `Trig.eval k x` is `cos x` or `sin x`, viewed in `ℂ`. -/
def Trig.eval : Trig → ℝ → ℂ
  | .cos, x => (Real.cos x : ℂ)
  | .sin, x => (Real.sin x : ℂ)

/-- The modulated amplitude `t ↦ 1_I(t) A(t) e^{iωt}`. -/
def modeFn (I : Set ℝ) (A : ℝ → ℂ) (ω : ℝ) : ℝ → ℂ :=
  I.indicator fun t => A t * Complex.exp (((ω * t : ℝ) : ℂ) * Complex.I)

/-- The product `t ↦ 1_I(t) A(t) P_r(t) Q_ρ(t)`. -/
def prodFn (I : Set ℝ) (A : ℝ → ℂ) (P Q : Trig) (r ρ : ℝ) : ℝ → ℂ :=
  I.indicator fun t => A t * P.eval (r * t) * Q.eval (ρ * t)

/-- The sign `σ ∈ {1, -1}`, indexed by `Bool`. -/
def sgn : Bool → ℝ
  | true => 1
  | false => -1

/-- Coefficients of a single factor: `cos x = ½e^{ix} + ½e^{-ix}`,
`sin x = (-i/2)e^{ix} + (i/2)e^{-ix}`. -/
def coef1 : Trig → Bool → ℂ
  | .cos, _ => 1 / 2
  | .sin, true => -Complex.I / 2
  | .sin, false => Complex.I / 2

/-- Coefficient of the mode `e^{i(σr+τρ)t}` in `P_r Q_ρ`. -/
def coef (P Q : Trig) (j : Bool × Bool) : ℂ := coef1 P j.1 * coef1 Q j.2

/-- Frequency `σr + τρ` of the mode indexed by `j = (σ, τ)`. -/
def freq (r ρ : ℝ) (j : Bool × Bool) : ℝ := sgn j.1 * r + sgn j.2 * ρ

/-! ### (2) The four-mode expansions (TeX l. 363-365) -/

theorem norm_coef1 (k : Trig) (σ : Bool) : ‖coef1 k σ‖ = 1 / 2 := by
  cases k <;> cases σ <;> simp [coef1]

/-- Every coefficient has absolute value `1/4`. -/
theorem norm_coef (P Q : Trig) (j : Bool × Bool) : ‖coef P Q j‖ = 1 / 4 := by
  rw [coef, norm_mul, norm_coef1, norm_coef1]; norm_num

/-- The coefficient sum `Σ|c_j|` is one (TeX l. 370). -/
theorem sum_norm_coef (P Q : Trig) : ∑ j : Bool × Bool, ‖coef P Q j‖ = 1 := by
  simp only [norm_coef, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_bool, nsmul_eq_mul]
  norm_num

theorem exp_sgn (σ : Bool) (x : ℝ) :
    Complex.exp (((sgn σ * x : ℝ) : ℂ) * Complex.I) =
      if σ then Complex.exp ((x : ℂ) * Complex.I)
      else Complex.exp (-((x : ℂ) * Complex.I)) := by
  cases σ <;> simp [sgn]

/-- One-factor expansion. -/
theorem Trig.eval_expand (k : Trig) (x : ℝ) :
    k.eval x = ∑ σ : Bool, coef1 k σ * Complex.exp (((sgn σ * x : ℝ) : ℂ) * Complex.I) := by
  simp only [Fintype.sum_bool, exp_sgn, ite_true, Bool.false_eq_true, ite_false]
  cases k
  · simp only [Trig.eval, coef1, Complex.ofReal_cos, Complex.cos, neg_mul]
    ring
  · simp only [Trig.eval, coef1, Complex.ofReal_sin, Complex.sin, neg_mul]
    field_simp
    ring

/-- The generic four-mode expansion: `P_r(t) Q_ρ(t) = Σ_{σ,τ} c_{στ} e^{i(σr+τρ)t}`
with `|c_{στ}| = 1/4` (`norm_coef`). -/
theorem four_mode (P Q : Trig) (r ρ t : ℝ) :
    P.eval (r * t) * Q.eval (ρ * t) =
      ∑ j : Bool × Bool, coef P Q j * Complex.exp (((freq r ρ j * t : ℝ) : ℂ) * Complex.I) := by
  rw [P.eval_expand, Q.eval_expand, Finset.sum_mul_sum, ← Finset.univ_product_univ,
    Finset.sum_product]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
  simp only [coef, freq]
  have : (((sgn σ * r + sgn τ * ρ) * t : ℝ) : ℂ) * Complex.I =
      ((sgn σ * (r * t) : ℝ) : ℂ) * Complex.I + ((sgn τ * (ρ * t) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_add]
  ring

/-- Explicit expansion, cosine-cosine. -/
theorem cos_cos_expand (r ρ t : ℝ) :
    (Real.cos (r * t) : ℂ) * Real.cos (ρ * t) =
      1 / 4 * Complex.exp ((((r + ρ) * t : ℝ) : ℂ) * Complex.I)
      + 1 / 4 * Complex.exp ((((r - ρ) * t : ℝ) : ℂ) * Complex.I)
      + 1 / 4 * Complex.exp ((((-r + ρ) * t : ℝ) : ℂ) * Complex.I)
      + 1 / 4 * Complex.exp ((((-r - ρ) * t : ℝ) : ℂ) * Complex.I) := by
  have h := four_mode .cos .cos r ρ t
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, coef, coef1, freq, sgn, Trig.eval] at h
  rw [h]
  ring_nf

/-- Explicit expansion, sine-sine. -/
theorem sin_sin_expand (r ρ t : ℝ) :
    (Real.sin (r * t) : ℂ) * Real.sin (ρ * t) =
      -(1 / 4) * Complex.exp ((((r + ρ) * t : ℝ) : ℂ) * Complex.I)
      + 1 / 4 * Complex.exp ((((r - ρ) * t : ℝ) : ℂ) * Complex.I)
      + 1 / 4 * Complex.exp ((((-r + ρ) * t : ℝ) : ℂ) * Complex.I)
      - 1 / 4 * Complex.exp ((((-r - ρ) * t : ℝ) : ℂ) * Complex.I) := by
  have h := four_mode .sin .sin r ρ t
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, coef, coef1, freq, sgn, Trig.eval] at h
  rw [h]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Explicit expansion, sine-cosine. -/
theorem sin_cos_expand (r ρ t : ℝ) :
    (Real.sin (r * t) : ℂ) * Real.cos (ρ * t) =
      -(Complex.I / 4) * Complex.exp ((((r + ρ) * t : ℝ) : ℂ) * Complex.I)
      - Complex.I / 4 * Complex.exp ((((r - ρ) * t : ℝ) : ℂ) * Complex.I)
      + Complex.I / 4 * Complex.exp ((((-r + ρ) * t : ℝ) : ℂ) * Complex.I)
      + Complex.I / 4 * Complex.exp ((((-r - ρ) * t : ℝ) : ℂ) * Complex.I) := by
  have h := four_mode .sin .cos r ρ t
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, coef, coef1, freq, sgn, Trig.eval] at h
  rw [h]
  ring_nf

/-- Explicit expansion, cosine-sine. -/
theorem cos_sin_expand (r ρ t : ℝ) :
    (Real.cos (r * t) : ℂ) * Real.sin (ρ * t) =
      -(Complex.I / 4) * Complex.exp ((((r + ρ) * t : ℝ) : ℂ) * Complex.I)
      + Complex.I / 4 * Complex.exp ((((r - ρ) * t : ℝ) : ℂ) * Complex.I)
      - Complex.I / 4 * Complex.exp ((((-r + ρ) * t : ℝ) : ℂ) * Complex.I)
      + Complex.I / 4 * Complex.exp ((((-r - ρ) * t : ℝ) : ℂ) * Complex.I) := by
  have h := four_mode .cos .sin r ρ t
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, coef, coef1, freq, sgn, Trig.eval] at h
  rw [h]
  ring_nf

/-- The masked product is the same combination of masked modes. -/
theorem prodFn_eq (I : Set ℝ) (A : ℝ → ℂ) (P Q : Trig) (r ρ : ℝ) :
    prodFn I A P Q r ρ = ∑ j : Bool × Bool, coef P Q j • modeFn I A (freq r ρ j) := by
  funext t
  simp only [prodFn, modeFn, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  by_cases ht : t ∈ I
  · simp only [Set.indicator_of_mem ht]
    rw [mul_assoc, four_mode, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  · simp [Set.indicator_of_notMem ht]

/-! ### (3) The bound, abstract form -/

/-- The masked product belongs to the accepted class once the modes do. -/
theorem prodFn_mem (V : Submodule ℂ (ℝ → ℂ)) (I : Set ℝ) (A : ℝ → ℂ)
    (hmem : ∀ ω : ℝ, modeFn I A ω ∈ V) (P Q : Trig) (r ρ : ℝ) :
    prodFn I A P Q r ρ ∈ V := by
  rw [prodFn_eq]
  exact V.sum_mem fun j _ => V.smul_mem _ (hmem _)

/-- Sum of the four mode brackets: two have `|r-ρ|`, two `r+ρ`. -/
theorem sum_bracket_freq (a h r ρ : ℝ) :
    ∑ j : Bool × Bool, bracket (h * freq r ρ j) ^ (a - 1) = 2 * frequencyPair a h r ρ := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, freq, sgn, frequencyPair]
  have e1 : h * (-1 * r + 1 * ρ) = -(h * (r - ρ)) := by ring
  have e2 : h * (-1 * r + -1 * ρ) = -(h * (r + ρ)) := by ring
  have e3 : h * (1 * r + 1 * ρ) = h * (r + ρ) := by ring
  have e4 : h * (1 * r + -1 * ρ) = h * (r - ρ) := by ring
  rw [e1, e2, e3, e4, bracket_neg, bracket_neg]
  ring

/-- Main abstract bound, with the factor `1/2` the proof actually yields
(TeX l. 373: "one half of the asserted right side").  No sign conditions:
`C, a, h, M, D, r, ρ` arbitrary reals, `I` any set. -/
theorem trig_product_bound_half {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (V : Submodule ℂ (ℝ → ℂ)) (emb : V →ₗ[ℂ] E) (I : Set ℝ) (A : ℝ → ℂ)
    (C a h M D : ℝ)
    (hmem : ∀ ω : ℝ, modeFn I A ω ∈ V)
    (hmod : ∀ ω : ℝ, ‖emb ⟨modeFn I A ω, hmem ω⟩‖ ^ 2 ≤
      C * h ^ (2 - a) * (M + h * D) ^ 2 * bracket (h * ω) ^ (a - 1))
    (P Q : Trig) (r ρ : ℝ) (hp : prodFn I A P Q r ρ ∈ V) :
    ‖emb ⟨prodFn I A P Q r ρ, hp⟩‖ ^ 2 ≤
      C * h ^ (2 - a) * (M + h * D) ^ 2 * frequencyPair a h r ρ / 2 := by
  set K := C * h ^ (2 - a) * (M + h * D) ^ 2
  have hsum : (⟨prodFn I A P Q r ρ, hp⟩ : V) =
      ∑ j : Bool × Bool, coef P Q j • (⟨modeFn I A (freq r ρ j), hmem _⟩ : V) := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    exact prodFn_eq I A P Q r ρ
  rw [hsum, map_sum]
  simp only [map_smul]
  refine (norm_sq_sum_le _ _ _).trans ?_
  rw [sum_norm_coef, one_mul]
  calc ∑ j : Bool × Bool, ‖coef P Q j‖ * ‖emb ⟨modeFn I A (freq r ρ j), hmem _⟩‖ ^ 2
      ≤ ∑ j : Bool × Bool, 1 / 4 * (K * bracket (h * freq r ρ j) ^ (a - 1)) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_coef]
        exact mul_le_mul_of_nonneg_left (hmod _) (by norm_num)
    _ = K * frequencyPair a h r ρ / 2 := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, sum_bracket_freq]
        ring

/-- The manuscript's bound `(E:masked-trig-products)`, abstract form.  The
right side is nonnegative because it dominates a squared norm, so no sign
condition on `C` is needed to pass from the half bound. -/
theorem trig_product_bound {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (V : Submodule ℂ (ℝ → ℂ)) (emb : V →ₗ[ℂ] E) (I : Set ℝ) (A : ℝ → ℂ)
    (C a h M D : ℝ)
    (hmem : ∀ ω : ℝ, modeFn I A ω ∈ V)
    (hmod : ∀ ω : ℝ, ‖emb ⟨modeFn I A ω, hmem ω⟩‖ ^ 2 ≤
      C * h ^ (2 - a) * (M + h * D) ^ 2 * bracket (h * ω) ^ (a - 1))
    (P Q : Trig) (r ρ : ℝ) (hp : prodFn I A P Q r ρ ∈ V) :
    ‖emb ⟨prodFn I A P Q r ρ, hp⟩‖ ^ 2 ≤
      C * h ^ (2 - a) * (M + h * D) ^ 2 * frequencyPair a h r ρ := by
  have h1 := trig_product_bound_half V emb I A C a h M D hmem hmod P Q r ρ hp
  have h0 : 0 ≤ ‖emb ⟨prodFn I A P Q r ρ, hp⟩‖ ^ 2 := sq_nonneg _
  linarith

/-! ### (4) The paper wrapper -/

/-- `C₀(a) = 16/(1-a)` (TeX l. 306). -/
def C₀ (a : ℝ) : ℝ := 16 / (1 - a)

/-- Lemma `L:masked-trig-products`, with the manuscript's hypotheses.

Supplied inputs (named hypotheses):
* `hmem` — from `L:masked-time-completion` (TeX l. 148-155): the modulated
  amplitudes `1_I A e^{iωt}` lie in the accepted class `V`, whose inclusion
  `emb` into the complexified completion `E = H_a^ℂ` is linear;
* `hmod` — `L:masked-temporal-modulation` (TeX l. 300-309), in exactly its
  manuscript form, for every real `ω`.

The hypotheses `ha0 ha1 hT hh0 hh1 hs hsT hA hM hD hr hρ` are the
manuscript's standing hypotheses; they are not used by this proof (they are
consumed by the supplied modulation input). -/
theorem masked_trig_products_paper {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (a T s h : ℝ) (_ha0 : 0 < a) (_ha1 : a < 1) (_hT : 0 < T)
    (_hh0 : 0 < h) (_hh1 : h ≤ 1) (_hs : 0 ≤ s) (_hsT : s + h ≤ T)
    (A : ℝ → ℂ) (_hA : ContDiffOn ℝ 1 A (Set.Icc s (s + h)))
    (M D : ℝ)
    (_hM : M = sSup ((fun t => ‖A t‖) '' Set.Icc s (s + h)))
    (_hD : D = sSup ((fun t => ‖derivWithin A (Set.Icc s (s + h)) t‖) '' Set.Icc s (s + h)))
    (r ρ : ℝ) (_hr : 0 ≤ r) (_hρ : 0 ≤ ρ) (P Q : Trig)
    (V : Submodule ℂ (ℝ → ℂ)) (emb : V →ₗ[ℂ] E)
    (hmem : ∀ ω : ℝ, modeFn (Set.Icc s (s + h)) A ω ∈ V)
    (hmod : ∀ ω : ℝ, ‖emb ⟨modeFn (Set.Icc s (s + h)) A ω, hmem ω⟩‖ ^ 2 ≤
      C₀ a * h ^ (2 - a) * (M + h * D) ^ 2 * bracket (h * ω) ^ (a - 1)) :
    prodFn (Set.Icc s (s + h)) A P Q r ρ ∈ V ∧
      ∀ hp : prodFn (Set.Icc s (s + h)) A P Q r ρ ∈ V,
        ‖emb ⟨prodFn (Set.Icc s (s + h)) A P Q r ρ, hp⟩‖ ^ 2 ≤
          C₀ a * h ^ (2 - a) * (M + h * D) ^ 2 * frequencyPair a h r ρ :=
  ⟨prodFn_mem V _ A hmem P Q r ρ,
    fun hp => trig_product_bound V emb _ A (C₀ a) a h M D hmem hmod P Q r ρ hp⟩

end StratonovichHAMSecondMoment.MaskedTrigProducts
