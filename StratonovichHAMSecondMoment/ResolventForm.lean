module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

The form layer on `H^1(ℝ^d)` (wave L13, item K5b): complex Lax-Milgram, the shifted signed
Schrödinger form `q_V + c` and its bounded resolvent `R_V = (H_V + c)⁻¹` on `L²`.  A narrower
result for `P:signed-closed-form` (inputs supplied): no manuscript label becomes whole here.

Manuscript anchors (revision 39f2597a, `notes/integrated_signed_static.tex`):
* `L:signed-limiting-multiplier` (lines 11-19), display `E:signed-multiplier-form`
  (`|v_V(u,w)| ≤ k ‖u‖_{H^{1/2}} ‖w‖_{H^{1/2}}`, lines 16-18).  Here it is a hypothesis
  (`SignedMultiplierForm`), not proved: the lemma that produces `V` is not formalized.
* `P:signed-closed-form` (lines 49-130): `K ≥ max(1, ‖L‖)`, `c = 2 + K²`,
  `q_V(u) = ‖∇u‖₂² - v_V(u,u)` on `Q(q_V) = H^1` (line 53), `L_K = 3(1 + K²)`, the form bounds
  `E:signed-form-bounds` (lines 58-59) with the proof's scalar steps (lines 77-89):
  `‖u‖²_{H^{1/2}} ≤ b z`, `|v_V(u,u)| ≤ K b z ≤ z²/2 + K² b²/2`, and
  `q_V + c b² ≥ z²/2 + (1 + K²/2) b²`, `q_V + c b² ≤ L_K z²`, where `b = ‖u‖₂`, `z = ‖u‖_{H^1}`.
* `L:signed-spectral-wave` (lines 137-165), line 164: "Real and complex form infima agree because
  a complex diagonal splits into the two real diagonals" (`re_diag_split`).

Norm conventions (wave L13 decision 5).  `H^{1}(Rd d)` is Mathlib's Bessel-potential space
(`2π` Fourier convention), consumed from `H1Mathlib` (K5a).  Manuscript constants are stated in
the manuscript norm `z² = ‖u‖₂² + Σ_j ‖∂_j u‖₂²` (`msNormSq`), which on real profiles is K5a's
`manuscriptH1NormSq` (`msNormSq_toH1`).  The manuscript `H^{1/2}` norm is
`‖u‖²_{H^{1/2}} = ∫ (1 + 4π²|ξ|²)^{1/2} |𝓕u(ξ)|² dξ` (`h12NormSq`), the same convention as its
`H^1` norm (`‖⟨ξ⟩^r û‖₂` with `e^{-ixξ}`, `notes/integrated_compact_gaussian.tex` line 277).

Formalized here, with no supplied inputs:
1. Lax-Milgram over any `RCLike` field (`IsCoerciveSesq.equiv`), a port of Mathlib's real
   `IsCoercive.continuousLinearEquivOfBilin` to sesquilinear forms.
2. The resolvent of a Hermitian coercive form relative to `ι : V → L` (`solOp`, `formResolvent`):
   the weak equation `B w (S f) = ⟪ι w, f⟫`, uniqueness, self-adjointness, positivity,
   `‖R‖ ≤ 1` when `‖ι u‖² ≤ re B u u`, injectivity when `(range ι)ᗮ = 0` (dense range).
3. On `H^1`: the embedding `embL2 : H^1 →L[ℂ] L²` and the gradient components
   `gradOp j = 2πi · 𝓕⁻ (ξ_j ⟨ξ⟩⁻¹) 𝓕 (u.toLp)`; their identification with `f` and its weak
   gradient on real profiles (`embL2_toH1`, `gradOp_toH1`); `‖u‖² ≤ z² ≤ (2π)² ‖u‖²`;
   `‖u‖²_{H^{1/2}} ≤ b z`; dense range of `embL2`.
4. The form operator `formOp P c` (`⟪formOp P c u, w⟫ = Σ⟪∂u,∂w⟫ - v(u,w) + c⟪u,w⟫₂`, with
   `v(u,w) = ⟪P u, w⟫`), the bounds `E:signed-form-bounds` under `E:signed-multiplier-form`,
   and the resolvent `resolventV` with its properties (`signed_closed_form_resolvent_paper`).
   A bounded real `V` (`potOp`) satisfies `E:signed-multiplier-form` with `k = sup |V|`.

Not formalized (named for the consumers): the self-adjoint operator `H_V` itself (no
`LinearPMap` construction; `H_V` is defined by its resolvent), `D(A^{1/2}) = H^1` and
`E:signed-form-domain`'s domain clause (K6a), `E:signed-quarter-phase` (K6b), the negative
dual completion `H^{-1/2}`, `L:signed-limiting-multiplier` (the existence of `V`), and the
decomposition of a complex `H^1` element into real and imaginary real-profile parts (needed to
turn `re_diag_split` into the equality of real and complex infima).
-/
public import Mathlib
public import StratonovichHAMSecondMoment.H1Mathlib

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Filter Topology FourierTransform
open scoped ENNReal InnerProductSpace ComplexConjugate BesselPotentialSpace Real

namespace StratonovichHAMSecondMoment.ResolventForm

/-! ### 1. Lax-Milgram over `RCLike` -/

section LaxMilgram

variable {𝕜 : Type*} [RCLike 𝕜] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [CompleteSpace V]

open InnerProductSpace RCLike LinearMap ContinuousLinearMap

open LinearMap (ker range)

local postfix:1024 "♯" => continuousLinearMapOfBilin (𝕜 := 𝕜)

/-- A bounded sesquilinear form `B` (conjugate-linear in the first slot) is coercive if
`C ‖u‖² ≤ re B(u,u)` for some `C > 0`. -/
def IsCoerciveSesq (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ u, C * ‖u‖ * ‖u‖ ≤ re (B u u)

namespace IsCoerciveSesq

variable {B : V →L⋆[𝕜] V →L[𝕜] 𝕜}

/-- Auxiliary to the Lean proof route: `C ‖v‖ ≤ ‖B♯ v‖`. -/
theorem bounded_below (h : IsCoerciveSesq B) : ∃ C, 0 < C ∧ ∀ v, C * ‖v‖ ≤ ‖B♯ v‖ := by
  rcases h with ⟨C, C_pos, coercivity⟩
  refine ⟨C, C_pos, fun v => ?_⟩
  by_cases hv : 0 < ‖v‖
  · refine (mul_le_mul_iff_left₀ hv).mp ?_
    calc C * ‖v‖ * ‖v‖ ≤ re (B v v) := coercivity v
      _ = re ⟪B♯ v, v⟫_𝕜 := by rw [continuousLinearMapOfBilin_apply]
      _ ≤ ‖⟪B♯ v, v⟫_𝕜‖ := re_le_norm _
      _ ≤ ‖B♯ v‖ * ‖v‖ := norm_inner_le_norm _ _
  · have : v = 0 := by simpa using hv
    simp [this]

/-- Auxiliary to the Lean proof route: `B♯` is antilipschitz. -/
theorem antilipschitz (h : IsCoerciveSesq B) : ∃ C : NNReal, 0 < C ∧ AntilipschitzWith C B♯ := by
  rcases h.bounded_below with ⟨C, C_pos, below_bound⟩
  refine ⟨C⁻¹.toNNReal, Real.toNNReal_pos.mpr (inv_pos.mpr C_pos), ?_⟩
  refine ContinuousLinearMap.antilipschitz_of_bound B♯ ?_
  simp_rw [Real.coe_toNNReal', max_eq_left_of_lt (inv_pos.mpr C_pos), ←
    inv_mul_le_iff₀ (inv_pos.mpr C_pos)]
  simpa using below_bound

/-- Auxiliary to the Lean proof route: `B♯` is injective. -/
theorem ker_eq_bot (h : IsCoerciveSesq B) : B♯.ker = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  rcases h.antilipschitz with ⟨_, _, hA⟩
  exact hA.injective

/-- Auxiliary to the Lean proof route: `B♯` has closed range. -/
theorem isClosed_range (h : IsCoerciveSesq B) : IsClosed (B♯.range : Set V) := by
  rcases h.antilipschitz with ⟨_, _, hA⟩
  exact hA.isClosed_range B♯.uniformContinuous

/-- Auxiliary to the Lean proof route: `B♯` is surjective. -/
theorem range_eq_top (h : IsCoerciveSesq B) : B♯.range = ⊤ := by
  have := h.isClosed_range.completeSpace_coe
  rw [← B♯.range.orthogonal_orthogonal, Submodule.eq_top_iff']
  intro v w hw
  rcases h with ⟨C, C_pos, coercivity⟩
  obtain rfl : w = 0 := by
    rw [← norm_eq_zero, ← mul_self_eq_zero, ← mul_right_inj' C_pos.ne', mul_zero, ← mul_assoc]
    apply le_antisymm
    · calc C * ‖w‖ * ‖w‖ ≤ re (B w w) := coercivity w
        _ = re ⟪B♯ w, w⟫_𝕜 := by rw [continuousLinearMapOfBilin_apply]
        _ = 0 := by rw [(hw _ ⟨w, rfl⟩ : ⟪B♯ w, w⟫_𝕜 = 0), map_zero]
    · positivity
  exact inner_zero_left _

/-- **Lax-Milgram over `RCLike`.** A coercive bounded sesquilinear form `B` on a Hilbert space
gives a continuous linear equivalence `E` with `⟪E v, w⟫ = B v w`. -/
def equiv (h : IsCoerciveSesq B) : V ≃L[𝕜] V :=
  ContinuousLinearEquiv.ofBijective B♯ h.ker_eq_bot h.range_eq_top

/-- The defining identity `⟪E v, w⟫ = B v w` of the Lax-Milgram equivalence. -/
theorem equiv_apply (h : IsCoerciveSesq B) (v w : V) : ⟪h.equiv v, w⟫_𝕜 = B v w :=
  continuousLinearMapOfBilin_apply B v w

/-- Uniqueness in Lax-Milgram: `⟪f, w⟫ = B v w` for all `w` forces `f = E v`. -/
theorem unique_equiv (h : IsCoerciveSesq B) {v f : V} (hf : ∀ w, ⟪f, w⟫_𝕜 = B v w) :
    f = h.equiv v :=
  unique_continuousLinearMapOfBilin B hf

end IsCoerciveSesq

/-- The sesquilinear form `(v, w) ↦ ⟪A v, w⟫` of a bounded operator `A`. -/
def sesqOf (A : V →L[𝕜] V) : V →L⋆[𝕜] V →L[𝕜] 𝕜 := (innerSL 𝕜 : V →L⋆[𝕜] V →L[𝕜] 𝕜).comp A

omit [CompleteSpace V] in
@[simp]
theorem sesqOf_apply (A : V →L[𝕜] V) (v w : V) : sesqOf A v w = ⟪A v, w⟫_𝕜 := by
  simp [sesqOf, innerSL_apply_apply]

/-- A form is Hermitian if `conj B(u,w) = B(w,u)`. -/
def IsHermitianForm (B : V →L⋆[𝕜] V →L[𝕜] 𝕜) : Prop := ∀ u w, conj (B u w) = B w u

/-- The form of a self-adjoint operator is Hermitian. -/
theorem isHermitianForm_sesqOf {A : V →L[𝕜] V} (hA : IsSelfAdjoint A) :
    IsHermitianForm (sesqOf A) := fun u w => by
  rw [sesqOf_apply, sesqOf_apply, inner_conj_symm]
  exact (hA.isSymmetric w u).symm

/-- **Real/complex reduction of the diagonal** (`L:signed-spectral-wave`, line 164).  For a
Hermitian form whose value `B(x,y)` is real, the diagonal at `x + i y` is the sum of the two
real diagonals. -/
theorem re_diag_split {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (B : W →L⋆[ℂ] W →L[ℂ] ℂ) (hH : IsHermitianForm B) (x y : W) (hxy : (B x y).im = 0) :
    (B (x + Complex.I • y) (x + Complex.I • y)).re = (B x x).re + (B y y).re := by
  have hr : conj (B x y) = B x y := Complex.conj_eq_iff_im.mpr hxy
  have hyx : B y x = B x y := by rw [← hH x y, hr]
  have e : B (x + Complex.I • y) (x + Complex.I • y) =
      B x x + B y y + Complex.I * (B x y - B y x) := by
    simp [Complex.conj_I]
    ring_nf
    simp only [Complex.I_sq]
    ring
  rw [e, hyx, sub_self, mul_zero, add_zero, Complex.add_re]

end LaxMilgram

/-! ### 2. The resolvent of a Hermitian coercive form -/

section Resolvent

variable {𝕜 : Type*} [RCLike 𝕜] {V L : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [CompleteSpace V] [NormedAddCommGroup L] [InnerProductSpace 𝕜 L] [CompleteSpace L]

open RCLike

variable {B : V →L⋆[𝕜] V →L[𝕜] 𝕜} (hB : IsCoerciveSesq B) (ι : V →L[𝕜] L)

/-- The operator `S = E⁻¹ ι* : L → V`; for Hermitian `B` it solves the weak problem
`B(w, S f) = ⟪ι w, f⟫` (`form_solOp`). -/
def solOp : L →L[𝕜] V := (hB.equiv.symm : V →L[𝕜] V) ∘L ι.adjoint

/-- The resolvent `R = ι ∘ S` on `L`. -/
def formResolvent : L →L[𝕜] L := ι ∘L solOp hB ι


/-- **Weak equation.** `B(w, S f) = ⟪ι w, f⟫` for every `w`. -/
theorem form_solOp (hH : IsHermitianForm B) (w : V) (f : L) :
    B w (solOp hB ι f) = ⟪ι w, f⟫_𝕜 := by
  have e : hB.equiv (solOp hB ι f) = ι.adjoint f := by simp [solOp]
  rw [← hH, ← hB.equiv_apply, e, ContinuousLinearMap.adjoint_inner_left, inner_conj_symm]

/-- **Uniqueness of the weak solution.** -/
theorem eq_solOp (hH : IsHermitianForm B) {u : V} {f : L} (hu : ∀ w, B w u = ⟪ι w, f⟫_𝕜) :
    u = solOp hB ι f := by
  have h1 : hB.equiv u = hB.equiv (solOp hB ι f) := by
    refine ext_inner_right 𝕜 fun w => ?_
    rw [hB.equiv_apply, hB.equiv_apply, ← hH, hu, ← hH, form_solOp hB ι hH]
  exact hB.equiv.injective h1

/-- `⟪R f, g⟫ = B(S f, S g)`. -/
theorem inner_resolvent (hH : IsHermitianForm B) (f g : L) :
    ⟪formResolvent hB ι f, g⟫_𝕜 = B (solOp hB ι f) (solOp hB ι g) :=
  (form_solOp hB ι hH _ _).symm

/-- The resolvent is self-adjoint. -/
theorem resolvent_isSelfAdjoint (hH : IsHermitianForm B) :
    IsSelfAdjoint (formResolvent hB ι) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  change ⟪formResolvent hB ι f, g⟫_𝕜 = ⟪f, formResolvent hB ι g⟫_𝕜
  rw [← inner_conj_symm f, inner_resolvent hB ι hH, inner_resolvent hB ι hH, hH]

/-- `‖R f‖² ≤ re ⟪R f, f⟫` when `‖ι u‖² ≤ re B(u,u)`. -/
theorem norm_sq_resolvent_le (hH : IsHermitianForm B) (hlow : ∀ u, ‖ι u‖ ^ 2 ≤ re (B u u))
    (f : L) : ‖formResolvent hB ι f‖ ^ 2 ≤ re ⟪formResolvent hB ι f, f⟫_𝕜 := by
  rw [inner_resolvent hB ι hH]; exact hlow _

/-- The resolvent is positive. -/
theorem resolvent_isPositive (hH : IsHermitianForm B) (hlow : ∀ u, ‖ι u‖ ^ 2 ≤ re (B u u)) :
    (formResolvent hB ι).IsPositive := by
  refine ContinuousLinearMap.isPositive_def'.mpr ⟨resolvent_isSelfAdjoint hB ι hH, fun f => ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf_apply]
  exact (sq_nonneg _).trans (norm_sq_resolvent_le hB ι hH hlow f)

/-- `‖R f‖ ≤ ‖f‖`. -/
theorem norm_resolvent_apply_le (hH : IsHermitianForm B) (hlow : ∀ u, ‖ι u‖ ^ 2 ≤ re (B u u))
    (f : L) : ‖formResolvent hB ι f‖ ≤ ‖f‖ := by
  have h1 := norm_sq_resolvent_le hB ι hH hlow f
  have h2 : re ⟪formResolvent hB ι f, f⟫_𝕜 ≤ ‖formResolvent hB ι f‖ * ‖f‖ :=
    (re_le_norm _).trans (norm_inner_le_norm _ _)
  rcases (norm_nonneg (formResolvent hB ι f)).eq_or_lt with h0 | hp
  · rw [← h0]; exact norm_nonneg _
  · nlinarith

/-- `‖R‖ ≤ 1`. -/
theorem norm_resolvent_le (hH : IsHermitianForm B) (hlow : ∀ u, ‖ι u‖ ^ 2 ≤ re (B u u)) :
    ‖formResolvent hB ι‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
    rw [one_mul]; exact norm_resolvent_apply_le hB ι hH hlow f

/-- The resolvent is injective when `(range ι)ᗮ = 0`. -/
theorem resolvent_injective (hH : IsHermitianForm B)
    (hsep : ∀ f : L, (∀ u, ⟪ι u, f⟫_𝕜 = 0) → f = 0) :
    Function.Injective (formResolvent hB ι) := by
  refine (injective_iff_map_eq_zero (formResolvent hB ι)).mpr fun f hf => ?_
  obtain ⟨C, hC, hcoer⟩ := id hB
  have h0 : re (B (solOp hB ι f) (solOp hB ι f)) = 0 := by
    rw [← inner_resolvent hB ι hH, hf, inner_zero_left, map_zero]
  have hs : solOp hB ι f = 0 := by
    by_contra hne
    have hp : 0 < ‖solOp hB ι f‖ := norm_pos_iff.mpr hne
    have := hcoer (solOp hB ι f)
    nlinarith [mul_pos (mul_pos hC hp) hp]
  exact hsep f fun u => by rw [← form_solOp hB ι hH, hs, map_zero]

end Resolvent

/-! ### 3. Multiplication operators on `L²(ℝ^d; ℂ)` -/

open HomogHypothesis (Rd)
open H1Mathlib WeakSobolev

local notation "L²[" d "]" => Lp ℂ 2 (volume : Measure (Rd d))

section Mul

variable {d : ℕ}

/-- Auxiliary to the Lean proof route: `a f ∈ L²` for bounded measurable `a`. -/
theorem memLp_mul (a : Rd d → ℝ) (ha : Measurable a) (M : ℝ) (hM : ∀ x, |a x| ≤ M)
    (f : L²[d]) : MemLp (fun x => (a x : ℂ) * f x) 2 volume :=
  (Lp.memLp f).of_le_mul ((Complex.measurable_ofReal.comp ha).aestronglyMeasurable.mul
    (Lp.aestronglyMeasurable f)) (Eventually.of_forall fun x => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _))

/-- Auxiliary to the Lean proof route: multiplication by `a` as a linear map on `L²`. -/
def mulLin (a : Rd d → ℝ) (ha : Measurable a) (M : ℝ) (hM : ∀ x, |a x| ≤ M) :
    L²[d] →ₗ[ℂ] L²[d] where
  toFun f := (memLp_mul a ha M hM f).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add]
    refine (MemLp.toLp_eq_toLp_iff _ _).2 ?_
    filter_upwards [Lp.coeFn_add f g] with x hx
    simp only [Pi.add_apply, hx, mul_add]
  map_smul' c f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine (MemLp.toLp_eq_toLp_iff _ _).2 ?_
    filter_upwards [Lp.coeFn_smul c f] with x hx
    simp only [Pi.smul_apply, hx, smul_eq_mul]
    ring

/-- Auxiliary to the Lean proof route: `mulLin` acts by `a` almost everywhere. -/
theorem mulLin_ae (a : Rd d → ℝ) (ha : Measurable a) (M : ℝ)
    (hM : ∀ x, |a x| ≤ M) (f : L²[d]) :
    (mulLin a ha M hM f : Rd d → ℂ) =ᵐ[volume] fun x => (a x : ℂ) * f x :=
  (memLp_mul a ha M hM f).coeFn_toLp

/-- Auxiliary to the Lean proof route: `‖a f‖ ≤ M ‖f‖`. -/
theorem norm_mulLin_le (a : Rd d → ℝ) (ha : Measurable a) (M : ℝ)
    (hM : ∀ x, |a x| ≤ M) (f : L²[d]) : ‖mulLin a ha M hM f‖ ≤ M * ‖f‖ :=
  Lp.norm_le_mul_norm_of_ae_le_mul (by
    filter_upwards [mulLin_ae a ha M hM f] with x hx
    rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _))

/-- Multiplication by a bounded measurable real function `a` (`|a| ≤ M`) on `L²(ℝ^d; ℂ)`. -/
def mulOp (a : Rd d → ℝ) (ha : Measurable a) (M : ℝ) (hM : ∀ x, |a x| ≤ M) :
    L²[d] →L[ℂ] L²[d] := (mulLin a ha M hM).mkContinuous M (norm_mulLin_le a ha M hM)

/-- `M_a f = a f` almost everywhere. -/
theorem mulOp_ae (a : Rd d → ℝ) (ha : Measurable a) (M : ℝ)
    (hM : ∀ x, |a x| ≤ M) (f : L²[d]) :
    (mulOp a ha M hM f : Rd d → ℂ) =ᵐ[volume] fun x => (a x : ℂ) * f x :=
  mulLin_ae a ha M hM f

/-- `‖M_a f‖ ≤ M ‖f‖`. -/
theorem norm_mulOp_le (a : Rd d → ℝ) (ha : Measurable a) (M : ℝ)
    (hM : ∀ x, |a x| ≤ M) (f : L²[d]) : ‖mulOp a ha M hM f‖ ≤ M * ‖f‖ :=
  norm_mulLin_le a ha M hM f

/-- Auxiliary to the Lean proof route: `x ↦ b(x) ‖f x‖²` is integrable for bounded `b`. -/
theorem integrable_mul_norm_sq {b : Rd d → ℝ} (hb : Measurable b) {N : ℝ}
    (hN : ∀ x, |b x| ≤ N) (f : L²[d]) : Integrable (fun x => b x * ‖f x‖ ^ 2) volume :=
  ((integrable_norm_sq f).const_mul N).mono'
    (hb.aestronglyMeasurable.mul (integrable_norm_sq f).aestronglyMeasurable)
    (Eventually.of_forall fun x => by
      rw [norm_mul, Real.norm_eq_abs, norm_pow, norm_norm]
      exact mul_le_mul_of_nonneg_right (hN x) (sq_nonneg _))


/-- `⟪M_a f, M_b f⟫ = ∫ a b ‖f‖²`. -/
theorem inner_mulOp_mulOp (a : Rd d → ℝ) (ha : Measurable a) (M : ℝ) (hM : ∀ x, |a x| ≤ M)
    (b : Rd d → ℝ) (hb : Measurable b) (N : ℝ) (hN : ∀ x, |b x| ≤ N) (f : L²[d]) :
    ⟪mulOp a ha M hM f, mulOp b hb N hN f⟫_ℂ = ((∫ x, a x * b x * ‖f x‖ ^ 2 : ℝ) : ℂ) := by
  rw [L2.inner_def, ← integral_complex_ofReal]
  refine integral_congr_ae ?_
  filter_upwards [mulOp_ae a ha M hM f, mulOp_ae b hb N hN f] with x h1 h2
  rw [h1, h2, RCLike.inner_apply', map_mul, Complex.conj_ofReal,
    show (a x : ℂ) * (starRingEnd ℂ) (f x) * ((b x : ℂ) * f x) =
      (a x : ℂ) * (b x) * ((starRingEnd ℂ) (f x) * f x) by ring, Complex.conj_mul']
  push_cast
  ring

/-- `‖M_a f‖² = ∫ a² ‖f‖²`. -/
theorem norm_mulOp_sq (a : Rd d → ℝ) (ha : Measurable a) (M : ℝ) (hM : ∀ x, |a x| ≤ M)
    (f : L²[d]) :
    ‖mulOp a ha M hM f‖ ^ 2 = ∫ x, a x ^ 2 * ‖f x‖ ^ 2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_mulOp_mulOp a ha M hM a ha M hM]
  simp only [RCLike.re_to_complex, Complex.ofReal_re]
  congr 1
  ext x
  ring

/-- `⟪M_a f, f⟫ = ∫ a ‖f‖²`. -/
theorem inner_mulOp_left (a : Rd d → ℝ) (ha : Measurable a) (M : ℝ) (hM : ∀ x, |a x| ≤ M)
    (f : L²[d]) : ⟪mulOp a ha M hM f, f⟫_ℂ = ((∫ x, a x * ‖f x‖ ^ 2 : ℝ) : ℂ) := by
  rw [L2.inner_def, ← integral_complex_ofReal]
  refine integral_congr_ae ?_
  filter_upwards [mulOp_ae a ha M hM f] with x h1
  rw [h1, RCLike.inner_apply', map_mul, Complex.conj_ofReal, mul_assoc, Complex.conj_mul']
  push_cast
  ring

/-- A real multiplication operator is symmetric: `⟪M_a f, g⟫ = ⟪f, M_a g⟫`. -/
theorem mulOp_isSelfAdjoint (a : Rd d → ℝ) (ha : Measurable a) (M : ℝ)
    (hM : ∀ x, |a x| ≤ M) : IsSelfAdjoint (mulOp a ha M hM) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  change ⟪mulOp a ha M hM f, g⟫_ℂ = ⟪f, mulOp a ha M hM g⟫_ℂ
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [mulOp_ae a ha M hM f, mulOp_ae a ha M hM g] with x hf hg
  rw [hf, hg, RCLike.inner_apply', RCLike.inner_apply', map_mul, Complex.conj_ofReal]
  ring

end Mul

/-! ### 4. Embedding and gradient on `H^1` -/

section H1Ops

variable {d : ℕ}

/-- The Fourier side of the Bessel representative, `u ↦ 𝓕 (u.toLp)`: an isometric
equivalence `H^{1}(ℝ^d) ≃ L²` (Mathlib's norm). -/
def fourierH1 : H^{1}(Rd d) ≃ₗᵢ[ℂ] L²[d] :=
  (BesselPotentialSpace.toLpₗᵢ (Rd d) ℂ 1 2).trans (Lp.fourierTransformₗᵢ (Rd d) ℂ)

theorem fourierH1_apply (u : H^{1}(Rd d)) : fourierH1 u = 𝓕 u.toLp := by
  rw [fourierH1, LinearIsometryEquiv.trans_apply, BesselPotentialSpace.toLpₗᵢ_apply]
  rfl

/-- The inverse Fourier transform on `L²` as a bounded operator. -/
def fourierInvL2 : L²[d] →L[ℂ] L²[d] :=
  ((Lp.fourierTransformₗᵢ (Rd d) ℂ).symm.toContinuousLinearEquiv : L²[d] →L[ℂ] L²[d])

theorem fourierInvL2_apply (g : L²[d]) : fourierInvL2 g = 𝓕⁻ g := rfl

/-- The weight `⟨ξ⟩⁻¹ = (1 + ‖ξ‖²)^{-1/2}`. -/
def jinv (ξ : Rd d) : ℝ := (1 + ‖ξ‖ ^ 2) ^ ((-1 : ℝ) / 2)

/-- The real Riesz symbol `ξ_j ⟨ξ⟩⁻¹`; `rieszSym j ξ = rz j ξ` (K5a). -/
def rz (j : Fin d) (ξ : Rd d) : ℝ := inner ℝ ξ (eb d j) * jinv ξ

theorem rieszSym_eq_rz (j : Fin d) (ξ : Rd d) : rieszSym j ξ = (rz j ξ : ℂ) := rfl

theorem measurable_jinv : Measurable (jinv (d := d)) := by unfold jinv; fun_prop

theorem measurable_rz (j : Fin d) : Measurable (rz j) := by unfold rz jinv; fun_prop

theorem jinv_pos (ξ : Rd d) : 0 < jinv ξ := Real.rpow_pos_of_pos (by positivity) _

theorem jinv_sq (ξ : Rd d) : jinv ξ ^ 2 = (1 + ‖ξ‖ ^ 2)⁻¹ := by
  rw [jinv, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num [Real.rpow_neg_one]

theorem abs_jinv_le (ξ : Rd d) : |jinv ξ| ≤ 1 := by
  rw [abs_of_pos (jinv_pos ξ)]
  refine (pow_le_one_iff_of_nonneg (jinv_pos ξ).le two_ne_zero).mp ?_
  rw [jinv_sq]; exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg ‖ξ‖])

theorem abs_rz_le (j : Fin d) (ξ : Rd d) : |rz j ξ| ≤ 1 := by
  have := norm_rieszSym_le j ξ
  rwa [rieszSym_eq_rz, Complex.norm_real, Real.norm_eq_abs] at this

/-- `⟨ξ⟩⁻¹ ⟨ξ⟩ = 1`. -/
theorem jinv_mul_bes (ξ : Rd d) : jinv ξ * (1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2) = 1 := by
  rw [jinv, ← Real.rpow_add (by positivity)]; norm_num

/-- `M_{⟨ξ⟩⁻¹}`. -/
def mulJ : L²[d] →L[ℂ] L²[d] := mulOp jinv measurable_jinv 1 abs_jinv_le

/-- `M_{ξ_j ⟨ξ⟩⁻¹}`. -/
def mulR (j : Fin d) : L²[d] →L[ℂ] L²[d] := mulOp (rz j) (measurable_rz j) 1 (abs_rz_le j)

/-- The embedding `ι : H^1 → L²`, `ι u = 𝓕⁻ (⟨ξ⟩⁻¹ 𝓕 (u.toLp))` (the `L²` function `u`). -/
def embL2 : H^{1}(Rd d) →L[ℂ] L²[d] :=
  fourierInvL2 ∘L mulJ ∘L (fourierH1 (d := d)).toContinuousLinearEquiv.toContinuousLinearMap

/-- The gradient component `∂_j u = 2πi · 𝓕⁻ (ξ_j ⟨ξ⟩⁻¹ 𝓕 (u.toLp))`. -/
def gradOp (j : Fin d) : H^{1}(Rd d) →L[ℂ] L²[d] :=
  (2 * π * Complex.I) •
    (fourierInvL2 ∘L mulR j ∘L (fourierH1 (d := d)).toContinuousLinearEquiv.toContinuousLinearMap)

theorem fourier_embL2 (u : H^{1}(Rd d)) : 𝓕 (embL2 u) = mulJ (fourierH1 u) := by
  rw [embL2, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, fourierInvL2_apply,
    fourier_fourierInv_eq]
  rfl

theorem fourier_gradOp (j : Fin d) (u : H^{1}(Rd d)) :
    𝓕 (gradOp j u) = (2 * π * Complex.I) • mulR j (fourierH1 u) := by
  change 𝓕 ((2 * π * Complex.I) • fourierInvL2 (mulR j (fourierH1 u))) = _
  rw [fourier_smul, fourierInvL2_apply, fourier_fourierInv_eq]

/-- `‖ι u‖² = ∫ ⟨ξ⟩⁻² |𝓕 u.toLp|²`. -/
theorem norm_embL2_sq (u : H^{1}(Rd d)) :
    ‖embL2 u‖ ^ 2 = ∫ x, jinv x ^ 2 * ‖fourierH1 u x‖ ^ 2 := by
  rw [← Lp.norm_fourier_eq, fourier_embL2, mulJ, norm_mulOp_sq]

/-- `‖∂_j u‖² = (2π)² ∫ (ξ_j ⟨ξ⟩⁻¹)² |𝓕 u.toLp|²`. -/
theorem norm_gradOp_sq (j : Fin d) (u : H^{1}(Rd d)) :
    ‖gradOp j u‖ ^ 2 = (2 * π) ^ 2 * ∫ x, rz j x ^ 2 * ‖fourierH1 u x‖ ^ 2 := by
  rw [← Lp.norm_fourier_eq, fourier_gradOp, norm_smul, mul_pow, mulR, norm_mulOp_sq]
  congr 1
  simp [Complex.norm_I, abs_of_pos Real.pi_pos]

/-- The manuscript norm squared `z² = ‖u‖₂² + Σ_j ‖∂_j u‖₂²` (no `2π`). -/
def msNormSq (u : H^{1}(Rd d)) : ℝ := ‖embL2 u‖ ^ 2 + ∑ j, ‖gradOp j u‖ ^ 2

/-- The Fourier weight of `z²`: `(1 + 4π² ‖ξ‖²)/(1 + ‖ξ‖²)`. -/
def msWeight (ξ : Rd d) : ℝ := (1 + (2 * π) ^ 2 * ‖ξ‖ ^ 2) / (1 + ‖ξ‖ ^ 2)

theorem msWeight_eq (ξ : Rd d) :
    msWeight ξ = jinv ξ ^ 2 + ∑ j, (2 * π) ^ 2 * rz j ξ ^ 2 := by
  have e : ∀ j, rz j ξ ^ 2 = inner ℝ ξ (eb d j) ^ 2 * (1 + ‖ξ‖ ^ 2)⁻¹ := fun j => by
    rw [rz, mul_pow, jinv_sq]
  simp only [e, ← Finset.mul_sum, ← Finset.sum_mul, sum_sq_coord, jinv_sq, msWeight]
  rw [div_eq_mul_inv]
  ring

/-- `z² = ∫ msWeight |𝓕 u.toLp|²`. -/
theorem msNormSq_eq_integral (u : H^{1}(Rd d)) :
    msNormSq u = ∫ x, msWeight x * ‖fourierH1 u x‖ ^ 2 := by
  have hi : ∀ j ∈ Finset.univ, Integrable (fun x => (2 * π) ^ 2 *
      (rz j x ^ 2 * ‖fourierH1 u x‖ ^ 2)) volume := fun j _ =>
    (integrable_mul_norm_sq ((measurable_rz j).pow_const 2) (N := 1) (fun x => by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_one_iff_abs_le_one _).mpr (abs_rz_le j x)) _).const_mul _
  have h0 : Integrable (fun x => jinv x ^ 2 * ‖fourierH1 u x‖ ^ 2) volume :=
    integrable_mul_norm_sq (measurable_jinv.pow_const 2) (N := 1) (fun x => by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_one_iff_abs_le_one _).mpr (abs_jinv_le x)) _
  simp only [msNormSq, norm_embL2_sq, norm_gradOp_sq, ← integral_const_mul]
  rw [← integral_finsetSum _ hi, ← integral_add h0 (integrable_finsetSum _ hi)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [msWeight_eq, add_mul, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => by ring

/-- **Norm comparison.** `‖u‖² ≤ z² ≤ (2π)² ‖u‖²` (Mathlib's norm against the manuscript's). -/
theorem norm_sq_le_msNormSq (u : H^{1}(Rd d)) :
    ‖u‖ ^ 2 ≤ msNormSq u ∧ msNormSq u ≤ (2 * π) ^ 2 * ‖u‖ ^ 2 := by
  have hn : ‖u‖ ^ 2 = ∫ x, ‖fourierH1 u x‖ ^ 2 := by
    rw [← norm_sq_eq_integral, LinearIsometryEquiv.norm_map]
  have hpi : (1 : ℝ) ≤ (2 * π) ^ 2 := by nlinarith [Real.pi_gt_three]
  have hw : ∀ x : Rd d, 1 ≤ msWeight x ∧ msWeight x ≤ (2 * π) ^ 2 := fun x => by
    have hp : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
    rw [msWeight, le_div_iff₀ hp, div_le_iff₀ hp]
    constructor <;> nlinarith [sq_nonneg ‖x‖]
  have hm : Measurable (msWeight (d := d)) := by unfold msWeight; fun_prop
  have hb : ∀ x : Rd d, |msWeight x| ≤ (2 * π) ^ 2 := fun x => by
    rw [abs_of_nonneg (zero_le_one.trans (hw x).1)]; exact (hw x).2
  have hI := integrable_mul_norm_sq hm hb (fourierH1 u)
  rw [msNormSq_eq_integral, hn, ← integral_const_mul]
  constructor
  · exact integral_mono (integrable_norm_sq _) hI fun x =>
      le_mul_of_one_le_left (sq_nonneg _) (hw x).1
  · exact integral_mono hI ((integrable_norm_sq _).const_mul _) fun x =>
      mul_le_mul_of_nonneg_right (hw x).2 (sq_nonneg _)

/-- The manuscript `H^{1/2}` norm squared, `∫ (1 + 4π²|ξ|²)^{1/2} |𝓕 (ι u)(ξ)|²`. -/
def h12NormSq (u : H^{1}(Rd d)) : ℝ :=
  ∫ x, Real.sqrt (1 + (2 * π) ^ 2 * ‖x‖ ^ 2) * ‖(𝓕 (embL2 u) : L²[d]) x‖ ^ 2

/-- The manuscript `H^{1/2}` norm. -/
def h12Norm (u : H^{1}(Rd d)) : ℝ := Real.sqrt (h12NormSq u)

/-- The weight `(1 + 4π²|ξ|²)^{1/2} ⟨ξ⟩⁻¹`, bounded by `2π`. -/
def om (ξ : Rd d) : ℝ := Real.sqrt (1 + (2 * π) ^ 2 * ‖ξ‖ ^ 2) * jinv ξ

theorem om_sq (ξ : Rd d) : om ξ ^ 2 = msWeight ξ := by
  rw [om, mul_pow, Real.sq_sqrt (by positivity), jinv_sq, msWeight, div_eq_mul_inv]

theorem abs_om_le (ξ : Rd d) : |om ξ| ≤ 2 * π := by
  have h1 : 0 ≤ om ξ := mul_nonneg (Real.sqrt_nonneg _) (jinv_pos ξ).le
  rw [abs_of_nonneg h1]
  refine (pow_le_pow_iff_left₀ h1 (by positivity) two_ne_zero).mp ?_
  have hp : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
  rw [om_sq, msWeight, div_le_iff₀ hp]
  nlinarith [sq_nonneg ‖ξ‖, Real.pi_gt_three]

theorem measurable_om : Measurable (om (d := d)) := by unfold om jinv; fun_prop

/-- `‖u‖²_{H^{1/2}} = ⟪M_{om} 𝓕u, M_{⟨ξ⟩⁻¹} 𝓕u⟫`. -/
theorem h12NormSq_eq (u : H^{1}(Rd d)) :
    (h12NormSq u : ℂ) =
      ⟪mulOp om measurable_om (2 * π) abs_om_le (fourierH1 u), mulJ (fourierH1 u)⟫_ℂ := by
  rw [mulJ, inner_mulOp_mulOp, h12NormSq]
  congr 1
  refine integral_congr_ae ?_
  rw [fourier_embL2, mulJ]
  filter_upwards [mulOp_ae jinv measurable_jinv 1 abs_jinv_le (fourierH1 u)] with x hx
  rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (jinv_pos x), om]
  ring

theorem h12NormSq_nonneg (u : H^{1}(Rd d)) : 0 ≤ h12NormSq u :=
  integral_nonneg fun _ => mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)

/-- **Fourier Cauchy-Schwarz** (`P:signed-closed-form`, line 80): `‖u‖²_{H^{1/2}} ≤ b z`. -/
theorem h12NormSq_le (u : H^{1}(Rd d)) :
    h12NormSq u ≤ ‖embL2 u‖ * Real.sqrt (msNormSq u) := by
  have e1 : ‖mulOp om measurable_om (2 * π) abs_om_le (fourierH1 u)‖ = Real.sqrt (msNormSq u) := by
    rw [← Real.sqrt_sq (norm_nonneg _), norm_mulOp_sq, msNormSq_eq_integral]
    simp only [om_sq]
  have e2 : ‖mulJ (fourierH1 u)‖ = ‖embL2 u‖ := by
    rw [← fourier_embL2, Lp.norm_fourier_eq]
  have h := congrArg Complex.re (h12NormSq_eq u)
  rw [Complex.ofReal_re] at h
  rw [h]
  calc _ ≤ ‖⟪mulOp om measurable_om (2 * π) abs_om_le (fourierH1 u), mulJ (fourierH1 u)⟫_ℂ‖ :=
        Complex.re_le_norm _
    _ ≤ ‖mulOp om measurable_om (2 * π) abs_om_le (fourierH1 u)‖ * ‖mulJ (fourierH1 u)‖ :=
        norm_inner_le_norm _ _
    _ = _ := by rw [e1, e2]; ring

/-- `‖u‖²_{H^{1/2}} = ∫ om ⟨ξ⟩⁻¹ |𝓕 u.toLp|²`. -/
theorem h12NormSq_eq_integral (u : H^{1}(Rd d)) :
    h12NormSq u = ∫ x, om x * jinv x * ‖fourierH1 u x‖ ^ 2 := by
  have h := congrArg Complex.re (h12NormSq_eq u)
  rwa [Complex.ofReal_re, mulJ, inner_mulOp_mulOp, Complex.ofReal_re] at h

/-- `‖u‖₂² ≤ ‖u‖²_{H^{1/2}}`. -/
theorem norm_embL2_sq_le_h12 (u : H^{1}(Rd d)) : ‖embL2 u‖ ^ 2 ≤ h12NormSq u := by
  rw [norm_embL2_sq, h12NormSq_eq_integral]
  have hb : ∀ x : Rd d, |jinv x ^ 2| ≤ 1 := fun x => by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_one_iff_abs_le_one _).mpr (abs_jinv_le x)
  have hb' : ∀ x : Rd d, |om x * jinv x| ≤ 2 * π := fun x => by
    rw [abs_mul]
    exact (mul_le_mul (abs_om_le x) (abs_jinv_le x) (abs_nonneg _) (by positivity)).trans
      (le_of_eq (mul_one _))
  refine integral_mono (integrable_mul_norm_sq (measurable_jinv.pow_const 2) hb _)
    (integrable_mul_norm_sq (measurable_om.mul measurable_jinv) hb' _) fun x => ?_
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  rw [sq, om]
  refine mul_le_mul_of_nonneg_right ?_ (jinv_pos x).le
  exact le_mul_of_one_le_left (jinv_pos x).le
    (Real.one_le_sqrt.mpr (le_add_of_nonneg_right (by positivity)))

end H1Ops

/-! ### 5. Real profiles, real cross terms and dense range -/

section Profiles

variable {d : ℕ}

/-- **Real profiles: the embedding.** For a real `f ∈ H^1`, `ι (toH1 h)` is `f` (complexified). -/
theorem embL2_toH1 {f : Rd d → ℝ} (h : MemH1 f) : embL2 (toH1 h) = toL2C h.1 := by
  apply (Lp.fourierTransformₗᵢ (Rd d) ℂ).injective
  change 𝓕 (embL2 (toH1 h)) = 𝓕 (toL2C h.1)
  rw [fourier_embL2, fourierH1_apply, mulJ]
  have hB := (toH1 h).bessel_toDistr_eq_toLp
  rw [toH1_toDistr] at hB
  refine Lp.ext ?_
  filter_upwards [mulOp_ae jinv measurable_jinv 1 abs_jinv_le (𝓕 (toH1 h).toLp),
    fourier_bessel_ae h.1 _ hB] with x h1 h2
  have e : (jinv x : ℂ) * (1 * besSym d 1 x) = 1 := by
    rw [one_mul, besSym, ← Complex.ofReal_mul, jinv_mul_bes, Complex.ofReal_one]
  rw [h1, h2, ← mul_assoc, e, one_mul]

/-- **Real profiles: the gradient.** For a real `f ∈ H^1` with weak gradient `g`,
`∂_j (toH1 h) = ⟪g, e_j⟫` (complexified). -/
theorem gradOp_toH1 {f : Rd d → ℝ} (h : MemH1 f) {g : Rd d → Rd d} (hg : MemLp g 2 volume)
    (hw : HasWeakGradient f g) (j : Fin d) :
    gradOp j (toH1 h) = toL2C (memLp_inner hg (eb d j)) := by
  apply (Lp.fourierTransformₗᵢ (Rd d) ℂ).injective
  change 𝓕 (gradOp j (toH1 h)) = 𝓕 (toL2C (memLp_inner hg (eb d j)))
  rw [fourier_gradOp, fourierH1_apply, mulR]
  have hB := (toH1 h).bessel_toDistr_eq_toLp
  rw [toH1_toDistr] at hB
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_smul (2 * π * Complex.I : ℂ)
      (mulOp (rz j) (measurable_rz j) 1 (abs_rz_le j) (𝓕 (toH1 h).toLp)),
    mulOp_ae (rz j) (measurable_rz j) 1 (abs_rz_le j) (𝓕 (toH1 h).toLp),
    fourier_bessel_ae h.1 _ hB, fourier_grad_ae h.1 hg hw j] with x h0 h1 h2 h3
  have e : (rz j x : ℂ) * (1 * besSym d 1 x) = coordSym j x := by
    rw [one_mul, besSym, coordSym, rz, ← Complex.ofReal_mul, mul_assoc, jinv_mul_bes, mul_one]
  rw [h0, Pi.smul_apply, h1, h2, h3, smul_eq_mul, ← e]
  ring

/-- On real profiles the manuscript norm is K5a's `manuscriptH1NormSq`: `z² = ∫ f² + ∫ ‖g‖²`. -/
theorem msNormSq_toH1 {f : Rd d → ℝ} (h : MemH1 f) {g : Rd d → Rd d} (hg : MemLp g 2 volume)
    (hw : HasWeakGradient f g) : msNormSq (toH1 h) = manuscriptH1NormSq f g := by
  simp only [msNormSq, embL2_toH1, gradOp_toH1 h hg hw, norm_toL2C_sq, manuscriptH1NormSq]
  congr 1
  rw [← integral_finsetSum _ fun j _ => (memLp_inner hg (eb d j)).integrable_sq]
  congr 1
  funext x
  rw [sum_sq_coord]

/-- The inner product of two almost everywhere real `L²` functions is real. -/
theorem im_inner_eq_zero {F G : L²[d]} (hF : ∀ᵐ x ∂volume, (F x).im = 0)
    (hG : ∀ᵐ x ∂volume, (G x).im = 0) : (⟪F, G⟫_ℂ).im = 0 := by
  have hi := integral_im (𝕜 := ℂ) (L2.integrable_inner (𝕜 := ℂ) F G)
  simp only [RCLike.im_to_complex] at hi
  rw [L2.inner_def, ← hi]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hF, hG] with x h1 h2
  simp [Complex.mul_im, h1, h2]

/-- Auxiliary: `toL2C hf` is almost everywhere real. -/
theorem toL2C_im {f : Rd d → ℝ} (hf : MemLp f 2 volume) :
    ∀ᵐ x ∂volume, ((toL2C hf : L²[d]) x).im = 0 := by
  filter_upwards [coeFn_toL2C hf] with x hx
  rw [hx, Complex.ofReal_im]

/-- **Dense range of `ι`**: an `L²` element orthogonal to `ι(H^1)` vanishes. -/
theorem embL2_sep (F : L²[d]) (hF : ∀ u, ⟪embL2 u, F⟫_ℂ = 0) : F = 0 := by
  have hu := hF (fourierH1.symm (𝓕 F))
  rw [← Lp.inner_fourier_eq, fourier_embL2, LinearIsometryEquiv.apply_symm_apply, mulJ,
    inner_mulOp_left, Complex.ofReal_eq_zero] at hu
  have hI := integrable_mul_norm_sq measurable_jinv abs_jinv_le (𝓕 F)
  have hae := (integral_eq_zero_iff_of_nonneg
    (fun x => mul_nonneg (jinv_pos x).le (sq_nonneg _)) hI).mp hu
  have hG : ‖(𝓕 F : L²[d])‖ ^ 2 = 0 := by
    rw [norm_sq_eq_integral]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hae] with x hx
    simp only [Pi.zero_apply] at hx ⊢
    rcases mul_eq_zero.mp hx with h | h
    · exact absurd h (jinv_pos x).ne'
    · exact h
  have h0 : (𝓕 F : L²[d]) = 0 := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hG)
  exact (Lp.fourierTransformₗᵢ (Rd d) ℂ).map_eq_zero_iff.mp h0

end Profiles

/-! ### 6. The form operator, the form bounds and the resolvent -/

section Form

variable {d : ℕ}

/-- Auxiliary: the operator `Σ_j ∂_j* ∂_j` of the gradient energy. -/
def gradForm : H^{1}(Rd d) →L[ℂ] H^{1}(Rd d) := ∑ j, (gradOp j).adjoint ∘L gradOp j

/-- Auxiliary: the operator `ι* ι` of the `L²` energy. -/
def embForm : H^{1}(Rd d) →L[ℂ] H^{1}(Rd d) := (embL2 (d := d)).adjoint ∘L embL2

/-- The operator of the shifted form `q_V + c`:
`⟪formOp P c u, w⟫ = Σ_j ⟪∂_j u, ∂_j w⟫ - v_V(u,w) + c ⟪u, w⟫₂`, with the potential pairing
`v_V(u,w) = ⟪P u, w⟫` given by a bounded operator `P` on `H^1`. -/
def formOp (P : H^{1}(Rd d) →L[ℂ] H^{1}(Rd d)) (c : ℝ) : H^{1}(Rd d) →L[ℂ] H^{1}(Rd d) :=
  gradForm - P + (c : ℂ) • embForm

theorem inner_formOp (P : H^{1}(Rd d) →L[ℂ] H^{1}(Rd d)) (c : ℝ) (u w : H^{1}(Rd d)) :
    ⟪formOp P c u, w⟫_ℂ = (∑ j, ⟪gradOp j u, gradOp j w⟫_ℂ) - ⟪P u, w⟫_ℂ +
      (c : ℂ) * ⟪embL2 u, embL2 w⟫_ℂ := by
  have e : formOp P c u = gradForm u - P u + (c : ℂ) • embForm u := rfl
  rw [e, inner_add_left, inner_sub_left, inner_smul_left, Complex.conj_ofReal]
  simp [gradForm, embForm, sum_inner, ContinuousLinearMap.adjoint_inner_left]

/-- `re ⟪formOp P c u, u⟫ = Σ_j ‖∂_j u‖² - re v_V(u,u) + c ‖u‖₂²`. -/
theorem re_inner_formOp_self (P : H^{1}(Rd d) →L[ℂ] H^{1}(Rd d)) (c : ℝ) (u : H^{1}(Rd d)) :
    (⟪formOp P c u, u⟫_ℂ).re =
      (∑ j, ‖gradOp j u‖ ^ 2) - (⟪P u, u⟫_ℂ).re + c * ‖embL2 u‖ ^ 2 := by
  have hn : ∀ v : L²[d], (⟪v, v⟫_ℂ).re = ‖v‖ ^ 2 := fun v => by
    rw [← RCLike.re_to_complex]; exact inner_self_eq_norm_sq v
  rw [inner_formOp, Complex.add_re, Complex.sub_re, Complex.re_sum, Complex.re_ofReal_mul, hn]
  simp only [hn]

/-- `formOp P c` is self-adjoint when `P` is: its form is Hermitian. -/
theorem isHermitianForm_formOp {P : H^{1}(Rd d) →L[ℂ] H^{1}(Rd d)} (hP : IsSelfAdjoint P)
    (c : ℝ) : IsHermitianForm (sesqOf (formOp P c)) := fun u w => by
  have hs : ⟪P w, u⟫_ℂ = ⟪w, P u⟫_ℂ := hP.isSymmetric w u
  simp only [sesqOf_apply, inner_formOp, map_add, map_sub, map_sum, map_mul,
    Complex.conj_ofReal, inner_conj_symm, hs]

/-- **The hypothesis `E:signed-multiplier-form`** of `L:signed-limiting-multiplier`
(`notes/integrated_signed_static.tex`, lines 16-18): `|v_V(u,w)| ≤ k ‖u‖_{H^{1/2}} ‖w‖_{H^{1/2}}`
for the potential pairing `v_V(u,w) = ⟪P u, w⟫`.  A hypothesis of `P:signed-closed-form`
carried here; the lemma that supplies it for the limiting multipliers is not formalized. -/
def SignedMultiplierForm (P : H^{1}(Rd d) →L[ℂ] H^{1}(Rd d)) (k : ℝ) : Prop :=
  ∀ u w, ‖⟪P u, w⟫_ℂ‖ ≤ k * h12Norm u * h12Norm w

/-- `|Re v_V(u,u)| ≤ K b z` (`P:signed-closed-form`, line 81, for the real part). -/
theorem abs_re_pot_le {P : H^{1}(Rd d) →L[ℂ] H^{1}(Rd d)} {k K : ℝ}
    (hk : SignedMultiplierForm P k) (hkK : k ≤ K) (hK : 1 ≤ K) (u : H^{1}(Rd d)) :
    |(⟪P u, u⟫_ℂ).re| ≤ K * (‖embL2 u‖ * Real.sqrt (msNormSq u)) := by
  have hh : h12Norm u * h12Norm u = h12NormSq u := Real.mul_self_sqrt (h12NormSq_nonneg u)
  calc |(⟪P u, u⟫_ℂ).re| ≤ ‖⟪P u, u⟫_ℂ‖ := Complex.abs_re_le_norm _
    _ ≤ k * h12Norm u * h12Norm u := hk u u
    _ = k * h12NormSq u := by rw [mul_assoc, hh]
    _ ≤ K * h12NormSq u := mul_le_mul_of_nonneg_right hkK (h12NormSq_nonneg u)
    _ ≤ _ := mul_le_mul_of_nonneg_left (h12NormSq_le u) (by linarith)

/-- **`E:signed-form-bounds`** (`P:signed-closed-form`, lines 58-59 and 83-89).  With
`c = 2 + K²` and `L_K = 3(1 + K²)`:
`z²/2 + (1 + K²/2) b² ≤ q_V(u) + c b² ≤ L_K z²`, where `q_V(u) + c b² = re ⟪formOp P c u, u⟫`,
`b = ‖u‖₂` and `z² = msNormSq u`. -/
theorem signed_form_bounds {P : H^{1}(Rd d) →L[ℂ] H^{1}(Rd d)} {k K : ℝ}
    (hk : SignedMultiplierForm P k) (hkK : k ≤ K) (hK : 1 ≤ K) (u : H^{1}(Rd d)) :
    1 / 2 * msNormSq u + (1 + K ^ 2 / 2) * ‖embL2 u‖ ^ 2 ≤
        (⟪formOp P (2 + K ^ 2) u, u⟫_ℂ).re ∧
      (⟪formOp P (2 + K ^ 2) u, u⟫_ℂ).re ≤ 3 * (1 + K ^ 2) * msNormSq u := by
  have hv := abs_re_pot_le hk hkK hK u
  set b := ‖embL2 u‖
  set G := ∑ j, ‖gradOp j u‖ ^ 2
  have hG : 0 ≤ G := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hz2 : msNormSq u = b ^ 2 + G := rfl
  set z := Real.sqrt (msNormSq u)
  have hz0 : 0 ≤ z := Real.sqrt_nonneg _
  have hzz : z ^ 2 = msNormSq u := Real.sq_sqrt (by rw [hz2]; positivity)
  have hb0 : 0 ≤ b := norm_nonneg _
  have hamgm : K * (b * z) ≤ z ^ 2 / 2 + K ^ 2 * b ^ 2 / 2 := by nlinarith [sq_nonneg (z - K * b)]
  have hbz : b ^ 2 ≤ msNormSq u := by rw [hz2]; linarith
  have hKb : K ^ 2 * b ^ 2 ≤ K ^ 2 * msNormSq u := mul_le_mul_of_nonneg_left hbz (sq_nonneg K)
  have hre := re_inner_formOp_self P (2 + K ^ 2) u
  have habs := abs_le.mp hv
  constructor
  · rw [hre]; nlinarith
  · rw [hre]; nlinarith

/-- The form `q_V + c` is coercive on `H^1` (Mathlib's norm, constant `1/2`). -/
theorem coercive_formOp {P : H^{1}(Rd d) →L[ℂ] H^{1}(Rd d)} {k K : ℝ}
    (hk : SignedMultiplierForm P k) (hkK : k ≤ K) (hK : 1 ≤ K) :
    IsCoerciveSesq (sesqOf (formOp P (2 + K ^ 2))) := by
  refine ⟨1 / 2, by norm_num, fun u => ?_⟩
  rw [sesqOf_apply, RCLike.re_to_complex]
  have h1 := (signed_form_bounds hk hkK hK u).1
  have h2 := (norm_sq_le_msNormSq u).1
  have h3 : 0 ≤ (1 + K ^ 2 / 2) * ‖embL2 u‖ ^ 2 := by positivity
  nlinarith

/-- `‖u‖₂² ≤ q_V(u) + c ‖u‖₂²` (the form version of `A ≥ 1`, `E:signed-form-domain`). -/
theorem norm_embL2_sq_le_form {P : H^{1}(Rd d) →L[ℂ] H^{1}(Rd d)} {k K : ℝ}
    (hk : SignedMultiplierForm P k) (hkK : k ≤ K) (hK : 1 ≤ K) (u : H^{1}(Rd d)) :
    ‖embL2 u‖ ^ 2 ≤ RCLike.re (sesqOf (formOp P (2 + K ^ 2)) u u) := by
  rw [sesqOf_apply, RCLike.re_to_complex]
  have h1 := (signed_form_bounds hk hkK hK u).1
  have h2 : 0 ≤ msNormSq u := by
    unfold msNormSq; positivity
  nlinarith [sq_nonneg K, sq_nonneg ‖embL2 u‖]

/-- The operator `S_V` built by `solOp`; for self-adjoint `P` it is the solution operator
`f ↦ u` of `(H_V + c) u = f` in weak form (`resolventV_spec`). -/
def solV {P : H^{1}(Rd d) →L[ℂ] H^{1}(Rd d)} {k K : ℝ} (hk : SignedMultiplierForm P k)
    (hkK : k ≤ K) (hK : 1 ≤ K) : L²[d] →L[ℂ] H^{1}(Rd d) :=
  solOp (coercive_formOp hk hkK hK) embL2

/-- The bounded resolvent `R_V = (H_V + c)⁻¹` on `L²`, `c = 2 + K²`, defined through the form. -/
def resolventV {P : H^{1}(Rd d) →L[ℂ] H^{1}(Rd d)} {k K : ℝ} (hk : SignedMultiplierForm P k)
    (hkK : k ≤ K) (hK : 1 ≤ K) : L²[d] →L[ℂ] L²[d] :=
  formResolvent (coercive_formOp hk hkK hK) embL2

/-- **The resolvent of the signed form.**  Under `E:signed-multiplier-form` with `k ≤ K`,
`1 ≤ K` and Hermitian `v_V`, the resolvent `R_V = ι S_V` satisfies:
1. the weak equation `⟪(q_V + c)(w, S_V f)⟫ = ⟪ι w, f⟫` for all `w ∈ H^1`, with uniqueness;
2. `R_V` is self-adjoint and positive;
3. `‖R_V‖ ≤ 1`;
4. `R_V` is injective. -/
theorem resolventV_spec {P : H^{1}(Rd d) →L[ℂ] H^{1}(Rd d)} (hP : IsSelfAdjoint P) {k K : ℝ}
    (hk : SignedMultiplierForm P k) (hkK : k ≤ K) (hK : 1 ≤ K) :
    (∀ f w, ⟪formOp P (2 + K ^ 2) w, solV hk hkK hK f⟫_ℂ = ⟪embL2 w, f⟫_ℂ) ∧
    (∀ (f : L²[d]) (u : H^{1}(Rd d)),
      (∀ w, ⟪formOp P (2 + K ^ 2) w, u⟫_ℂ = ⟪embL2 w, f⟫_ℂ) → u = solV hk hkK hK f) ∧
    (∀ f, resolventV hk hkK hK f = embL2 (solV hk hkK hK f)) ∧
    IsSelfAdjoint (resolventV hk hkK hK) ∧ (resolventV hk hkK hK).IsPositive ∧
    ‖resolventV hk hkK hK‖ ≤ 1 ∧ Function.Injective (resolventV hk hkK hK) := by
  have hH := isHermitianForm_formOp hP (2 + K ^ 2)
  have hcoer := coercive_formOp hk hkK hK
  have hlow := norm_embL2_sq_le_form hk hkK hK
  refine ⟨fun f w => ?_, fun f u hu => ?_, fun f => rfl, resolvent_isSelfAdjoint hcoer _ hH,
    resolvent_isPositive hcoer _ hH hlow, norm_resolvent_le hcoer _ hH hlow,
    resolvent_injective hcoer _ hH embL2_sep⟩
  · have := form_solOp hcoer embL2 hH w f
    rwa [sesqOf_apply] at this
  · exact eq_solOp hcoer embL2 hH fun w => by rw [sesqOf_apply]; exact hu w

/-- The potential pairing of a bounded real potential `V` (`|V| ≤ M`): `⟪ι* M_V ι u, w⟫`. -/
def potOp (V : Rd d → ℝ) (hV : Measurable V) (M : ℝ) (hM : ∀ x, |V x| ≤ M) :
    H^{1}(Rd d) →L[ℂ] H^{1}(Rd d) :=
  (embL2 (d := d)).adjoint ∘L mulOp V hV M hM ∘L embL2

theorem inner_potOp (V : Rd d → ℝ) (hV : Measurable V) (M : ℝ) (hM : ∀ x, |V x| ≤ M)
    (u w : H^{1}(Rd d)) : ⟪potOp V hV M hM u, w⟫_ℂ = ⟪mulOp V hV M hM (embL2 u), embL2 w⟫_ℂ := by
  simp [potOp, ContinuousLinearMap.adjoint_inner_left]

/-- A bounded real potential gives a Hermitian pairing. -/
theorem potOp_isSelfAdjoint (V : Rd d → ℝ) (hV : Measurable V) (M : ℝ) (hM : ∀ x, |V x| ≤ M) :
    IsSelfAdjoint (potOp V hV M hM) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro u w
  change ⟪potOp V hV M hM u, w⟫_ℂ = ⟪u, potOp V hV M hM w⟫_ℂ
  rw [inner_potOp, ← inner_conj_symm u, inner_potOp, inner_conj_symm]
  exact (mulOp_isSelfAdjoint V hV M hM).isSymmetric _ _

/-- A bounded real potential satisfies `E:signed-multiplier-form` with `k = M`. -/
theorem potOp_signedMultiplierForm (V : Rd d → ℝ) (hV : Measurable V) (M : ℝ)
    (hM : ∀ x, |V x| ≤ M) : SignedMultiplierForm (potOp V hV M hM) M := fun u w => by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hl : ∀ v : H^{1}(Rd d), ‖embL2 v‖ ≤ h12Norm v := fun v =>
    Real.le_sqrt_of_sq_le (norm_embL2_sq_le_h12 v)
  rw [inner_potOp]
  calc _ ≤ ‖mulOp V hV M hM (embL2 u)‖ * ‖embL2 w‖ := norm_inner_le_norm _ _
    _ ≤ M * ‖embL2 u‖ * ‖embL2 w‖ :=
        mul_le_mul_of_nonneg_right (norm_mulOp_le V hV M hM _) (norm_nonneg _)
    _ ≤ M * h12Norm u * h12Norm w :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hl u) hM0) (hl w) (norm_nonneg _)
          (mul_nonneg hM0 ((norm_nonneg _).trans (hl u)))

/-- **Real/complex reduction for real profiles.**  If the potential cross term is real on the real
profiles `f₁, f₂ ∈ H^1`, the shifted form at `f₁ + i f₂` is the sum of the two real forms.  The
hypothesis on `P` holds for a bounded real potential (`im_potOp_toH1`). -/
theorem re_formOp_split {P : H^{1}(Rd d) →L[ℂ] H^{1}(Rd d)} (hP : IsSelfAdjoint P) (c : ℝ)
    {f₁ f₂ : Rd d → ℝ} (h₁ : MemH1 f₁) (h₂ : MemH1 f₂)
    (hPr : (⟪P (toH1 h₁), toH1 h₂⟫_ℂ).im = 0) :
    (⟪formOp P c (toH1 h₁ + Complex.I • toH1 h₂), toH1 h₁ + Complex.I • toH1 h₂⟫_ℂ).re =
      (⟪formOp P c (toH1 h₁), toH1 h₁⟫_ℂ).re + (⟪formOp P c (toH1 h₂), toH1 h₂⟫_ℂ).re := by
  obtain ⟨g₁, hg₁, hw₁⟩ := h₁.2
  obtain ⟨g₂, hg₂, hw₂⟩ := h₂.2
  have hr := re_diag_split (sesqOf (formOp P c)) (isHermitianForm_formOp hP c)
    (toH1 h₁) (toH1 h₂) (by
      rw [sesqOf_apply, inner_formOp, Complex.add_im, Complex.sub_im, Complex.im_sum,
        Complex.im_ofReal_mul, hPr, embL2_toH1, embL2_toH1,
        im_inner_eq_zero (toL2C_im h₁.1) (toL2C_im h₂.1)]
      simp only [gradOp_toH1 h₁ hg₁ hw₁, gradOp_toH1 h₂ hg₂ hw₂,
        im_inner_eq_zero (toL2C_im _) (toL2C_im _)]
      simp)
  simpa only [sesqOf_apply] using hr

/-- A bounded real potential has a real cross term on real profiles. -/
theorem im_potOp_toH1 (V : Rd d → ℝ) (hV : Measurable V) (M : ℝ) (hM : ∀ x, |V x| ≤ M)
    {f₁ f₂ : Rd d → ℝ} (h₁ : MemH1 f₁) (h₂ : MemH1 f₂) :
    (⟪potOp V hV M hM (toH1 h₁), toH1 h₂⟫_ℂ).im = 0 := by
  rw [inner_potOp, embL2_toH1, embL2_toH1]
  refine im_inner_eq_zero ?_ (toL2C_im h₂.1)
  filter_upwards [mulOp_ae V hV M hM (toL2C h₁.1), toL2C_im h₁.1] with x hx h0
  rw [hx, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, h0]
  ring

end Form

/-! ### 7. The wrapper with the manuscript's hypotheses -/

/-- **`P:signed-closed-form`, form and resolvent part** (`notes/integrated_signed_static.tex`,
lines 49-130).  Hypotheses as in the TeX: the potential pairing `v_V(u,w) = ⟪P u, w⟫` is
Hermitian and satisfies `E:signed-multiplier-form` with constant `k`; `K ≥ max(1, k)`;
`c = 2 + K²`, `L_K = 3(1 + K²)`.  Conclusions, for every `u ∈ H^1`:
1. `E:signed-form-bounds`: `z²/2 ≤ q_V(u) + c b² ≤ L_K z²` (with `z² = ‖u‖₂² + ‖∇u‖₂²`);
2. the form version of `A ≥ 1`: `b² ≤ q_V(u) + c b²`;
3. the Fourier Cauchy-Schwarz step `‖u‖²_{H^{1/2}} ≤ b z`;
and the bounded resolvent `R_V` of the form is self-adjoint, positive, injective, of norm at
most one, and given by the unique weak solution.  The self-adjoint `H_V` itself,
`D(A^{1/2}) = H^1`, `E:signed-quarter-phase` and the negative completion are not concluded. -/
theorem signed_closed_form_resolvent_paper {d : ℕ} {P : H^{1}(Rd d) →L[ℂ] H^{1}(Rd d)}
    (hP : IsSelfAdjoint P) {k K : ℝ} (hk : SignedMultiplierForm P k) (hK : max 1 k ≤ K) :
    (∀ u : H^{1}(Rd d), 1 / 2 * msNormSq u ≤ (⟪formOp P (2 + K ^ 2) u, u⟫_ℂ).re ∧
      (⟪formOp P (2 + K ^ 2) u, u⟫_ℂ).re ≤ 3 * (1 + K ^ 2) * msNormSq u) ∧
    (∀ u : H^{1}(Rd d), ‖embL2 u‖ ^ 2 ≤ (⟪formOp P (2 + K ^ 2) u, u⟫_ℂ).re) ∧
    (∀ u : H^{1}(Rd d), h12NormSq u ≤ ‖embL2 u‖ * Real.sqrt (msNormSq u)) ∧
    ∃ R : L²[d] →L[ℂ] L²[d], ∃ S : L²[d] →L[ℂ] H^{1}(Rd d),
      (∀ f w, ⟪formOp P (2 + K ^ 2) w, S f⟫_ℂ = ⟪embL2 w, f⟫_ℂ) ∧
      (∀ f u, (∀ w, ⟪formOp P (2 + K ^ 2) w, u⟫_ℂ = ⟪embL2 w, f⟫_ℂ) → u = S f) ∧
      (∀ f, R f = embL2 (S f)) ∧ IsSelfAdjoint R ∧ R.IsPositive ∧ ‖R‖ ≤ 1 ∧
      Function.Injective R := by
  have hK1 : 1 ≤ K := le_of_max_le_left hK
  have hkK : k ≤ K := le_of_max_le_right hK
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := resolventV_spec hP hk hkK hK1
  refine ⟨fun u => ?_, fun u => ?_, h12NormSq_le, resolventV hk hkK hK1, solV hk hkK hK1,
    h1, h2, h3, h4, h5, h6, h7⟩
  · have hb := signed_form_bounds hk hkK hK1 u
    have : 0 ≤ (1 + K ^ 2 / 2) * ‖embL2 u‖ ^ 2 := by positivity
    exact ⟨by linarith [hb.1], hb.2⟩
  · have := norm_embL2_sq_le_form hk hkK hK1 u
    rwa [sesqOf_apply, RCLike.re_to_complex] at this

end StratonovichHAMSecondMoment.ResolventForm
