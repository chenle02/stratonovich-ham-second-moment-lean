module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

The real Sobolev space `H^1(ℝ^d; ℝ)` through weak gradients, the real
Rayleigh value set of `E:variational-real-rayleigh`
(`notes/integrated_unmasked_variational.tex`, Proposition
`P:variational-unmasked-rate`, TeX lines 101-110) for a general real
potential `V`, and its behaviour under the `L^2` dilation
`U_r f(x) = r^{d/2} f(r x)` used in the proof of Lemma
`L:variational-control-dilation` (TeX lines 260-266).

Mathlib has no Sobolev spaces and no weak derivatives, so this foundation is
built here by hand:
* `IsTestFunction φ`: `φ ∈ C_c^∞(ℝ^d; ℝ)` (smooth with compact support).
* `HasWeakGradient f g`: `g : ℝ^d → ℝ^d` is a weak gradient of `f`, i.e.
  `∫ f ∂_v φ = -∫ ⟪g, v⟫ φ` for every test function `φ` and direction `v`.
* `MemH1 f`: `f ∈ L^2` and `f` has a weak gradient in `L^2`.
* `weakGradient_ae_unique`: the weak gradient is unique almost everywhere, so
  `‖∇f‖₂² = ∫ ‖g‖²` does not depend on the choice of `g`.  This justifies
  stating the Rayleigh set over pairs `(f, g)`.

The Rayleigh set `rayleighSet V` is the set of values
`∫ V f² - ∫ ‖g‖²` over `f ∈ H^1(ℝ^d; ℝ)` with `‖f‖₂ = 1` and weak gradient
`g`, which is the set whose supremum is the right side of
`E:variational-real-rayleigh`.  One side condition is made explicit:
`V f²` is integrable.  In the manuscript `V = h_s` is bounded
(`L:variational-global-mean`, not formalized here), so for that potential this
condition holds for every `f ∈ L^2` and the set is the manuscript's set; the
condition only prevents Lean's junk value `0` for a non-integrable Bochner
integral from entering the set.  `rayleighRate V = √(sSup (rayleighSet V))`.

Proved here (auxiliary to the Lean proof route of
`L:variational-control-dilation`; the TeX states these facts in one sentence,
lines 260-264): `U_r` preserves `L^2` and the `L^2` norm, transports a weak
gradient `g` of `f` to the weak gradient `r U_r g` of `U_r f`, and therefore
`rayleighSet (r² V(r ·)) = r² · rayleighSet V` as sets, whence
`rayleighRate (r² V(r ·)) = r · rayleighRate V`.  These set and rate
identities hold for every real potential and need neither boundedness nor
nonemptiness of the set (for an empty or unbounded set Lean's `sSup` is `0`
on both sides).
-/
public import Mathlib
public import StratonovichHAMSecondMoment.HomogHypothesis

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory
open scoped ContDiff Pointwise

namespace StratonovichHAMSecondMoment.WeakSobolev

open HomogHypothesis (Rd)

variable {d : ℕ}

/-! ### Test functions, weak gradients and `H^1(ℝ^d; ℝ)` -/

/-- `φ ∈ C_c^∞(ℝ^d; ℝ)`: smooth with compact support. -/
def IsTestFunction (φ : Rd d → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ

/-- `g` is a weak gradient of `f`: for every test function `φ` and every
direction `v`, `∫ f ∂_v φ = -∫ ⟪g, v⟫ φ`. -/
def HasWeakGradient (f : Rd d → ℝ) (g : Rd d → Rd d) : Prop :=
  ∀ φ : Rd d → ℝ, IsTestFunction φ → ∀ v : Rd d,
    ∫ x, f x * fderiv ℝ φ x v = -∫ x, inner ℝ (g x) v * φ x

/-- The real Sobolev space `H^1(ℝ^d; ℝ)`: `f ∈ L^2` with a weak gradient in
`L^2`. -/
def MemH1 (f : Rd d → ℝ) : Prop :=
  MemLp f 2 volume ∧ ∃ g : Rd d → Rd d, MemLp g 2 volume ∧ HasWeakGradient f g

/-- An `L^2` weak gradient is unique almost everywhere. -/
theorem weakGradient_ae_unique {f : Rd d → ℝ} {g₁ g₂ : Rd d → Rd d}
    (h₁ : HasWeakGradient f g₁) (h₂ : HasWeakGradient f g₂)
    (hg₁ : MemLp g₁ 2 volume) (hg₂ : MemLp g₂ 2 volume) :
    g₁ =ᵐ[volume] g₂ := by
  have hloc : ∀ (g : Rd d → Rd d), MemLp g 2 volume → ∀ v : Rd d,
      LocallyIntegrable (fun x => inner ℝ (g x) v) volume := by
    intro g hg v
    have : MemLp (fun x => inner ℝ (g x) v) 2 volume := by
      have := (innerSL ℝ v).comp_memLp' hg
      refine this.congr_norm ?_ (Filter.Eventually.of_forall fun x => ?_)
      · exact hg.aestronglyMeasurable.inner_const
      · simp [real_inner_comm]
    exact this.locallyIntegrable (by norm_num)
  have hcoord : ∀ v : Rd d, ∀ᵐ x ∂volume, inner ℝ (g₁ x - g₂ x) v = 0 := by
    intro v
    have hL : LocallyIntegrable (fun x => inner ℝ (g₁ x - g₂ x) v) volume := by
      simp_rw [inner_sub_left]
      exact (hloc g₁ hg₁ v).sub (hloc g₂ hg₂ v)
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hL ?_
    intro φ hφ hφc
    have i₁ : Integrable (fun x => φ x • inner ℝ (g₁ x) v) volume :=
      (hloc g₁ hg₁ v).integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
    have i₂ : Integrable (fun x => φ x • inner ℝ (g₂ x) v) volume :=
      (hloc g₂ hg₂ v).integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
    have e₁ := h₁ φ ⟨hφ, hφc⟩ v
    have e₂ := h₂ φ ⟨hφ, hφc⟩ v
    have : ∀ x, φ x • inner ℝ (g₁ x - g₂ x) v =
        φ x • inner ℝ (g₁ x) v - φ x • inner ℝ (g₂ x) v := by
      intro x; rw [inner_sub_left, smul_sub]
    simp_rw [this]
    rw [integral_sub i₁ i₂]
    simp only [smul_eq_mul] at *
    have c₁ : ∫ x, φ x * inner ℝ (g₁ x) v = ∫ x, inner ℝ (g₁ x) v * φ x := by
      congr 1; funext x; ring
    have c₂ : ∫ x, φ x * inner ℝ (g₂ x) v = ∫ x, inner ℝ (g₂ x) v * φ x := by
      congr 1; funext x; ring
    rw [c₁, c₂]
    linarith
  have hall : ∀ᵐ x ∂volume, ∀ i : Fin d,
      inner ℝ (g₁ x - g₂ x) (EuclideanSpace.single i (1 : ℝ)) = 0 :=
    ae_all_iff.mpr fun i => hcoord _
  filter_upwards [hall] with x hx
  have : g₁ x - g₂ x = 0 := by
    ext i
    have := hx i
    rw [EuclideanSpace.inner_single_right] at this
    simpa using this
  exact sub_eq_zero.mp this

/-! ### The `L^2` dilation `U_r` -/

/-- `U_r f(x) = r^{d/2} f(r x)` (TeX line 260), for real- or vector-valued `f`. -/
def dilL2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (f : Rd d → E) : Rd d → E :=
  fun x => r ^ ((d : ℝ) / 2) • f (r • x)

/-- Auxiliary to the Lean proof route: `(r^{d/2})² = r^d`. -/
theorem rpow_half_sq {r : ℝ} (hr : 0 < r) : (r ^ ((d : ℝ) / 2)) ^ 2 = r ^ d := by
  rw [← Real.rpow_natCast (r ^ ((d : ℝ) / 2)) 2, ← Real.rpow_mul hr.le,
    ← Real.rpow_natCast r d]
  congr 1; push_cast; ring

/-- Auxiliary to the Lean proof route: Lebesgue substitution `y = r x`,
`∫ r^d G(r x) dx = ∫ G` (unconditional). -/
theorem integral_jacobian {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℝ} (hr : 0 < r) (G : Rd d → E) :
    ∫ x, (r ^ d : ℝ) • G (r • x) = ∫ y, G y := by
  rw [integral_smul, Measure.integral_comp_smul_of_nonneg volume G r (hR := hr.le),
    finrank_euclideanSpace_fin, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]

/-- Auxiliary to the Lean proof route: integrability is invariant under the
substitution `y = r x`. -/
theorem integrable_jacobian_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℝ} (hr : 0 < r) (G : Rd d → E) :
    Integrable (fun x => (r ^ d : ℝ) • G (r • x)) volume ↔ Integrable G volume := by
  have e : (fun x => (r ^ d : ℝ) • G (r • x)) = (r ^ d : ℝ) • (fun x => G (r • x)) := rfl
  rw [e, integrable_smul_iff (by positivity : (r ^ d : ℝ) ≠ 0),
    integrable_comp_smul_iff volume G hr.ne']

/-- `U_r` maps `L^2` into `L^2`. -/
theorem memLp_dilL2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℝ} (hr : 0 < r) {f : Rd d → E} (hf : MemLp f 2 volume) :
    MemLp (dilL2 r f) 2 volume := by
  have hm : AEStronglyMeasurable (fun x => f (r • x)) volume :=
    hf.aestronglyMeasurable.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_smul volume hr.ne')
  have : MemLp (fun x => f (r • x)) 2 volume := by
    rw [memLp_two_iff_integrable_sq_norm hm]
    rw [memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable] at hf
    exact (integrable_comp_smul_iff volume (fun y => ‖f y‖ ^ 2) hr.ne').mpr hf
  exact this.const_smul _

/-- Auxiliary to the Lean proof route: `‖U_r f(x)‖² = r^d ‖f(r x)‖²`. -/
theorem norm_dilL2_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℝ} (hr : 0 < r) (f : Rd d → E) (x : Rd d) :
    ‖dilL2 r f x‖ ^ 2 = (r ^ d : ℝ) • ‖f (r • x)‖ ^ 2 := by
  rw [dilL2, norm_smul, mul_pow, Real.norm_of_nonneg (Real.rpow_nonneg hr.le _),
    rpow_half_sq hr, smul_eq_mul]

/-- `U_r` preserves the `L^2` norm: `∫ ‖U_r f‖² = ∫ ‖f‖²`. -/
theorem integral_norm_dilL2_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℝ} (hr : 0 < r) (f : Rd d → E) :
    ∫ x, ‖dilL2 r f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  simp_rw [norm_dilL2_sq hr]
  exact integral_jacobian hr (fun y => ‖f y‖ ^ 2)

/-- `U_r` transports weak gradients: if `g` is a weak gradient of `f`, then
`r U_r g` is a weak gradient of `U_r f` (TeX line 262,
`‖∇U_r f‖₂² = r² ‖∇f‖₂²`). -/
theorem hasWeakGradient_dilL2 {r : ℝ} (hr : 0 < r) {f : Rd d → ℝ} {g : Rd d → Rd d}
    (h : HasWeakGradient f g) :
    HasWeakGradient (dilL2 r f) (fun x => r • dilL2 r g x) := by
  intro φ hφ v
  set ψ : Rd d → ℝ := fun y => φ (r⁻¹ • y) with hψdef
  have hψ : IsTestFunction ψ :=
    ⟨hφ.1.comp (contDiff_const_smul r⁻¹), hφ.2.comp_smul (inv_ne_zero hr.ne')⟩
  have hφψ : φ = fun x => ψ (r • x) := by
    funext x; simp [hψdef, smul_smul, inv_mul_cancel₀ hr.ne']
  have hD : ∀ x, fderiv ℝ φ x v = r * fderiv ℝ ψ (r • x) v := by
    intro x; rw [hφψ, fderiv_comp_smul]; rfl
  have hL : ∀ x, dilL2 r f x * fderiv ℝ φ x v =
      (r ^ ((d : ℝ) / 2) * r / r ^ d) *
        ((r ^ d : ℝ) • (f (r • x) * fderiv ℝ ψ (r • x) v)) := by
    intro x
    rw [hD, dilL2, smul_eq_mul, smul_eq_mul]
    field_simp
  have hR : ∀ x, inner ℝ (r • dilL2 r g x) v * φ x =
      (r ^ ((d : ℝ) / 2) * r / r ^ d) *
        ((r ^ d : ℝ) • (inner ℝ (g (r • x)) v * ψ (r • x))) := by
    intro x
    rw [hφψ, dilL2, real_inner_smul_left, real_inner_smul_left, smul_eq_mul]
    field_simp
  simp_rw [hL, hR]
  rw [integral_const_mul, integral_const_mul,
    integral_jacobian hr (fun y => f y * fderiv ℝ ψ y v),
    integral_jacobian hr (fun y => inner ℝ (g y) v * ψ y), h ψ hψ v]
  ring

/-! ### The real Rayleigh set of `E:variational-real-rayleigh` -/

/-- A trial of the real Rayleigh supremum for the potential `V`: `f ∈ L^2`
with `L^2` weak gradient `g` (so `f ∈ H^1(ℝ^d; ℝ)`), `‖f‖₂ = 1`, and
`V f²` integrable (explicit side condition, see the module doc). -/
structure IsRayleighTrial (V : Rd d → ℝ) (f : Rd d → ℝ) (g : Rd d → Rd d) : Prop where
  memLp_f : MemLp f 2 volume
  memLp_g : MemLp g 2 volume
  weakGrad : HasWeakGradient f g
  unit : ∫ x, f x ^ 2 = 1
  integrable_pot : Integrable (fun x => V x * f x ^ 2) volume

/-- The Rayleigh value `∫ V f² - ‖∇f‖₂²`. -/
def rayleighValue (V : Rd d → ℝ) (f : Rd d → ℝ) (g : Rd d → Rd d) : ℝ :=
  (∫ x, V x * f x ^ 2) - ∫ x, ‖g x‖ ^ 2

/-- The set of real Rayleigh values over unit `f ∈ H^1(ℝ^d; ℝ)`; its
supremum is the right side of `E:variational-real-rayleigh`. -/
def rayleighSet (V : Rd d → ℝ) : Set ℝ :=
  {q | ∃ f g, IsRayleighTrial V f g ∧ rayleighValue V f g = q}

/-- The rate attached to a potential: `√(sup of the real Rayleigh values)`.
For `V = h_{Ψ,s}` this is the manuscript's `λ_{Ψ,s}` through
`E:variational-real-rayleigh` (see `VariationalDilation`). -/
def rayleighRate (V : Rd d → ℝ) : ℝ :=
  Real.sqrt (sSup (rayleighSet V))

/-- Every trial `f` lies in `H^1(ℝ^d; ℝ)`. -/
theorem IsRayleighTrial.memH1 {V : Rd d → ℝ} {f : Rd d → ℝ} {g : Rd d → Rd d}
    (h : IsRayleighTrial V f g) : MemH1 f :=
  ⟨h.memLp_f, g, h.memLp_g, h.weakGrad⟩

/-- The Rayleigh value of a trial depends only on `f` (uniqueness of the weak
gradient), so the set over pairs is the set over `f ∈ H^1`. -/
theorem rayleighValue_indep {V : Rd d → ℝ} {f : Rd d → ℝ} {g₁ g₂ : Rd d → Rd d}
    (h₁ : IsRayleighTrial V f g₁) (h₂ : IsRayleighTrial V f g₂) :
    rayleighValue V f g₁ = rayleighValue V f g₂ := by
  have := weakGradient_ae_unique h₁.weakGrad h₂.weakGrad h₁.memLp_g h₂.memLp_g
  unfold rayleighValue
  congr 1
  exact integral_congr_ae (this.mono fun x hx => by simp only [hx])

/-- Auxiliary to the Lean proof route: a trial for `V` dilates to a trial for
`r² V(r ·)` with `r²` times the value. -/
theorem IsRayleighTrial.dil {V : Rd d → ℝ} {f : Rd d → ℝ} {g : Rd d → Rd d}
    {r : ℝ} (hr : 0 < r) (h : IsRayleighTrial V f g) :
    IsRayleighTrial (fun x => r ^ 2 * V (r • x)) (dilL2 r f) (fun x => r • dilL2 r g x) ∧
      rayleighValue (fun x => r ^ 2 * V (r • x)) (dilL2 r f) (fun x => r • dilL2 r g x) =
        r ^ 2 * rayleighValue V f g := by
  have hpot : ∀ x, r ^ 2 * V (r • x) * dilL2 r f x ^ 2 =
      r ^ 2 * ((r ^ d : ℝ) • (V (r • x) * f (r • x) ^ 2)) := by
    intro x
    have := norm_dilL2_sq hr f x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs] at this
    rw [this, smul_eq_mul, smul_eq_mul]; ring
  have hgrad : ∀ x, ‖r • dilL2 r g x‖ ^ 2 = r ^ 2 * ((r ^ d : ℝ) • ‖g (r • x)‖ ^ 2) := by
    intro x
    rw [norm_smul, mul_pow, Real.norm_of_nonneg hr.le, norm_dilL2_sq hr]
  have hsq : ∀ x, dilL2 r f x ^ 2 = (r ^ d : ℝ) • f (r • x) ^ 2 := by
    intro x
    have := norm_dilL2_sq hr f x
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs] at this
  refine ⟨⟨memLp_dilL2 hr h.memLp_f, (memLp_dilL2 hr h.memLp_g).const_smul r,
    hasWeakGradient_dilL2 hr h.weakGrad, ?_, ?_⟩, ?_⟩
  · simp_rw [hsq]; rw [integral_jacobian hr (fun y => f y ^ 2)]; exact h.unit
  · simp_rw [hpot]
    exact ((integrable_jacobian_iff hr (fun y => V y * f y ^ 2)).mpr
      h.integrable_pot).const_mul _
  · unfold rayleighValue
    simp_rw [hpot, hgrad]
    rw [integral_const_mul, integral_const_mul, integral_jacobian hr (fun y => V y * f y ^ 2),
      integral_jacobian hr (fun y => ‖g y‖ ^ 2)]
    ring

/-- The real Rayleigh bijection (TeX lines 260-264):
`rayleighSet (r² V(r ·)) = r² · rayleighSet V` for every real potential `V`
and `r > 0`. -/
theorem rayleighSet_dil (V : Rd d → ℝ) {r : ℝ} (hr : 0 < r) :
    rayleighSet (fun x => r ^ 2 * V (r • x)) = (r ^ 2) • rayleighSet V := by
  ext q
  constructor
  · rintro ⟨F, G, hT, rfl⟩
    have hri : 0 < r⁻¹ := inv_pos.mpr hr
    obtain ⟨hT', hv'⟩ := hT.dil hri
    have hV : (fun x => r⁻¹ ^ 2 * (r ^ 2 * V (r • r⁻¹ • x))) = V := by
      funext x
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, ← mul_assoc, ← mul_pow,
        inv_mul_cancel₀ hr.ne', one_pow, one_mul]
    rw [hV] at hT' hv'
    refine Set.mem_smul_set.mpr ⟨_, ⟨_, _, hT', rfl⟩, ?_⟩
    rw [hv', smul_eq_mul, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hr.ne', one_pow, one_mul]
  · rintro ⟨_, ⟨f, g, hT, rfl⟩, rfl⟩
    obtain ⟨hT', hv'⟩ := hT.dil hr
    exact ⟨_, _, hT', hv'⟩

/-- Auxiliary to the Lean proof route: `√(sSup (r² S)) = r √(sSup S)` for every
set `S` of reals and `r > 0` (no boundedness or nonemptiness needed). -/
theorem sqrt_sSup_scale (S : Set ℝ) {r : ℝ} (hr : 0 < r) :
    Real.sqrt (sSup ((r ^ 2) • S)) = r * Real.sqrt (sSup S) := by
  rw [Real.sSup_smul_of_nonneg (by positivity), smul_eq_mul, Real.sqrt_mul (by positivity),
    Real.sqrt_sq hr.le]

/-- The squared-rate identity: `sup R(r² V(r ·)) = r² sup R(V)`. -/
theorem sSup_rayleighSet_dil (V : Rd d → ℝ) {r : ℝ} (hr : 0 < r) :
    sSup (rayleighSet (fun x => r ^ 2 * V (r • x))) = r ^ 2 * sSup (rayleighSet V) := by
  rw [rayleighSet_dil V hr, Real.sSup_smul_of_nonneg (by positivity), smul_eq_mul]

/-- The rate identity: `rayleighRate (r² V(r ·)) = r · rayleighRate V`. -/
theorem rayleighRate_dil (V : Rd d → ℝ) {r : ℝ} (hr : 0 < r) :
    rayleighRate (fun x => r ^ 2 * V (r • x)) = r * rayleighRate V := by
  rw [rayleighRate, rayleighSet_dil V hr, sqrt_sSup_scale _ hr, rayleighRate]

end StratonovichHAMSecondMoment.WeakSobolev
