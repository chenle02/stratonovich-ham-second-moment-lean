module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Lemma `L:variational-control-dilation` (Radon and Rayleigh dilation) of
`notes/integrated_unmasked_variational.tex` (TeX lines 225-268), with the
definitions it uses: the control class `E:variational-positive-class`
(lines 5-10, with its nonemptiness, lines 13-17), the original mean
`h_{Ψ,s}` of `E:compact-raw-mean` and the variance `v_Ψ` of
`E:compact-raw-cost` in its integral form
(`notes/integrated_compact_mean_family.tex` lines 402-412), the rate
`λ_{Ψ,s}` through the real Rayleigh supremum `E:variational-real-rayleigh`
(lines 101-110) and `I_Ψ = ∫_0^1 λ_{Ψ,s} ds` (line 109).  The section's
standing assumption (lines 4-5) is a nonzero covariance satisfying `H:homog`
with `a = α₀`; the wrapper `variational_control_dilation_paper` carries it
as `HomogHypothesis.HomogCovariance`, `Γ ≠ 0`, `a = α₀`.

Definitions and conventions:
* A control `Ψ ∈ C_c^∞((0,1) × ℝ^d)` is a smooth `Ψ : ℝ × ℝ^d → ℝ` with
  compact support whose closed support lies in `(0,1) × ℝ^d` (its extension
  by zero; `CPos`).
* `(Γ * φ)(x) = ∫ φ(x - y) Γ(dy)` (`conv`), and
  `h_{Ψ,s}(x) = ∫_{(0,1)} |s-u|^{-a} (Γ * Ψ(u,·))(x) du` (`mean`); the kernel
  is Lean's `rpow`, whose value at `u = s` (a null set) is irrelevant.
* `v_Ψ = ∫_{(0,1)} ∫ Ψ(σ,x) h_{Ψ,σ}(x) dx dσ` (`rawCost`).
* `λ_{Ψ,s} = √(sup R_s)` where `R_s` is the real Rayleigh value set of
  `h_{Ψ,s}` over unit `f ∈ H^1(ℝ^d; ℝ)` (`rate`, from
  `WeakSobolev.rayleighRate`, a hand-rolled weak-gradient `H^1`), and
  `I_Ψ = ∫_{(0,1)} λ_{Ψ,s} ds` (`integratedRate`).

Not formalized here (recorded, not assumed):
* `P:variational-unmasked-rate`: that `sup R_s = -E_s` for the spectral
  bottom `E_s` of the self-adjoint operator `-Δ - h_s` on `H^2`, i.e. the
  manuscript's primary definition `λ_{Ψ,s} = √(-E_s)`, and that this value is
  positive and finite.  It needs the unbounded self-adjoint/spectral theory
  of foundation D8.  In this module `λ` is *defined* by the Rayleigh form
  `E:variational-real-rayleigh`, which the manuscript proves equal to
  `√(-E_s)`.
* `L:compact-raw-profile`: that the integral form `v_Ψ` equals `E W(Ψ)²`
  (and is finite and positive).  It needs the Gaussian noise construction of
  foundation D1.  Here `v_Ψ` is its integral form.
* `L:variational-global-mean` (boundedness of `h_s`), used only to see that
  the integrability side condition in `WeakSobolev.IsRayleighTrial` is
  automatic for the manuscript's potential.

The scaling identities are exact identities of the defined quantities and
need none of these: they hold for every continuous `Ψ` and every real
potential, including Lean's junk cases (a non-integrable Bochner integral, or
`sSup` of an empty or unbounded set, is `0` on both sides).  This module
does not exclude those junk cases.  It proves only that the integrability of
every integrand transfers exactly between `Ψ` and `D_r Ψ`
(`*_integrable_iff`, collected in
`variational_control_dilation_integrable_paper`), and that the Rayleigh value
sets scale.  These are conditional transfers: if a quantity is a genuine
integral or a genuine supremum for `Ψ`, so is the corresponding quantity for
`D_r Ψ`, and conversely.  They do not prove that any integrand is integrable,
or that any Rayleigh set is nonempty and bounded above; the finiteness and
positivity of `v_Ψ` and `I_Ψ` and the boundedness of `h_s` are the results
listed above as not formalized.  The integrability transfers are additional
Lean-route statements, not steps of the TeX proof, which works with
nonnegative integrands and Tonelli.

Proof route: as in the TeX (lines 240-268): the Radon pushforward
`Γ ∘ (r·)⁻¹ = r^{α-d} Γ` from the scaling field of `H:homog`, the Lebesgue
substitution `z = r x` in the variance, and the real Rayleigh bijection via
`U_r f(x) = r^{d/2} f(r x)` (`WeakSobolev.rayleighSet_dil`).  The TeX's
square-root step uses positivity of the rates; here `√(sSup (r² S)) = r √(sSup S)`
holds for every set `S`, so positivity is not needed.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.HomogHypothesis
public import StratonovichHAMSecondMoment.WeakSobolev

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory
open scoped ContDiff Pointwise

namespace StratonovichHAMSecondMoment.VariationalDilation

open HomogHypothesis (Rd HomogCovariance)

variable {d : ℕ}

/-! ### The control class and the dilation -/

/-- `E:variational-positive-class`: nonnegative, nonzero
`Ψ ∈ C_c^∞((0,1) × ℝ^d; ℝ)`, as smooth functions on `ℝ × ℝ^d` with compact
support inside `(0,1) × ℝ^d`. -/
def CPos (d : ℕ) : Set (ℝ × Rd d → ℝ) :=
  {Ψ | ContDiff ℝ ∞ Ψ ∧ HasCompactSupport Ψ ∧
    tsupport Ψ ⊆ Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ ∧ (∀ p, 0 ≤ Ψ p) ∧ Ψ ≠ 0}

/-- `E:variational-control-dilation`: `(D_r Ψ)(s,x) = r^{d+2-α} Ψ(s, r x)`. -/
def dil (alpha r : ℝ) (Ψ : ℝ × Rd d → ℝ) : ℝ × Rd d → ℝ :=
  fun p => r ^ ((d : ℝ) + 2 - alpha) * Ψ (p.1, r • p.2)

/-- The class `CPos` is nonempty (TeX lines 13-17; here a smooth bump on
`ℝ × ℝ^d` centred at `(1/2, 0)` with outer radius `1/4` replaces the
manuscript's explicit product of `e^{-1/(1-z²)}` bumps). -/
theorem CPos_nonempty (d : ℕ) : (CPos d).Nonempty := by
  let b : ContDiffBump ((1 / 2 : ℝ), (0 : Rd d)) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩
  refine ⟨b, b.contDiff, b.hasCompactSupport, ?_, fun p => b.nonneg, ?_⟩
  · rw [b.tsupport_eq]
    intro p hp
    refine ⟨⟨?_, ?_⟩, Set.mem_univ _⟩
    · have h1 : dist p.1 (1 / 2) ≤ 1 / 4 :=
        (le_max_left _ _).trans (Prod.dist_eq.symm.trans_le (Metric.mem_closedBall.mp hp))
      have := (abs_le.mp (Real.dist_eq _ _ ▸ h1)).1
      show (0 : ℝ) < p.1
      change (-(1 / 4 : ℝ)) ≤ p.1 - 1 / 2 at this
      linarith
    · have h1 : dist p.1 (1 / 2) ≤ 1 / 4 :=
        (le_max_left _ _).trans (Prod.dist_eq.symm.trans_le (Metric.mem_closedBall.mp hp))
      have := (abs_le.mp (Real.dist_eq _ _ ▸ h1)).2
      linarith
  · intro h
    have := congrFun h ((1 / 2 : ℝ), (0 : Rd d))
    rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num))] at this
    exact one_ne_zero this

/-- Auxiliary to the Lean proof route: the spatial dilation of `ℝ × ℝ^d` as a
homeomorphism. -/
def dilHomeo {r : ℝ} (hr : r ≠ 0) : ℝ × Rd d ≃ₜ ℝ × Rd d :=
  (Homeomorph.refl ℝ).prodCongr (Homeomorph.smulOfNeZero r hr)

/-- `D_r` maps `CPos` into `CPos` for `r > 0`. -/
theorem dil_mapsTo (alpha : ℝ) {r : ℝ} (hr : 0 < r) :
    Set.MapsTo (dil (d := d) alpha r) (CPos d) (CPos d) := by
  rintro Ψ ⟨hs, hc, ht, hn, hne⟩
  have hL : ContDiff ℝ ∞ (fun p : ℝ × Rd d => (p.1, r • p.2)) :=
    contDiff_fst.prodMk (contDiff_snd.const_smul r)
  have hcomp : (fun p : ℝ × Rd d => Ψ (p.1, r • p.2)) = Ψ ∘ (dilHomeo hr.ne') := rfl
  refine ⟨contDiff_const.mul (hs.comp hL), ?_, ?_, ?_, ?_⟩
  · have := hc.comp_homeomorph (dilHomeo hr.ne')
    rw [← hcomp] at this
    exact this.mul_left (f := fun _ => r ^ ((d : ℝ) + 2 - alpha))
  · have hsub : tsupport (dil alpha r Ψ) ⊆ (dilHomeo hr.ne') ⁻¹' tsupport Ψ := by
      refine closure_minimal ?_ ((isClosed_tsupport Ψ).preimage (dilHomeo hr.ne').continuous)
      intro p hp
      refine subset_tsupport Ψ ?_
      intro h0
      have e : (p.1, r • p.2) = dilHomeo hr.ne' p := rfl
      exact hp (show r ^ ((d : ℝ) + 2 - alpha) * Ψ (p.1, r • p.2) = 0 by rw [e, h0, mul_zero])
    intro p hp
    have := ht (hsub hp)
    exact ⟨this.1, Set.mem_univ _⟩
  · intro p
    exact mul_nonneg (Real.rpow_nonneg hr.le _) (hn _)
  · intro h
    apply hne
    funext p
    have := congrFun h (p.1, r⁻¹ • p.2)
    simp only [dil, smul_smul, mul_inv_cancel₀ hr.ne', one_smul, Pi.zero_apply] at this
    exact (mul_eq_zero.mp this).resolve_left (Real.rpow_pos_of_pos hr _).ne'

/-- `D_{1/r} ∘ D_r = id` on all functions, for `r > 0`. -/
theorem dil_inv_dil (alpha : ℝ) {r : ℝ} (hr : 0 < r) (Ψ : ℝ × Rd d → ℝ) :
    dil alpha (1 / r) (dil alpha r Ψ) = Ψ := by
  funext p
  simp only [dil, smul_smul, one_div, ← mul_assoc]
  rw [mul_inv_cancel₀ hr.ne', one_smul, ← Real.mul_rpow (inv_pos.mpr hr).le hr.le,
    inv_mul_cancel₀ hr.ne', Real.one_rpow, one_mul]

/-- `D_r ∘ D_{1/r} = id` on all functions, for `r > 0`. -/
theorem dil_dil_inv (alpha : ℝ) {r : ℝ} (hr : 0 < r) (Ψ : ℝ × Rd d → ℝ) :
    dil alpha r (dil alpha (1 / r) Ψ) = Ψ := by
  have := dil_inv_dil (d := d) alpha (one_div_pos.mpr hr) Ψ
  rwa [one_div_one_div] at this

/-- First claim of `L:variational-control-dilation`: for `r > 0`, `D_r` is a
bijection of `CPos` with inverse `D_{1/r}`. -/
theorem dil_bijOn (alpha : ℝ) {r : ℝ} (hr : 0 < r) :
    Set.InvOn (dil alpha (1 / r)) (dil alpha r) (CPos d) (CPos d) ∧
      Set.BijOn (dil (d := d) alpha r) (CPos d) (CPos d) := by
  have hinv : Set.InvOn (dil alpha (1 / r)) (dil alpha r) (CPos d) (CPos d) :=
    ⟨fun Ψ _ => dil_inv_dil alpha hr Ψ, fun Ψ _ => dil_dil_inv alpha hr Ψ⟩
  exact ⟨hinv, hinv.bijOn (dil_mapsTo alpha hr) (dil_mapsTo alpha (one_div_pos.mpr hr))⟩

/-! ### The Radon pushforward of `Γ` -/

/-- The set-scaling field of `H:homog`, `Γ(cA) = c^{d-α} Γ(A)`. -/
def SetScaling (alpha : ℝ) (Γ : Measure (Rd d)) : Prop :=
  ∀ A : Set (Rd d), MeasurableSet A → ∀ c : ℝ, 0 < c →
    Γ (c • A) = ENNReal.ofReal (c ^ ((d : ℝ) - alpha)) * Γ A

/-- The pushforward of `Γ` under `y ↦ r y` is `r^{α-d} Γ` (TeX lines 250-251). -/
theorem map_dilation {alpha : ℝ} {Γ : Measure (Rd d)} (hΓ : SetScaling alpha Γ)
    {r : ℝ} (hr : 0 < r) :
    Γ.map (fun y => r • y) = ENNReal.ofReal (r ^ (alpha - d)) • Γ := by
  ext A hA
  rw [Measure.map_apply (measurable_const_smul r) hA, Measure.smul_apply, smul_eq_mul]
  have : (fun y : Rd d => r • y) ⁻¹' A = r⁻¹ • A := by
    have h := Set.preimage_smul_inv₀ (inv_ne_zero hr.ne') A
    simpa using h
  rw [this, hΓ A hA r⁻¹ (inv_pos.mpr hr)]
  congr 2
  rw [Real.inv_rpow hr.le, ← Real.rpow_neg hr.le]
  ring_nf

/-- `∫ G(r y) Γ(dy) = r^{α-d} ∫ G dΓ` (TeX lines 246-248) for continuous `G`
(unconditional as an identity of Bochner integrals). -/
theorem integral_dilation {alpha : ℝ} {Γ : Measure (Rd d)} (hΓ : SetScaling alpha Γ)
    {r : ℝ} (hr : 0 < r) (G : Rd d → ℝ) (hG : Continuous G) :
    ∫ y, G (r • y) ∂Γ = r ^ (alpha - d) * ∫ z, G z ∂Γ := by
  rw [← integral_map (measurable_const_smul r).aemeasurable hG.aestronglyMeasurable,
    map_dilation hΓ hr, integral_smul_measure, smul_eq_mul,
    ENNReal.toReal_ofReal (Real.rpow_nonneg hr.le _)]

/-- Integrability against `Γ` transfers exactly under the dilation. -/
theorem integrable_dilation_iff {alpha : ℝ} {Γ : Measure (Rd d)} (hΓ : SetScaling alpha Γ)
    {r : ℝ} (hr : 0 < r) (G : Rd d → ℝ) (hG : Continuous G) :
    Integrable (fun y => G (r • y)) Γ ↔ Integrable G Γ := by
  have hm := (measurable_const_smul (M := ℝ) (α := Rd d) r).aemeasurable (μ := Γ)
  show Integrable (G ∘ fun y => r • y) Γ ↔ _
  rw [← integrable_map_measure hG.aestronglyMeasurable hm, map_dilation hΓ hr,
    integrable_smul_measure]
  · simpa using Real.rpow_pos_of_pos hr _
  · exact ENNReal.ofReal_ne_top

/-! ### Mean, variance, rate and integrated rate -/

/-- The convolution `(Γ * φ)(x) = ∫ φ(x - y) Γ(dy)`. -/
def conv (Γ : Measure (Rd d)) (φ : Rd d → ℝ) (x : Rd d) : ℝ :=
  ∫ y, φ (x - y) ∂Γ

/-- `E:compact-raw-mean`: `h_{Ψ,s}(x) = ∫_0^1 |s-u|^{-a} (Γ * Ψ(u,·))(x) du`. -/
def mean (a : ℝ) (Γ : Measure (Rd d)) (Ψ : ℝ × Rd d → ℝ) (s : ℝ) (x : Rd d) : ℝ :=
  ∫ u in Set.Ioo (0 : ℝ) 1, |s - u| ^ (-a) * conv Γ (fun y => Ψ (u, y)) x

/-- `E:compact-raw-cost` in its integral form:
`v_Ψ = ∫_0^1 ∫ Ψ(σ,x) h_{Ψ,σ}(x) dx dσ`. (Its identification with
`E W(Ψ)²` is `L:compact-raw-profile`, not formalized here.) -/
def rawCost (a : ℝ) (Γ : Measure (Rd d)) (Ψ : ℝ × Rd d → ℝ) : ℝ :=
  ∫ σ in Set.Ioo (0 : ℝ) 1, ∫ x, Ψ (σ, x) * mean a Γ Ψ σ x

/-- `λ_{Ψ,s}` by `E:variational-real-rayleigh`:
`λ_{Ψ,s} = √(sup{∫ h_s f² - ‖∇f‖₂² : f ∈ H^1(ℝ^d;ℝ), ‖f‖₂ = 1})`.
(Its identification with `√(-E_s)` is `P:variational-unmasked-rate`, not
formalized here.) -/
def rate (a : ℝ) (Γ : Measure (Rd d)) (Ψ : ℝ × Rd d → ℝ) (s : ℝ) : ℝ :=
  WeakSobolev.rayleighRate (mean a Γ Ψ s)

/-- `I_Ψ = ∫_0^1 λ_{Ψ,s} ds`. -/
def integratedRate (a : ℝ) (Γ : Measure (Rd d)) (Ψ : ℝ × Rd d → ℝ) : ℝ :=
  ∫ s in Set.Ioo (0 : ℝ) 1, rate a Γ Ψ s

/-- Auxiliary to the Lean proof route: the amplitude exponents,
`r^{d+2-α} r^{α-d} = r²`. -/
theorem amp_mul_push {alpha r : ℝ} (hr : 0 < r) :
    r ^ ((d : ℝ) + 2 - alpha) * r ^ (alpha - d) = r ^ 2 := by
  rw [← Real.rpow_add hr, ← Real.rpow_natCast]
  congr 1; push_cast; ring

/-- Auxiliary to the Lean proof route: `r^{d+2-α} r² (r^d)⁻¹ = r^{4-α}`. -/
theorem amp_variance {alpha r : ℝ} (hr : 0 < r) :
    r ^ ((d : ℝ) + 2 - alpha) * r ^ 2 * (r ^ d)⁻¹ = r ^ (4 - alpha) := by
  rw [← Real.rpow_natCast r 2, ← Real.rpow_natCast r d, ← Real.rpow_neg hr.le,
    ← Real.rpow_add hr, ← Real.rpow_add hr]
  congr 1; push_cast; ring

/-- The convolution of a dilated control:
`(Γ * D_rΨ(u,·))(x) = r² (Γ * Ψ(u,·))(r x)` (TeX lines 252-253). -/
theorem conv_dil {alpha : ℝ} {Γ : Measure (Rd d)} (hΓ : SetScaling alpha Γ)
    {r : ℝ} (hr : 0 < r) {Ψ : ℝ × Rd d → ℝ} (hΨ : Continuous Ψ) (u : ℝ) (x : Rd d) :
    conv Γ (fun y => dil alpha r Ψ (u, y)) x = r ^ 2 * conv Γ (fun y => Ψ (u, y)) (r • x) := by
  have hG : Continuous (fun z : Rd d => Ψ (u, r • x - z)) := by fun_prop
  simp only [conv, dil, smul_sub]
  rw [integral_const_mul, integral_dilation hΓ hr (fun z => Ψ (u, r • x - z)) hG,
    ← mul_assoc, amp_mul_push hr]

/-- Integrability of the convolution integrand transfers under `D_r`. -/
theorem conv_dil_integrable_iff {alpha : ℝ} {Γ : Measure (Rd d)} (hΓ : SetScaling alpha Γ)
    {r : ℝ} (hr : 0 < r) {Ψ : ℝ × Rd d → ℝ} (hΨ : Continuous Ψ) (u : ℝ) (x : Rd d) :
    Integrable (fun y => dil alpha r Ψ (u, x - y)) Γ ↔
      Integrable (fun y => Ψ (u, r • x - y)) Γ := by
  have hG : Continuous (fun z : Rd d => Ψ (u, r • x - z)) := by fun_prop
  simp only [dil, smul_sub]
  rw [integrable_const_mul_iff (Real.rpow_pos_of_pos hr _).ne'.isUnit]
  exact integrable_dilation_iff hΓ hr _ hG

/-- `h_{D_rΨ,s}(x) = r² h_{Ψ,s}(r x)` (`E:variational-dilation-values`). -/
theorem mean_dil {alpha : ℝ} {Γ : Measure (Rd d)} (hΓ : SetScaling alpha Γ)
    {r : ℝ} (hr : 0 < r) {Ψ : ℝ × Rd d → ℝ} (hΨ : Continuous Ψ) (a s : ℝ) (x : Rd d) :
    mean a Γ (dil alpha r Ψ) s x = r ^ 2 * mean a Γ Ψ s (r • x) := by
  simp only [mean, conv_dil hΓ hr hΨ]
  rw [← integral_const_mul]
  congr 1; funext u; ring

/-- Integrability of the time integrand of the mean transfers under `D_r`. -/
theorem mean_dil_integrable_iff {alpha : ℝ} {Γ : Measure (Rd d)} (hΓ : SetScaling alpha Γ)
    {r : ℝ} (hr : 0 < r) {Ψ : ℝ × Rd d → ℝ} (hΨ : Continuous Ψ) (a s : ℝ) (x : Rd d) :
    IntegrableOn (fun u => |s - u| ^ (-a) * conv Γ (fun y => dil alpha r Ψ (u, y)) x)
        (Set.Ioo 0 1) ↔
      IntegrableOn (fun u => |s - u| ^ (-a) * conv Γ (fun y => Ψ (u, y)) (r • x))
        (Set.Ioo 0 1) := by
  have e : (fun u => |s - u| ^ (-a) * conv Γ (fun y => dil alpha r Ψ (u, y)) x) =
      fun u => r ^ 2 * (|s - u| ^ (-a) * conv Γ (fun y => Ψ (u, y)) (r • x)) := by
    funext u; rw [conv_dil hΓ hr hΨ]; ring
  rw [IntegrableOn, e, integrable_const_mul_iff (pow_pos hr 2).ne'.isUnit]
  rfl

/-- Auxiliary to the Lean proof route: the spatial variance integrand of
`D_rΨ` at time `σ`. -/
theorem cost_integrand_dil {alpha : ℝ} {Γ : Measure (Rd d)} (hΓ : SetScaling alpha Γ)
    {r : ℝ} (hr : 0 < r) {Ψ : ℝ × Rd d → ℝ} (hΨ : Continuous Ψ) (a σ : ℝ) (x : Rd d) :
    dil alpha r Ψ (σ, x) * mean a Γ (dil alpha r Ψ) σ x =
      (r ^ ((d : ℝ) + 2 - alpha) * r ^ 2 * (r ^ d)⁻¹) *
        ((r ^ d : ℝ) • (Ψ (σ, r • x) * mean a Γ Ψ σ (r • x))) := by
  rw [mean_dil hΓ hr hΨ, smul_eq_mul, dil]
  field_simp

/-- Integrability of the spatial variance integrand transfers under `D_r`. -/
theorem cost_inner_integrable_iff {alpha : ℝ} {Γ : Measure (Rd d)} (hΓ : SetScaling alpha Γ)
    {r : ℝ} (hr : 0 < r) {Ψ : ℝ × Rd d → ℝ} (hΨ : Continuous Ψ) (a σ : ℝ) :
    Integrable (fun x => dil alpha r Ψ (σ, x) * mean a Γ (dil alpha r Ψ) σ x) volume ↔
      Integrable (fun x => Ψ (σ, x) * mean a Γ Ψ σ x) volume := by
  simp_rw [cost_integrand_dil hΓ hr hΨ a σ, amp_variance hr]
  rw [integrable_const_mul_iff (Real.rpow_pos_of_pos hr _).ne'.isUnit]
  exact WeakSobolev.integrable_jacobian_iff hr (fun y => Ψ (σ, y) * mean a Γ Ψ σ y)

/-- Auxiliary to the Lean proof route: the inner spatial integral scales by
`r^{4-α}`. -/
theorem cost_inner_dil {alpha : ℝ} {Γ : Measure (Rd d)} (hΓ : SetScaling alpha Γ)
    {r : ℝ} (hr : 0 < r) {Ψ : ℝ × Rd d → ℝ} (hΨ : Continuous Ψ) (a σ : ℝ) :
    ∫ x, dil alpha r Ψ (σ, x) * mean a Γ (dil alpha r Ψ) σ x =
      r ^ (4 - alpha) * ∫ x, Ψ (σ, x) * mean a Γ Ψ σ x := by
  simp_rw [cost_integrand_dil hΓ hr hΨ a σ]
  rw [integral_const_mul, WeakSobolev.integral_jacobian hr
    (fun y => Ψ (σ, y) * mean a Γ Ψ σ y), amp_variance hr]

/-- `v_{D_rΨ} = r^{4-α} v_Ψ` (`E:variational-dilation-values`, TeX lines
254-258: Radon pushforward `r^{d+2-α}·r²`, Lebesgue volume factor `r^{-d}`). -/
theorem rawCost_dil {alpha : ℝ} {Γ : Measure (Rd d)} (hΓ : SetScaling alpha Γ)
    {r : ℝ} (hr : 0 < r) {Ψ : ℝ × Rd d → ℝ} (hΨ : Continuous Ψ) (a : ℝ) :
    rawCost a Γ (dil alpha r Ψ) = r ^ (4 - alpha) * rawCost a Γ Ψ := by
  simp only [rawCost, cost_inner_dil hΓ hr hΨ]
  exact integral_const_mul _ _

/-- Integrability of the time integrand of the variance transfers under
`D_r`. -/
theorem rawCost_integrable_iff {alpha : ℝ} {Γ : Measure (Rd d)} (hΓ : SetScaling alpha Γ)
    {r : ℝ} (hr : 0 < r) {Ψ : ℝ × Rd d → ℝ} (hΨ : Continuous Ψ) (a : ℝ) :
    IntegrableOn (fun σ => ∫ x, dil alpha r Ψ (σ, x) * mean a Γ (dil alpha r Ψ) σ x)
        (Set.Ioo 0 1) ↔
      IntegrableOn (fun σ => ∫ x, Ψ (σ, x) * mean a Γ Ψ σ x) (Set.Ioo 0 1) := by
  simp only [cost_inner_dil hΓ hr hΨ]
  exact integrable_const_mul_iff (Real.rpow_pos_of_pos hr _).ne'.isUnit _

/-- The Rayleigh value sets scale: `R_{D_rΨ,s} = r² R_{Ψ,s}` (TeX lines
260-264). -/
theorem rayleighSet_mean_dil {alpha : ℝ} {Γ : Measure (Rd d)} (hΓ : SetScaling alpha Γ)
    {r : ℝ} (hr : 0 < r) {Ψ : ℝ × Rd d → ℝ} (hΨ : Continuous Ψ) (a s : ℝ) :
    WeakSobolev.rayleighSet (mean a Γ (dil alpha r Ψ) s) =
      (r ^ 2) • WeakSobolev.rayleighSet (mean a Γ Ψ s) := by
  have : mean a Γ (dil alpha r Ψ) s = fun x => r ^ 2 * mean a Γ Ψ s (r • x) :=
    funext (mean_dil hΓ hr hΨ a s)
  rw [this, WeakSobolev.rayleighSet_dil _ hr]

/-- The squared rate identity `λ²_{D_rΨ,s} = r² λ²_{Ψ,s}`, as suprema. -/
theorem sSup_rayleighSet_mean_dil {alpha : ℝ} {Γ : Measure (Rd d)}
    (hΓ : SetScaling alpha Γ) {r : ℝ} (hr : 0 < r) {Ψ : ℝ × Rd d → ℝ} (hΨ : Continuous Ψ)
    (a s : ℝ) :
    sSup (WeakSobolev.rayleighSet (mean a Γ (dil alpha r Ψ) s)) =
      r ^ 2 * sSup (WeakSobolev.rayleighSet (mean a Γ Ψ s)) := by
  rw [rayleighSet_mean_dil hΓ hr hΨ, Real.sSup_smul_of_nonneg (by positivity), smul_eq_mul]

/-- `λ_{D_rΨ,s} = r λ_{Ψ,s}` (`E:variational-dilation-values`). -/
theorem rate_dil {alpha : ℝ} {Γ : Measure (Rd d)} (hΓ : SetScaling alpha Γ)
    {r : ℝ} (hr : 0 < r) {Ψ : ℝ × Rd d → ℝ} (hΨ : Continuous Ψ) (a s : ℝ) :
    rate a Γ (dil alpha r Ψ) s = r * rate a Γ Ψ s := by
  rw [rate, WeakSobolev.rayleighRate, rayleighSet_mean_dil hΓ hr hΨ,
    WeakSobolev.sqrt_sSup_scale _ hr]
  rfl

/-- Integrability of the rate on `(0,1)` transfers under `D_r`. -/
theorem rate_integrable_iff {alpha : ℝ} {Γ : Measure (Rd d)} (hΓ : SetScaling alpha Γ)
    {r : ℝ} (hr : 0 < r) {Ψ : ℝ × Rd d → ℝ} (hΨ : Continuous Ψ) (a : ℝ) :
    IntegrableOn (rate a Γ (dil alpha r Ψ)) (Set.Ioo 0 1) ↔
      IntegrableOn (rate a Γ Ψ) (Set.Ioo 0 1) := by
  have : rate a Γ (dil alpha r Ψ) = fun s => r * rate a Γ Ψ s :=
    funext (rate_dil hΓ hr hΨ a)
  rw [this]
  exact integrable_const_mul_iff hr.ne'.isUnit _

/-- `I_{D_rΨ} = r I_Ψ` (`E:variational-dilation-values`). -/
theorem integratedRate_dil {alpha : ℝ} {Γ : Measure (Rd d)} (hΓ : SetScaling alpha Γ)
    {r : ℝ} (hr : 0 < r) {Ψ : ℝ × Rd d → ℝ} (hΨ : Continuous Ψ) (a : ℝ) :
    integratedRate a Γ (dil alpha r Ψ) = r * integratedRate a Γ Ψ := by
  simp only [integratedRate, rate_dil hΓ hr hΨ]
  exact integral_const_mul _ _

/-! ### The manuscript's statement -/

/-- `H:homog` supplies the set scaling of `Γ`. -/
theorem setScaling_of_homog {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (h : HomogCovariance d alpha alpha0 Γ μ) : SetScaling alpha Γ :=
  h.scaling

/-- Lemma `L:variational-control-dilation` (TeX lines 225-237) with the
section's standing hypotheses (lines 4-5: a nonzero covariance satisfying
`H:homog`, `a = α₀`): for `r > 0`, `D_r` is a bijection of `CPos` with
inverse `D_{1/r}`, and for every `Ψ ∈ CPos`,
`h_{D_rΨ,s}(x) = r² h_{Ψ,s}(r x)`, `v_{D_rΨ} = r^{4-α} v_Ψ`,
`λ_{D_rΨ,s} = r λ_{Ψ,s}` and `I_{D_rΨ} = r I_Ψ`.  The hypotheses `Γ ≠ 0`
and all fields of `H:homog` except the scaling are carried but unused. -/
theorem variational_control_dilation_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (_hΓ0 : Γ ≠ 0) {r : ℝ} (hr : 0 < r) :
    Set.InvOn (dil alpha (1 / r)) (dil alpha r) (CPos d) (CPos d) ∧
      Set.BijOn (dil (d := d) alpha r) (CPos d) (CPos d) ∧
      ∀ Ψ ∈ CPos d,
        (∀ s x, mean alpha0 Γ (dil alpha r Ψ) s x = r ^ 2 * mean alpha0 Γ Ψ s (r • x)) ∧
        rawCost alpha0 Γ (dil alpha r Ψ) = r ^ (4 - alpha) * rawCost alpha0 Γ Ψ ∧
        (∀ s, rate alpha0 Γ (dil alpha r Ψ) s = r * rate alpha0 Γ Ψ s) ∧
        integratedRate alpha0 Γ (dil alpha r Ψ) = r * integratedRate alpha0 Γ Ψ := by
  obtain ⟨hinv, hbij⟩ := dil_bijOn (d := d) alpha hr
  refine ⟨hinv, hbij, fun Ψ hΨ => ?_⟩
  have hc : Continuous Ψ := hΨ.1.continuous
  have hS := setScaling_of_homog hH
  exact ⟨mean_dil hS hr hc alpha0, rawCost_dil hS hr hc alpha0, rate_dil hS hr hc alpha0,
    integratedRate_dil hS hr hc alpha0⟩

/-- The integrability companion of `variational_control_dilation_paper`:
under the same hypotheses, every integrand in the definitions of
`h`, `v` and `I` is integrable for `D_rΨ` exactly when it is for `Ψ`, and
the Rayleigh value sets scale (`R_{D_rΨ,s} = r² R_{Ψ,s}`), so nonemptiness and
boundedness above hold for one side exactly when they hold for the other.
This is a conditional transfer: it does not prove that either side is
integrable, nonempty or bounded, so it does not by itself make the identities
of `E:variational-dilation-values` identities of genuine integrals and
suprema.  The integrability equivalences are Lean-route auxiliaries; the TeX
proof states none of them. -/
theorem variational_control_dilation_integrable_paper {alpha alpha0 : ℝ}
    {Γ μ : Measure (Rd d)} (hH : HomogCovariance d alpha alpha0 Γ μ) (_hΓ0 : Γ ≠ 0)
    {r : ℝ} (hr : 0 < r) (Ψ : ℝ × Rd d → ℝ) (hΨ : Ψ ∈ CPos d) :
    (∀ u x, Integrable (fun y => dil alpha r Ψ (u, x - y)) Γ ↔
      Integrable (fun y => Ψ (u, r • x - y)) Γ) ∧
    (∀ s x, IntegrableOn
        (fun u => |s - u| ^ (-alpha0) * conv Γ (fun y => dil alpha r Ψ (u, y)) x)
        (Set.Ioo 0 1) ↔
      IntegrableOn (fun u => |s - u| ^ (-alpha0) * conv Γ (fun y => Ψ (u, y)) (r • x))
        (Set.Ioo 0 1)) ∧
    (∀ σ, Integrable
        (fun x => dil alpha r Ψ (σ, x) * mean alpha0 Γ (dil alpha r Ψ) σ x) volume ↔
      Integrable (fun x => Ψ (σ, x) * mean alpha0 Γ Ψ σ x) volume) ∧
    (IntegrableOn
        (fun σ => ∫ x, dil alpha r Ψ (σ, x) * mean alpha0 Γ (dil alpha r Ψ) σ x)
        (Set.Ioo 0 1) ↔
      IntegrableOn (fun σ => ∫ x, Ψ (σ, x) * mean alpha0 Γ Ψ σ x) (Set.Ioo 0 1)) ∧
    (∀ s, WeakSobolev.rayleighSet (mean alpha0 Γ (dil alpha r Ψ) s) =
      (r ^ 2) • WeakSobolev.rayleighSet (mean alpha0 Γ Ψ s)) ∧
    (IntegrableOn (rate alpha0 Γ (dil alpha r Ψ)) (Set.Ioo 0 1) ↔
      IntegrableOn (rate alpha0 Γ Ψ) (Set.Ioo 0 1)) := by
  have hc : Continuous Ψ := hΨ.1.continuous
  have hS := setScaling_of_homog hH
  exact ⟨conv_dil_integrable_iff hS hr hc, mean_dil_integrable_iff hS hr hc alpha0,
    cost_inner_integrable_iff hS hr hc alpha0, rawCost_integrable_iff hS hr hc alpha0,
    rayleighSet_mean_dil hS hr hc alpha0, rate_integrable_iff hS hr hc alpha0⟩

end StratonovichHAMSecondMoment.VariationalDilation
