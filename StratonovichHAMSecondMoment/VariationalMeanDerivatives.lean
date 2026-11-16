module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

The first sentence of `L:variational-global-mean` (global regularity of the
original mean; statement lines 85-95, proof 97-118 of
`notes/integrated_unmasked_variational.tex` at revision 39f2597a): "Every mixed
time and space derivative of `h_s` is globally bounded in space, uniformly on
compact time intervals" (lines 87-88).  `VariationalMean` formalizes the
displayed consequence `E:variational-global-mean`; this module adds the
derivative sentence and the combined wrapper.

Objects reused, unchanged: `VariationalDilation.conv`
(`(Γ * φ)(x) = ∫ φ(x - y) Γ(dy)`), `VariationalDilation.mean`
(`h_s(x) = ∫_{(0,1)} |s-u|^{-a} (Γ * Ψ(u,·))(x) du`, `E:compact-raw-mean`),
the control class `VariationalDilation.CPos` (`E:variational-positive-class`),
and `VariationalMean.gMass` (the Gaussian mass of `Γ`, from
`L:variational-heat-envelope` at `ε = 1`).

Formalized:
* `mean_derivatives` (general form: tempered `Γ`, `μ`, spectral convention,
  `Ψ ∈ CPos`, `a < 1`): the map `(s,x) ↦ h_s(x)` on `ℝ × ℝ^d` is `C^∞`; the
  integrand defining `h_s(x)` is integrable on `(0,1)` for EVERY real `s` and
  every `x` (so `h_s(x)` is a genuine integral, not Lean's junk value, at every
  point where a derivative is taken); and for every order `n` and every compact
  `K ⊆ ℝ` there is a finite `C ≥ 0` with
  `‖D^n h(s,x)‖ ≤ C` for all `s ∈ K` and all `x ∈ ℝ^d`, where `D^n h` is the
  `n`-th Fréchet derivative in the joint variable `(s,x)`.
* `mean_partial_bound`: the same bound for every mixed partial derivative,
  i.e. `|D^n h(s,x)(v_1,…,v_n)| ≤ C ∏ ‖v_i‖` for arbitrary directions `v_i`,
  in particular for the time direction `(1,0)` and the space directions
  `(0,e_j)`.
* `variational_global_mean_derivatives_paper`: the above under the section's
  standing hypotheses (`H:homog`, `Γ ≠ 0`, `a = α₀`, `Ψ ∈ CPos`).
* `variational_global_mean_whole_paper`: every conclusion of
  `L:variational-global-mean`: the derivative sentence (above) and the display
  `E:variational-global-mean` on `I = [0,1]` (`0 ≤ h_s(x) ≤ M`,
  `|h_s(x) - h_t(x)| ≤ C_Ψ |s - t|`, from `VariationalMean`).

How the formal statement reads the sentence.  "Every mixed time and space
derivative" is read as every iterated Fréchet derivative of the joint map
`(s,x) ↦ h_s(x)`; its operator norm bounds every mixed partial
`∂_s^j ∂_x^β h` of total order `n` (`mean_partial_bound`).  "Globally bounded
in space, uniformly on compact time intervals" is read as one constant for all
`x ∈ ℝ^d` and all `s` in a given compact set.  Existence (smoothness) of these
derivatives is part of the conclusion (`ContDiff ℝ ∞`).

Supplied inputs: none (no named analytic hypotheses).

Implicit hypotheses made explicit: none beyond those of `VariationalMean`
(`a < 1` is `α₀ < 1` of `H:homog`).  Hypotheses of `H:homog` used:
`Γ_tempered`, `μ_tempered`, `spectral`, `alpha0_lt_one`; `Γ ≠ 0` and the
other fields are carried, unused, in the derivative wrapper.  Nonnegativity
and `Ψ ≠ 0` (part of `CPos`) are not used for the derivative sentence; they
are used by the display (nonnegativity of `h_s`).

Proof route.  As in the TeX (lines 98-116), in two parametric-integral steps,
each "differentiate under the integral sign against a measure":
1. `F(u,x) = (Γ * Ψ(u,·))(x) = ∫ Ψ((u,x) - (0,y)) Γ(dy)`: every derivative of
   `Ψ` is bounded and vanishes for `|z| > R`, hence is dominated by
   `C e^{R²/2} e^{-|z|²/2}`, and `y ↦ e^{-|x-y|²/2}` is `Γ`-integrable with
   integral at most `gMass Γ` (`VariationalMean.gauss_conv`, i.e.
   `L:variational-heat-envelope`).  This is the TeX's `|DΨ| ≤ C_D p_ε` (lines
   99-103) at `ε = 1`.  So `F` is `C^∞` with every derivative globally bounded on
   `ℝ × ℝ^d`, and `F(u,·) = 0` for `u ∉ [0,1]`.
2. `h(s,x) = ∫ |r|^{-a} F((s,x) - (r,0)) dr` (the change `r = s - u`, lines
   105-109, valid for every real `s` because `F` vanishes outside `u ∈ [0,1]`):
   for `(s,x)` near `(s₀,x₀)` only `|r| < |s₀| + 3` contribute, and `|r|^{-a}`
   is integrable there for `a < 1` (lines 111-113).  Every derivative falls on
   `F` (lines 113-114).
Both steps are instances of one engine (`tInt`, `contDiff_tInt`,
`norm_iteratedFDeriv_tInt_le`): for `Φ` smooth, with all derivatives bounded and
support in a set `S`, and a weight `w` whose modulus on
`{y : p - τ y ∈ S}` is dominated, locally uniformly in `p`, by an integrable
function, `p ↦ ∫ w(y) Φ(p - τ y) ν(dy)` is `C^∞`, its derivative is the
integral of the derivative (Mathlib's
`hasFDerivAt_integral_of_dominated_of_fderiv_le`), and
`‖D^n(∫ w Φ(· - τ))(p)‖ ≤ ∫ |w(y)| ‖D^n Φ(p - τ y)‖ ν(dy)`.  The TeX's
dominated convergence for the passage of derivatives is that Mathlib theorem;
the TeX's "ordinary local differentiation against the Radon measure" (lines 103-104)
is the same theorem with `ν = Γ`.  Lemmas marked "Auxiliary to the Lean proof
route" have no manuscript label.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.HomogHypothesis
public import StratonovichHAMSecondMoment.VariationalDilation
public import StratonovichHAMSecondMoment.VariationalMean

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped ContDiff

namespace StratonovichHAMSecondMoment.VariationalMeanDerivatives

open HomogHypothesis (Rd HomogCovariance IsTempered IsSpectralMeasure)
open VariationalDilation (CPos conv mean)
open VariationalMean (gMass gauss_conv gMass_nonneg exists_radius eq_zero_of_time
  one_le_gauss conv_eq_zero_of_time)

/-! ### The engine: weighted translated integrals of smooth functions -/

section engine

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Y : Type}

/-- Auxiliary to the Lean proof route.  The weighted translated integral
`p ↦ ∫ w(y) Φ(p - τ y) ν(dy)`.  With `ν = Γ`, `τ y = (0,y)`, `w = 1` it is
`(u,x) ↦ (Γ * Φ(u,·))(x)`; with `ν = dr`, `τ r = (r,0)`, `w r = |r|^{-a}` it is
the time integral of TeX lines 107-109. -/
def tInt [MeasurableSpace Y] (ν : Measure Y) (τ : Y → E) (w : Y → ℝ) {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (Φ : E → F) (p : E) : F :=
  ∫ y, w y • Φ (p - τ y) ∂ν

/-- Auxiliary to the Lean proof route.  A smooth function with support in `S`
all of whose derivatives are globally bounded. -/
structure Good {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (S : Set E) (Φ : E → F) :
    Prop where
  smooth : ContDiff ℝ ∞ Φ
  supp : tsupport Φ ⊆ S
  bdd : ∀ n : ℕ, ∃ B : ℝ, ∀ q, ‖iteratedFDeriv ℝ n Φ q‖ ≤ B

/-- Auxiliary to the Lean proof route.  The weight is dominated on the
relevant translates, locally uniformly: near every `p₀` there is a
nonnegative integrable `g` with `|w y| ≤ g y` whenever `p - τ y ∈ S`. -/
def Dominated [MeasurableSpace Y] (ν : Measure Y) (τ : Y → E) (w : Y → ℝ) (S : Set E) : Prop :=
  ∀ p₀ : E, ∃ g : Y → ℝ, Integrable g ν ∧ (∀ y, 0 ≤ g y) ∧
    ∀ p ∈ ball p₀ 1, ∀ y, p - τ y ∈ S → |w y| ≤ g y

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Auxiliary to the Lean proof route.  The derivative of a `Good` function is
`Good` on the same set. -/
theorem Good.fderiv {S : Set E} {Φ : E → F} (h : Good S Φ) : Good S (fderiv ℝ Φ) where
  smooth := (contDiff_infty_iff_fderiv.1 h.smooth).2
  supp := (tsupport_fderiv_subset ℝ).trans h.supp
  bdd n := by
    obtain ⟨B, hB⟩ := h.bdd (n + 1)
    exact ⟨B, fun q => by rw [norm_iteratedFDeriv_fderiv]; exact hB q⟩

/-- Auxiliary to the Lean proof route.  A `Good` function is bounded. -/
theorem Good.norm_le {S : Set E} {Φ : E → F} (h : Good S Φ) : ∃ B, ∀ q, ‖Φ q‖ ≤ B := by
  obtain ⟨B, hB⟩ := h.bdd 0
  exact ⟨B, fun q => by simpa using hB q⟩

/-- Auxiliary to the Lean proof route.  Every derivative of a `Good` function
vanishes off `S`. -/
theorem Good.iteratedFDeriv_eq_zero {S : Set E} {Φ : E → F} (h : Good S Φ) (n : ℕ) {q : E}
    (hq : q ∉ S) : iteratedFDeriv ℝ n Φ q = 0 :=
  Function.notMem_support.1 fun hs => hq (h.supp (support_iteratedFDeriv_subset n hs))

/-- Auxiliary to the Lean proof route.  A `Good` function vanishes off `S`. -/
theorem Good.eq_zero {S : Set E} {Φ : E → F} (h : Good S Φ) {q : E} (hq : q ∉ S) : Φ q = 0 :=
  image_eq_zero_of_notMem_tsupport fun hs => hq (h.supp hs)

omit [NormedSpace ℝ E] in
/-- Auxiliary to the Lean proof route.  The pointwise domination
`|w y| ‖G(p - τ y)‖ ≤ B g y` for `G` bounded by `B` and vanishing off `S`. -/
theorem wbound {G : Type} [NormedAddCommGroup G] {τ : Y → E} {w : Y → ℝ} {S : Set E}
    {Φ : E → G} {B : ℝ} (hB : ∀ q, ‖Φ q‖ ≤ B) (h0 : ∀ q ∉ S, Φ q = 0) {g : Y → ℝ}
    (hg0 : ∀ y, 0 ≤ g y) {p : E} (hp : ∀ y, p - τ y ∈ S → |w y| ≤ g y) (y : Y) :
    |w y| * ‖Φ (p - τ y)‖ ≤ B * g y := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB p)
  by_cases hS : p - τ y ∈ S
  · rw [mul_comm B]
    exact mul_le_mul (hp y hS) (hB _) (norm_nonneg _) (hg0 y)
  · rw [h0 _ hS, norm_zero, mul_zero]
    exact mul_nonneg hB0 (hg0 y)

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Y]

omit [NormedSpace ℝ E] in
/-- Auxiliary to the Lean proof route.  Measurability of the integrand. -/
theorem meas_integrand {ν : Measure Y} {τ : Y → E} {w : Y → ℝ} (hτ : Measurable τ)
    (hw : AEStronglyMeasurable w ν) {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {Φ : E → G} (hΦ : Continuous Φ) (p : E) :
    AEStronglyMeasurable (fun y => w y • Φ (p - τ y)) ν :=
  hw.smul (hΦ.comp_aestronglyMeasurable (measurable_const.sub hτ).aestronglyMeasurable)

variable {ν : Measure Y} {τ : Y → E} {w : Y → ℝ} {S : Set E}

/-- Auxiliary to the Lean proof route.  The integrand of `tInt` is integrable
(so `tInt` is a genuine integral). -/
theorem integrable_tInt (hτ : Measurable τ) (hw : AEStronglyMeasurable w ν)
    (hdom : Dominated ν τ w S) {Φ : E → F} (h : Good S Φ) (p : E) :
    Integrable (fun y => w y • Φ (p - τ y)) ν := by
  obtain ⟨g, hg, hg0, hgb⟩ := hdom p
  obtain ⟨B, hB⟩ := h.norm_le
  refine Integrable.mono' (hg.const_mul B) (meas_integrand hτ hw h.smooth.continuous p)
    (ae_of_all _ fun y => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact wbound hB (fun q hq => h.eq_zero hq) hg0
    (hgb p (mem_ball_self one_pos)) y

/-- Auxiliary to the Lean proof route.  Differentiation under the integral:
`D(∫ w Φ(· - τ)) = ∫ w DΦ(· - τ)` (TeX lines 103-104 and 113-114). -/
theorem hasFDerivAt_tInt (hτ : Measurable τ) (hw : AEStronglyMeasurable w ν)
    (hdom : Dominated ν τ w S) {Φ : E → F} (h : Good S Φ) (p₀ : E) :
    HasFDerivAt (tInt ν τ w Φ) (tInt ν τ w (fderiv ℝ Φ) p₀) p₀ := by
  obtain ⟨g, hg, hg0, hgb⟩ := hdom p₀
  have h1 := h.fderiv
  obtain ⟨B1, hB1⟩ := h1.norm_le
  have hd : Differentiable ℝ Φ := h.smooth.differentiable (by simp)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun p y => w y • Φ (p - τ y)) (F' := fun p y => w y • fderiv ℝ Φ (p - τ y))
    (bound := fun y => B1 * g y)
    (ball_mem_nhds p₀ one_pos)
    (Filter.Eventually.of_forall fun p => meas_integrand hτ hw h.smooth.continuous p)
    (integrable_tInt hτ hw hdom h p₀)
    (meas_integrand hτ hw h1.smooth.continuous p₀)
    (ae_of_all _ fun y p hp => ?_) (hg.const_mul B1) (ae_of_all _ fun y p _ => ?_)
  · rw [norm_smul, Real.norm_eq_abs]
    exact wbound hB1 (fun q hq => h1.eq_zero hq) hg0
      (hgb p hp) y
  · have := ((hd (p - τ y)).hasFDerivAt.comp p ((hasFDerivAt_id p).sub_const (τ y))).const_smul
      (w y)
    rw [ContinuousLinearMap.comp_id] at this
    exact this

/-- Auxiliary to the Lean proof route.  `fderiv (tInt Φ) = tInt (fderiv Φ)`. -/
theorem fderiv_tInt (hτ : Measurable τ) (hw : AEStronglyMeasurable w ν)
    (hdom : Dominated ν τ w S) {Φ : E → F} (h : Good S Φ) :
    fderiv ℝ (tInt ν τ w Φ) = tInt ν τ w (fderiv ℝ Φ) :=
  funext fun p => (hasFDerivAt_tInt hτ hw hdom h p).fderiv

/-- Auxiliary to the Lean proof route.  `tInt Φ` is `C^n` for every `n`. -/
theorem contDiff_tInt_nat (hτ : Measurable τ) (hw : AEStronglyMeasurable w ν)
    (hdom : Dominated ν τ w S) (n : ℕ) :
    ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {Φ : E → F}, Good S Φ →
      ContDiff ℝ n (tInt ν τ w Φ) := by
  induction n with
  | zero =>
    intro F _ _ Φ h
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun p =>
      (hasFDerivAt_tInt hτ hw hdom h p).continuousAt)
  | succ n ih =>
    intro F _ _ Φ h
    have e : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; rfl
    rw [e, contDiff_succ_iff_fderiv]
    refine ⟨fun p => (hasFDerivAt_tInt hτ hw hdom h p).differentiableAt, fun hn => ?_, ?_⟩
    · exact absurd hn (by simp)
    · rw [fderiv_tInt hτ hw hdom h]
      exact ih h.fderiv

/-- Auxiliary to the Lean proof route.  `tInt Φ` is `C^∞`. -/
theorem contDiff_tInt (hτ : Measurable τ) (hw : AEStronglyMeasurable w ν)
    (hdom : Dominated ν τ w S) {Φ : E → F} (h : Good S Φ) : ContDiff ℝ ∞ (tInt ν τ w Φ) :=
  contDiff_infty.2 fun n => contDiff_tInt_nat hτ hw hdom n h

/-- Auxiliary to the Lean proof route.  Every derivative falls on `Φ`:
`‖D^n(tInt Φ)(p)‖ ≤ ∫ |w y| ‖D^n Φ(p - τ y)‖ ν(dy)`. -/
theorem norm_iteratedFDeriv_tInt_le (hτ : Measurable τ) (hw : AEStronglyMeasurable w ν)
    (hdom : Dominated ν τ w S) (n : ℕ) :
    ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {Φ : E → F}, Good S Φ → ∀ p,
      ‖iteratedFDeriv ℝ n (tInt ν τ w Φ) p‖ ≤
        ∫ y, |w y| * ‖iteratedFDeriv ℝ n Φ (p - τ y)‖ ∂ν := by
  induction n with
  | zero =>
    intro F _ _ Φ h p
    simp only [norm_iteratedFDeriv_zero]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1; funext y; rw [norm_smul, Real.norm_eq_abs]
  | succ n ih =>
    intro F _ _ Φ h p
    rw [← norm_iteratedFDeriv_fderiv, fderiv_tInt hτ hw hdom h]
    refine (ih h.fderiv p).trans (le_of_eq ?_)
    simp_rw [norm_iteratedFDeriv_fderiv]

end engine

/-! ### Step 1: the spatial convolution `F(u,x) = (Γ * Ψ(u,·))(x)` -/

variable {d : ℕ}

/-- Auxiliary to the Lean proof route.  The spatial translation `y ↦ (0,y)`. -/
def τ₁ (y : Rd d) : ℝ × Rd d := (0, y)

/-- Auxiliary to the Lean proof route.  The set `{|z| ≤ R}` of `ℝ × ℝ^d`. -/
def S₁ (R : ℝ) : Set (ℝ × Rd d) := {q | ‖q.2‖ ≤ R}

/-- Auxiliary to the Lean proof route.  The time slab `{u ∈ [0,1]}`. -/
def S₂ : Set (ℝ × Rd d) := {q | q.1 ∈ Icc (0 : ℝ) 1}

/-- Auxiliary to the Lean proof route.  The time translation `r ↦ (r,0)`. -/
def τ₂ (r : ℝ) : ℝ × Rd d := (r, 0)

/-- Auxiliary to the Lean proof route.  The time weight `|r|^{-a}`. -/
def w₂ (a r : ℝ) : ℝ := |r| ^ (-a)

/-- Auxiliary to the Lean proof route.  `τ₁` is measurable. -/
theorem measurable_τ₁ : Measurable (τ₁ (d := d)) :=
  (continuous_const.prodMk continuous_id).measurable

/-- Auxiliary to the Lean proof route.  `τ₂` is measurable. -/
theorem measurable_τ₂ : Measurable (τ₂ (d := d)) :=
  (continuous_id.prodMk continuous_const).measurable

/-- Auxiliary to the Lean proof route.  Step 1 is the convolution:
`tInt Γ τ₁ 1 Ψ (u,x) = (Γ * Ψ(u,·))(x)`. -/
theorem tInt_one_eq_conv (Γ : Measure (Rd d)) (Ψ : ℝ × Rd d → ℝ) (u : ℝ) (x : Rd d) :
    tInt Γ τ₁ (fun _ => (1 : ℝ)) Ψ (u, x) = conv Γ (fun y => Ψ (u, y)) x := by
  simp [tInt, conv, τ₁]

/-- Auxiliary to the Lean proof route.  If `‖G q‖ ≤ B` and `G(u,z) = 0` for
`|z| > R`, then `‖G(u,z)‖ ≤ B e^{R²/2} e^{-|z|²/2}` (TeX lines 99-101, for every
derivative `D`). -/
theorem pt_bound_norm {G : Type} [NormedAddCommGroup G] {Φ : ℝ × Rd d → G} {B R : ℝ}
    (hB : ∀ q, ‖Φ q‖ ≤ B) (hR : ∀ u z, R < ‖z‖ → Φ (u, z) = 0) (u : ℝ) (z : Rd d) :
    ‖Φ (u, z)‖ ≤ B * Real.exp (R ^ 2 / 2) * Real.exp (-(‖z‖ ^ 2 / 2)) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB (u, z))
  by_cases hz : ‖z‖ ≤ R
  · calc ‖Φ (u, z)‖ ≤ B := hB _
      _ ≤ B * (Real.exp (R ^ 2 / 2) * Real.exp (-(‖z‖ ^ 2 / 2))) :=
          le_mul_of_one_le_right hB0 (one_le_gauss hz)
      _ = _ := by ring
  · rw [hR u z (not_le.1 hz), norm_zero]
    positivity

/-- Auxiliary to the Lean proof route.  A control in `CPos` is `Good` on a
spatial ball `{|z| ≤ R}`. -/
theorem good_ctrl {Ψ : ℝ × Rd d → ℝ} (hΨ : Ψ ∈ CPos d) :
    ∃ R : ℝ, 0 ≤ R ∧ Good (S₁ (d := d) R) Ψ := by
  obtain ⟨hs, hc, -, -, -⟩ := hΨ
  obtain ⟨R, hR0, hR⟩ := exists_radius hc
  refine ⟨R, hR0, hs, closure_minimal (fun q hq => ?_)
    (isClosed_le continuous_snd.norm continuous_const), fun n => ?_⟩
  · by_contra h
    exact hq (hR q.1 q.2 (not_le.1 h))
  · obtain ⟨B, hB⟩ := (hs.continuous_iteratedFDeriv (m := n)
      (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (hc.iteratedFDeriv n)
    exact ⟨B, hB⟩

section step1
variable {Γ μ : Measure (Rd d)} (hΓt : IsTempered Γ) (hμt : IsTempered μ)
  (hsp : IsSpectralMeasure Γ μ)
include hΓt hμt hsp

/-- Auxiliary to the Lean proof route.  Step 1 domination: near `(u₀,x₀)` the
translates with `|x - y| ≤ R` are dominated by `e^{(R+1)²/2} e^{-|x₀-y|²/2}`,
which is `Γ`-integrable (`L:variational-heat-envelope` at `ε = 1`). -/
theorem dominated₁ (R : ℝ) : Dominated Γ τ₁ (fun _ => (1 : ℝ)) (S₁ (d := d) R) := by
  intro p₀
  refine ⟨fun y => Real.exp ((R + 1) ^ 2 / 2) * Real.exp (-(‖p₀.2 - y‖ ^ 2 / 2)),
    (gauss_conv hΓt hμt hsp p₀.2).1.const_mul _, fun y => by positivity, fun p hp y hy => ?_⟩
  rw [abs_one]
  apply one_le_gauss
  have h1 : ‖p.2 - p₀.2‖ < 1 := by
    have := norm_snd_le (p - p₀)
    rw [mem_ball, dist_eq_norm] at hp
    simpa using this.trans_lt hp
  have h2 : ‖p.2 - y‖ ≤ R := by simpa [S₁, τ₁] using hy
  calc ‖p₀.2 - y‖ = ‖(p.2 - y) - (p.2 - p₀.2)‖ := by congr 1; abel
    _ ≤ ‖p.2 - y‖ + ‖p.2 - p₀.2‖ := norm_sub_le _ _
    _ ≤ R + 1 := by linarith

/-- Auxiliary to the Lean proof route.  The convolution `F = tInt Γ τ₁ 1 Ψ` is
`Good` on the time slab `[0,1] × ℝ^d`, with every derivative bounded on all of
`ℝ × ℝ^d` (TeX lines 99-104). -/
theorem good_conv {Ψ : ℝ × Rd d → ℝ} (hΨ : Ψ ∈ CPos d) :
    Good (S₂ (d := d)) (tInt Γ τ₁ (fun _ => (1 : ℝ)) Ψ) := by
  obtain ⟨R, -, hg⟩ := good_ctrl hΨ
  have hdom := dominated₁ hΓt hμt hsp (d := d) R
  have hw : AEStronglyMeasurable (fun _ : Rd d => (1 : ℝ)) Γ := aestronglyMeasurable_const
  refine ⟨contDiff_tInt measurable_τ₁ hw hdom hg, closure_minimal (fun q hq => ?_)
    (isClosed_Icc.preimage continuous_fst), fun n => ?_⟩
  · by_contra h
    apply hq
    have h' : q.1 ∉ Ioo (0 : ℝ) 1 := fun h'' => h (Ioo_subset_Icc_self h'')
    rw [show q = (q.1, q.2) from rfl, tInt_one_eq_conv]
    exact conv_eq_zero_of_time hΨ.2.2.1 h' q.2
  · obtain ⟨B, hB⟩ := hg.bdd n
    refine ⟨B * Real.exp (R ^ 2 / 2) * gMass Γ, fun p => ?_⟩
    have hpt : ∀ y, |(1 : ℝ)| * ‖iteratedFDeriv ℝ n Ψ (p - τ₁ y)‖ ≤
        B * Real.exp (R ^ 2 / 2) * Real.exp (-(‖p.2 - y‖ ^ 2 / 2)) := by
      intro y
      rw [abs_one, one_mul]
      have e : p - τ₁ y = (p.1, p.2 - y) := by ext <;> simp [τ₁]
      rw [e]
      exact pt_bound_norm hB (fun u z hz => hg.iteratedFDeriv_eq_zero n
        (show (u, z) ∉ S₁ R by simpa [S₁] using hz)) p.1 (p.2 - y)
    have hgc := gauss_conv hΓt hμt hsp p.2
    refine (norm_iteratedFDeriv_tInt_le measurable_τ₁ hw hdom n hg p).trans ?_
    refine (integral_mono_of_nonneg (ae_of_all _ fun y => by positivity)
      (hgc.1.const_mul (B * Real.exp (R ^ 2 / 2))) (ae_of_all _ hpt)).trans ?_
    rw [integral_const_mul]
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB p)
    exact mul_le_mul_of_nonneg_left hgc.2 (by positivity)

end step1

/-! ### Step 2: the time integral against `|r|^{-a}` -/

/-- Auxiliary to the Lean proof route.  For `a < 1`, `r ↦ |r|^{-a}` is
integrable on `(-T, T)` (TeX lines 111-113, on any bounded interval). -/
theorem abs_rpow_integrableOn_Ioo {a : ℝ} (ha : a < 1) (T : ℝ) :
    IntegrableOn (fun r : ℝ => |r| ^ (-a)) (Ioo (-T) T) := by
  rcases le_or_gt T 0 with hT | hT
  · rw [Ioo_eq_empty (by linarith)]; exact integrableOn_empty
  have hpos : IntegrableOn (fun r : ℝ => |r| ^ (-a)) (Ioo 0 T) := by
    have := (intervalIntegral.integrableOn_Ioo_rpow_iff (s := -a) hT).2 (by linarith)
    refine this.congr_fun (fun r hr => ?_) measurableSet_Ioo
    simp [abs_of_pos hr.1]
  have hneg : IntegrableOn (fun r : ℝ => |r| ^ (-a)) (Ioo (-T) 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Ioo, neg_neg, neg_zero]
    exact hpos
  have hu : Ioo (-T) T ⊆ Ioo (-T) 0 ∪ {0} ∪ Ioo 0 T := by
    intro r hr
    rcases lt_trichotomy r 0 with h | h | h
    · exact Or.inl (Or.inl ⟨hr.1, h⟩)
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨h, hr.2⟩
  refine IntegrableOn.mono_set ?_ hu
  refine (hneg.union ?_).union hpos
  exact integrableOn_singleton (by simp) (by simp)

/-- Auxiliary to the Lean proof route.  `w₂ a` is measurable. -/
theorem measurable_w₂ (a : ℝ) : Measurable (w₂ a) :=
  continuous_abs.measurable.pow_const _

/-- Auxiliary to the Lean proof route.  Translates `(s,x) - (r,0)` landing in
the time slab have `|r| < T` once `|s| < T - 1`, and then `|w₂ r| ≤`
the truncated kernel. -/
theorem slab_bound {a T : ℝ} {p : ℝ × Rd d} (hp : |p.1| < T - 1) (r : ℝ)
    (hr : p - τ₂ r ∈ S₂ (d := d)) :
    |w₂ a r| ≤ (Ioo (-T) T).indicator (fun r => |r| ^ (-a)) r := by
  have h : p.1 - r ∈ Icc (0 : ℝ) 1 := by simpa [S₂, τ₂] using hr
  have hr' : r ∈ Ioo (-T) T := by
    rw [abs_lt] at hp
    exact ⟨by linarith [h.2], by linarith [h.1]⟩
  rw [indicator_of_mem hr', w₂, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]

/-- Auxiliary to the Lean proof route.  Step 2 domination: near `(s₀,x₀)` the
kernel on the relevant `r` is dominated by `|r|^{-a}` on `(-(|s₀|+3), |s₀|+3)`. -/
theorem dominated₂ {a : ℝ} (ha : a < 1) :
    Dominated (volume : Measure ℝ) τ₂ (w₂ a) (S₂ (d := d)) := by
  intro p₀
  refine ⟨(Ioo (-(|p₀.1| + 3)) (|p₀.1| + 3)).indicator (fun r => |r| ^ (-a)),
    (abs_rpow_integrableOn_Ioo ha _).integrable_indicator measurableSet_Ioo,
    fun r => indicator_nonneg (fun r _ => Real.rpow_nonneg (abs_nonneg r) _) r,
    fun p hp r hr => slab_bound ?_ r hr⟩
  have h1 : |p.1 - p₀.1| < 1 := by
    have := norm_fst_le (p - p₀)
    rw [mem_ball, dist_eq_norm] at hp
    simpa [Real.norm_eq_abs] using this.trans_lt hp
  have := abs_sub_abs_le_abs_sub p.1 p₀.1
  linarith

/-- Auxiliary to the Lean proof route.  The change of variables `r = s - u` of
TeX lines 105-109, for every real `s`:
`h_s(x) = ∫ |r|^{-a} F((s,x) - (r,0)) dr` with `F = Γ * Ψ`. -/
theorem mean_eq_tInt {Γ : Measure (Rd d)} {Ψ : ℝ × Rd d → ℝ}
    (ht : tsupport Ψ ⊆ Ioo (0 : ℝ) 1 ×ˢ univ) (a s : ℝ) (x : Rd d) :
    mean a Γ Ψ s x = tInt volume τ₂ (w₂ a) (tInt Γ τ₁ (fun _ => (1 : ℝ)) Ψ) (s, x) := by
  set G : ℝ → ℝ := fun u => |s - u| ^ (-a) * conv Γ (fun y => Ψ (u, y)) x with hG
  have h1 : mean a Γ Ψ s x = ∫ u, G u := by
    rw [mean]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun u hu => by simp only [conv_eq_zero_of_time ht hu, mul_zero])
  have h2 : ∫ u, G u = ∫ r, G (s - r) := (integral_sub_left_eq_self G volume s).symm
  rw [h1, h2, tInt]
  congr 1; funext r
  have e : (s, x) - τ₂ r = (s - r, x) := by simp [τ₂]
  rw [e, tInt_one_eq_conv, smul_eq_mul, w₂]
  simp only [hG, sub_sub_cancel]

/-! ### `L:variational-global-mean`, first sentence -/

section mean
variable {Γ μ : Measure (Rd d)} (hΓt : IsTempered Γ) (hμt : IsTempered μ)
  (hsp : IsSpectralMeasure Γ μ)
include hΓt hμt hsp

/-- **`L:variational-global-mean`, first sentence**, general form: for tempered
`Γ`, `μ` with the spectral convention, `Ψ ∈ CPos` and `a < 1`, the map
`(s,x) ↦ h_s(x)` is `C^∞` on `ℝ × ℝ^d`; for every real `s` and every `x` the
integrand defining `h_s(x)` is integrable on `(0,1)`; and for every order `n`
and every compact `K ⊆ ℝ` there is a finite `C ≥ 0` with
`‖D^n h(s,x)‖ ≤ C` for all `s ∈ K`, `x ∈ ℝ^d` (every mixed time and space
derivative is globally bounded in space, uniformly on compact time sets). -/
theorem mean_derivatives {Ψ : ℝ × Rd d → ℝ} (hΨ : Ψ ∈ CPos d) {a : ℝ} (ha : a < 1) :
    ContDiff ℝ ∞ (fun p : ℝ × Rd d => mean a Γ Ψ p.1 p.2) ∧
    (∀ s x, IntegrableOn (fun u => |s - u| ^ (-a) * conv Γ (fun y => Ψ (u, y)) x)
      (Ioo 0 1)) ∧
    ∀ n : ℕ, ∀ K : Set ℝ, IsCompact K → ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ K, ∀ x : Rd d,
      ‖iteratedFDeriv ℝ n (fun p : ℝ × Rd d => mean a Γ Ψ p.1 p.2) (s, x)‖ ≤ C := by
  have hF := good_conv hΓt hμt hsp hΨ
  have hdom := dominated₂ (d := d) ha
  have hw : AEStronglyMeasurable (w₂ a) (volume : Measure ℝ) :=
    (measurable_w₂ a).aestronglyMeasurable
  have heq : (fun p : ℝ × Rd d => mean a Γ Ψ p.1 p.2) =
      tInt volume τ₂ (w₂ a) (tInt Γ τ₁ (fun _ => (1 : ℝ)) Ψ) :=
    funext fun p => mean_eq_tInt hΨ.2.2.1 a p.1 p.2
  refine ⟨by rw [heq]; exact contDiff_tInt measurable_τ₂ hw hdom hF, fun s x => ?_,
    fun n K hK => ?_⟩
  · set H : ℝ → ℝ := fun r => |r| ^ (-a) * conv Γ (fun y => Ψ (s - r, y)) x with hHdef
    have hH : Integrable H := by
      refine (integrable_tInt measurable_τ₂ hw hdom hF (s, x)).congr
        (ae_of_all _ fun r => ?_)
      have e : (s, x) - τ₂ r = (s - r, x) := by simp [τ₂]
      simp only [hHdef, e, tInt_one_eq_conv, smul_eq_mul, w₂]
    have := ((integrable_comp_sub_left H s).2 hH).integrableOn (s := Ioo (0 : ℝ) 1)
    refine this.congr_fun (fun u _ => ?_) measurableSet_Ioo
    simp only [hHdef, sub_sub_cancel]
  · obtain ⟨T, hT⟩ := hK.isBounded.exists_norm_le
    obtain ⟨B, hB⟩ := hF.bdd n
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
    set T' : ℝ := |T| + 2 with hT'
    have hI := abs_rpow_integrableOn_Ioo ha T'
    refine ⟨B * ∫ r in Ioo (-T') T', |r| ^ (-a),
      mul_nonneg hB0 (setIntegral_nonneg measurableSet_Ioo fun r _ =>
        Real.rpow_nonneg (abs_nonneg r) _), fun s hs x => ?_⟩
    have hsT : |((s, x) : ℝ × Rd d).1| < T' - 1 := by
      have := hT s hs
      rw [Real.norm_eq_abs] at this
      simp only [hT']
      linarith [le_abs_self T]
    have hpt := wbound (τ := τ₂ (d := d)) (w := w₂ a) hB
      (fun q hq => hF.iteratedFDeriv_eq_zero n hq)
      (g := (Ioo (-T') T').indicator (fun r => |r| ^ (-a)))
      (fun r => indicator_nonneg (fun r _ => Real.rpow_nonneg (abs_nonneg r) _) r)
      (fun r hr => slab_bound hsT r hr)
    rw [heq]
    refine (norm_iteratedFDeriv_tInt_le measurable_τ₂ hw hdom n hF (s, x)).trans ?_
    refine (integral_mono_of_nonneg (ae_of_all _ fun r => by positivity)
      ((hI.integrable_indicator measurableSet_Ioo).const_mul B)
      (ae_of_all _ hpt)).trans (le_of_eq ?_)
    rw [integral_const_mul, integral_indicator measurableSet_Ioo]

/-- **`L:variational-global-mean`, first sentence, for mixed partial
derivatives**: under the hypotheses of `mean_derivatives`, for every order `n`
and compact `K` there is `C ≥ 0` such that for all directions
`v₁,…,vₙ ∈ ℝ × ℝ^d` (e.g. the time direction `(1,0)` and space directions
`(0,e_j)`), `|D^n h(s,x)(v₁,…,vₙ)| ≤ C ∏ ‖vᵢ‖` for `s ∈ K`, `x ∈ ℝ^d`. -/
theorem mean_partial_bound {Ψ : ℝ × Rd d → ℝ} (hΨ : Ψ ∈ CPos d) {a : ℝ} (ha : a < 1)
    (n : ℕ) {K : Set ℝ} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ K, ∀ x : Rd d, ∀ v : Fin n → ℝ × Rd d,
      |iteratedFDeriv ℝ n (fun p : ℝ × Rd d => mean a Γ Ψ p.1 p.2) (s, x) v| ≤
        C * ∏ i, ‖v i‖ := by
  obtain ⟨-, -, h⟩ := mean_derivatives hΓt hμt hsp hΨ ha
  obtain ⟨C, hC, hb⟩ := h n K hK
  refine ⟨C, hC, fun s hs x v => ?_⟩
  rw [← Real.norm_eq_abs]
  exact ((iteratedFDeriv ℝ n (fun p : ℝ × Rd d => mean a Γ Ψ p.1 p.2) (s, x)).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (hb s hs x) (Finset.prod_nonneg fun i _ => norm_nonneg _))

end mean

/-! ### The manuscript's statements -/

/-- **`L:variational-global-mean`, first sentence** (TeX lines 87-88), with the
section's standing hypotheses (line 4: a nonzero covariance satisfying
`H:homog`, `a = α₀`) and `Ψ ∈ CPos`: `(s,x) ↦ h_s(x)` is `C^∞` on `ℝ × ℝ^d`,
every integrand defining `h_s(x)` is integrable (every real `s`), and every
derivative of every order is bounded on `K × ℝ^d` for every compact `K ⊆ ℝ`.
`Γ ≠ 0` and the fields of `H:homog` other than `Γ_tempered`, `μ_tempered`,
`spectral`, `alpha0_lt_one` are carried, unused. -/
theorem variational_global_mean_derivatives_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (_hΓ0 : Γ ≠ 0) {Ψ : ℝ × Rd d → ℝ}
    (hΨ : Ψ ∈ CPos d) :
    ContDiff ℝ ∞ (fun p : ℝ × Rd d => mean alpha0 Γ Ψ p.1 p.2) ∧
    (∀ s x, IntegrableOn (fun u => |s - u| ^ (-alpha0) * conv Γ (fun y => Ψ (u, y)) x)
      (Ioo 0 1)) ∧
    ∀ n : ℕ, ∀ K : Set ℝ, IsCompact K → ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ K, ∀ x : Rd d,
      ‖iteratedFDeriv ℝ n (fun p : ℝ × Rd d => mean alpha0 Γ Ψ p.1 p.2) (s, x)‖ ≤ C :=
  mean_derivatives hH.Γ_tempered hH.μ_tempered hH.spectral hΨ hH.alpha0_lt_one

/-- **`L:variational-global-mean`** (TeX lines 85-95), every conclusion, with
the section's standing hypotheses and `Ψ ∈ CPos`: (1) the first sentence
(`variational_global_mean_derivatives_paper`): `(s,x) ↦ h_s(x)` is `C^∞`, its
integrands are integrable for every `s`, and every derivative is bounded on
`K × ℝ^d` for every compact `K`; (2) the display `E:variational-global-mean` on
`I = [0,1]`: real `M, C_Ψ ≥ 0` with `0 ≤ h_s(x) ≤ M` and
`|h_s(x) - h_t(x)| ≤ C_Ψ |s - t|` for all `s, t ∈ I`, `x` (the sup-norm bound,
pointwise; from `VariationalMean.variational_global_mean_paper`).  `Γ ≠ 0` is
carried, unused. -/
theorem variational_global_mean_whole_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ0 : Γ ≠ 0) {Ψ : ℝ × Rd d → ℝ}
    (hΨ : Ψ ∈ CPos d) :
    (ContDiff ℝ ∞ (fun p : ℝ × Rd d => mean alpha0 Γ Ψ p.1 p.2) ∧
      (∀ s x, IntegrableOn (fun u => |s - u| ^ (-alpha0) * conv Γ (fun y => Ψ (u, y)) x)
        (Ioo 0 1)) ∧
      ∀ n : ℕ, ∀ K : Set ℝ, IsCompact K → ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ K, ∀ x : Rd d,
        ‖iteratedFDeriv ℝ n (fun p : ℝ × Rd d => mean alpha0 Γ Ψ p.1 p.2) (s, x)‖ ≤ C) ∧
    ∃ M CΨ : ℝ, 0 ≤ M ∧ 0 ≤ CΨ ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ x, 0 ≤ mean alpha0 Γ Ψ s x ∧ mean alpha0 Γ Ψ s x ≤ M) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
        |mean alpha0 Γ Ψ s x - mean alpha0 Γ Ψ t x| ≤ CΨ * |s - t|) := by
  obtain ⟨M, C, hM, hC, -, -, h3, h4, -, -⟩ :=
    VariationalMean.variational_global_mean_paper hH hΓ0 hΨ
  exact ⟨variational_global_mean_derivatives_paper hH hΓ0 hΨ, M, C, hM, hC, h3, h4⟩

end StratonovichHAMSecondMoment.VariationalMeanDerivatives
