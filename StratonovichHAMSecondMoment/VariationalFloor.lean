module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Foundations for the variational rates of
`notes/integrated_unmasked_variational.tex` (Section
`S:unmasked-variational`) and of `notes/integrated_spatial_occupation.tex`
(Section `S:spatial-occupation-foundation`), at revision a284420.  These are
the five deterministic foundations of wave L6 (item L6-d); they carry no
manuscript label of their own and are stated as general lemmas with every
hypothesis explicit.  Exported for use (as hypotheses, instantiated at
integration) by the items that formalize `L:spatial-static-controls` and
`P:spatial-smooth-ratio`.

* (F1) `dilation_floor`, `rayleighSet_floor`: the dilation floor.  For a
  nonzero locally finite `Γ` with the set scaling `Γ(cA) = c^{d-α} Γ(A)` of
  `H:homog` and `α < 2`, and a continuous, nonnegative, nonzero, compactly
  supported `z` with `y ↦ z(x - y)` `Γ`-integrable for every `x`, there are one
  unit test `f ∈ C_c^∞` with an `L²` weak gradient `g` and one `ε > 0` such that
  `∫ V f² - ∫ ‖g‖² ≥ ε` for every potential `V ≥ Γ * z` with `V f²`
  integrable.  Hence the real Rayleigh value set `WeakSobolev.rayleighSet V`
  of `E:variational-real-rayleigh` contains a positive element.  The test is
  the dilation `U_ℓ φ/‖φ‖₂` of a fixed bump, with small `ℓ`; the potential term
  is at least `ℓ^α (∫ z) Γ(B̄₁)/‖φ‖₂²` (Tonelli and the scaling of `Γ` on
  balls) and the gradient term is `ℓ² ‖∇φ‖₂²/‖φ‖₂²`.  This is the elementary
  scaling principle behind the positivity in `P:variational-unmasked-rate`
  (TeX lines 150-155), which the manuscript obtains instead from the compact
  trial of `P:compact-original-common-trial`; it is a pure inequality (no
  limit and no supremum is taken).
* (F2) `measure_ball_pos`, `measure_closedBall_pos`: `Γ(B_r) > 0` for every
  `r > 0` when `Γ ≠ 0` has the set scaling (exhaustion by balls plus scaling;
  the argument of `L:spatial-static-controls`, lines 89-91 of the occupation
  file).
* (F3) `autocorr_nonneg_of_posDef`: for real `Q ∈ C_c^∞`, the
  autocorrelation `c_Q = SpatialFourierBound.autocorr Q`
  (`c_Q(x) = ∫ Q(t) Q(t - x) dt`, the inner integral of `B_Γ(Q,Q)` in
  `E:spatial-physical-pair`) has `∫ c_Q dΓ ≥ 0` when `Γ` is positive definite
  in the sense of the field `Γ_posdef` of `H:homog`
  (`HomogHypothesis.IsPosDefDistr`), through
  `HasCompactSupport.toSchwartzMap` and the cast of the real pairing to `ℂ`;
  and `autocorr_pos` (strict positivity for nonnegative nonzero `Q`, no
  positive definiteness used).  The autocorrelation, its continuity, compact
  support and `Γ`-integrability are those of `SpatialFourierBound` (one
  definition, shared with `P:spatial-smooth-ratio`).
* (F4) `hasWeakGradient_of_test`: a test function has its classical gradient
  as weak gradient (`WeakSobolev.HasWeakGradient`).
* (F5) `ae_eq_zero_of_hasWeakGradient_zero`: for `d ≥ 1`, an `L²` function
  with zero weak gradient vanishes a.e. (half (b) of the D8-lite foundation;
  by mollification, not by the TeX's Fourier argument).

Also: `conv_pos` and `integral_pos_of_pos_zero` (positivity of integrals
against such `Γ`), used by `VariationalRate`.

Supplied inputs: none.  Every lemma is unconditional apart from its stated
hypotheses.  Lemmas marked "Auxiliary to the Lean proof route" serve only the
Lean proofs and are not TeX steps.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.HomogHypothesis
public import StratonovichHAMSecondMoment.WeakSobolev
public import StratonovichHAMSecondMoment.VariationalDilation
public import StratonovichHAMSecondMoment.SpatialFourierBound

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Metric
open scoped ContDiff Pointwise Convolution

namespace StratonovichHAMSecondMoment.VariationalFloor

open HomogHypothesis (Rd)
open WeakSobolev
open VariationalDilation (SetScaling conv)

variable {d : ℕ}

/-- **(F4)** A test function `f ∈ C_c^∞(ℝ^d; ℝ)` has its classical gradient
`x ↦ (Df(x))^♯` as weak gradient (integration by parts against a test
function). -/
theorem hasWeakGradient_of_test {f : Rd d → ℝ} (hf : IsTestFunction f) :
    HasWeakGradient f (fun x => (InnerProductSpace.toDual ℝ (Rd d)).symm (fderiv ℝ f x)) := by
  intro φ hφ v
  have hf1 : ContDiff ℝ 1 f := hf.1.of_le (by exact_mod_cast le_top)
  have hφ1 : ContDiff ℝ 1 φ := hφ.1.of_le (by exact_mod_cast le_top)
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := f)
    (g := φ) (v := v)
    ((hf1.continuous_fderiv one_ne_zero).clm_apply continuous_const |>.mul hφ1.continuous
      |>.integrable_of_hasCompactSupport hφ.2.mul_left)
    ((hf1.continuous).mul ((hφ1.continuous_fderiv one_ne_zero).clm_apply continuous_const)
      |>.integrable_of_hasCompactSupport (hf.2.mul_right))
    ((hf1.continuous.mul hφ1.continuous).integrable_of_hasCompactSupport hf.2.mul_right)
    (fun x _ => hf1.differentiable one_ne_zero x) (fun x _ => hφ1.differentiable one_ne_zero x)
  rw [key]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [InnerProductSpace.toDual_symm_apply]

/-- The classical gradient field `∇f = (Df)^♯` of a differentiable `f`. -/
def grad (f : Rd d → ℝ) (x : Rd d) : Rd d :=
  (InnerProductSpace.toDual ℝ (Rd d)).symm (fderiv ℝ f x)

/-- Auxiliary to the Lean proof route: the gradient field of a test function
is continuous. -/
theorem continuous_grad {f : Rd d → ℝ} (hf : IsTestFunction f) : Continuous (grad f) :=
  (InnerProductSpace.toDual ℝ (Rd d)).symm.continuous.comp
    (hf.1.continuous_fderiv (by simp))

/-- Auxiliary to the Lean proof route: the gradient field of a test function
has compact support. -/
theorem hasCompactSupport_grad {f : Rd d → ℝ} (hf : IsTestFunction f) :
    HasCompactSupport (grad f) :=
  (hf.2.fderiv ℝ).comp_left (by simp)

/-- Auxiliary to the Lean proof route: a test function lies in `L²`. -/
theorem memLp_test {f : Rd d → ℝ} (hf : IsTestFunction f) : MemLp f 2 volume :=
  hf.1.continuous.memLp_of_hasCompactSupport hf.2

/-- Auxiliary to the Lean proof route: the gradient field of a test function
lies in `L²`. -/
theorem memLp_grad {f : Rd d → ℝ} (hf : IsTestFunction f) : MemLp (grad f) 2 volume :=
  (continuous_grad hf).memLp_of_hasCompactSupport (hasCompactSupport_grad hf)

/-- Auxiliary to the Lean proof route: if `g` is a weak gradient of `f`, then
`c g` is a weak gradient of `c f`. -/
theorem hasWeakGradient_const_mul {f : Rd d → ℝ} {g : Rd d → Rd d}
    (h : HasWeakGradient f g) (c : ℝ) :
    HasWeakGradient (fun x => c * f x) (fun x => c • g x) := by
  intro φ hφ v
  have e := h φ hφ v
  simp_rw [real_inner_smul_left, mul_assoc]
  rw [integral_const_mul, integral_const_mul, e]
  ring

/-! ### (F2) Positive mass of balls -/

/-- **(F2)** For a nonzero measure with the set scaling of `H:homog`, every
centred open ball of positive radius has positive mass. -/
theorem measure_ball_pos {alpha : ℝ} {Γ : Measure (Rd d)} (hS : SetScaling alpha Γ)
    (hΓ : Γ ≠ 0) {r : ℝ} (hr : 0 < r) : 0 < Γ (ball (0 : Rd d) r) := by
  have hex : ∃ n : ℕ, Γ (ball (0 : Rd d) ((n : ℝ) + 1)) ≠ 0 := by
    by_contra h
    push Not at h
    apply hΓ
    have hu : (Set.univ : Set (Rd d)) = ⋃ n : ℕ, ball (0 : Rd d) ((n : ℝ) + 1) := by
      ext x
      simp only [Set.mem_univ, Set.mem_iUnion, mem_ball, dist_zero_right, true_iff]
      obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
      exact ⟨n, by linarith⟩
    have : Γ Set.univ = 0 := by
      rw [hu]; exact measure_iUnion_null h
    exact Measure.measure_univ_eq_zero.mp this
  obtain ⟨n, hn⟩ := hex
  set R : ℝ := (n : ℝ) + 1 with hR
  have hRpos : 0 < R := by positivity
  have hc : 0 < R / r := div_pos hRpos hr
  have hball : (R / r) • ball (0 : Rd d) r = ball 0 R := by
    rw [smul_ball hc.ne', smul_zero, Real.norm_eq_abs, abs_of_pos hc]
    congr 1; field_simp
  have := hS _ (measurableSet_ball (x := (0 : Rd d)) (ε := r)) (R / r) hc
  rw [hball] at this
  rw [this] at hn
  exact pos_iff_ne_zero.mpr (right_ne_zero_of_mul hn)

/-- (F2), closed-ball form. -/
theorem measure_closedBall_pos {alpha : ℝ} {Γ : Measure (Rd d)} (hS : SetScaling alpha Γ)
    (hΓ : Γ ≠ 0) {r : ℝ} (hr : 0 < r) : 0 < Γ (closedBall (0 : Rd d) r) :=
  (measure_ball_pos hS hΓ hr).trans_le (measure_mono ball_subset_closedBall)

/-! ### (F1) The dilation floor -/

/-- Auxiliary to the Lean proof route: the fixed profile `φ` of the floor test,
a smooth bump equal to `1` on the closed ball of radius `2`. -/
def floorBump (d : ℕ) : ContDiffBump (0 : Rd d) := ⟨2, 3, by norm_num, by norm_num⟩

/-- Auxiliary to the Lean proof route: the profile `φ` as a real function. -/
def prof (d : ℕ) (x : Rd d) : ℝ := floorBump d x

/-- Auxiliary to the Lean proof route: the profile is a test function. -/
theorem prof_test : IsTestFunction (prof d) :=
  ⟨(floorBump d).contDiff, (floorBump d).hasCompactSupport⟩

/-- Auxiliary to the Lean proof route: the profile is `1` on `‖x‖ ≤ 2`. -/
theorem prof_eq_one {x : Rd d} (hx : ‖x‖ ≤ 2) : prof d x = 1 :=
  (floorBump d).one_of_mem_closedBall (by rw [mem_closedBall, dist_zero_right]; exact hx)


/-- Auxiliary to the Lean proof route: `N = ∫ φ²`. -/
def profMass (d : ℕ) : ℝ := ∫ x, prof d x ^ 2

/-- Auxiliary to the Lean proof route: `N > 0`. -/
theorem profMass_pos : 0 < profMass d := by
  have hc : Continuous fun x => prof d x ^ 2 := (prof_test (d := d)).1.continuous.pow 2
  refine hc.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0)
    ((prof_test (d := d)).2.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num))
    (fun x => sq_nonneg _) ?_
  simp [prof_eq_one (d := d) (x := 0) (by simp)]

/-- Auxiliary to the Lean proof route: the floor test `f_ℓ = U_ℓ φ / √N`. -/
def fl (ℓ : ℝ) (x : Rd d) : ℝ := (Real.sqrt (profMass d))⁻¹ * dilL2 ℓ (prof d) x

/-- Auxiliary to the Lean proof route: the weak gradient `g_ℓ = ℓ U_ℓ ∇φ / √N`
of `f_ℓ`. -/
def gl (ℓ : ℝ) (x : Rd d) : Rd d :=
  (Real.sqrt (profMass d))⁻¹ • (ℓ • dilL2 ℓ (grad (prof d)) x)

/-- Auxiliary to the Lean proof route: `(U_ℓ f)(x)² = ℓ^d f(ℓ x)²` for real `f`. -/
theorem sq_dilL2_real {ℓ : ℝ} (hℓ : 0 < ℓ) (f : Rd d → ℝ) (x : Rd d) :
    dilL2 ℓ f x ^ 2 = ℓ ^ d * f (ℓ • x) ^ 2 := by
  have := norm_dilL2_sq hℓ f x
  rwa [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, smul_eq_mul] at this

/-- Auxiliary to the Lean proof route: `f_ℓ(x)² = N⁻¹ ℓ^d φ(ℓ x)²`. -/
theorem fl_sq {ℓ : ℝ} (hℓ : 0 < ℓ) (x : Rd d) :
    fl ℓ x ^ 2 = (profMass d)⁻¹ * (ℓ ^ d * prof d (ℓ • x) ^ 2) := by
  have hN := profMass_pos (d := d)
  rw [fl, mul_pow, inv_pow, Real.sq_sqrt hN.le, sq_dilL2_real hℓ]

/-- Auxiliary to the Lean proof route: `f_ℓ` is a test function (`ℓ > 0`). -/
theorem fl_test {ℓ : ℝ} (hℓ : 0 < ℓ) : IsTestFunction (fl (d := d) ℓ) := by
  have e : fl (d := d) ℓ = fun x =>
      (Real.sqrt (profMass d))⁻¹ * (ℓ ^ ((d : ℝ) / 2) * prof d (ℓ • x)) := by
    funext x; simp [fl, dilL2]
  refine ⟨?_, ?_⟩
  · rw [e]
    exact contDiff_const.mul (contDiff_const.mul
      ((prof_test (d := d)).1.comp (contDiff_const_smul ℓ)))
  have h1 : HasCompactSupport (fun x : Rd d => prof d (ℓ • x)) :=
    (prof_test (d := d)).2.comp_smul hℓ.ne'
  rw [e]
  exact (h1.mul_left (f := fun _ => ℓ ^ ((d : ℝ) / 2))).mul_left

/-- Auxiliary to the Lean proof route: `∫ f_ℓ² = 1` (`ℓ > 0`). -/
theorem fl_unit {ℓ : ℝ} (hℓ : 0 < ℓ) : ∫ x, fl (d := d) ℓ x ^ 2 = 1 := by
  have hN := profMass_pos (d := d)
  have e : ∀ x, fl (d := d) ℓ x ^ 2 = (profMass d)⁻¹ * ‖dilL2 ℓ (prof d) x‖ ^ 2 := by
    intro x
    rw [fl, mul_pow, inv_pow, Real.sq_sqrt hN.le, Real.norm_eq_abs, sq_abs]
  simp_rw [e]
  rw [integral_const_mul, integral_norm_dilL2_sq hℓ]
  simp_rw [Real.norm_eq_abs, sq_abs]
  exact inv_mul_cancel₀ hN.ne'

/-- Auxiliary to the Lean proof route: `g_ℓ ∈ L²` (`ℓ > 0`). -/
theorem gl_memLp {ℓ : ℝ} (hℓ : 0 < ℓ) : MemLp (gl (d := d) ℓ) 2 volume := by
  have h1 : MemLp (dilL2 ℓ (grad (prof d))) 2 volume :=
    memLp_dilL2 (E := Rd d) hℓ (memLp_grad (prof_test (d := d)))
  have h2 := (h1.const_smul ℓ).const_smul (Real.sqrt (profMass d))⁻¹
  exact h2

/-- Auxiliary to the Lean proof route: `∫ ‖g_ℓ‖² = N⁻¹ ℓ² ∫ ‖∇φ‖²`
(`ℓ > 0`). -/
theorem gl_norm {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∫ x, ‖gl (d := d) ℓ x‖ ^ 2 = (profMass d)⁻¹ * ℓ ^ 2 * ∫ x, ‖grad (prof d) x‖ ^ 2 := by
  have hN := profMass_pos (d := d)
  have e : ∀ x, ‖gl (d := d) ℓ x‖ ^ 2 =
      (profMass d)⁻¹ * ℓ ^ 2 * ‖dilL2 ℓ (grad (prof d)) x‖ ^ 2 := by
    intro x
    rw [gl, norm_smul, norm_smul, mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
      sq_abs, inv_pow, Real.sq_sqrt hN.le, mul_assoc]
  simp_rw [e]
  rw [integral_const_mul, integral_norm_dilL2_sq hℓ]

/-- Auxiliary to the Lean proof route: `g_ℓ` is a weak gradient of `f_ℓ`
(`ℓ > 0`). -/
theorem gl_weak {ℓ : ℝ} (hℓ : 0 < ℓ) : HasWeakGradient (fl (d := d) ℓ) (gl ℓ) := by
  have h := hasWeakGradient_dilL2 hℓ (hasWeakGradient_of_test (prof_test (d := d)))
  exact hasWeakGradient_const_mul h _

/-- Auxiliary to the Lean proof route: the potential lower bound
`∫ V f_ℓ² ≥ ℓ^α (∫ z) Γ(B̄₁)/N` for every `V ≥ Γ * z` with `V f_ℓ²`
integrable, when `ℓ ≤ 1` and `ℓ R_z ≤ 1`. -/
theorem pot_lower {alpha : ℝ} {Γ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ]
    (hS : SetScaling alpha Γ) {z : Rd d → ℝ} (hzc : Continuous z) (hzs : HasCompactSupport z)
    (hz0 : ∀ x, 0 ≤ z x) (hzi : ∀ x, Integrable (fun y => z (x - y)) Γ) {Rz : ℝ}
    (hRz : ∀ y, Rz < ‖y‖ → z y = 0) {ℓ : ℝ} (hℓ : 0 < ℓ) (hRℓ : ℓ * Rz ≤ 1)
    (V : Rd d → ℝ) (hV : ∀ x, conv Γ z x ≤ V x)
    (hVi : Integrable (fun x => V x * fl ℓ x ^ 2) volume) :
    ℓ ^ alpha * ((∫ x, z x) * (Γ (closedBall 0 1)).toReal / profMass d) ≤
      ∫ x, V x * fl ℓ x ^ 2 := by
  have hN := profMass_pos (d := d)
  set c : ℝ := (profMass d)⁻¹ * ℓ ^ d with hc
  have hc0 : 0 ≤ c := mul_nonneg (inv_nonneg.2 hN.le) (pow_nonneg hℓ.le _)
  have hflc : Continuous (fl (d := d) ℓ) := (fl_test hℓ).1.continuous
  have hconv0 : ∀ x, 0 ≤ conv Γ z x := fun x => integral_nonneg fun y => hz0 _
  -- Step A: on the plateau the test is constant
  have hA : ∀ y ∈ closedBall (0 : Rd d) (1 / ℓ), ∀ x,
      z (x - y) * fl ℓ x ^ 2 = z (x - y) * c := by
    intro y hy x
    by_cases hzx : z (x - y) = 0
    · simp [hzx]
    · have h1 : ‖x - y‖ ≤ Rz := by
        by_contra h; exact hzx (hRz _ (lt_of_not_ge h))
      have h2 : ‖y‖ ≤ 1 / ℓ := by simpa using hy
      have h3 : ‖ℓ • x‖ ≤ 2 := by
        rw [norm_smul, Real.norm_of_nonneg hℓ.le]
        have : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by
          calc ‖x‖ = ‖y + (x - y)‖ := by congr 1; abel
            _ ≤ _ := norm_add_le _ _
        have h4 : ℓ * ‖y‖ ≤ 1 := by
          calc ℓ * ‖y‖ ≤ ℓ * (1 / ℓ) := mul_le_mul_of_nonneg_left h2 hℓ.le
            _ = 1 := by field_simp
        nlinarith [mul_le_mul_of_nonneg_left h1 hℓ.le]
      rw [fl_sq hℓ, prof_eq_one h3, hc]; ring
  -- Step B: Tonelli form of the left side
  have hB : ∀ x, ENNReal.ofReal (conv Γ z x * fl ℓ x ^ 2) =
      ∫⁻ y, ENNReal.ofReal (z (x - y) * fl ℓ x ^ 2) ∂Γ := by
    intro x
    rw [conv, ← integral_mul_const]
    exact ofReal_integral_eq_lintegral_ofReal ((hzi x).mul_const _)
      (Filter.Eventually.of_forall fun y => mul_nonneg (hz0 _) (sq_nonneg _))
  have hmeas : AEMeasurable (Function.uncurry fun (x : Rd d) (y : Rd d) =>
      ENNReal.ofReal (z (x - y) * fl ℓ x ^ 2)) (volume.prod Γ) := by
    refine (ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)).aemeasurable
    exact (hzc.comp (continuous_fst.sub continuous_snd)).mul ((hflc.comp continuous_fst).pow 2)
  have hswap := lintegral_lintegral_swap hmeas
  -- Step D: the inner integral on the ball
  have hz_int : Integrable z volume := hzc.integrable_of_hasCompactSupport hzs
  have hD : ∀ y ∈ closedBall (0 : Rd d) (1 / ℓ),
      ∫⁻ x, ENNReal.ofReal (z (x - y) * fl ℓ x ^ 2) =
        ENNReal.ofReal (c * ∫ x, z x) := by
    intro y hy
    have e : ∀ x, ENNReal.ofReal (z (x - y) * fl ℓ x ^ 2) =
        ENNReal.ofReal c * ENNReal.ofReal (z (x - y)) := by
      intro x; rw [hA y hy x, mul_comm, ENNReal.ofReal_mul hc0]
    simp_rw [e]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_sub_right_eq_self (fun x => ENNReal.ofReal (z x)) y,
      ← ofReal_integral_eq_lintegral_ofReal hz_int (Filter.Eventually.of_forall hz0),
      ← ENNReal.ofReal_mul hc0]
  -- Step E: the ball mass
  have hE : Γ (closedBall (0 : Rd d) (1 / ℓ)) =
      ENNReal.ofReal ((1 / ℓ) ^ ((d : ℝ) - alpha)) * Γ (closedBall 0 1) := by
    have hl : 0 < 1 / ℓ := by positivity
    have hb : (1 / ℓ) • closedBall (0 : Rd d) 1 = closedBall 0 (1 / ℓ) := by
      rw [smul_closedBall _ _ zero_le_one, smul_zero, Real.norm_eq_abs, abs_of_pos hl, mul_one]
    rw [← hb]
    exact hS _ (measurableSet_closedBall (x := (0 : Rd d)) (ε := 1)) _ hl
  have hfin : Γ (closedBall (0 : Rd d) 1) ≠ ⊤ := (isCompact_closedBall _ _).measure_lt_top.ne
  -- Step F: assemble
  have hlow : ENNReal.ofReal (c * ∫ x, z x) * Γ (closedBall (0 : Rd d) (1 / ℓ)) ≤
      ∫⁻ x, ENNReal.ofReal (V x * fl ℓ x ^ 2) := by
    calc ENNReal.ofReal (c * ∫ x, z x) * Γ (closedBall (0 : Rd d) (1 / ℓ))
        = ∫⁻ y, (closedBall (0 : Rd d) (1 / ℓ)).indicator
            (fun _ => ENNReal.ofReal (c * ∫ x, z x)) y ∂Γ := by
          rw [lintegral_indicator_const measurableSet_closedBall]
      _ ≤ ∫⁻ y, ∫⁻ x, ENNReal.ofReal (z (x - y) * fl ℓ x ^ 2) ∂volume ∂Γ := by
          refine lintegral_mono fun y => ?_
          by_cases hy : y ∈ closedBall (0 : Rd d) (1 / ℓ)
          · rw [Set.indicator_of_mem hy, hD y hy]
          · rw [Set.indicator_of_notMem hy]; exact bot_le
      _ = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (z (x - y) * fl ℓ x ^ 2) ∂Γ := hswap.symm
      _ = ∫⁻ x, ENNReal.ofReal (conv Γ z x * fl ℓ x ^ 2) := by simp_rw [hB]
      _ ≤ ∫⁻ x, ENNReal.ofReal (V x * fl ℓ x ^ 2) := by
          refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
          exact mul_le_mul_of_nonneg_right (hV x) (sq_nonneg _)
  have hVnn : 0 ≤ᵐ[volume] fun x => V x * fl ℓ x ^ 2 :=
    Filter.Eventually.of_forall fun x => mul_nonneg ((hconv0 x).trans (hV x)) (sq_nonneg _)
  rw [integral_eq_lintegral_of_nonneg_ae hVnn hVi.aestronglyMeasurable]
  have hmono := ENNReal.toReal_mono hVi.lintegral_lt_top.ne hlow
  refine le_trans (le_of_eq ?_) hmono
  rw [hE, ← mul_assoc, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal,
    ENNReal.toReal_ofReal (by positivity)]
  · have hpow : (ℓ : ℝ) ^ d * (1 / ℓ) ^ ((d : ℝ) - alpha) = ℓ ^ alpha := by
      rw [one_div, Real.inv_rpow hℓ.le, ← Real.rpow_neg hℓ.le, ← Real.rpow_natCast,
        ← Real.rpow_add hℓ]
      congr 1; ring
    rw [hc]
    calc ℓ ^ alpha * ((∫ x, z x) * (Γ (closedBall 0 1)).toReal / profMass d)
        = (profMass d)⁻¹ * (ℓ ^ d * (1 / ℓ) ^ ((d : ℝ) - alpha)) * (∫ x, z x) *
            (Γ (closedBall 0 1)).toReal := by rw [hpow]; field_simp
      _ = _ := by ring
  · exact mul_nonneg hc0 (integral_nonneg hz0)

/-- Auxiliary to the Lean proof route: a compactly supported function on
`ℝ^d` vanishes outside a centred ball of some radius `R ≥ 0`. -/
theorem exists_radius_fn {z : Rd d → ℝ} (hz : HasCompactSupport z) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ y, R < ‖y‖ → z y = 0 := by
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_closedBall (0 : Rd d)).1 hz.isCompact.isBounded
  refine ⟨max R 0, le_max_right _ _, fun y hy => ?_⟩
  by_contra h
  have hm := hR (subset_tsupport z h)
  rw [mem_closedBall, dist_zero_right] at hm
  linarith [le_max_left R 0]

/-- Auxiliary to the Lean proof route: a continuous, nonnegative, nonzero,
compactly supported function has positive Lebesgue integral. -/
theorem integral_pos_of_nonzero {z : Rd d → ℝ} (hzc : Continuous z) (hzs : HasCompactSupport z)
    (hz0 : ∀ x, 0 ≤ z x) (hzne : z ≠ 0) : 0 < ∫ x, z x := by
  obtain ⟨x, hx⟩ : ∃ x, z x ≠ 0 := by
    by_contra h; push Not at h; exact hzne (funext h)
  exact hzc.integral_pos_of_hasCompactSupport_nonneg_nonzero hzs hz0 hx

/-- **(F1) The dilation floor.**  Let `Γ` be a nonzero locally finite measure
on `ℝ^d` with the set scaling `Γ(cA) = c^{d-α} Γ(A)` of `H:homog`, and
`α < 2`.  Let `z ≥ 0` be continuous, compactly supported and nonzero, with
`y ↦ z(x - y)` `Γ`-integrable for every `x` (so `Γ * z` is a genuine
integral).  Then there are a smooth compactly supported unit test `f`
(`∫ f² = 1`), an `L²` weak gradient `g` of `f`, and `ε > 0` such that
`ε ≤ ∫ V f² - ∫ ‖g‖²` for EVERY potential `V ≥ Γ * z` for which `V f²` is
integrable.  The test is `f = U_ℓ φ / ‖φ‖₂` with a fixed bump `φ` and a
small dilation parameter `ℓ`; the bound comes from
`∫ V f² ≥ ℓ^α (∫ z) Γ(B̄₁)/‖φ‖₂²` (Tonelli in `(x, y)` and the scaling of
`Γ` on balls) and `∫ ‖g‖² = ℓ² ‖∇φ‖₂²/‖φ‖₂²`, with `ℓ^α` dominating `ℓ²`
for small `ℓ` because `α < 2`.  A pure inequality: no limit and no supremum
is taken. -/
theorem dilation_floor {alpha : ℝ} {Γ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ]
    (hS : SetScaling alpha Γ) (hα : alpha < 2) (hΓ : Γ ≠ 0)
    {z : Rd d → ℝ} (hzc : Continuous z) (hzs : HasCompactSupport z) (hz0 : ∀ x, 0 ≤ z x)
    (hzne : z ≠ 0) (hzi : ∀ x, Integrable (fun y => z (x - y)) Γ) :
    ∃ (f : Rd d → ℝ) (g : Rd d → Rd d) (ε : ℝ), 0 < ε ∧ IsTestFunction f ∧
      MemLp f 2 volume ∧ MemLp g 2 volume ∧ HasWeakGradient f g ∧ ∫ x, f x ^ 2 = 1 ∧
      ∀ V : Rd d → ℝ, (∀ x, conv Γ z x ≤ V x) →
        Integrable (fun x => V x * f x ^ 2) volume → ε ≤ rayleighValue V f g := by
  obtain ⟨Rz, hRz0, hRz⟩ := exists_radius_fn hzs
  have hN := profMass_pos (d := d)
  set A : ℝ := (∫ x, z x) * (Γ (closedBall 0 1)).toReal / profMass d with hA
  set B : ℝ := (profMass d)⁻¹ * ∫ x, ‖grad (prof d) x‖ ^ 2 with hB
  have hB0 : 0 ≤ B := mul_nonneg (inv_nonneg.2 hN.le) (integral_nonneg fun _ => sq_nonneg _)
  have hA0 : 0 < A := by
    have h1 := integral_pos_of_nonzero hzc hzs hz0 hzne
    have h2 : 0 < (Γ (closedBall (0 : Rd d) 1)).toReal :=
      ENNReal.toReal_pos (measure_closedBall_pos hS hΓ one_pos).ne'
        (isCompact_closedBall _ _).measure_lt_top.ne
    positivity
  have hk : 0 < 2 - alpha := by linarith
  set X : ℝ := (A / (B + 1)) ^ (2 - alpha)⁻¹ with hX
  have hXpos : 0 < X := Real.rpow_pos_of_pos (by positivity) _
  set ℓ : ℝ := min (1 / (Rz + 1)) X with hℓdef
  have hℓ : 0 < ℓ := lt_min (by positivity) hXpos
  have hRℓ : ℓ * Rz ≤ 1 := by
    have h1 : ℓ ≤ 1 / (Rz + 1) := min_le_left _ _
    calc ℓ * Rz ≤ 1 / (Rz + 1) * Rz := mul_le_mul_of_nonneg_right h1 hRz0
      _ ≤ 1 := by rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]; linarith
  have hpow : ℓ ^ (2 - alpha) ≤ A / (B + 1) := by
    have h1 : ℓ ^ (2 - alpha) ≤ X ^ (2 - alpha) :=
      Real.rpow_le_rpow hℓ.le (min_le_right _ _) hk.le
    rwa [hX, Real.rpow_inv_rpow (by positivity) hk.ne'] at h1
  have hsplit : ℓ ^ 2 = ℓ ^ alpha * ℓ ^ (2 - alpha) := by
    rw [← Real.rpow_add hℓ, ← Real.rpow_natCast]; congr 1; push_cast; ring
  set ε : ℝ := ℓ ^ alpha * A - ℓ ^ 2 * B with hε
  have hεpos : 0 < ε := by
    have hm : ℓ ^ (2 - alpha) * B ≤ A / (B + 1) * B := mul_le_mul_of_nonneg_right hpow hB0
    have hq : A / (B + 1) * B < A := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith
    have hpa : 0 < ℓ ^ alpha := Real.rpow_pos_of_pos hℓ _
    rw [hε, hsplit]
    nlinarith [mul_lt_mul_of_pos_left (show ℓ ^ (2 - alpha) * B < A by linarith) hpa]
  refine ⟨fl ℓ, gl ℓ, ε, hεpos, fl_test hℓ, memLp_test (fl_test hℓ), gl_memLp hℓ, gl_weak hℓ,
    fl_unit hℓ, fun V hV hVi => ?_⟩
  have hlow := pot_lower hS hzc hzs hz0 hzi hRz hℓ hRℓ V hV hVi
  rw [rayleighValue, gl_norm hℓ]
  have e : (profMass d)⁻¹ * ℓ ^ 2 * ∫ x, ‖grad (prof d) x‖ ^ 2 = ℓ ^ 2 * B := by
    rw [hB]; ring
  rw [e, hε]
  linarith

/-- (F1), set form: under the hypotheses of `dilation_floor`, for every
potential `V ≥ Γ * z` such that `V f²` is integrable for every `f ∈ L²`, the
real Rayleigh value set of `V` contains a positive element; if it is also
bounded above, its supremum is positive. -/
theorem rayleighSet_floor {alpha : ℝ} {Γ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ]
    (hS : SetScaling alpha Γ) (hα : alpha < 2) (hΓ : Γ ≠ 0)
    {z : Rd d → ℝ} (hzc : Continuous z) (hzs : HasCompactSupport z) (hz0 : ∀ x, 0 ≤ z x)
    (hzne : z ≠ 0) (hzi : ∀ x, Integrable (fun y => z (x - y)) Γ)
    {V : Rd d → ℝ} (hV : ∀ x, conv Γ z x ≤ V x)
    (hVi : ∀ f : Rd d → ℝ, MemLp f 2 volume → Integrable (fun x => V x * f x ^ 2) volume) :
    (∃ q ∈ rayleighSet V, 0 < q) ∧ (BddAbove (rayleighSet V) → 0 < sSup (rayleighSet V)) := by
  obtain ⟨f, g, ε, hε, -, hf, hg, hw, hu, hval⟩ :=
    dilation_floor hS hα hΓ hzc hzs hz0 hzne hzi
  have hmem : rayleighValue V f g ∈ rayleighSet V :=
    ⟨f, g, ⟨hf, hg, hw, hu, hVi f hf⟩, rfl⟩
  have hpos : 0 < rayleighValue V f g := hε.trans_le (hval V hV (hVi f hf))
  exact ⟨⟨_, hmem, hpos⟩, fun hb => hpos.trans_le (le_csSup hb hmem)⟩

/-! ### Positivity of integrals against `Γ` -/

/-- Auxiliary to the Lean proof route: a continuous nonnegative `Γ`-integrable
`F` with `F(0) > 0` has positive `Γ`-integral, for a nonzero `Γ` with the set
scaling of `H:homog` (every centred ball has positive mass, (F2)). -/
theorem integral_pos_of_pos_zero {alpha : ℝ} {Γ : Measure (Rd d)} (hS : SetScaling alpha Γ)
    (hΓ : Γ ≠ 0) {F : Rd d → ℝ} (hFc : Continuous F) (hF0 : ∀ x, 0 ≤ F x) (hpos : 0 < F 0)
    (hFi : Integrable F Γ) : 0 < ∫ x, F x ∂Γ := by
  have ho : IsOpen {x | 0 < F x} := isOpen_lt continuous_const hFc
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 ho 0 hpos
  rw [integral_pos_iff_support_of_nonneg hF0 hFi]
  refine (measure_ball_pos hS hΓ hr).trans_le (measure_mono fun x hx => ?_)
  exact (hball hx).ne'

/-- `Γ * z` is positive at `x` when `z(x) > 0` (continuous `z ≥ 0` with
`y ↦ z(x - y)` `Γ`-integrable; `Γ ≠ 0` with the set scaling). -/
theorem conv_pos {alpha : ℝ} {Γ : Measure (Rd d)} (hS : SetScaling alpha Γ) (hΓ : Γ ≠ 0)
    {z : Rd d → ℝ} (hzc : Continuous z) (hz0 : ∀ x, 0 ≤ z x) {x : Rd d} (hx : 0 < z x)
    (hzi : Integrable (fun y => z (x - y)) Γ) : 0 < conv Γ z x :=
  integral_pos_of_pos_zero hS hΓ (hzc.comp (continuous_const.sub continuous_id))
    (fun _ => hz0 _) (by simpa using hx) hzi

/-! ### (F3) Autocorrelation -/

/-- Auxiliary to the Lean proof route: the autocorrelation
`SpatialFourierBound.autocorr Q x = ∫ Q(t) Q(t - x) dt` in the shifted form
`∫ Q(x + y) Q(y) dy` (translation invariance of Lebesgue measure). -/
theorem autocorr_eq_shift (Q : Rd d → ℝ) (x : Rd d) :
    SpatialFourierBound.autocorr Q x = ∫ y, Q (x + y) * Q y := by
  unfold SpatialFourierBound.autocorr
  rw [← integral_add_right_eq_self (fun t => Q t * Q (t - x)) x]
  simp only [add_comm _ x, add_sub_cancel_left]

/-- **(F3) Autocorrelation positivity.**  If `Γ` is positive definite as a
tempered distribution (the field `Γ_posdef` of `H:homog`), then for every real
smooth compactly supported `Q`, the autocorrelation
`c_Q = SpatialFourierBound.autocorr Q` (`c_Q(x) = ∫ Q(t) Q(t - x) dt`) has
`∫ c_Q dΓ ≥ 0`.  Route: `Q` (as a complex function) is a Schwartz function
(`HasCompactSupport.toSchwartzMap`), and the complex pairing of
`IsPosDefDistr` is the real pairing cast to `ℂ`.  The statement concerns the
Bochner integral; its integrand is `Γ`-integrable for locally finite `Γ`
(`SpatialFourierBound.integrable_autocorr`), so the value is genuine there. -/
theorem autocorr_nonneg_of_posDef {Γ : Measure (Rd d)} (hP : HomogHypothesis.IsPosDefDistr Γ)
    {Q : Rd d → ℝ} (hQ : IsTestFunction Q) :
    0 ≤ ∫ x, SpatialFourierBound.autocorr Q x ∂Γ := by
  have hsm : ContDiff ℝ ∞ (fun x => (Q x : ℂ)) := Complex.ofRealCLM.contDiff.comp hQ.1
  have hcs : HasCompactSupport (fun x => (Q x : ℂ)) := hQ.2.comp_left Complex.ofReal_zero
  have h := (hP (hcs.toSchwartzMap hsm)).2
  have e1 : ∀ a, (hcs.toSchwartzMap hsm) a = (Q a : ℂ) := fun a =>
    HasCompactSupport.toSchwartzMap_toFun _ _ a
  simp only [e1, Complex.conj_ofReal] at h
  have e : ∀ x : Rd d, (∫ y, (Q (x + y) : ℂ) * (Q y : ℂ)) =
      ((SpatialFourierBound.autocorr Q x : ℝ) : ℂ) := by
    intro x
    rw [autocorr_eq_shift, ← integral_complex_ofReal]
    congr 1; funext y; push_cast; ring
  simp only [e] at h
  rw [integral_complex_ofReal, Complex.ofReal_re] at h
  exact h

/-- (F3), strict form for nonnegative profiles: for continuous, nonnegative,
nonzero, compactly supported `Q`, a nonzero locally finite `Γ` with the set
scaling of `H:homog` has `B_Γ(Q,Q) = ∫ c_Q dΓ > 0`; this uses no positive
definiteness (TeX lines 88-91 and 182-185 of the occupation file: the
autocorrelation is positive near zero and every centred ball has positive
mass). -/
theorem autocorr_pos {alpha : ℝ} {Γ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ]
    (hS : SetScaling alpha Γ) (hΓ : Γ ≠ 0) {Q : Rd d → ℝ} (hQc : Continuous Q)
    (hQs : HasCompactSupport Q) (hQ0 : ∀ x, 0 ≤ Q x) (hQne : Q ≠ 0) :
    0 < ∫ x, SpatialFourierBound.autocorr Q x ∂Γ := by
  have h0 : SpatialFourierBound.autocorr Q 0 = ∫ y, Q y ^ 2 := by
    unfold SpatialFourierBound.autocorr; simp only [sub_zero, sq]
  refine integral_pos_of_pos_zero (F := SpatialFourierBound.autocorr Q) hS hΓ
    (SpatialFourierBound.autocorr_continuous hQc hQs)
    (SpatialFourierBound.autocorr_nonneg hQ0) ?_
    (SpatialFourierBound.integrable_autocorr hQc hQs Γ)
  rw [h0]
  obtain ⟨x, hx⟩ : ∃ x, Q x ≠ 0 := by
    by_contra h; push Not at h; exact hQne (funext h)
  have hc2 : Continuous fun y => Q y ^ 2 := hQc.pow 2
  have hs2 : HasCompactSupport fun y => Q y ^ 2 :=
    hQs.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  have hn2 : (0 : Rd d → ℝ) ≤ fun y => Q y ^ 2 := fun y => sq_nonneg (Q y)
  have hx2 : (fun y => Q y ^ 2) x ≠ 0 := pow_ne_zero 2 hx
  exact hc2.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := volume) hs2 hn2 hx2

/-! ### (F5) Zero weak gradient -/

/-- Auxiliary to the Lean proof route: the mollifier bumps, radii
`1/(n+2) < 2/(n+2)`. -/
def bumpN (d : ℕ) (n : ℕ) : ContDiffBump (0 : Rd d) :=
  ⟨1 / (n + 2 : ℝ), 2 / (n + 2 : ℝ), by positivity, by
    rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num⟩

/-- Auxiliary to the Lean proof route: the mollification `ρ_n ⋆ f`. -/
def moll (f : Rd d → ℝ) (n : ℕ) (x : Rd d) : ℝ :=
  convolution ((bumpN d n).normed volume) f (ContinuousLinearMap.lsmul ℝ ℝ) volume x

/-- Auxiliary to the Lean proof route: `ρ_n ⋆ f → f` almost everywhere for a
locally integrable `f` (Lebesgue differentiation through Mathlib's
`ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`). -/
theorem moll_tendsto (f : Rd d → ℝ) (hf : LocallyIntegrable f volume) :
    ∀ᵐ x ∂volume, Filter.Tendsto (fun n : ℕ => moll f n x) Filter.atTop (nhds (f x)) := by
  refine ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (K := 2) ?_ ?_ hf
  · show Filter.Tendsto (fun n : ℕ => (2 : ℝ) / (n + 2)) Filter.atTop (nhds 0)
    have h := tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)
    refine (h.comp (Filter.tendsto_add_atTop_nat 2)).congr' ?_
    filter_upwards with n; simp [Nat.cast_add]
  · filter_upwards with n
    show (2 : ℝ) / (n + 2) ≤ 2 * (1 / (n + 2))
    rw [mul_one_div]

/-- Auxiliary to the Lean proof route: if `f` is locally integrable with weak
gradient `0`, every mollification `ρ_n ⋆ f` is constant: its derivative is
`(Dρ_n) ⋆ f`, whose value in a direction `v` is the weak-gradient identity
tested against `y ↦ ρ_n(x - y)`. -/
theorem moll_const {f : Rd d → ℝ} (hf : LocallyIntegrable f volume) (h0 : HasWeakGradient f 0)
    (n : ℕ) (x y : Rd d) : moll f n x = moll f n y := by
  set ρ : Rd d → ℝ := (bumpN d n).normed volume with hρ
  have hρs : HasCompactSupport ρ := (bumpN d n).hasCompactSupport_normed
  have hρc : ContDiff ℝ ∞ ρ := (bumpN d n).contDiff_normed
  have hρ1 : ContDiff ℝ 1 ρ := hρc.of_le (by exact_mod_cast le_top)
  have hD : ∀ x, HasFDerivAt (moll f n)
      (convolution (fderiv ℝ ρ) f (ContinuousLinearMap.precompL (Rd d)
        (ContinuousLinearMap.lsmul ℝ ℝ)) volume x) x := fun x =>
    hρs.hasFDerivAt_convolution_left _ hρ1 hf x
  have hzero : ∀ x, convolution (fderiv ℝ ρ) f (ContinuousLinearMap.precompL (Rd d)
        (ContinuousLinearMap.lsmul ℝ ℝ)) volume x = 0 := by
    intro x
    have hex := (hρs.fderiv ℝ).convolutionExists_left
      (ContinuousLinearMap.precompL (Rd d) (ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)))
      (hρc.continuous_fderiv (by simp)) hf x
    ext v
    rw [convolution_def, ContinuousLinearMap.integral_apply hex v]
    simp only [ContinuousLinearMap.precompL_apply, zero_apply,
      ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    rw [← integral_sub_left_eq_self _ volume x]
    simp only [sub_sub_cancel]
    set φ : Rd d → ℝ := fun s => ρ (x - s) with hφ
    have hφt : IsTestFunction φ := by
      refine ⟨hρc.comp (contDiff_const.sub contDiff_id), ?_⟩
      exact hρs.comp_homeomorph (Homeomorph.subLeft x)
    have hφd : ∀ s, fderiv ℝ φ s v = -(fderiv ℝ ρ (x - s) v) := by
      intro s
      have h1 : HasFDerivAt (fun s => x - s) (-ContinuousLinearMap.id ℝ (Rd d)) s :=
        (hasFDerivAt_id s).const_sub x
      have h2 := ((hρc.differentiable (by simp)) (x - s)).hasFDerivAt.comp s h1
      rw [show φ = ρ ∘ fun s => x - s from rfl, h2.fderiv]
      simp
    have hw := h0 φ hφt v
    simp only [Pi.zero_apply, inner_zero_left, zero_mul, integral_zero, neg_zero, hφd,
      mul_neg, integral_neg, neg_eq_zero] at hw
    rw [← hw]
    congr 1; funext s; ring
  exact is_const_of_fderiv_eq_zero (fun x => (hD x).differentiableAt)
    (fun x => by rw [(hD x).fderiv, hzero x]) x y

/-- **(F5) Zero weak gradient implies zero** (half (b) of the D8-lite
foundation): for `d ≥ 1`, an `f ∈ L²(ℝ^d)` whose weak gradient is `0` is zero
almost everywhere.  This is the fact used in `P:spatial-smooth-ratio`
(`notes/integrated_spatial_occupation.tex`, lines 180-182 at a284420: "a nonzero
`L²` function with zero weak gradient would have Fourier transform supported
only at zero, and hence would vanish").  Lean proof route (different from the
TeX's Fourier argument): the mollifications `ρ_n ⋆ f` are smooth with
derivative `(Dρ_n) ⋆ f = 0` (`moll_const`), hence constant; they converge to
`f` almost everywhere, so `f` is a.e. a constant `c`; and a nonzero constant
is not in `L²(ℝ^d)` for `d ≥ 1` (infinite Lebesgue measure).  The hypothesis
`d ≥ 1` is necessary: on `ℝ⁰` (one point) every function has weak gradient
`0`. -/
theorem ae_eq_zero_of_hasWeakGradient_zero (hd : 0 < d) {f : Rd d → ℝ}
    (hf : MemLp f 2 volume) (h0 : HasWeakGradient f 0) : f =ᵐ[volume] 0 := by
  have hloc : LocallyIntegrable f volume := hf.locallyIntegrable (by norm_num)
  have hT := moll_tendsto f hloc
  obtain ⟨x₀, hx₀⟩ := hT.exists
  have hconst : f =ᵐ[volume] fun _ => f x₀ := by
    filter_upwards [hT] with x hx
    have : Filter.Tendsto (fun n : ℕ => moll f n x₀) Filter.atTop (nhds (f x)) := by
      refine hx.congr fun n => ?_
      exact moll_const hloc h0 n x x₀
    exact tendsto_nhds_unique this hx₀
  have hc : MemLp (fun _ : Rd d => f x₀) 2 volume := hf.ae_eq hconst
  rw [memLp_const_iff (by norm_num) (by norm_num)] at hc
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have htop : (volume : Measure (Rd d)) Set.univ = ⊤ :=
    measure_univ_of_isAddLeftInvariant _
  rcases hc with hc | hc
  · filter_upwards [hconst] with x hx
    rw [hx, hc]; rfl
  · exact absurd hc (by rw [htop]; exact lt_irrefl _)

end StratonovichHAMSecondMoment.VariationalFloor
