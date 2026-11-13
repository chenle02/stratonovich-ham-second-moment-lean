module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Proposition `P:spatial-smooth-ratio` (The finite smooth spatial ratio) of
`notes/integrated_spatial_occupation.tex` (revision a284420, lines 166-217),
under the section's standing assumptions (lines 4-10: a nonzero covariance
satisfying `H:homog`, `a = α₀`).

Formalized (wrappers `*_paper` with the manuscript's hypotheses
`HomogHypothesis.HomogCovariance d α α₀ Γ μ`, `Γ ≠ 0`, `a = α₀`):
* `spatial_smooth_ratio_R0_paper` (no supplied input): for every real unit
  `g ∈ C_c^∞(ℝ^d)`, `b(g) > 0`, `A_sp(g)` is a genuine (integrable) integral
  and positive, `0 < R(g) ≤ 2^{1+α} R_Γ(1)`; the ratio set is nonempty and
  bounded above and `0 < R_0 ≤ 2^{1+α} R_Γ(1)`, `R(g) ≤ R_0`, i.e. "`R_0` is a
  positive finite real number" (lines 168-170).  Finiteness as in the TeX
  (proof lines 185-188): the deterministic Fourier bound
  `L:spatial-fourier-bound` (`SpatialFourierBound`), not the finiteness of
  `S_1^pos`, so `R_0 < ∞` does not depend on `T:full-upper`, for every `Γ` in
  `H:homog`, including singular ones.  Positivity as in the TeX (lines
  182-187):
  `Γ(B_r) > 0` for every `r > 0` and positivity of the autocorrelation of
  `g² ≥ 0` near `0` (lines 89-91; `VariationalFloor.autocorr_pos`), plus a
  normalized bump (`exists_unitTest`).
* `spatial_dilation_paper`: `E:spatial-dilation` (lines 189-195) on
  `C_c^∞`, `A_sp(U_ℓ g) = ℓ^α A_sp(g)`, `b(U_ℓ g) = ℓ² b(g)`, via
  `VariationalDilation.integral_dilation` and the Lebesgue substitution.
* `spatial_smooth_score_paper`: `E:spatial-smooth-score` (lines 171-176) in the
  EXISTENTIAL form of Le's decision 2 (classified same-assumptions with a
  note): for every real unit `g` and every
  `y < k [R(g) α^{α/2}/(8 M_a q^{q/2})]^{1/k}` (`k = 3-α`, `q = 4-α`) some
  `Ψ ∈ C_pos` has `y < I_Ψ - v_Ψ/2`.  This form is implied by the TeX's
  `S_1^pos ≥ ...` and equivalent to it whenever `S_1^pos` is finite; it needs
  no `S1Bdd`.  Proof as in the TeX (lines 197-213): the control
  `z = θ (U_ℓ g)²`, the Rayleigh trial `U_ℓ g`, the choices
  `ℓ² = uL²/b`, `θ = (1+u)L²/(ℓ^α A)` (`u = α/q`), and the maximiser
  `L = q X^{1/k}` of `L - C L^q` substituted directly (the identity
  `C L^q = X^{1/k}` is `score_algebra`).
* `spatial_smooth_score_sSup_paper`: the TeX's `sSup` form of
  `E:spatial-smooth-score`, on the named input `S1Bdd α₀ Γ`.
* `R0_finite_of_S1Bdd_paper`: "`S1Bdd ⇒ R_0` finite",
  `R_0 ≤ 8 M_a q^{q/2} (S_1^pos/k)^k / α^{α/2}`, `E:spatial-smooth-score`
  solved for `R(g)`: the manuscript's route to finiteness before revision
  a284420, which now proves it by `L:spatial-fourier-bound` and keeps the
  finite `S_1^pos` only for the score inequality (lines 213-215).
* `spatial_smooth_ratio_paper`: both claims of the proposition together.

Supplied inputs (named hypotheses):
* `StaticControls a Γ` = `L:spatial-static-controls` (lines 40-96; wave item
  L6-f) for every nonnegative nonzero `z ∈ C_c^∞`: the finiteness of
  `λ_z(1)² = sup R(Γ*z)` (BddAbove of `WeakSobolev.rayleighSet (Γ*z)`, part
  of "positive and finite", lines 47-48) and `E:spatial-static-score`
  (lines 50-53) in the existential form.  It is that lemma's conclusion
  (existential form implied by the `sup` form), so no stronger than the
  manuscript.  Used only for the score statements; the `R_0` statement is
  input-free.
* `S1Bdd a Γ` (BddAbove of `{I_Ψ - v_Ψ/2 : Ψ ∈ C_pos}`, the first claim of
  `P:variational-positive-scores`, unmasked TeX lines 270-274; Le's decision
  1): only for the `sSup` statements and "`S1Bdd ⇒ R_0` finite".

The L6-d foundations used here are imported, not assumed: F2 and F3 in the
form needed here, positivity of `B_Γ(Q,Q) = ∫ c_Q dΓ` for continuous compactly
supported NONNEGATIVE nonzero `Q` (`VariationalFloor.autocorr_pos`, which uses
`Γ(B_r) > 0`, `VariationalFloor.measure_ball_pos`; the positive-definiteness
of `Γ` is not needed), and F4, the weak gradient of a test function
(`VariationalFloor.hasWeakGradient_of_test`, with the gradient field
`VariationalFloor.grad`).

Definitions: `ratio` (`R(g)`), `ratioSet`, `R0` (`sSup`; nonemptiness and
boundedness of `ratioSet` are established wherever `R0` is used as a genuine
supremum: asserted by the positivity statements, and for
`R0_finite_of_S1Bdd` and its `_paper` wrapper boundedness is asserted and
nonemptiness established in the proof, so none rests on the `sSup` junk
value),
`StaticControls`, and `smoothScoreBound` (the right side of
`E:spatial-smooth-score`).  The coefficient-one score set, `S1Bdd` and
`S1pos = sup` (used only under `S1Bdd`) are those of `VariationalRate`
(`score1Set`, `S1Bdd`, `S1pos`).
The rate `I_Ψ`, the cost `v_Ψ` and the control class `C_pos` are those of
`VariationalDilation` (Rayleigh form of the rate and integral form of the cost,
with the boundaries recorded there); `M_a` is `TemporalEquilibrium.mass`
(positive by `TemporalEquilibrium.mass_pos`).  The named input
`StaticControls` is discharged in `SpatialOccupationCompleted`.

Implicit hypotheses made explicit: `d ≥ 1`, `0 < α < 2` and `M_a > 0` are
derived from `H:homog` (`homog_consequences`); the general forms state them.
`U_z = Γ*z` is `VariationalDilation.conv`, continuous for continuous compactly
supported `z` (`conv_continuous`); the pairing `∫ (Γ*G) F = B_Γ(F,G)` is
proved with its integrability (`integral_conv_mul`).

Hypotheses of `H:homog` used: `dim`, `alpha0_pos`, `alpha0_lt_one`,
`alpha_range`, `threshold`, `Γ_radon`, `μ_radon`, `spectral`, `μ_tempered`,
`scaling`; the others are carried, unused.  In `spatial_dilation_paper`,
`Γ ≠ 0` is carried, unused.

Proof-route differences from the TeX (finiteness of `R_0` is not one: both
use the deterministic Fourier bound `L:spatial-fourier-bound`): `b(g) > 0`
by constancy instead of Fourier support; the scalar optimisation substitutes
the maximiser instead of maximising `L - C L^q`.  Lemmas marked "Auxiliary to
the Lean proof route" have no manuscript label.  Fallback (`R0Fin` as a named
input) not used.
-/

public import Mathlib
public import StratonovichHAMSecondMoment.HomogHypothesis
public import StratonovichHAMSecondMoment.SpectralHomog
public import StratonovichHAMSecondMoment.WeakSobolev
public import StratonovichHAMSecondMoment.VariationalDilation
public import StratonovichHAMSecondMoment.TemporalEquilibrium
public import StratonovichHAMSecondMoment.SpatialFourierBound
public import StratonovichHAMSecondMoment.VariationalRate

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Real Filter Metric
open scoped ContDiff Pointwise

namespace StratonovichHAMSecondMoment.SpatialSmoothRatio

open HomogHypothesis (Rd HomogCovariance)
open SpatialFourierBound
open VariationalDilation (SetScaling conv CPos integratedRate rawCost)
open WeakSobolev (IsTestFunction HasWeakGradient IsRayleighTrial rayleighSet rayleighRate
  rayleighValue dilL2)
open VariationalFloor (grad)
open VariationalRate (score1Set S1Bdd S1pos)

variable {d : ℕ}

/-! ### Positivity of `Γ` on balls and of the autocorrelation -/

/-- Auxiliary to the Lean proof route: a unit test is nonzero and `g² ≠ 0`. -/
theorem sq_ne_zero_of_unit {g : Rd d → ℝ} (hg : IsUnitTest g) :
    (fun x => g x ^ 2) ≠ 0 := by
  intro h
  have := hg.2.2
  simp only [show (fun x => g x ^ 2) = fun _ => (0 : ℝ) from h, integral_zero] at this
  exact zero_ne_one this

/-- `0 < A_sp(g)` for a real unit `g ∈ C_c^∞(ℝ^d)` (TeX lines 182-185), with
`Γ ≠ 0` locally finite and `Γ(cA) = c^{d-α}Γ(A)`. -/
theorem spatialEnergy_pos {alpha : ℝ} {Γ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ]
    (hS : SetScaling alpha Γ) (hΓ : Γ ≠ 0) {g : Rd d → ℝ} (hg : IsUnitTest g) :
    0 < spatialEnergy Γ g :=
  VariationalFloor.autocorr_pos hS hΓ (hg.1.continuous.pow 2)
    (hg.2.1.comp_left (g := fun r : ℝ => r ^ 2) (by norm_num)) (fun x => sq_nonneg _)
    (sq_ne_zero_of_unit hg)

/-! ### The dilation `U_ℓ` on smooth profiles (`E:spatial-dilation`) -/

/-- Auxiliary to the Lean proof route: `U_ℓ` maps real unit tests to real unit tests (`ℓ > 0`). -/
theorem isUnitTest_dilL2 {ℓ : ℝ} (hℓ : 0 < ℓ) {g : Rd d → ℝ} (hg : IsUnitTest g) :
    IsUnitTest (dilL2 ℓ g) := by
  obtain ⟨hs, hc, hu⟩ := hg
  refine ⟨?_, ?_, ?_⟩
  · exact (hs.comp (contDiff_const_smul ℓ)).const_smul _
  · exact (hc.comp_smul hℓ.ne').smul_left (f := fun _ : Rd d => ℓ ^ ((d : ℝ) / 2))
  · have h := WeakSobolev.integral_norm_dilL2_sq hℓ g
    simp only [Real.norm_eq_abs, sq_abs] at h
    rw [h, hu]

/-- `b(U_ℓ g) = ℓ² b(g)` (second identity of `E:spatial-dilation`, TeX line
192), for differentiable `g`. -/
theorem gradEnergy_dilL2 {ℓ : ℝ} (hℓ : 0 < ℓ) {g : Rd d → ℝ} (hg : Differentiable ℝ g) :
    gradEnergy (dilL2 ℓ g) = ℓ ^ 2 * gradEnergy g := by
  have hD : ∀ x, fderiv ℝ (dilL2 ℓ g) x = ℓ ^ ((d : ℝ) / 2) • (ℓ • fderiv ℝ g (ℓ • x)) := by
    intro x
    have h1 : HasFDerivAt (fun y : Rd d => ℓ • y) (ℓ • ContinuousLinearMap.id ℝ (Rd d)) x :=
      (hasFDerivAt_id x).const_smul ℓ
    have h2 := ((hg (ℓ • x)).hasFDerivAt.comp x h1).const_smul (ℓ ^ ((d : ℝ) / 2))
    have e : dilL2 ℓ g = ℓ ^ ((d : ℝ) / 2) • (g ∘ HSMul.hSMul ℓ) := rfl
    rw [e, h2.fderiv]
    congr 1
    ext v
    simp
  have hn : ∀ x, ‖fderiv ℝ (dilL2 ℓ g) x‖ ^ 2 =
      ℓ ^ 2 * ((ℓ ^ d : ℝ) • ‖fderiv ℝ g (ℓ • x)‖ ^ 2) := by
    intro x
    rw [hD, norm_smul, norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hℓ.le _),
      Real.norm_of_nonneg hℓ.le, mul_pow, mul_pow, WeakSobolev.rpow_half_sq hℓ, smul_eq_mul]
    ring
  unfold gradEnergy
  simp_rw [hn]
  rw [integral_const_mul, WeakSobolev.integral_jacobian hℓ (fun y => ‖fderiv ℝ g y‖ ^ 2)]

/-- `A_sp(U_ℓ g) = ℓ^α A_sp(g)` (first identity of `E:spatial-dilation`, TeX
lines 191-195): the factors `ℓ^{2d}` from the two squares, `ℓ^{-d}` from `dx`
and `ℓ^{α-d}` from the Radon pushforward (`VariationalDilation.integral_dilation`).
For continuous compactly supported `g` and `Γ(cA) = c^{d-α}Γ(A)`. -/
theorem spatialEnergy_dilL2 {alpha : ℝ} {Γ : Measure (Rd d)} (hS : SetScaling alpha Γ)
    {ℓ : ℝ} (hℓ : 0 < ℓ) {g : Rd d → ℝ} (hg : Continuous g) (hc : HasCompactSupport g) :
    spatialEnergy Γ (dilL2 ℓ g) = ℓ ^ alpha * spatialEnergy Γ g := by
  set Q : Rd d → ℝ := fun x => g x ^ 2 with hQdef
  have hsq : ∀ x, dilL2 ℓ g x ^ 2 = (ℓ ^ d : ℝ) * Q (ℓ • x) := by
    intro x
    have := WeakSobolev.norm_dilL2_sq hℓ g x
    simp only [Real.norm_eq_abs, sq_abs, smul_eq_mul] at this
    exact this
  have hin : ∀ y, ∫ x, dilL2 ℓ g x ^ 2 * dilL2 ℓ g (x - y) ^ 2 =
      (ℓ ^ d : ℝ) * autocorr Q (ℓ • y) := by
    intro y
    simp_rw [hsq]
    have e : ∀ x, (ℓ ^ d : ℝ) * Q (ℓ • x) * ((ℓ ^ d : ℝ) * Q (ℓ • (x - y))) =
        (ℓ ^ d : ℝ) * ((ℓ ^ d : ℝ) • (fun z => Q z * Q (z - ℓ • y)) (ℓ • x)) := by
      intro x; simp only [smul_sub, smul_eq_mul]; ring
    simp_rw [e]
    have hj := WeakSobolev.integral_jacobian hℓ (fun z => Q z * Q (z - ℓ • y))
    rw [integral_const_mul, hj]
    rfl
  have hcont : Continuous (autocorr Q) :=
    autocorr_continuous (hg.pow 2) (hc.comp_left (g := fun r : ℝ => r ^ 2) (by norm_num))
  unfold spatialEnergy spatialPair
  simp_rw [hin]
  rw [integral_const_mul, VariationalDilation.integral_dilation hS hℓ _ hcont, ← mul_assoc,
    ← Real.rpow_natCast, ← Real.rpow_add hℓ]
  congr 2
  · ring

/-! ### The pairing as a potential integral -/

/-- `Γ * G` as a convolution in Mathlib's sense (auxiliary to the Lean proof
route). -/
theorem conv_eq_convolution (Γ : Measure (Rd d)) (G : Rd d → ℝ) :
    conv Γ G = convolution (fun _ => (1 : ℝ)) G (ContinuousLinearMap.lsmul ℝ ℝ) Γ := by
  funext x
  simp [conv, convolution]

/-- Auxiliary to the Lean proof route: `Γ * G` is continuous for continuous compactly supported `G` and locally
finite `Γ` (the manuscript's `U_z = Γ * z` "in its usual pointwise sense",
line 37-38). -/
theorem conv_continuous (Γ : Measure (Rd d)) [IsLocallyFiniteMeasure Γ] {G : Rd d → ℝ}
    (hG : Continuous G) (hc : HasCompactSupport G) : Continuous (conv Γ G) := by
  rw [conv_eq_convolution]
  exact hc.continuous_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    (locallyIntegrable_const 1) hG

/-- Auxiliary to the Lean proof route: the physical pairing as a potential integral: for continuous compactly
supported real `F, G` and locally finite `Γ`, `(Γ * G) F` is integrable and
`∫ (Γ * G)(x) F(x) dx = B_Γ(F, G)` (Tonelli/Fubini for the sigma-finite
`dx Γ(dy)` of `L:spatial-physical-pair`; the TeX uses it at lines 198-199,
`λ_z(1)² ≥ θ ℓ^α A - ℓ² b`). -/
theorem integral_conv_mul (Γ : Measure (Rd d)) [IsLocallyFiniteMeasure Γ] {F G : Rd d → ℝ}
    (hF : Continuous F) (hFc : HasCompactSupport F) (hG : Continuous G)
    (hGc : HasCompactSupport G) :
    Integrable (fun x => conv Γ G x * F x) volume ∧
      ∫ x, conv Γ G x * F x = spatialPair Γ F G := by
  have hcv := conv_continuous Γ hG hGc
  refine ⟨(hcv.mul hF).integrable_of_hasCompactSupport hFc.mul_left, ?_⟩
  have hK := HasCompactSupport.isCompact hFc
  have hL := HasCompactSupport.isCompact hGc
  have hcs : HasCompactSupport (Function.uncurry fun (x y : Rd d) => F x * G (x - y)) := by
    refine HasCompactSupport.intro (hK.prod ((hK.prod hL).image
      (continuous_fst.sub continuous_snd))) ?_
    rintro ⟨x, y⟩ hxy
    simp only [Function.uncurry_apply_pair]
    by_cases hx : x ∈ tsupport F
    · by_cases hy : x - y ∈ tsupport G
      · exact absurd ⟨hx, ⟨(x, x - y), ⟨hx, hy⟩, by simp⟩⟩ hxy
      · rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  have hint : Integrable (Function.uncurry fun (x y : Rd d) => F x * G (x - y))
      (volume.prod Γ) :=
    ((hF.comp continuous_fst).mul (hG.comp (continuous_fst.sub continuous_snd))
      ).integrable_of_hasCompactSupport hcs
  have e : ∀ x, conv Γ G x * F x = ∫ y, F x * G (x - y) ∂Γ := by
    intro x; rw [conv, integral_const_mul, mul_comm]
  simp_rw [e]
  rw [integral_integral_swap hint]
  rfl

/-- Auxiliary to the Lean proof route: `B_Γ(F, cG) = c B_Γ(F, G)`. -/
theorem spatialPair_const_mul_right (Γ : Measure (Rd d)) (F G : Rd d → ℝ) (c : ℝ) :
    spatialPair Γ F (fun x => c * G x) = c * spatialPair Γ F G := by
  unfold spatialPair
  rw [← integral_const_mul]
  congr 1; funext y
  rw [← integral_const_mul]
  congr 1; funext x; ring

/-- Auxiliary to the Lean proof route: `B_Γ(cF, G) = c B_Γ(F, G)`. -/
theorem spatialPair_const_mul_left (Γ : Measure (Rd d)) (F G : Rd d → ℝ) (c : ℝ) :
    spatialPair Γ (fun x => c * F x) G = c * spatialPair Γ F G := by
  unfold spatialPair
  rw [← integral_const_mul]
  congr 1; funext y
  rw [← integral_const_mul]
  congr 1; funext x; ring

/-! ### The smooth ratio `R(g)` and its supremum `R_0` -/

/-- `R(g) = A_sp(g)/b(g)^{α/2}` (TeX lines 168-169).  On real unit tests in
`d ≥ 1`, `b(g) > 0` (`SpatialFourierBound.gradEnergy_pos`), so no division
by zero occurs there. -/
def ratio (Γ : Measure (Rd d)) (alpha : ℝ) (g : Rd d → ℝ) : ℝ :=
  spatialEnergy Γ g / gradEnergy g ^ (alpha / 2)

/-- The set `{R(g) : g ∈ C_c^∞(ℝ^d; ℝ), ‖g‖₂ = 1}`. -/
def ratioSet (Γ : Measure (Rd d)) (alpha : ℝ) : Set ℝ :=
  {r | ∃ g, IsUnitTest g ∧ ratio Γ alpha g = r}

/-- `R_0 = sup R(g)` over real unit `g ∈ C_c^∞(ℝ^d)` (TeX line 169).  The
statements below establish nonemptiness and boundedness of `ratioSet` (the
positivity statements assert both; `R0_finite_of_S1Bdd` and its `_paper`
wrapper assert boundedness and their proofs establish nonemptiness), so they
never rest on Lean's `sSup` junk value. -/
def R0 (Γ : Measure (Rd d)) (alpha : ℝ) : ℝ := sSup (ratioSet Γ alpha)

/-- A real unit test exists (a normalized smooth bump; the TeX's "normalized
compact bump", lines 186-187). -/
theorem exists_unitTest (d : ℕ) : ∃ g : Rd d → ℝ, IsUnitTest g := by
  obtain ⟨b⟩ : Nonempty (ContDiffBump (0 : Rd d)) := ⟨⟨1, 2, one_pos, one_lt_two⟩⟩
  have hbs : ContDiff ℝ ∞ (fun x => b x) := b.contDiff
  have hbc : HasCompactSupport (fun x => b x) := b.hasCompactSupport
  have hk : Continuous (fun x => b x ^ 2) := b.continuous.pow 2
  have hk2 : HasCompactSupport (fun x => b x ^ 2) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => r ^ 2) (by norm_num)
  have hint : Integrable (fun x => b x ^ 2) volume := hk.integrable_of_hasCompactSupport hk2
  have hNpos : 0 < ∫ x, b x ^ 2 := by
    rw [integral_pos_iff_support_of_nonneg (fun x => sq_nonneg _) hint]
    refine (Metric.measure_ball_pos volume (0 : Rd d) b.rIn_pos).trans_le
      (measure_mono fun x hx => ?_)
    have : b x = 1 := b.one_of_mem_closedBall (ball_subset_closedBall hx)
    simp [Function.mem_support, this]
  set N : ℝ := ∫ x, b x ^ 2 with hN
  refine ⟨fun x => (Real.sqrt N)⁻¹ * b x, contDiff_const.mul hbs, hbc.mul_left, ?_⟩
  have hs : (Real.sqrt N)⁻¹ ^ 2 = N⁻¹ := by rw [inv_pow, Real.sq_sqrt hNpos.le]
  simp_rw [mul_pow, hs]
  rw [integral_const_mul, ← hN, inv_mul_cancel₀ hNpos.ne']

/-- **First claim of `P:spatial-smooth-ratio`** (TeX lines 168-170), general
form: `R_0` is a positive finite real number.  Precisely: the ratio set is
nonempty and bounded above, every ratio is positive and at most
`2^{1+α} R_Γ(1)`, `0 < R_0 ≤ 2^{1+α} R_Γ(1)` and `R(g) ≤ R_0` for every unit
test.  Hypotheses: `Γ, μ` locally finite, `μ` a spectral measure of `Γ`
(manuscript convention), `μ` `α`-homogeneous, `Γ(cA) = c^{d-α}Γ(A)`,
`Γ ≠ 0`, `d ≥ 1`, `α < 2`.  Finiteness is proved by the deterministic Fourier
bound (`SpatialFourierBound.spatial_fourier_bound`), `L:spatial-fourier-bound`,
as in the TeX (proof lines 185-188). -/
theorem R0_pos_finite {Γ μ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ]
    [IsLocallyFiniteMeasure μ] (hsp : HomogHypothesis.IsSpectralMeasure Γ μ) {alpha : ℝ}
    (hI : SpectralHomog.SpectralHomogeneous μ alpha) (hS : SetScaling alpha Γ)
    (hΓ : Γ ≠ 0) (hd : 0 < d) (ha2 : alpha < 2) :
    (∀ g, IsUnitTest g → 0 < ratio Γ alpha g ∧
        ratio Γ alpha g ≤ 2 ^ (1 + alpha) * SpectralHomog.resolvent μ 1) ∧
      (ratioSet Γ alpha).Nonempty ∧ BddAbove (ratioSet Γ alpha) ∧
      0 < R0 Γ alpha ∧ R0 Γ alpha ≤ 2 ^ (1 + alpha) * SpectralHomog.resolvent μ 1 ∧
      ∀ g, IsUnitTest g → ratio Γ alpha g ≤ R0 Γ alpha := by
  have hone : ∀ g, IsUnitTest g → 0 < ratio Γ alpha g ∧
      ratio Γ alpha g ≤ 2 ^ (1 + alpha) * SpectralHomog.resolvent μ 1 := by
    intro g hg
    have hb := gradEnergy_pos hd hg
    have hbα : 0 < gradEnergy g ^ (alpha / 2) := Real.rpow_pos_of_pos hb _
    obtain ⟨-, -, -, -, -, hle⟩ := spatial_fourier_bound hsp hI ha2 hg hb
    refine ⟨div_pos (spatialEnergy_pos hS hΓ hg) hbα, ?_⟩
    rw [ratio, div_le_iff₀ hbα]
    exact hle
  obtain ⟨g0, hg0⟩ := exists_unitTest d
  have hne : (ratioSet Γ alpha).Nonempty := ⟨_, g0, hg0, rfl⟩
  have hbdd : BddAbove (ratioSet Γ alpha) := by
    refine ⟨2 ^ (1 + alpha) * SpectralHomog.resolvent μ 1, ?_⟩
    rintro _ ⟨g, hg, rfl⟩
    exact (hone g hg).2
  have hle : ∀ g, IsUnitTest g → ratio Γ alpha g ≤ R0 Γ alpha :=
    fun g hg => le_csSup hbdd ⟨g, hg, rfl⟩
  refine ⟨hone, hne, hbdd, (hone g0 hg0).1.trans_le (hle g0 hg0), ?_, hle⟩
  refine csSup_le hne ?_
  rintro _ ⟨g, hg, rfl⟩
  exact (hone g hg).2

/-! ### Smooth unit tests as Rayleigh trials -/

/-- Auxiliary to the Lean proof route: a real unit test `f` with its classical gradient is a Rayleigh trial for
every continuous potential `V`, with value `∫ V f² - b(f)`. -/
theorem isRayleighTrial_of_unitTest {V : Rd d → ℝ} (hV : Continuous V) {f : Rd d → ℝ}
    (hf : IsUnitTest f) :
    IsRayleighTrial V f (grad f) ∧ rayleighValue V f (grad f) =
      (∫ x, V x * f x ^ 2) - gradEnergy f := by
  obtain ⟨hs, hc, hu⟩ := hf
  have hD : Continuous (fderiv ℝ f) := hs.continuous_fderiv (by simp)
  set T := (InnerProductSpace.toDual ℝ (Rd d)).symm with hT
  have hgc : Continuous (grad f) := T.continuous.comp hD
  have hgs : HasCompactSupport (grad f) := by
    have h0 : T 0 = 0 := map_zero T
    exact (hc.fderiv ℝ).comp_left (g := fun L => T L) h0
  have m1 : MemLp f 2 volume := hs.continuous.memLp_of_hasCompactSupport hc
  have m2 : MemLp (grad f) 2 volume := hgc.memLp_of_hasCompactSupport hgs
  have hk : Continuous (fun x => V x * f x ^ 2) := hV.mul (hs.continuous.pow 2)
  have hk2 : HasCompactSupport (fun x => V x * f x ^ 2) :=
    (hc.comp_left (g := fun r : ℝ => r ^ 2) (by norm_num)).mul_left
  have m3 : Integrable (fun x => V x * f x ^ 2) volume := hk.integrable_of_hasCompactSupport hk2
  refine ⟨⟨m1, m2, VariationalFloor.hasWeakGradient_of_test ⟨hs, hc⟩, hu, m3⟩, ?_⟩
  · unfold rayleighValue gradEnergy grad
    simp only [LinearIsometryEquiv.norm_map]

/-! ### The static-control input and the score set -/

/-- **Supplied input: `L:spatial-static-controls`** (TeX lines 40-96; wave item
L6-f), in the existential form of Le's decision 2.  For every nonnegative
nonzero `z ∈ C_c^∞(ℝ^d)`: `λ_z(1)² = sup R(Γ*z)` is finite (the Rayleigh set
of the potential `U_z = Γ*z` is bounded above; part of "positive and finite",
lines 47-48), and `E:spatial-static-score` (lines 50-53) in the form "every
`y < λ_z(1) - (M_a/2) B_Γ(z,z)` is exceeded by `I_Ψ - v_Ψ/2` for some
`Ψ ∈ C_pos`", with `λ_z(1) = rayleighRate (Γ*z)`, `M_a = mass a` and
`B_Γ(z,z) = spatialPair Γ z z`.  This is that lemma's conclusion: the TeX's
`S_1^pos ≥ λ_z(1) - (M_a/2)B_Γ(z,z)`, with `S_1^pos` the finite supremum of the
score set, implies the existential form (and is equivalent to it when
`S_1^pos` is finite), so the input is no stronger than the manuscript; the
positivity and the Lipschitz claim of the lemma are not used. -/
def StaticControls (a : ℝ) (Γ : Measure (Rd d)) : Prop :=
  ∀ z : Rd d → ℝ, IsTestFunction z → (∀ x, 0 ≤ z x) → z ≠ 0 →
    BddAbove (rayleighSet (conv Γ z)) ∧
      ∀ y : ℝ, y < rayleighRate (conv Γ z) -
          TemporalEquilibrium.mass a / 2 * spatialPair Γ z z →
        ∃ Ψ ∈ CPos d, y < integratedRate a Γ Ψ - rawCost a Γ Ψ / 2

/-- The right side of `E:spatial-smooth-score` (TeX lines 172-176):
`k [R α^{α/2} / (8 M_a q^{q/2})]^{1/k}` with `k = 3 - α`, `q = 4 - α`. -/
def smoothScoreBound (alpha a R : ℝ) : ℝ :=
  (3 - alpha) * (R * alpha ^ (alpha / 2) /
    (8 * TemporalEquilibrium.mass a * (4 - alpha) ^ ((4 - alpha) / 2))) ^ (1 / (3 - alpha))

/-- Auxiliary to the Lean proof route: the scalar identity behind the optimisation
of TeX lines 200-213.  With `k = 3-α`, `q = 4-α`, `X = R α^{α/2}/(8 M q^{q/2})`,
`L = q X^{1/k}` (the maximiser `L^k = 1/(qC)`) and `u = α/q`:
`M (1+u)² L^q = 2 X^{1/k} u^{α/2} R`, i.e. `C L^q = X^{1/k}` for the TeX's
`C = M(1+u)²/(2 R u^{α/2})`. -/
theorem score_algebra {alpha M R : ℝ} (ha0 : 0 < alpha) (ha2 : alpha < 2) (hM : 0 < M)
    (hR : 0 < R) :
    M * (1 + alpha / (4 - alpha)) ^ 2 *
        ((4 - alpha) * (R * alpha ^ (alpha / 2) /
          (8 * M * (4 - alpha) ^ ((4 - alpha) / 2))) ^ (1 / (3 - alpha))) ^ (4 - alpha) =
      2 * (R * alpha ^ (alpha / 2) /
          (8 * M * (4 - alpha) ^ ((4 - alpha) / 2))) ^ (1 / (3 - alpha)) *
        (alpha / (4 - alpha)) ^ (alpha / 2) * R := by
  set q := 4 - alpha with hq
  set k := 3 - alpha with hk
  have hq0 : 0 < q := by linarith
  have hk0 : 0 < k := by linarith
  set a1 := q ^ (q / 2) with ha1
  set a2 := q ^ (alpha / 2) with ha2'
  set aa := alpha ^ (alpha / 2) with haa
  have h1 : 0 < a1 := Real.rpow_pos_of_pos hq0 _
  have h2 : 0 < a2 := Real.rpow_pos_of_pos hq0 _
  have h3 : 0 < aa := Real.rpow_pos_of_pos ha0 _
  set X := R * aa / (8 * M * a1) with hX
  have hX0 : 0 < X := by positivity
  set P := X ^ (1 / k) with hP
  have hP0 : 0 < P := Real.rpow_pos_of_pos hX0 _
  have hPk : P ^ k = X := by
    rw [hP, ← Real.rpow_mul hX0.le, one_div_mul_cancel hk0.ne', Real.rpow_one]
  have hPq : P ^ q = X * P := by
    have : q = k + 1 := by rw [hq, hk]; ring
    rw [this, Real.rpow_add hP0, hPk, Real.rpow_one]
  have hLq : (q * P) ^ q = q ^ q * (X * P) := by
    rw [Real.mul_rpow hq0.le hP0.le, hPq]
  have hqq : q ^ q = a1 * a1 := by
    rw [ha1, ← Real.rpow_add hq0]; congr 1; ring
  have h12 : a1 * a2 = q ^ 2 := by
    rw [ha1, ha2', ← Real.rpow_add hq0, ← Real.rpow_natCast]; congr 1; rw [hq]; push_cast; ring
  have hu : (alpha / q) ^ (alpha / 2) = aa / a2 := by
    rw [Real.div_rpow ha0.le hq0.le]
  have h1u : 1 + alpha / q = 4 / q := by field_simp; rw [hq]; ring
  rw [hLq, hqq, hu, h1u, hX]
  field_simp
  rw [mul_assoc _ a1 a2, h12]; ring

/-- **`E:spatial-smooth-score`** (TeX lines 171-176, proof lines 197-213), in the
existential form (Le's decision 2), general form.  For a real unit
`g ∈ C_c^∞(ℝ^d)` with `b(g) > 0`: every `y` below
`k [R(g) α^{α/2}/(8 M_a q^{q/2})]^{1/k}` is exceeded by `I_Ψ - v_Ψ/2` for some
`Ψ ∈ C_pos`.  Hypotheses: `Γ ≠ 0` locally finite with
`Γ(cA) = c^{d-α}Γ(A)`, `0 < α < 2`, `M_a > 0`, and the supplied input
`StaticControls a Γ` (`L:spatial-static-controls`).  Proof as in the TeX: the
control `z = θ (U_ℓ g)²` with `ℓ² = uL²/b`, `θ = (1+u)L²/(ℓ^α A)`, the Rayleigh
trial `U_ℓ g` (radicand `L²`), and `L = q X^{1/k}`, the maximiser of
`L - C L^q`. -/
theorem spatial_smooth_score {alpha a : ℝ} {Γ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ]
    (hS : SetScaling alpha Γ) (hΓ : Γ ≠ 0) (ha0 : 0 < alpha) (ha2 : alpha < 2)
    (hM : 0 < TemporalEquilibrium.mass a) (hSC : StaticControls a Γ) {g : Rd d → ℝ}
    (hg : IsUnitTest g) (hb : 0 < gradEnergy g) :
    ∀ y < smoothScoreBound alpha a (ratio Γ alpha g),
      ∃ Ψ ∈ CPos d, y < integratedRate a Γ Ψ - rawCost a Γ Ψ / 2 := by
  intro y hy
  set A := spatialEnergy Γ g with hAdef
  have hA : 0 < A := spatialEnergy_pos hS hΓ hg
  set b := gradEnergy g with hbdef
  set M := TemporalEquilibrium.mass a with hMdef
  have hbα : 0 < b ^ (alpha / 2) := Real.rpow_pos_of_pos hb _
  set R := ratio Γ alpha g with hRdef
  have hRA : A = R * b ^ (alpha / 2) := by
    rw [hRdef, ratio, div_mul_cancel₀ _ hbα.ne']
  have hR : 0 < R := div_pos hA hbα
  set q := 4 - alpha with hq
  set k := 3 - alpha with hk
  have hq0 : 0 < q := by linarith
  set X := R * alpha ^ (alpha / 2) / (8 * M * q ^ (q / 2)) with hX
  have hX0 : 0 < X := by
    have := Real.rpow_pos_of_pos ha0 (alpha / 2)
    have := Real.rpow_pos_of_pos hq0 (q / 2)
    positivity
  set P := X ^ (1 / k) with hP
  have hP0 : 0 < P := Real.rpow_pos_of_pos hX0 _
  have hbound : smoothScoreBound alpha a R = k * P := rfl
  set L := q * P with hL
  have hL0 : 0 < L := mul_pos hq0 hP0
  set u := alpha / q with hu
  have hu0 : 0 < u := div_pos ha0 hq0
  set ℓ := L * Real.sqrt (u / b) with hℓdef
  have hℓ : 0 < ℓ := mul_pos hL0 (Real.sqrt_pos.2 (div_pos hu0 hb))
  have hℓα : 0 < ℓ ^ alpha := Real.rpow_pos_of_pos hℓ _
  set θ := (1 + u) * L ^ 2 / (ℓ ^ alpha * A) with hθdef
  have hθ : 0 < θ := by positivity
  have halg : M * (1 + u) ^ 2 * L ^ q = 2 * P * u ^ (alpha / 2) * R := by
    rw [hu, hL, hP, hX, hq, hk]; exact score_algebra ha0 ha2 hM hR
  clear_value θ ℓ u L P X q k
  set f := dilL2 ℓ g with hfdef
  have hf : IsUnitTest f := isUnitTest_dilL2 hℓ hg
  have hAf : spatialEnergy Γ f = ℓ ^ alpha * A :=
    spatialEnergy_dilL2 hS hℓ hg.1.continuous hg.2.1
  have hbf : gradEnergy f = ℓ ^ 2 * b := gradEnergy_dilL2 hℓ (hg.1.differentiable (by simp))
  set F : Rd d → ℝ := fun x => f x ^ 2 with hFdef
  have hFc : Continuous F := hf.1.continuous.pow 2
  have hFs : HasCompactSupport F := hf.2.1.comp_left (g := fun r : ℝ => r ^ 2) (by norm_num)
  set z : Rd d → ℝ := fun x => θ * F x with hzdef
  have hzs : ContDiff ℝ ∞ z := contDiff_const.mul (hf.1.pow 2)
  have hzc : HasCompactSupport z := hFs.mul_left
  have hz0 : ∀ x, 0 ≤ z x := fun x => mul_nonneg hθ.le (sq_nonneg _)
  have hzne : z ≠ 0 := by
    intro h
    apply sq_ne_zero_of_unit hf
    funext x
    have := congrFun h x
    exact (mul_eq_zero.1 this).resolve_left hθ.ne'
  obtain ⟨hbdd, hscore⟩ := hSC z ⟨hzs, hzc⟩ hz0 hzne
  have hVc : Continuous (conv Γ z) := conv_continuous Γ hzs.continuous hzc
  obtain ⟨htrial, hval⟩ := isRayleighTrial_of_unitTest hVc hf
  have hpot : ∫ x, conv Γ z x * f x ^ 2 = θ * (ℓ ^ alpha * A) := by
    rw [(integral_conv_mul Γ hFc hFs hzs.continuous hzc).2, ← hAf]
    exact spatialPair_const_mul_right Γ F F θ
  have hsq : Real.sqrt (u / b) ^ 2 = u / b := Real.sq_sqrt (div_pos hu0 hb).le
  have hθA : θ * (ℓ ^ alpha * A) = (1 + u) * L ^ 2 := by
    rw [hθdef]; field_simp
  have hℓ2 : ℓ ^ 2 * b = u * L ^ 2 := by
    rw [hℓdef, mul_pow, hsq]; field_simp
  have hvalL : rayleighValue (conv Γ z) f (grad f) = L ^ 2 := by
    rw [hval, hpot, hbf, hθA, hℓ2]
    ring
  have hL2 : L ^ 2 ≤ sSup (rayleighSet (conv Γ z)) :=
    le_csSup hbdd ⟨f, grad f, htrial, hvalL⟩
  have hrate : L ≤ rayleighRate (conv Γ z) := by
    rw [rayleighRate, ← Real.sqrt_sq hL0.le]
    exact Real.sqrt_le_sqrt hL2
  have hBzz : spatialPair Γ z z = θ * (θ * (ℓ ^ alpha * A)) := by
    rw [spatialPair_const_mul_left, ← hAf]
    congr 1
    exact spatialPair_const_mul_right Γ F F θ
  have hℓpow : ℓ ^ alpha = L ^ alpha * (u ^ (alpha / 2) / b ^ (alpha / 2)) := by
    rw [hℓdef, Real.mul_rpow hL0.le (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
      ← Real.rpow_mul (div_pos hu0 hb).le, Real.div_rpow hu0.le hb.le]
    congr 3 <;> ring
  have hL4 : L ^ 2 * L ^ 2 = L ^ q * L ^ alpha := by
    rw [← Real.rpow_add hL0, hq, show (4 : ℝ) - alpha + alpha = (4 : ℕ) by norm_num,
      Real.rpow_natCast]; ring
  have hLα : 0 < L ^ alpha := Real.rpow_pos_of_pos hL0 _
  have huα : 0 < u ^ (alpha / 2) := Real.rpow_pos_of_pos hu0 _
  have hcost : M / 2 * spatialPair Γ z z = P := by
    rw [hBzz, hθdef]
    have e1 : M / 2 * ((1 + u) * L ^ 2 / (ℓ ^ alpha * A) *
        ((1 + u) * L ^ 2 / (ℓ ^ alpha * A) * (ℓ ^ alpha * A))) =
        M * (1 + u) ^ 2 * (L ^ 2 * L ^ 2) / (2 * (ℓ ^ alpha * A)) := by
      field_simp
    rw [e1, hL4, hℓpow, hRA]
    have e2 : L ^ alpha * (u ^ (alpha / 2) / b ^ (alpha / 2)) *
        (R * b ^ (alpha / 2)) = L ^ alpha * (u ^ (alpha / 2) * R) := by
      field_simp
    rw [e2, div_eq_iff (by positivity)]
    calc M * (1 + u) ^ 2 * (L ^ q * L ^ alpha) = (M * (1 + u) ^ 2 * L ^ q) * L ^ alpha := by
          ring
      _ = _ := by rw [halg]; ring
  refine hscore y ?_
  rw [hcost]
  have : k * P = L - P := by rw [hL, hq, hk]; ring
  linarith [hbound ▸ hy]


/-- `E:spatial-smooth-score` in the `sSup` form of the TeX (lines 171-176),
general form: under the hypotheses of `spatial_smooth_score` and the named
input `S1Bdd a Γ` (so that `S_1^pos = sSup score1Set` is a genuine supremum),
`S_1^pos ≥ k [R(g) α^{α/2}/(8 M_a q^{q/2})]^{1/k}`. -/
theorem spatial_smooth_score_sSup {alpha a : ℝ} {Γ : Measure (Rd d)}
    [IsLocallyFiniteMeasure Γ] (hS : SetScaling alpha Γ) (hΓ : Γ ≠ 0) (ha0 : 0 < alpha)
    (ha2 : alpha < 2) (hM : 0 < TemporalEquilibrium.mass a) (hSC : StaticControls a Γ)
    (hB : S1Bdd a Γ) {g : Rd d → ℝ} (hg : IsUnitTest g) (hb : 0 < gradEnergy g) :
    smoothScoreBound alpha a (ratio Γ alpha g) ≤ S1pos a Γ := by
  refine le_of_forall_lt fun y hy => ?_
  obtain ⟨Ψ, hΨ, hlt⟩ := spatial_smooth_score hS hΓ ha0 ha2 hM hSC hg hb y hy
  exact hlt.trans_le (le_csSup hB ⟨Ψ, hΨ, rfl⟩)

/-- The bound on every ratio by the finite `S_1^pos` (`E:spatial-smooth-score`
solved for `R(g)`; the manuscript's finiteness argument for `R_0` before
revision a284420), general form: under the hypotheses of `spatial_smooth_score_sSup` (in particular
the named input `S1Bdd a Γ`), every ratio satisfies
`R(g) ≤ 8 M_a q^{q/2} (S_1^pos/k)^k / α^{α/2}`.  (The package also proves
`R_0 < ∞` without `S1Bdd`: `R0_pos_finite`.) -/
theorem ratio_le_of_S1Bdd {alpha a : ℝ} {Γ : Measure (Rd d)}
    [IsLocallyFiniteMeasure Γ] (hS : SetScaling alpha Γ) (hΓ : Γ ≠ 0) (ha0 : 0 < alpha)
    (ha2 : alpha < 2) (hM : 0 < TemporalEquilibrium.mass a) (hSC : StaticControls a Γ)
    (hB : S1Bdd a Γ) {g : Rd d → ℝ} (hg : IsUnitTest g) (hb : 0 < gradEnergy g) :
    ratio Γ alpha g ≤ 8 * TemporalEquilibrium.mass a * (4 - alpha) ^ ((4 - alpha) / 2) *
      (S1pos a Γ / (3 - alpha)) ^ (3 - alpha) / alpha ^ (alpha / 2) := by
  have h := spatial_smooth_score_sSup hS hΓ ha0 ha2 hM hSC hB hg hb
  set M := TemporalEquilibrium.mass a
  set R := ratio Γ alpha g
  have hk : 0 < 3 - alpha := by linarith
  have hq : 0 < 4 - alpha := by linarith
  have haα : 0 < alpha ^ (alpha / 2) := Real.rpow_pos_of_pos ha0 _
  have hqq : 0 < (4 - alpha) ^ ((4 - alpha) / 2) := Real.rpow_pos_of_pos hq _
  have hR : 0 < R := div_pos (spatialEnergy_pos hS hΓ hg) (Real.rpow_pos_of_pos hb _)
  set X := R * alpha ^ (alpha / 2) / (8 * M * (4 - alpha) ^ ((4 - alpha) / 2)) with hX
  have hX0 : 0 < X := by positivity
  have h1 : X ^ (1 / (3 - alpha)) ≤ S1pos a Γ / (3 - alpha) := by
    rw [le_div_iff₀ hk, mul_comm]; exact h
  have h2 : X ≤ (S1pos a Γ / (3 - alpha)) ^ (3 - alpha) := by
    have := Real.rpow_le_rpow (Real.rpow_nonneg hX0.le _) h1 hk.le
    rwa [← Real.rpow_mul hX0.le, one_div_mul_cancel hk.ne', Real.rpow_one] at this
  rw [hX, div_le_iff₀ (by positivity)] at h2
  rw [le_div_iff₀ haα]
  linarith

/-- `S1Bdd ⇒ R_0` finite (the manuscript's route before revision a284420),
general form: the ratio set is
bounded above by `8 M_a q^{q/2} (S_1^pos/k)^k / α^{α/2}`, and so is `R_0`.
Needs `d ≥ 1` (for `b(g) > 0`). -/
theorem R0_finite_of_S1Bdd {alpha a : ℝ} {Γ : Measure (Rd d)}
    [IsLocallyFiniteMeasure Γ] (hS : SetScaling alpha Γ) (hΓ : Γ ≠ 0) (hd : 0 < d)
    (ha0 : 0 < alpha) (ha2 : alpha < 2) (hM : 0 < TemporalEquilibrium.mass a)
    (hSC : StaticControls a Γ) (hB : S1Bdd a Γ) :
    BddAbove (ratioSet Γ alpha) ∧
      R0 Γ alpha ≤ 8 * TemporalEquilibrium.mass a * (4 - alpha) ^ ((4 - alpha) / 2) *
        (S1pos a Γ / (3 - alpha)) ^ (3 - alpha) / alpha ^ (alpha / 2) := by
  have hall : ∀ r ∈ ratioSet Γ alpha, r ≤ 8 * TemporalEquilibrium.mass a *
      (4 - alpha) ^ ((4 - alpha) / 2) * (S1pos a Γ / (3 - alpha)) ^ (3 - alpha) /
        alpha ^ (alpha / 2) := by
    rintro _ ⟨g, hg, rfl⟩
    exact ratio_le_of_S1Bdd hS hΓ ha0 ha2 hM hSC hB hg (gradEnergy_pos hd hg)
  obtain ⟨g0, hg0⟩ := exists_unitTest d
  exact ⟨⟨_, hall⟩, csSup_le ⟨_, g0, hg0, rfl⟩ hall⟩

/-! ### The manuscript's statements under `H:homog` -/

/-- Auxiliary to the Lean proof route: the numerical consequences of `H:homog`
used here (`d ≥ 1`, `0 < α < 2`, `M_{α₀} > 0`). -/
theorem homog_consequences {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) :
    0 < d ∧ 0 < alpha ∧ alpha < 2 ∧ 0 < TemporalEquilibrium.mass alpha0 := by
  refine ⟨by rcases hH.dim with h | h | h <;> omega, ?_, ?_,
    TemporalEquilibrium.mass_pos hH.alpha0_pos hH.alpha0_lt_one⟩
  · rcases hH.alpha_range with h | ⟨h1, h2⟩
    · exact h.1
    · rw [h1, h2]; norm_num
  · linarith [hH.threshold, hH.alpha0_pos]

/-- `E:spatial-dilation` (TeX lines 189-195) under the section's standing
assumptions (lines 4-6: `H:homog`, `Γ ≠ 0`, `a = α₀`): for a real unit
`g ∈ C_c^∞(ℝ^d)` and `ℓ > 0`, `U_ℓ g` is again a real unit test,
`A_sp(U_ℓ g) = ℓ^α A_sp(g)` and `b(U_ℓ g) = ℓ² b(g)`.  Only the scaling
field of `H:homog` is used; `Γ ≠ 0` is carried, unused. -/
theorem spatial_dilation_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (_hΓ : Γ ≠ 0) {g : Rd d → ℝ}
    (hg : IsUnitTest g) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    IsUnitTest (dilL2 ℓ g) ∧ spatialEnergy Γ (dilL2 ℓ g) = ℓ ^ alpha * spatialEnergy Γ g ∧
      gradEnergy (dilL2 ℓ g) = ℓ ^ 2 * gradEnergy g :=
  ⟨isUnitTest_dilL2 hℓ hg, spatialEnergy_dilL2 hH.scaling hℓ hg.1.continuous hg.2.1,
    gradEnergy_dilL2 hℓ (hg.1.differentiable (by simp))⟩

/-- **`P:spatial-smooth-ratio`, first claim** (TeX lines 166-170 and proof lines
180-188) under the section's standing assumptions (lines 4-6:
`H:homog`, `Γ ≠ 0`, `a = α₀`), with no supplied input: for every real unit
`g ∈ C_c^∞(ℝ^d)`, `b(g) > 0`, the autocorrelation of `g²` is `Γ`-integrable
(`A_sp(g) < ∞`) and `A_sp(g) > 0`, `0 < R(g) ≤ 2^{1+α} R_Γ(1)`; the ratio set
is nonempty and bounded above, `0 < R_0 ≤ 2^{1+α} R_Γ(1)` and `R(g) ≤ R_0`.
Finiteness by the deterministic Fourier bound `L:spatial-fourier-bound`
(`SpatialFourierBound.spatial_fourier_bound_paper`), as in the TeX (lines
185-188); `R_0 < ∞` does not depend on `T:full-upper`, for every `Γ` in
`H:homog` including singular ones.  Proof-route difference: `b(g) > 0` by a
constancy argument (as in the proof of `L:spatial-fourier-bound`) instead of
this proof's Fourier support argument (lines 180-182). -/
theorem spatial_smooth_ratio_R0_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) :
    (∀ g, IsUnitTest g → 0 < gradEnergy g ∧ Integrable (autocorr (fun x => g x ^ 2)) Γ ∧
        0 < spatialEnergy Γ g) ∧
      (∀ g, IsUnitTest g → 0 < ratio Γ alpha g ∧
        ratio Γ alpha g ≤ 2 ^ (1 + alpha) * SpectralHomog.resolvent μ 1) ∧
      (ratioSet Γ alpha).Nonempty ∧ BddAbove (ratioSet Γ alpha) ∧
      0 < R0 Γ alpha ∧ R0 Γ alpha ≤ 2 ^ (1 + alpha) * SpectralHomog.resolvent μ 1 ∧
      ∀ g, IsUnitTest g → ratio Γ alpha g ≤ R0 Γ alpha := by
  obtain ⟨hd, -, ha2, -⟩ := homog_consequences hH
  have := hH.Γ_radon
  have := hH.μ_radon
  refine ⟨fun g hg => ?_, R0_pos_finite hH.spectral
    (MaskedSpectralGrowth.spectralHomogeneous_of_homog hH) hH.scaling hΓ hd ha2⟩
  obtain ⟨hb, hi, -⟩ := spatial_fourier_bound_paper hH hg
  exact ⟨hb, hi, spatialEnergy_pos hH.scaling hΓ hg⟩

/-- **`P:spatial-smooth-ratio`, `E:spatial-smooth-score`** (TeX lines 171-176,
proof lines 197-213) under the section's standing assumptions (`H:homog`,
`Γ ≠ 0`, `a = α₀`) and the supplied input `StaticControls α₀ Γ`
(`L:spatial-static-controls`), in the existential form (Le's decision 2,
same-assumptions with a note: the form "every `y` below the right side is
exceeded by some `I_Ψ - v_Ψ/2`" is implied by, and when `S_1^pos < ∞`
equivalent to, the TeX's `S_1^pos ≥ ...`): for every real unit
`g ∈ C_c^∞(ℝ^d)` and every `y < k [R(g) α^{α/2}/(8 M_a q^{q/2})]^{1/k}`
(`k = 3-α`, `q = 4-α`, `a = α₀`) there is `Ψ ∈ C_pos` with
`y < I_Ψ - v_Ψ/2`. -/
theorem spatial_smooth_score_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0)
    (hSC : StaticControls alpha0 Γ) {g : Rd d → ℝ} (hg : IsUnitTest g) :
    ∀ y < smoothScoreBound alpha alpha0 (ratio Γ alpha g),
      ∃ Ψ ∈ CPos d, y < integratedRate alpha0 Γ Ψ - rawCost alpha0 Γ Ψ / 2 := by
  obtain ⟨hd, ha0, ha2, hM⟩ := homog_consequences hH
  have := hH.Γ_radon
  exact spatial_smooth_score hH.scaling hΓ ha0 ha2 hM hSC hg (gradEnergy_pos hd hg)

/-- `E:spatial-smooth-score` in the TeX's `sSup` form (lines 171-176) under the
standing assumptions, the input `StaticControls α₀ Γ` and the named input
`S1Bdd α₀ Γ` (`S_1^pos < ∞`, first claim of `P:variational-positive-scores`):
`S_1^pos ≥ k [R(g) α^{α/2}/(8 M_a q^{q/2})]^{1/k}` for every real unit
`g ∈ C_c^∞(ℝ^d)`. -/
theorem spatial_smooth_score_sSup_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0)
    (hSC : StaticControls alpha0 Γ) (hB : S1Bdd alpha0 Γ) {g : Rd d → ℝ}
    (hg : IsUnitTest g) :
    smoothScoreBound alpha alpha0 (ratio Γ alpha g) ≤ S1pos alpha0 Γ := by
  obtain ⟨hd, ha0, ha2, hM⟩ := homog_consequences hH
  have := hH.Γ_radon
  exact spatial_smooth_score_sSup hH.scaling hΓ ha0 ha2 hM hSC hB hg (gradEnergy_pos hd hg)

/-- "`S1Bdd ⇒ R_0` finite" (the manuscript's route before revision a284420,
now replaced by `L:spatial-fourier-bound`) under the standing assumptions and the inputs `StaticControls α₀ Γ`, `S1Bdd α₀ Γ`: the
ratio set is bounded above and
`R_0 ≤ 8 M_a q^{q/2} (S_1^pos/k)^k / α^{α/2}`. -/
theorem R0_finite_of_S1Bdd_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0)
    (hSC : StaticControls alpha0 Γ) (hB : S1Bdd alpha0 Γ) :
    BddAbove (ratioSet Γ alpha) ∧
      R0 Γ alpha ≤ 8 * TemporalEquilibrium.mass alpha0 * (4 - alpha) ^ ((4 - alpha) / 2) *
        (S1pos alpha0 Γ / (3 - alpha)) ^ (3 - alpha) / alpha ^ (alpha / 2) := by
  obtain ⟨hd, ha0, ha2, hM⟩ := homog_consequences hH
  have := hH.Γ_radon
  exact R0_finite_of_S1Bdd hH.scaling hΓ hd ha0 ha2 hM hSC hB

/-- **`P:spatial-smooth-ratio`** (TeX lines 166-176), both claims, under the
section's standing assumptions and the supplied input `StaticControls α₀ Γ`
(used only by the second claim): `R_0` is a positive finite real number
(nonempty bounded ratio set, `0 < R_0 ≤ 2^{1+α} R_Γ(1)`, `R(g) ≤ R_0`), and
`E:spatial-smooth-score` holds for every real unit `g` in the existential form
of `spatial_smooth_score_paper`. -/
theorem spatial_smooth_ratio_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0)
    (hSC : StaticControls alpha0 Γ) :
    ((ratioSet Γ alpha).Nonempty ∧ BddAbove (ratioSet Γ alpha) ∧
      0 < R0 Γ alpha ∧ R0 Γ alpha ≤ 2 ^ (1 + alpha) * SpectralHomog.resolvent μ 1 ∧
      ∀ g, IsUnitTest g → ratio Γ alpha g ≤ R0 Γ alpha) ∧
    ∀ g, IsUnitTest g → ∀ y < smoothScoreBound alpha alpha0 (ratio Γ alpha g),
      ∃ Ψ ∈ CPos d, y < integratedRate alpha0 Γ Ψ - rawCost alpha0 Γ Ψ / 2 := by
  obtain ⟨-, -, h1, h2, h3, h4, h5⟩ := spatial_smooth_ratio_R0_paper hH hΓ
  exact ⟨⟨h1, h2, h3, h4, h5⟩, fun g hg => spatial_smooth_score_paper hH hΓ hSC hg⟩

end StratonovichHAMSecondMoment.SpatialSmoothRatio
