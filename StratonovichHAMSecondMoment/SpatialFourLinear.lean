module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Propositions `P:spatial-four-linear` (The physical four-linear extension, lines 219-298) and
`P:spatial-energy-map` (The spatial energy and static lower variational expression, lines
300-348) of `notes/integrated_spatial_occupation.tex` (revision a284420), on real `H¹`
profiles, under the section's standing assumptions (lines 4-10: a nonzero covariance satisfying
`H:homog`, `a = α₀`).

Objects reused, not redefined: `B_Γ` is the extended pairing `OccupationKernelRow.pairing`
(`L:spatial-physical-pair`, `ν = dx Γ(dy)`), so `A_sp(f) = B_Γ(f², f²)` and `B_Γ(f², h²)` are
`pairing Γ (zE fun x => f x ^ 2) (zE fun x => h x ^ 2)` in `[0,∞]` (`zE = ofReal ∘ ·`, from
`SpatialStaticControls`); on smooth profiles they agree with the real
`SpatialFourierBound.spatialPair` and `spatialEnergy` (`SpatialStaticControls.pairing_eq_spatialPair`); `R_0` is
`SpatialSmoothRatio.R0`; `H¹` is the weak-gradient space of `WeakSobolev`, a profile being an
`H¹` pair `(f, g)` (`IsH1Pair`: `f, g ∈ L²`, `g` a weak gradient of `f`); unit profiles are
`SpatialStaticControls.IsUnitH1`; `b(g) = ∫ ‖∇g‖²` is written with the named weak gradient.
New definitions: `l2`, `Nnorm` (`N(f)`, line 221), `IsH1Pair`, `H1Tendsto` (`H¹` convergence),
`C4` (line 229), `ratioSetH1` and `Rsp` (`R_sp`, line 235), `energySet` and `Esp` (`𝓔_sp`,
lines 302-306), `energyValue` (right side of `E:spatial-energy-map`), `F0` (`F₀`, lines
319-321), and the auxiliary `SquareBound` (the conclusion of the Fatou step).

Formalized (`*_paper` wrappers with the hypotheses `HomogHypothesis.HomogCovariance d α α₀ Γ μ`,
`Γ ≠ 0` and the named input `hdense`):
* `spatial_four_linear_paper`: `E:spatial-homogeneous-bound` `A_sp(f) ≤ R_0 N(f)⁴` in `[0,∞]`
  (line 224); finiteness of every square pairing and `E:spatial-square-CS` (lines 225-227);
  `E:spatial-four-linear` and absolute convergence of `C₄` (lines 229-234); joint continuity of
  `C₄` on `(H¹)⁴` (sequential form); `R_sp = R_0` (line 235); `A_sp(f) > 0` for every nonzero
  profile (line 236).  Component wrappers: `spatial_homogeneous_bound_paper`,
  `spatial_square_CS_paper`, `spatial_four_linear_bound_paper` (also `|C₄| ≤ R_0 ∏ N`),
  `spatial_four_linear_multilinear_paper` (multilinearity, line 280),
  `spatial_four_linear_continuous_paper`, `spatial_ratio_H1_paper` (also `b > 0` for unit
  profiles, lines 288-289), `spatial_Asp_pos_paper` (no density input needed).
* `squarePairingBounds_paper`: the two fields of `OccupationPhysicalClass.SquarePairingBounds`
  (wave item L7-e) at `R = R_0`, in that structure's spelling, for integration.
* `spatial_energy_value_paper`: `E:spatial-energy-map` (lines 309-314): the energy set is
  nonempty and bounded above, `𝓔_sp = (2-α)/2 α^{α/(2-α)} R_sp^{2/(2-α)} ∈ (0,∞)`, `R_sp = R_0`.
* `spatial_static_energy_score_paper`: `E:spatial-static-energy-score` (lines 316-322) in the
  existential form of Le's decision 2 (as for `E:spatial-smooth-score` in `SpatialSmoothRatio`):
  every `y < M_a^{-1/k} F₀(𝓔_sp)` is exceeded by `I_Ψ - v_Ψ/2` for some `Ψ ∈ C_pos`;
  `spatial_static_energy_score_sSup_paper`: the TeX's `S_1^pos ≥ M_a^{-1/k} F₀(𝓔_sp)` on the
  named input `VariationalRate.S1Bdd α₀ Γ` (as in `SpatialOccupationCompleted`).

Supplied input (named hypothesis `hdense`, in exactly the form agreed for wave item L7-c, which
proves it): density of test functions in `H¹`: every `f ∈ L²` with an `L²` weak gradient `g` is
the `L²` limit of test functions `φ_n` whose gradient fields `VariationalFloor.grad (φ n)`
converge to `g` in `L²`.  It stands for TeX lines 262-268 ("Smooth compact functions are dense
in `H¹`", by cutoff and mollification) and is no stronger.  It is used by every statement
except positivity; `S1Bdd` is used only by the `sSup` score form.

Implicit hypotheses made explicit: `H¹` profiles carry their weak gradient; finiteness is part of
each `[0,∞]` bound; the real values of pairings are taken only where finiteness is proved;
`R_sp`, `𝓔_sp` are `sSup`s whose nonemptiness and boundedness are proved alongside.

Hypotheses of `H:homog` used: `dim`, `alpha0_pos`, `alpha0_lt_one`, `alpha_range`, `threshold`
(for `d ≥ 1`, `0 < α < 2`, `M_a > 0`), `Γ_radon`, `Γ_even` (symmetry of `B_Γ`), `spectral`
(positivity of smooth signed covariance), `μ_radon`, `μ_tempered`, `scaling` (through
`R_0 ∈ (0,∞)` of `SpatialSmoothRatio`, positivity of `A_sp`, smooth dilation); positivity of
`A_sp` (`spatial_Asp_pos_paper`) uses only `Γ_radon` and `scaling`.  `Γ_tempered` is used only by
the two energy-score wrappers, through `SpatialOccupationCompleted.spatial_smooth_score_completed_paper`
and `_sSup_completed_paper`, whose discharge of `StaticControls` calls
`SpatialStaticControls.spatial_static_score_paper` (`hH.Γ_tempered`).  `Γ_posdef`, `μ_even` are
carried, unused.

Proof route (as in the TeX unless stated): smooth homogeneous bound by normalization in `R_0`;
positive semidefiniteness of `B_Γ` on smooth signed profiles from the spectral identity; smooth
covariance Cauchy-Schwarz; Fatou along a.e.-convergent subsequences of the density
approximants (`squareBound_of_smooth`); Cauchy-Schwarz under `ν` for `E:spatial-four-linear`;
telescoping for continuity.  Differences: `E:spatial-square-CS` on `H¹` passes the smooth
inequality `B_Γ(φ²,ψ²)² ≤ A_sp(φ)A_sp(ψ)` to the limit by continuity of `C₄` (the TeX passes
positive semidefiniteness to combinations of `H¹` squares); `b > 0` on unit profiles by
`VariationalFloor.ae_eq_zero_of_hasWeakGradient_zero` (mollification) instead of the Fourier
support argument; positivity of `A_sp` uses a compact set and Mathlib's continuity of the
measure of translates instead of `L²` translation continuity of `1_E`; for
`E:spatial-energy-map` the upper bound applies `E:spatial-homogeneous-bound` and weighted AM-GM
to every unit profile and the lower bound dilates smooth unit tests only (the TeX extends the
dilation to `H¹`); scores are obtained by continuity of the scalar maps along smooth ratios
increasing to `R_0`.

Narrower than the TeX (recorded): joint continuity of `C₄` is stated sequentially for `H¹`
convergence of the pairs (equivalent to continuity for the `H¹` seminorm topology); continuity
of `A_sp` and the square pairings is not restated separately (they are `C₄(f,f,f,f)` and
`C₄(f,f,h,h)` by `pairing_toReal_eq_C4`); `E:spatial-static-energy-score` is in the existential
form, and in the `sSup` form only on `S1Bdd`.  Lemmas marked "Auxiliary to the Lean proof
route" have no manuscript label.  Both propositions are in this one module; the fallback scope
was not needed.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.SpatialOccupationCompleted
public import StratonovichHAMSecondMoment.OccupationKernelRow
public import StratonovichHAMSecondMoment.VariationalFloor

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Real Filter Metric Topology
open scoped ContDiff ENNReal Pointwise

namespace StratonovichHAMSecondMoment.SpatialFourLinear

open HomogHypothesis (Rd HomogCovariance IsSpectralMeasure IsEven)
open WeakSobolev (IsTestFunction HasWeakGradient)
open SpatialFourierBound (autocorr spatialPair spatialEnergy gradEnergy IsUnitTest)
open SpatialSmoothRatio (ratio ratioSet R0)
open SpatialStaticControls (IsUnitH1 zE)
open OccupationKernelRow (pairing pairMeasure ae_pair_of_ae)
open VariationalFloor (grad)

variable {d : ℕ}

/-! ### The real pairing on continuous compactly supported profiles -/

/-- Auxiliary to the Lean proof route: the cross-correlation `y ↦ ∫ F(x) G(x-y) dx` (the inner
integral of `B_Γ(F,G)`) is the convolution `F ⋆ G(-·)`. -/
theorem cross_eq_convolution (F G : Rd d → ℝ) :
    (fun y => ∫ x, F x * G (x - y)) =
      convolution F (fun x => G (-x)) (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
  funext y
  simp only [convolution, ContinuousLinearMap.lsmul_apply, smul_eq_mul, neg_sub]

/-- Auxiliary to the Lean proof route: for continuous compactly supported `F, G` and locally finite
`Γ`, the cross-correlation is `Γ`-integrable (it is continuous with compact support). -/
theorem cross_integrable (Γ : Measure (Rd d)) [IsLocallyFiniteMeasure Γ] {F G : Rd d → ℝ}
    (hF : Continuous F) (hFs : HasCompactSupport F) (hG : Continuous G)
    (hGs : HasCompactSupport G) : Integrable (fun y => ∫ x, F x * G (x - y)) Γ := by
  rw [cross_eq_convolution]
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (hGs.comp_homeomorph (Homeomorph.neg _)).continuous_convolution_right
      (ContinuousLinearMap.lsmul ℝ ℝ) hF.locallyIntegrable (hG.comp continuous_neg)
  · exact hFs.convolution (ContinuousLinearMap.lsmul ℝ ℝ) (hGs.comp_homeomorph (Homeomorph.neg _))

/-- Auxiliary to the Lean proof route: for continuous `F` with compact support and continuous `G`,
`x ↦ F(x) G(x-y)` is integrable for every `y`. -/
theorem inner_integrable {F G : Rd d → ℝ} (hF : Continuous F) (hFs : HasCompactSupport F)
    (hG : Continuous G) (y : Rd d) : Integrable (fun x => F x * G (x - y)) volume :=
  (hF.mul (hG.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
    hFs.mul_right

/-- Auxiliary to the Lean proof route: bilinear expansion of the real pairing `B_Γ(Q+tP, Q+tP)` for
continuous compactly supported `Q, P` and locally finite `Γ` (TeX lines 254-255, "the quadratic
polynomial for `Q+tP`"). -/
theorem spatialPair_quad (Γ : Measure (Rd d)) [IsLocallyFiniteMeasure Γ] {Q P : Rd d → ℝ}
    (hQ : Continuous Q) (hQs : HasCompactSupport Q) (hP : Continuous P)
    (hPs : HasCompactSupport P) (t : ℝ) :
    spatialPair Γ (fun x => Q x + t * P x) (fun x => Q x + t * P x) =
      spatialPair Γ Q Q + t * (spatialPair Γ Q P + spatialPair Γ P Q) +
        t ^ 2 * spatialPair Γ P P := by
  have hin : ∀ y, ∫ x, (Q x + t * P x) * (Q (x - y) + t * P (x - y)) =
      (∫ x, Q x * Q (x - y)) + (t * ((∫ x, Q x * P (x - y)) + ∫ x, P x * Q (x - y)) +
        t ^ 2 * ∫ x, P x * P (x - y)) := by
    intro y
    have i1 := inner_integrable hQ hQs hQ y
    have i2 := inner_integrable hQ hQs hP y
    have i3 := inner_integrable hP hPs hQ y
    have i4 := inner_integrable hP hPs hP y
    have e : (fun x => (Q x + t * P x) * (Q (x - y) + t * P (x - y))) = fun x =>
        Q x * Q (x - y) + (t * (Q x * P (x - y) + P x * Q (x - y)) +
          t ^ 2 * (P x * P (x - y))) := by
      funext x; ring
    have k2 : Integrable (fun x => t * (Q x * P (x - y) + P x * Q (x - y))) volume :=
      (i2.add i3).const_mul t
    have k3 : Integrable (fun x => t ^ 2 * (P x * P (x - y))) volume := i4.const_mul _
    have k1 : Integrable (fun x => t * (Q x * P (x - y) + P x * Q (x - y)) +
        t ^ 2 * (P x * P (x - y))) volume := k2.add k3
    rw [e, integral_add i1 k1, integral_add k2 k3, integral_const_mul, integral_const_mul,
      integral_add i2 i3]
  have j1 := cross_integrable Γ hQ hQs hQ hQs
  have j2 := cross_integrable Γ hQ hQs hP hPs
  have j3 := cross_integrable Γ hP hPs hQ hQs
  have j4 := cross_integrable Γ hP hPs hP hPs
  unfold spatialPair
  simp_rw [hin]
  have k2 : Integrable (fun y => t * ((∫ x, Q x * P (x - y)) + ∫ x, P x * Q (x - y))) Γ :=
    (j2.add j3).const_mul t
  have k3 : Integrable (fun y => t ^ 2 * ∫ x, P x * P (x - y)) Γ := j4.const_mul _
  have k1 : Integrable (fun y => t * ((∫ x, Q x * P (x - y)) + ∫ x, P x * Q (x - y)) +
      t ^ 2 * ∫ x, P x * P (x - y)) Γ := k2.add k3
  rw [integral_add j1 k1, integral_add k2 k3, integral_const_mul, integral_const_mul,
    integral_add j2 j3]
  ring

/-- Auxiliary to the Lean proof route: symmetry `B_Γ(Q,P) = B_Γ(P,Q)` for an even `Γ`
(`HomogHypothesis.IsEven`), continuous `P, Q` and compactly supported `Q` (TeX lines 253-254:
evenness of `Γ` and `(x,y) ↦ (x-y,-y)`; Lean route: translation `x ↦ x + y` and the pushforward
under `y ↦ -y`). -/
theorem spatialPair_comm {Γ : Measure (Rd d)} (hE : IsEven Γ) {Q P : Rd d → ℝ}
    (hP : Continuous P) (hQ : Continuous Q) (hQs : HasCompactSupport Q) :
    spatialPair Γ Q P = spatialPair Γ P Q := by
  have hin : ∀ y, ∫ x, Q x * P (x - y) = (fun z => ∫ x, P x * Q (x - z)) (-y) := by
    intro y
    rw [← integral_add_right_eq_self (fun x => Q x * P (x - y)) y]
    simp only [add_sub_cancel_right, sub_neg_eq_add]
    congr 1; funext x; ring
  have hc : Continuous fun z => ∫ x, P x * Q (x - z) := by
    rw [cross_eq_convolution]
    exact (hQs.comp_homeomorph (Homeomorph.neg _)).continuous_convolution_right
      (ContinuousLinearMap.lsmul ℝ ℝ) hP.locallyIntegrable (hQ.comp continuous_neg)
  unfold spatialPair
  simp_rw [hin]
  have hm := integral_map (μ := Γ) (φ := fun x : Rd d => -x) measurable_neg.aemeasurable
    (f := fun z => ∫ x, P x * Q (x - z)) hc.aestronglyMeasurable
  have hE' : Γ.map (fun x : Rd d => -x) = Γ := hE
  rw [hE'] at hm
  exact hm.symm

/-- Smooth signed covariance is positive (TeX lines 245-251): for real `Q ∈ C_c^∞` and a spectral
measure `μ` of `Γ` in the manuscript's convention, `B_Γ(Q,Q) = ∫ |Q̂|² dμ ≥ 0`
(`SpatialFourierBound.integral_autocorr_eq_spectral`).  As a Bochner-integral statement; for
locally finite `Γ` the integrand is integrable (`SpatialFourierBound.integrable_autocorr`). -/
theorem spatialPair_self_nonneg {Γ μ : Measure (Rd d)} (hsp : IsSpectralMeasure Γ μ)
    {Q : Rd d → ℝ} (hQ : IsTestFunction Q) : 0 ≤ spatialPair Γ Q Q := by
  show 0 ≤ ∫ y, autocorr Q y ∂Γ
  rw [SpatialFourierBound.integral_autocorr_eq_spectral hsp hQ.1 hQ.2]
  exact integral_nonneg fun _ => by positivity

/-- Covariance Cauchy-Schwarz on smooth profiles (TeX lines 254-256): for real `Q, P ∈ C_c^∞`, a
locally finite even `Γ` with spectral measure `μ`, `B_Γ(Q,P)² ≤ B_Γ(Q,Q) B_Γ(P,P)` (discriminant
of `t ↦ B_Γ(Q+tP,Q+tP) ≥ 0`). -/
theorem spatialPair_sq_le {Γ μ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ] (hE : IsEven Γ)
    (hsp : IsSpectralMeasure Γ μ) {Q P : Rd d → ℝ} (hQ : IsTestFunction Q)
    (hP : IsTestFunction P) :
    spatialPair Γ Q P ^ 2 ≤ spatialPair Γ Q Q * spatialPair Γ P P := by
  have hq : ∀ t : ℝ, 0 ≤ spatialPair Γ P P * (t * t) + 2 * spatialPair Γ Q P * t +
      spatialPair Γ Q Q := by
    intro t
    have hT : IsTestFunction fun x => Q x + t * P x :=
      ⟨hQ.1.add (contDiff_const.mul hP.1), hQ.2.add hP.2.mul_left⟩
    have h := spatialPair_self_nonneg hsp hT
    rw [spatialPair_quad Γ hQ.1.continuous hQ.2 hP.1.continuous hP.2,
      spatialPair_comm hE hQ.1.continuous hP.1.continuous hP.2] at h
    nlinarith [h]
  have := discrim_le_zero hq
  unfold discrim at this
  nlinarith [this]

/-! ### `L²` norms and the scale `N(f)` -/

/-- `‖f‖₂ = (eLpNorm f 2).toReal`, the `L²` norm as a real number (`0` if `f ∉ L²`; it is used only
on `L²` functions). -/
def l2 {E : Type*} [NormedAddCommGroup E] (f : Rd d → E) : ℝ :=
  (eLpNorm f 2 volume).toReal

/-- `N(f) = ‖f‖₂^{1-α/4} ‖∇f‖₂^{α/4}` (TeX line 221), with `∇f` given as an `L²` weak gradient `g`
of `f` (a.e. unique, `WeakSobolev.weakGradient_ae_unique`). -/
def Nnorm (alpha : ℝ) (f : Rd d → ℝ) (g : Rd d → Rd d) : ℝ :=
  l2 f ^ (1 - alpha / 4) * l2 g ^ (alpha / 4)

/-- Auxiliary to the Lean proof route: `‖f‖₂ ≥ 0`. -/
theorem l2_nonneg {E : Type*} [NormedAddCommGroup E] (f : Rd d → E) : 0 ≤ l2 f :=
  ENNReal.toReal_nonneg

/-- Auxiliary to the Lean proof route: `N(f) ≥ 0`. -/
theorem Nnorm_nonneg (alpha : ℝ) (f : Rd d → ℝ) (g : Rd d → Rd d) : 0 ≤ Nnorm alpha f g :=
  mul_nonneg (rpow_nonneg (l2_nonneg _) _) (rpow_nonneg (l2_nonneg _) _)

/-- Auxiliary to the Lean proof route: for `f ∈ L²`, `‖f‖₂² = ∫ ‖f‖²`. -/
theorem l2_sq {E : Type*} [NormedAddCommGroup E] {f : Rd d → E} (hf : MemLp f 2 volume) :
    l2 f ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  unfold l2
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, rpow_two]
  have h0 : 0 ≤ ∫ x, ‖f x‖ ^ 2 := integral_nonneg fun _ => by positivity
  rw [ENNReal.toReal_ofReal (rpow_nonneg h0 _), ← rpow_natCast, ← rpow_mul h0]
  norm_num

/-- Auxiliary to the Lean proof route: `N(f)⁴ = (‖f‖₂²)^{(4-α)/2} (‖g‖₂²)^{α/2}` (no hypotheses:
`‖·‖₂ ≥ 0`). -/
theorem Nnorm_pow_four (alpha : ℝ) (f : Rd d → ℝ) (g : Rd d → Rd d) :
    Nnorm alpha f g ^ 4 = (l2 f ^ 2) ^ ((4 - alpha) / 2) * (l2 g ^ 2) ^ (alpha / 2) := by
  have h1 := l2_nonneg f
  have h2 := l2_nonneg g
  unfold Nnorm
  rw [mul_pow, ← rpow_natCast, ← rpow_natCast (l2 g ^ (alpha / 4)), ← rpow_mul h1,
    ← rpow_mul h2, ← rpow_natCast (l2 f) 2, ← rpow_natCast (l2 g) 2, ← rpow_mul h1,
    ← rpow_mul h2]
  congr 2 <;> push_cast <;> ring

/-! ### The smooth homogeneous and square bounds -/

/-- Auxiliary to the Lean proof route: for a test function, `b(φ) = ‖∇φ‖₂²` with the gradient field
`VariationalFloor.grad φ`. -/
theorem gradEnergy_eq_l2_sq {φ : Rd d → ℝ} (hφ : IsTestFunction φ) :
    gradEnergy φ = l2 (grad φ) ^ 2 := by
  rw [l2_sq (VariationalFloor.memLp_grad hφ)]
  unfold gradEnergy grad
  congr 1; funext x
  rw [LinearIsometryEquiv.norm_map]

/-- Auxiliary to the Lean proof route: for real `f ∈ L²`, `∫ f² = ‖f‖₂²`. -/
theorem integral_sq_eq_l2_sq {f : Rd d → ℝ} (hf : MemLp f 2 volume) :
    ∫ x, f x ^ 2 = l2 f ^ 2 := by
  rw [l2_sq hf]; congr 1; funext x; rw [Real.norm_eq_abs, sq_abs]

/-- Auxiliary to the Lean proof route: `A_sp(g) ≥ 0` (Bochner form; nonnegative integrand). -/
theorem spatialEnergy_nonneg (Γ : Measure (Rd d)) (g : Rd d → ℝ) : 0 ≤ spatialEnergy Γ g :=
  integral_nonneg fun _ => integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-- Auxiliary to the Lean proof route: `b(c φ) = c² b(φ)` for differentiable `φ`. -/
theorem gradEnergy_const_mul {φ : Rd d → ℝ} (hφ : Differentiable ℝ φ) (c : ℝ) :
    gradEnergy (fun x => c * φ x) = c ^ 2 * gradEnergy φ := by
  unfold gradEnergy
  rw [← integral_const_mul]; congr 1; funext x
  rw [fderiv_const_mul (hφ x), norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

/-- Auxiliary to the Lean proof route: `A_sp(c g) = c⁴ A_sp(g)`. -/
theorem spatialEnergy_const_mul (Γ : Measure (Rd d)) (g : Rd d → ℝ) (c : ℝ) :
    spatialEnergy Γ (fun x => c * g x) = c ^ 4 * spatialEnergy Γ g := by
  show spatialPair Γ (fun x => (c * g x) ^ 2) (fun x => (c * g x) ^ 2) = _
  have e : (fun x => (c * g x) ^ 2) = fun x => c ^ 2 * g x ^ 2 := by funext x; ring
  rw [e, SpatialSmoothRatio.spatialPair_const_mul_left,
    SpatialSmoothRatio.spatialPair_const_mul_right]
  unfold spatialEnergy; ring

/-- Auxiliary to the Lean proof route: the square of a test function is a test function. -/
theorem isTest_sq {φ : Rd d → ℝ} (hφ : IsTestFunction φ) : IsTestFunction fun x => φ x ^ 2 :=
  ⟨hφ.1.pow 2, hφ.2.comp_left (g := fun r : ℝ => r ^ 2) (by norm_num)⟩

/-- `E:spatial-homogeneous-bound` for smooth compact profiles (TeX lines 240-241, "normalization in
`R_0`", including `f = 0`): if every real unit test `g` has `A_sp(g) ≤ R b(g)^{α/2}`, then every
`φ ∈ C_c^∞` has `A_sp(φ) ≤ R N(φ)⁴`, with `N` computed from the classical gradient.  Hypothesis
`α < 4`. -/
theorem smooth_homog_bound {Γ : Measure (Rd d)} {alpha R : ℝ} (ha4 : alpha < 4)
    (hR : ∀ g, IsUnitTest g → spatialEnergy Γ g ≤ R * gradEnergy g ^ (alpha / 2))
    {φ : Rd d → ℝ} (hφ : IsTestFunction φ) :
    spatialEnergy Γ φ ≤ R * Nnorm alpha φ (grad φ) ^ 4 := by
  rw [Nnorm_pow_four, ← integral_sq_eq_l2_sq (VariationalFloor.memLp_test hφ),
    ← gradEnergy_eq_l2_sq hφ]
  obtain ⟨m, hm⟩ : ∃ m, m = ∫ x, φ x ^ 2 := ⟨_, rfl⟩
  rw [← hm]
  have hm0 : 0 ≤ m := by rw [hm]; exact integral_nonneg fun x => sq_nonneg (φ x)
  rcases hm0.eq_or_lt with h | h
  · have hi : Integrable (fun x => φ x ^ 2) volume :=
      (isTest_sq hφ).1.continuous.integrable_of_hasCompactSupport (isTest_sq hφ).2
    have hae : (fun x => φ x ^ 2) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (φ x)) hi).1 (h.trans hm).symm
    have h2 : (fun x => φ x ^ 2) = 0 :=
      (Continuous.ae_eq_iff_eq volume (hφ.1.continuous.pow 2) continuous_zero).1 hae
    have hz : φ = 0 := funext fun x => by
      have := congr_fun h2 x
      simpa using this
    rw [← h, zero_rpow (by linarith : (4 - alpha) / 2 ≠ 0), zero_mul, mul_zero]
    subst hz
    simp [spatialEnergy, spatialPair]
  · have hc2 : (Real.sqrt m)⁻¹ ^ 2 = m⁻¹ := by rw [inv_pow, Real.sq_sqrt hm0]
    have hc4 : (Real.sqrt m)⁻¹ ^ 4 = m⁻¹ ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hc2]
    have hg : IsUnitTest fun x => (Real.sqrt m)⁻¹ * φ x := by
      refine ⟨contDiff_const.mul hφ.1, hφ.2.mul_left, ?_⟩
      simp_rw [mul_pow, hc2]
      rw [integral_const_mul, ← hm, inv_mul_cancel₀ h.ne']
    have h1 := hR _ hg
    rw [spatialEnergy_const_mul, gradEnergy_const_mul (hφ.1.differentiable (by simp)), hc4,
      hc2] at h1
    have hG0 : 0 ≤ gradEnergy φ := SpatialFourierBound.gradEnergy_nonneg φ
    have hma : 0 < m ^ (alpha / 2) := rpow_pos_of_pos h _
    have e1 : (m⁻¹ * gradEnergy φ) ^ (alpha / 2) =
        (m ^ (alpha / 2))⁻¹ * gradEnergy φ ^ (alpha / 2) := by
      rw [mul_rpow (inv_nonneg.2 hm0) hG0, inv_rpow hm0]
    have e2 : m ^ ((4 - alpha) / 2) = m ^ 2 / m ^ (alpha / 2) := by
      rw [show (4 - alpha) / 2 = (2 : ℝ) - alpha / 2 by ring, rpow_sub h, rpow_two]
    rw [e1] at h1
    rw [e2]
    have hm2 : 0 < m ^ 2 := by positivity
    calc spatialEnergy Γ φ = m ^ 2 * (m⁻¹ ^ 2 * spatialEnergy Γ φ) := by
          field_simp
      _ ≤ m ^ 2 * (R * ((m ^ (alpha / 2))⁻¹ * gradEnergy φ ^ (alpha / 2))) :=
          mul_le_mul_of_nonneg_left h1 hm2.le
      _ = R * (m ^ 2 / m ^ (alpha / 2) * gradEnergy φ ^ (alpha / 2)) := by
          field_simp

/-- The smooth square bound (TeX lines 256-259): for real `φ, ψ ∈ C_c^∞`, a locally finite even `Γ`
with spectral measure `μ`, `R ≥ 0` and the smooth homogeneous bound with constant `R`, `0 ≤
B_Γ(φ², ψ²) ≤ R N(φ)² N(ψ)²` (real pairing). -/
theorem smooth_square_bound {Γ μ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ] (hE : IsEven Γ)
    (hsp : IsSpectralMeasure Γ μ) {alpha R : ℝ} (hR0 : 0 ≤ R)
    (hbd : ∀ φ, IsTestFunction φ → spatialEnergy Γ φ ≤ R * Nnorm alpha φ (grad φ) ^ 4)
    {φ ψ : Rd d → ℝ} (hφ : IsTestFunction φ) (hψ : IsTestFunction ψ) :
    spatialPair Γ (fun x => φ x ^ 2) (fun x => ψ x ^ 2) ≤
      R * Nnorm alpha φ (grad φ) ^ 2 * Nnorm alpha ψ (grad ψ) ^ 2 := by
  have hcs := spatialPair_sq_le hE hsp (isTest_sq hφ) (isTest_sq hψ)
  have hB0 : 0 ≤ spatialPair Γ (fun x => φ x ^ 2) (fun x => ψ x ^ 2) :=
    integral_nonneg fun _ => integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have h1 := hbd φ hφ
  have h2 := hbd ψ hψ
  have hN1 := Nnorm_nonneg alpha φ (grad φ)
  have hN2 := Nnorm_nonneg alpha ψ (grad ψ)
  have hN : 0 ≤ R * Nnorm alpha φ (grad φ) ^ 2 * Nnorm alpha ψ (grad ψ) ^ 2 := by positivity
  refine (pow_le_pow_iff_left₀ hB0 hN two_ne_zero).1 ?_
  calc spatialPair Γ (fun x => φ x ^ 2) (fun x => ψ x ^ 2) ^ 2
      ≤ spatialEnergy Γ φ * spatialEnergy Γ ψ := hcs
    _ ≤ (R * Nnorm alpha φ (grad φ) ^ 4) * (R * Nnorm alpha ψ (grad ψ) ^ 4) :=
        mul_le_mul h1 h2 (spatialEnergy_nonneg _ _) ((spatialEnergy_nonneg _ _).trans h1)
    _ = (R * Nnorm alpha φ (grad φ) ^ 2 * Nnorm alpha ψ (grad ψ) ^ 2) ^ 2 := by ring

/-- Auxiliary to the Lean proof route: `smooth_square_bound` for the extended pairing
`OccupationKernelRow.pairing` (via `SpatialStaticControls.pairing_eq_spatialPair`). -/
theorem smooth_pairing_bound {Γ μ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ] (hE : IsEven Γ)
    (hsp : IsSpectralMeasure Γ μ) {alpha R : ℝ} (hR0 : 0 ≤ R)
    (hbd : ∀ φ, IsTestFunction φ → spatialEnergy Γ φ ≤ R * Nnorm alpha φ (grad φ) ^ 4)
    {φ ψ : Rd d → ℝ} (hφ : IsTestFunction φ) (hψ : IsTestFunction ψ) :
    pairing Γ (zE fun x => φ x ^ 2) (zE fun x => ψ x ^ 2) ≤
      ENNReal.ofReal (R * Nnorm alpha φ (grad φ) ^ 2 * Nnorm alpha ψ (grad ψ) ^ 2) := by
  show pairing Γ (fun x => ENNReal.ofReal (φ x ^ 2)) (fun x => ENNReal.ofReal (ψ x ^ 2)) ≤ _
  rw [(SpatialStaticControls.pairing_eq_spatialPair (isTest_sq hφ).1.continuous (isTest_sq hφ).2
    (fun _ => sq_nonneg _) (isTest_sq hψ).1.continuous (isTest_sq hψ).2
    (fun _ => sq_nonneg _)).2.1]
  exact ENNReal.ofReal_le_ofReal (smooth_square_bound hE hsp hR0 hbd hφ hψ)

/-! ### Convergence of the scale `N` -/

/-- Auxiliary to the Lean proof route: `|‖u‖₂ - ‖f‖₂| ≤ ‖u - f‖₂` for `u, f ∈ L²`. -/
theorem l2_sub_le {E : Type*} [NormedAddCommGroup E] {u f : Rd d → E} (hu : MemLp u 2 volume)
    (hf : MemLp f 2 volume) : |l2 u - l2 f| ≤ l2 (fun x => u x - f x) := by
  have := abs_norm_sub_norm_le (hu.toLp u) (hf.toLp f)
  rw [← MemLp.toLp_sub, Lp.norm_toLp, Lp.norm_toLp, Lp.norm_toLp] at this
  exact this

/-- Auxiliary to the Lean proof route: `eLpNorm (u n - f) 2 → 0` gives `‖u n - f‖₂ → 0` as reals. -/
theorem l2_sub_tendsto {E : Type*} [NormedAddCommGroup E] {u : ℕ → Rd d → E} {f : Rd d → E}
    (h : Tendsto (fun n => eLpNorm (fun x => u n x - f x) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => l2 (fun x => u n x - f x)) atTop (𝓝 0) := by
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simp only [ENNReal.toReal_zero] at this
  exact this

/-- Auxiliary to the Lean proof route: `L²` convergence `u n → f` (all in `L²`) gives `‖u n‖₂ →
‖f‖₂`. -/
theorem l2_tendsto {E : Type*} [NormedAddCommGroup E] {u : ℕ → Rd d → E} {f : Rd d → E}
    (hu : ∀ n, MemLp (u n) 2 volume) (hf : MemLp f 2 volume)
    (h : Tendsto (fun n => eLpNorm (fun x => u n x - f x) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => l2 (u n)) atTop (𝓝 (l2 f)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (l2_sub_tendsto h)
  rw [Real.norm_eq_abs]; exact l2_sub_le (hu n) hf

/-- Auxiliary to the Lean proof route: continuity of `(a,b) ↦ a^{1-α/4} b^{α/4}` along convergent
norms (`0 ≤ α ≤ 4`). -/
theorem Nnorm_tendsto {alpha : ℝ} (ha0 : 0 ≤ alpha) (ha4 : alpha ≤ 4) {u : ℕ → Rd d → ℝ}
    {v : ℕ → Rd d → Rd d} {a b : ℝ} (hu : Tendsto (fun n => l2 (u n)) atTop (𝓝 a))
    (hv : Tendsto (fun n => l2 (v n)) atTop (𝓝 b)) :
    Tendsto (fun n => Nnorm alpha (u n) (v n)) atTop
      (𝓝 (a ^ (1 - alpha / 4) * b ^ (alpha / 4))) :=
  (((Real.continuous_rpow_const (by linarith)).tendsto a).comp hu).mul
    (((Real.continuous_rpow_const (by linarith)).tendsto b).comp hv)

/-! ### The Fatou step -/

/-- A real `H¹` profile with a named gradient: `f ∈ L²`, `g ∈ L²` and `g` a weak gradient of `f`
(`WeakSobolev.MemH1` with the gradient named). -/
def IsH1Pair (f : Rd d → ℝ) (g : Rd d → Rd d) : Prop :=
  MemLp f 2 volume ∧ MemLp g 2 volume ∧ HasWeakGradient f g

/-- Auxiliary to the Lean proof route (the conclusion of the Fatou step, TeX lines 270-275):
`B_Γ(f², h²) ≤ R N(f)² N(h)²` in `[0,∞]` for all `H¹` pairs, with `B_Γ` the extended pairing
`OccupationKernelRow.pairing` of `L:spatial-physical-pair`. -/
def SquareBound (Γ : Measure (Rd d)) (alpha R : ℝ) : Prop :=
  ∀ (f h : Rd d → ℝ) (g k : Rd d → Rd d), IsH1Pair f g → IsH1Pair h k →
    pairing Γ (zE fun x => f x ^ 2) (zE fun x => h x ^ 2) ≤
      ENNReal.ofReal (R * Nnorm alpha f g ^ 2 * Nnorm alpha h k ^ 2)

/-- The Fatou step of `P:spatial-four-linear` (TeX lines 270-275): for a locally finite `Γ` and `0 ≤
α ≤ 4`, the smooth square bound with constant `R` (hypothesis `hsm`) and the density of test
functions in `H¹` (named input `hdense`, the statement proved by wave item L7-c; TeX lines
262-268) give `SquareBound Γ α R`: `B_Γ(f², h²) ≤ R N(f)² N(h)²` in `[0,∞]` for all `H¹` pairs.
Route as in the TeX: approximants converging in `H¹`, subsequences converging a.e. (separately
for `f` and `h`), transfer to `ν`-a.e. convergence (`OccupationKernelRow.ae_pair_of_ae`), Fatou,
continuity of `N`. -/
theorem squareBound_of_smooth {Γ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ] {alpha R : ℝ}
    (ha0 : 0 ≤ alpha) (ha4 : alpha ≤ 4)
    (hdense : ∀ (f : Rd d → ℝ) (g : Rd d → Rd d), MemLp f 2 volume → MemLp g 2 volume →
      WeakSobolev.HasWeakGradient f g →
      ∃ φ : ℕ → Rd d → ℝ, (∀ n, WeakSobolev.IsTestFunction (φ n)) ∧
        Tendsto (fun n => eLpNorm (fun x => φ n x - f x) 2 volume) atTop (𝓝 0) ∧
        Tendsto (fun n => eLpNorm (fun x => VariationalFloor.grad (φ n) x - g x) 2 volume)
          atTop (𝓝 0))
    (hsm : ∀ φ ψ, IsTestFunction φ → IsTestFunction ψ →
      pairing Γ (zE fun x => φ x ^ 2) (zE fun x => ψ x ^ 2) ≤
        ENNReal.ofReal (R * Nnorm alpha φ (grad φ) ^ 2 * Nnorm alpha ψ (grad ψ) ^ 2)) :
    SquareBound Γ alpha R := by
  intro f h g k ⟨hf, hg, hfg⟩ ⟨hh, hk, hhk⟩
  obtain ⟨φ, hφt, hφ1, hφ2⟩ := hdense f g hf hg hfg
  obtain ⟨ψ, hψt, hψ1, hψ2⟩ := hdense h k hh hk hhk
  obtain ⟨ns, hns, hae1⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (f := φ) (g := f) (by norm_num)
      hφ1).exists_seq_tendsto_ae
  obtain ⟨ms, hms, hae2⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (f := ψ) (g := h) (by norm_num)
      hψ1).exists_seq_tendsto_ae
  have hNφ : Tendsto (fun n => Nnorm alpha (φ n) (grad (φ n))) atTop (𝓝 (Nnorm alpha f g)) :=
    Nnorm_tendsto ha0 ha4 (l2_tendsto (fun n => VariationalFloor.memLp_test (hφt n)) hf hφ1)
      (l2_tendsto (fun n => VariationalFloor.memLp_grad (hφt n)) hg hφ2)
  have hNψ : Tendsto (fun n => Nnorm alpha (ψ n) (grad (ψ n))) atTop (𝓝 (Nnorm alpha h k)) :=
    Nnorm_tendsto ha0 ha4 (l2_tendsto (fun n => VariationalFloor.memLp_test (hψt n)) hh hψ1)
      (l2_tendsto (fun n => VariationalFloor.memLp_grad (hψt n)) hk hψ2)
  set F : ℕ → Rd d × Rd d → ℝ≥0∞ := fun i p =>
    ENNReal.ofReal (φ (ns i) p.1 ^ 2) * ENNReal.ofReal (ψ (ms i) (p.1 - p.2) ^ 2) with hF
  have hFm : ∀ i, AEMeasurable (F i) (pairMeasure Γ) := fun i => by
    have c1 : Continuous (φ (ns i)) := (hφt (ns i)).1.continuous
    have c2 : Continuous (ψ (ms i)) := (hψt (ms i)).1.continuous
    exact (((c1.pow 2).measurable.ennreal_ofReal.comp measurable_fst).mul
      ((c2.pow 2).measurable.ennreal_ofReal.comp (measurable_fst.sub measurable_snd))).aemeasurable
  have hlim : ∀ᵐ p ∂(pairMeasure Γ), Tendsto (fun i => F i p) atTop
      (𝓝 (ENNReal.ofReal (f p.1 ^ 2) * ENNReal.ofReal (h (p.1 - p.2) ^ 2))) := by
    filter_upwards [ae_pair_of_ae Γ hae1, ae_pair_of_ae Γ hae2] with p hp1 hp2
    have t := (hp1.1.pow 2).mul (hp2.2.pow 2)
    simp only [hF, ← ENNReal.ofReal_mul (sq_nonneg _)]
    exact ENNReal.tendsto_ofReal t
  have hbound : ∀ i, ∫⁻ p, F i p ∂(pairMeasure Γ) ≤ ENNReal.ofReal (R *
      Nnorm alpha (φ (ns i)) (grad (φ (ns i))) ^ 2 *
        Nnorm alpha (ψ (ms i)) (grad (ψ (ms i))) ^ 2) :=
    fun i => hsm _ _ (hφt _) (hψt _)
  have hlimR : Tendsto (fun i => ENNReal.ofReal (R *
      Nnorm alpha (φ (ns i)) (grad (φ (ns i))) ^ 2 * Nnorm alpha (ψ (ms i)) (grad (ψ (ms i))) ^ 2))
      atTop (𝓝 (ENNReal.ofReal (R * Nnorm alpha f g ^ 2 * Nnorm alpha h k ^ 2))) :=
    ENNReal.tendsto_ofReal ((tendsto_const_nhds.mul ((hNφ.comp hns.tendsto_atTop).pow 2)).mul
      ((hNψ.comp hms.tendsto_atTop).pow 2))
  calc pairing Γ (zE fun x => f x ^ 2) (zE fun x => h x ^ 2)
      = ∫⁻ p, liminf (fun i => F i p) atTop ∂(pairMeasure Γ) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hlim] with p hp
        exact hp.liminf_eq.symm
    _ ≤ liminf (fun i => ∫⁻ p, F i p ∂(pairMeasure Γ)) atTop := lintegral_liminf_le' hFm
    _ ≤ liminf (fun i => ENNReal.ofReal (R * Nnorm alpha (φ (ns i)) (grad (φ (ns i))) ^ 2 *
          Nnorm alpha (ψ (ms i)) (grad (ψ (ms i))) ^ 2)) atTop :=
        liminf_le_liminf (Eventually.of_forall hbound)
    _ = _ := hlimR.liminf_eq

/-! ### The four-linear bound -/

/-- Auxiliary to the Lean proof route: a.e.-strong measurability of `(x,y) ↦ f(x)` for `ν = dx
Γ(dy)`, `Γ` locally finite. -/
theorem aesm_fst (Γ : Measure (Rd d)) [IsLocallyFiniteMeasure Γ] {f : Rd d → ℝ}
    (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (fun p : Rd d × Rd d => f p.1) (pairMeasure Γ) :=
  ⟨fun p => hf.mk f p.1, hf.stronglyMeasurable_mk.comp_measurable measurable_fst, by
    filter_upwards [ae_pair_of_ae Γ hf.ae_eq_mk] with p hp using hp.1⟩

/-- Auxiliary to the Lean proof route: a.e.-strong measurability of `(x,y) ↦ f(x-y)` for `ν`, `Γ`
locally finite (`L:spatial-physical-pair` null-set transfer). -/
theorem aesm_sub (Γ : Measure (Rd d)) [IsLocallyFiniteMeasure Γ] {f : Rd d → ℝ}
    (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (fun p : Rd d × Rd d => f (p.1 - p.2)) (pairMeasure Γ) :=
  ⟨fun p => hf.mk f (p.1 - p.2),
    hf.stronglyMeasurable_mk.comp_measurable (measurable_fst.sub measurable_snd), by
    filter_upwards [ae_pair_of_ae Γ hf.ae_eq_mk] with p hp using hp.2⟩

/-- Auxiliary to the Lean proof route: `∫ |f(x) h(x-y)|² dν = B_Γ(f², h²)` in `[0,∞]`. -/
theorem lintegral_sq_prod {Γ : Measure (Rd d)} (f h : Rd d → ℝ) :
    ∫⁻ p, ‖f p.1 * h (p.1 - p.2)‖ₑ ^ (2 : ℝ) ∂(pairMeasure Γ) =
      pairing Γ (zE fun x => f x ^ 2) (zE fun x => h x ^ 2) := by
  unfold pairing zE
  refine lintegral_congr fun p => ?_
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
    ← ENNReal.ofReal_mul (sq_nonneg _), rpow_two, sq_abs, mul_pow]

/-- `E:spatial-four-linear` (TeX lines 231-234, proof lines 277-280): under `SquareBound Γ α R` with
`R ≥ 0` and locally finite `Γ`, for four `H¹` pairs `∫ |f₁(x) f₂(x) f₃(x-y) f₄(x-y)| dν ≤ R ∏
N(f_j)` (Cauchy-Schwarz under `ν` applied to `f₁(x)f₃(x-y)` and `f₂(x)f₄(x-y)`). -/
theorem four_lintegral_le {Γ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ] {alpha R : ℝ}
    (hB : SquareBound Γ alpha R) (hR0 : 0 ≤ R) {f₁ f₂ f₃ f₄ : Rd d → ℝ}
    {g₁ g₂ g₃ g₄ : Rd d → Rd d} (h₁ : IsH1Pair f₁ g₁) (h₂ : IsH1Pair f₂ g₂)
    (h₃ : IsH1Pair f₃ g₃) (h₄ : IsH1Pair f₄ g₄) :
    ∫⁻ p, ‖f₁ p.1 * f₂ p.1 * f₃ (p.1 - p.2) * f₄ (p.1 - p.2)‖ₑ ∂(pairMeasure Γ) ≤
      ENNReal.ofReal (R * (Nnorm alpha f₁ g₁ * Nnorm alpha f₂ g₂ * Nnorm alpha f₃ g₃ *
        Nnorm alpha f₄ g₄)) := by
  have m1 : AEMeasurable (fun p : Rd d × Rd d => ‖f₁ p.1 * f₃ (p.1 - p.2)‖ₑ) (pairMeasure Γ) :=
    ((aesm_fst Γ h₁.1.aestronglyMeasurable).mul (aesm_sub Γ h₃.1.aestronglyMeasurable)).enorm
  have m2 : AEMeasurable (fun p : Rd d × Rd d => ‖f₂ p.1 * f₄ (p.1 - p.2)‖ₑ) (pairMeasure Γ) :=
    ((aesm_fst Γ h₂.1.aestronglyMeasurable).mul (aesm_sub Γ h₄.1.aestronglyMeasurable)).enorm
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (pairMeasure Γ) Real.HolderConjugate.two_two m1 m2
  have N1 := Nnorm_nonneg alpha f₁ g₁
  have N2 := Nnorm_nonneg alpha f₂ g₂
  have N3 := Nnorm_nonneg alpha f₃ g₃
  have N4 := Nnorm_nonneg alpha f₄ g₄
  have q1 : R * Nnorm alpha f₁ g₁ ^ 2 * Nnorm alpha f₃ g₃ ^ 2 =
      (Real.sqrt R * Nnorm alpha f₁ g₁ * Nnorm alpha f₃ g₃) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hR0]
  have q2 : R * Nnorm alpha f₂ g₂ ^ 2 * Nnorm alpha f₄ g₄ ^ 2 =
      (Real.sqrt R * Nnorm alpha f₂ g₂ * Nnorm alpha f₄ g₄) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hR0]
  have hsR := Real.sqrt_nonneg R
  calc ∫⁻ p, ‖f₁ p.1 * f₂ p.1 * f₃ (p.1 - p.2) * f₄ (p.1 - p.2)‖ₑ ∂(pairMeasure Γ)
      = ∫⁻ p, ((fun p : Rd d × Rd d => ‖f₁ p.1 * f₃ (p.1 - p.2)‖ₑ) *
          (fun p : Rd d × Rd d => ‖f₂ p.1 * f₄ (p.1 - p.2)‖ₑ)) p ∂(pairMeasure Γ) := by
        refine lintegral_congr fun p => ?_
        simp only [Pi.mul_apply]
        rw [← enorm_mul]; congr 1; ring
    _ ≤ (∫⁻ p, ‖f₁ p.1 * f₃ (p.1 - p.2)‖ₑ ^ (2 : ℝ) ∂(pairMeasure Γ)) ^ (1 / (2 : ℝ)) *
          (∫⁻ p, ‖f₂ p.1 * f₄ (p.1 - p.2)‖ₑ ^ (2 : ℝ) ∂(pairMeasure Γ)) ^ (1 / (2 : ℝ)) := hH
    _ ≤ (ENNReal.ofReal (R * Nnorm alpha f₁ g₁ ^ 2 * Nnorm alpha f₃ g₃ ^ 2)) ^ (1 / (2 : ℝ)) *
          (ENNReal.ofReal (R * Nnorm alpha f₂ g₂ ^ 2 * Nnorm alpha f₄ g₄ ^ 2)) ^ (1 / (2 : ℝ)) := by
        rw [lintegral_sq_prod, lintegral_sq_prod]
        gcongr
        · exact hB _ _ _ _ h₁ h₃
        · exact hB _ _ _ _ h₂ h₄
    _ = ENNReal.ofReal (R * (Nnorm alpha f₁ g₁ * Nnorm alpha f₂ g₂ * Nnorm alpha f₃ g₃ *
          Nnorm alpha f₄ g₄)) := by
        rw [q1, q2, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← ENNReal.ofReal_mul
          (by positivity), ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity),
          Real.sqrt_sq (by positivity)]
        congr 1
        calc Real.sqrt R * Nnorm alpha f₁ g₁ * Nnorm alpha f₃ g₃ *
              (Real.sqrt R * Nnorm alpha f₂ g₂ * Nnorm alpha f₄ g₄)
            = (Real.sqrt R * Real.sqrt R) * (Nnorm alpha f₁ g₁ * Nnorm alpha f₂ g₂ *
                Nnorm alpha f₃ g₃ * Nnorm alpha f₄ g₄) := by ring
          _ = _ := by rw [Real.mul_self_sqrt hR0]

/-- The signed four-linear pairing `C₄(f₁,f₂,f₃,f₄) = B_Γ(f₁f₂, f₃f₄) = ∫ f₁(x) f₂(x) f₃(x-y)
f₄(x-y) ν(dx,dy)` (TeX line 229), `ν = dx Γ(dy)`, as a Bochner integral; it is a genuine
integral where `four_integrable` applies. -/
def C4 (Γ : Measure (Rd d)) (f₁ f₂ f₃ f₄ : Rd d → ℝ) : ℝ :=
  ∫ p, f₁ p.1 * f₂ p.1 * f₃ (p.1 - p.2) * f₄ (p.1 - p.2) ∂(pairMeasure Γ)

/-- Absolute convergence of `C₄` (TeX lines 229-230, 279-280): under the hypotheses of
`four_lintegral_le` the integrand of `C₄` is `ν`-integrable. -/
theorem four_integrable {Γ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ] {alpha R : ℝ}
    (hB : SquareBound Γ alpha R) (hR0 : 0 ≤ R) {f₁ f₂ f₃ f₄ : Rd d → ℝ}
    {g₁ g₂ g₃ g₄ : Rd d → Rd d} (h₁ : IsH1Pair f₁ g₁) (h₂ : IsH1Pair f₂ g₂)
    (h₃ : IsH1Pair f₃ g₃) (h₄ : IsH1Pair f₄ g₄) :
    Integrable (fun p : Rd d × Rd d => f₁ p.1 * f₂ p.1 * f₃ (p.1 - p.2) * f₄ (p.1 - p.2))
      (pairMeasure Γ) :=
  ⟨(((aesm_fst Γ h₁.1.aestronglyMeasurable).mul (aesm_fst Γ h₂.1.aestronglyMeasurable)).mul
      (aesm_sub Γ h₃.1.aestronglyMeasurable)).mul
      (aesm_sub Γ h₄.1.aestronglyMeasurable),
    (four_lintegral_le hB hR0 h₁ h₂ h₃ h₄).trans_lt ENNReal.ofReal_lt_top⟩

/-- `|C₄(f₁,f₂,f₃,f₄)| ≤ R ∏ N(f_j)` under the hypotheses of `four_lintegral_le`. -/
theorem abs_C4_le {Γ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ] {alpha R : ℝ}
    (hB : SquareBound Γ alpha R) (hR0 : 0 ≤ R) {f₁ f₂ f₃ f₄ : Rd d → ℝ}
    {g₁ g₂ g₃ g₄ : Rd d → Rd d} (h₁ : IsH1Pair f₁ g₁) (h₂ : IsH1Pair f₂ g₂)
    (h₃ : IsH1Pair f₃ g₃) (h₄ : IsH1Pair f₄ g₄) :
    |C4 Γ f₁ f₂ f₃ f₄| ≤ R * (Nnorm alpha f₁ g₁ * Nnorm alpha f₂ g₂ * Nnorm alpha f₃ g₃ *
      Nnorm alpha f₄ g₄) := by
  have h := (enorm_integral_le_lintegral_enorm _).trans (four_lintegral_le hB hR0 h₁ h₂ h₃ h₄)
  rw [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff (by
    have := Nnorm_nonneg alpha f₁ g₁
    have := Nnorm_nonneg alpha f₂ g₂
    have := Nnorm_nonneg alpha f₃ g₃
    have := Nnorm_nonneg alpha f₄ g₄
    positivity)] at h
  exact h

/-! ### Differences of `H¹` pairs -/

/-- Auxiliary to the Lean proof route: `f ∂_v φ` is integrable for `f ∈ L²` and a test
function `φ`. -/
theorem integrable_mul_dir {f : Rd d → ℝ} (hf : MemLp f 2 volume) {φ : Rd d → ℝ}
    (hφ : IsTestFunction φ) (v : Rd d) :
    Integrable (fun x => f x * fderiv ℝ φ x v) volume := by
  have hc : Continuous fun x => fderiv ℝ φ x v :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have := (hf.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport hc
    (hφ.2.fderiv_apply ℝ v)
  simp only [smul_eq_mul] at this
  exact this.congr (Eventually.of_forall fun x => mul_comm _ _)

/-- Auxiliary to the Lean proof route: `⟪g, v⟫ φ` is integrable for `g ∈ L²` and a test function
`φ`. -/
theorem integrable_inner_mul {g : Rd d → Rd d} (hg : MemLp g 2 volume) {φ : Rd d → ℝ}
    (hφ : IsTestFunction φ) (v : Rd d) :
    Integrable (fun x => inner ℝ (g x) v * φ x) volume := by
  have hm : MemLp (fun x => inner ℝ (g x) v) 2 volume := by
    have := (innerSL ℝ v).comp_memLp' hg
    refine this.congr_norm ?_ (Eventually.of_forall fun x => ?_)
    · exact hg.aestronglyMeasurable.inner_const
    · simp [real_inner_comm]
  have := (hm.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
    hφ.1.continuous hφ.2
  simp only [smul_eq_mul] at this
  exact this.congr (Eventually.of_forall fun x => mul_comm _ _)

/-- Auxiliary to the Lean proof route: the difference of two `H¹` pairs is an `H¹` pair (`g - g'` is
a weak gradient of `f - f'`). -/
theorem IsH1Pair.sub {f f' : Rd d → ℝ} {g g' : Rd d → Rd d} (h : IsH1Pair f g)
    (h' : IsH1Pair f' g') : IsH1Pair (fun x => f x - f' x) (fun x => g x - g' x) := by
  refine ⟨h.1.sub h'.1, h.2.1.sub h'.2.1, fun φ hφ v => ?_⟩
  have e1 := h.2.2 φ hφ v
  have e2 := h'.2.2 φ hφ v
  have i1 : Integrable (fun x => f x * fderiv ℝ φ x v) := integrable_mul_dir h.1 hφ v
  have i2 : Integrable (fun x => f' x * fderiv ℝ φ x v) := integrable_mul_dir h'.1 hφ v
  have j1 : Integrable (fun x => inner ℝ (g x) v * φ x) := integrable_inner_mul h.2.1 hφ v
  have j2 : Integrable (fun x => inner ℝ (g' x) v * φ x) := integrable_inner_mul h'.2.1 hφ v
  have l : ∫ x, (f x - f' x) * fderiv ℝ φ x v =
      (∫ x, f x * fderiv ℝ φ x v) - ∫ x, f' x * fderiv ℝ φ x v := by
    rw [← integral_sub i1 i2]; congr 1; funext x; ring
  have r : ∫ x, inner ℝ (g x - g' x) v * φ x =
      (∫ x, inner ℝ (g x) v * φ x) - ∫ x, inner ℝ (g' x) v * φ x := by
    rw [← integral_sub j1 j2]; congr 1; funext x; rw [inner_sub_left]; ring
  rw [l, r, e1, e2]; ring

/-- Auxiliary to the Lean proof route: a test function with its classical gradient field is an `H¹`
pair. -/
theorem isH1Pair_test {φ : Rd d → ℝ} (hφ : IsTestFunction φ) : IsH1Pair φ (grad φ) :=
  ⟨VariationalFloor.memLp_test hφ, VariationalFloor.memLp_grad hφ,
    VariationalFloor.hasWeakGradient_of_test hφ⟩

/-! ### Joint continuity of `C₄` -/

/-- Auxiliary to the Lean proof route: telescoping identity `C₄(a) - C₄(b) = Σ_j C₄(b₁,…,a_j -
b_j,…,a₄)` (TeX line 281), under `SquareBound` (for integrability). -/
theorem C4_sub_eq {Γ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ] {alpha R : ℝ}
    (hB : SquareBound Γ alpha R) (hR0 : 0 ≤ R) {a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : Rd d → ℝ}
    {e₁ e₂ e₃ e₄ k₁ k₂ k₃ k₄ : Rd d → Rd d} (ha₁ : IsH1Pair a₁ e₁) (ha₂ : IsH1Pair a₂ e₂)
    (ha₃ : IsH1Pair a₃ e₃) (ha₄ : IsH1Pair a₄ e₄) (hb₁ : IsH1Pair b₁ k₁)
    (hb₂ : IsH1Pair b₂ k₂) (hb₃ : IsH1Pair b₃ k₃) (hb₄ : IsH1Pair b₄ k₄) :
    C4 Γ a₁ a₂ a₃ a₄ - C4 Γ b₁ b₂ b₃ b₄ =
      C4 Γ (fun x => a₁ x - b₁ x) a₂ a₃ a₄ + C4 Γ b₁ (fun x => a₂ x - b₂ x) a₃ a₄ +
        (C4 Γ b₁ b₂ (fun x => a₃ x - b₃ x) a₄ + C4 Γ b₁ b₂ b₃ (fun x => a₄ x - b₄ x)) := by
  have iA : Integrable (fun p : Rd d × Rd d =>
      a₁ p.1 * a₂ p.1 * a₃ (p.1 - p.2) * a₄ (p.1 - p.2)) (pairMeasure Γ) :=
    four_integrable hB hR0 ha₁ ha₂ ha₃ ha₄
  have iB : Integrable (fun p : Rd d × Rd d =>
      b₁ p.1 * b₂ p.1 * b₃ (p.1 - p.2) * b₄ (p.1 - p.2)) (pairMeasure Γ) :=
    four_integrable hB hR0 hb₁ hb₂ hb₃ hb₄
  have i1 : Integrable (fun p : Rd d × Rd d =>
      (a₁ p.1 - b₁ p.1) * a₂ p.1 * a₃ (p.1 - p.2) * a₄ (p.1 - p.2)) (pairMeasure Γ) :=
    four_integrable hB hR0 (ha₁.sub hb₁) ha₂ ha₃ ha₄
  have i2 : Integrable (fun p : Rd d × Rd d =>
      b₁ p.1 * (a₂ p.1 - b₂ p.1) * a₃ (p.1 - p.2) * a₄ (p.1 - p.2)) (pairMeasure Γ) :=
    four_integrable hB hR0 hb₁ (ha₂.sub hb₂) ha₃ ha₄
  have i3 : Integrable (fun p : Rd d × Rd d =>
      b₁ p.1 * b₂ p.1 * (a₃ (p.1 - p.2) - b₃ (p.1 - p.2)) * a₄ (p.1 - p.2)) (pairMeasure Γ) :=
    four_integrable hB hR0 hb₁ hb₂ (ha₃.sub hb₃) ha₄
  have i4 : Integrable (fun p : Rd d × Rd d =>
      b₁ p.1 * b₂ p.1 * b₃ (p.1 - p.2) * (a₄ (p.1 - p.2) - b₄ (p.1 - p.2))) (pairMeasure Γ) :=
    four_integrable hB hR0 hb₁ hb₂ hb₃ (ha₄.sub hb₄)
  have i12 : Integrable (fun p : Rd d × Rd d =>
      (a₁ p.1 - b₁ p.1) * a₂ p.1 * a₃ (p.1 - p.2) * a₄ (p.1 - p.2) +
        b₁ p.1 * (a₂ p.1 - b₂ p.1) * a₃ (p.1 - p.2) * a₄ (p.1 - p.2)) (pairMeasure Γ) :=
    i1.add i2
  have i34 : Integrable (fun p : Rd d × Rd d =>
      b₁ p.1 * b₂ p.1 * (a₃ (p.1 - p.2) - b₃ (p.1 - p.2)) * a₄ (p.1 - p.2) +
        b₁ p.1 * b₂ p.1 * b₃ (p.1 - p.2) * (a₄ (p.1 - p.2) - b₄ (p.1 - p.2))) (pairMeasure Γ) :=
    i3.add i4
  simp only [C4]
  rw [← integral_sub iA iB, ← integral_add i1 i2, ← integral_add i3 i4, ← integral_add i12 i34]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only
  ring

/-- Auxiliary to the Lean proof route: the telescoped difference bound for `C₄` (TeX lines
281-282). -/
theorem C4_sub_le {Γ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ] {alpha R : ℝ}
    (hB : SquareBound Γ alpha R) (hR0 : 0 ≤ R) {a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : Rd d → ℝ}
    {e₁ e₂ e₃ e₄ k₁ k₂ k₃ k₄ : Rd d → Rd d} (ha₁ : IsH1Pair a₁ e₁) (ha₂ : IsH1Pair a₂ e₂)
    (ha₃ : IsH1Pair a₃ e₃) (ha₄ : IsH1Pair a₄ e₄) (hb₁ : IsH1Pair b₁ k₁)
    (hb₂ : IsH1Pair b₂ k₂) (hb₃ : IsH1Pair b₃ k₃) (hb₄ : IsH1Pair b₄ k₄) :
    |C4 Γ a₁ a₂ a₃ a₄ - C4 Γ b₁ b₂ b₃ b₄| ≤
      R * (Nnorm alpha (fun x => a₁ x - b₁ x) (fun x => e₁ x - k₁ x) * Nnorm alpha a₂ e₂ *
          Nnorm alpha a₃ e₃ * Nnorm alpha a₄ e₄) +
        R * (Nnorm alpha b₁ k₁ * Nnorm alpha (fun x => a₂ x - b₂ x) (fun x => e₂ x - k₂ x) *
          Nnorm alpha a₃ e₃ * Nnorm alpha a₄ e₄) +
        (R * (Nnorm alpha b₁ k₁ * Nnorm alpha b₂ k₂ *
          Nnorm alpha (fun x => a₃ x - b₃ x) (fun x => e₃ x - k₃ x) * Nnorm alpha a₄ e₄) +
        R * (Nnorm alpha b₁ k₁ * Nnorm alpha b₂ k₂ * Nnorm alpha b₃ k₃ *
          Nnorm alpha (fun x => a₄ x - b₄ x) (fun x => e₄ x - k₄ x))) := by
  rw [C4_sub_eq hB hR0 ha₁ ha₂ ha₃ ha₄ hb₁ hb₂ hb₃ hb₄]
  refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_))
    ((abs_add_le _ _).trans (add_le_add ?_ ?_)))
  · exact abs_C4_le hB hR0 (ha₁.sub hb₁) ha₂ ha₃ ha₄
  · exact abs_C4_le hB hR0 hb₁ (ha₂.sub hb₂) ha₃ ha₄
  · exact abs_C4_le hB hR0 hb₁ hb₂ (ha₃.sub hb₃) ha₄
  · exact abs_C4_le hB hR0 hb₁ hb₂ hb₃ (ha₄.sub hb₄)

/-- Convergence in `H¹`: `u n → f` and `v n → g` in `L²` (functions and weak gradients). -/
def H1Tendsto (u : ℕ → Rd d → ℝ) (v : ℕ → Rd d → Rd d) (f : Rd d → ℝ) (g : Rd d → Rd d) :
    Prop :=
  Tendsto (fun n => eLpNorm (fun x => u n x - f x) 2 volume) atTop (𝓝 0) ∧
    Tendsto (fun n => eLpNorm (fun x => v n x - g x) 2 volume) atTop (𝓝 0)

/-- Auxiliary to the Lean proof route: `N` is continuous along `H¹` convergence (`0 ≤ α ≤ 4`). -/
theorem Nnorm_tendsto_of_H1 {alpha : ℝ} (ha0 : 0 ≤ alpha) (ha4 : alpha ≤ 4)
    {u : ℕ → Rd d → ℝ} {v : ℕ → Rd d → Rd d} {f : Rd d → ℝ} {g : Rd d → Rd d}
    (hu : ∀ n, IsH1Pair (u n) (v n)) (hf : IsH1Pair f g) (hc : H1Tendsto u v f g) :
    Tendsto (fun n => Nnorm alpha (u n) (v n)) atTop (𝓝 (Nnorm alpha f g)) :=
  Nnorm_tendsto ha0 ha4 (l2_tendsto (fun n => (hu n).1) hf.1 hc.1)
    (l2_tendsto (fun n => (hu n).2.1) hf.2.1 hc.2)

/-- Auxiliary to the Lean proof route: `N(u n - f) → 0` along `H¹` convergence (`0 < α < 4`, both
exponents positive). -/
theorem Nnorm_sub_tendsto_of_H1 {alpha : ℝ} (ha0 : 0 < alpha) (ha4 : alpha < 4)
    {u : ℕ → Rd d → ℝ} {v : ℕ → Rd d → Rd d} {f : Rd d → ℝ} {g : Rd d → Rd d}
    (hc : H1Tendsto u v f g) :
    Tendsto (fun n => Nnorm alpha (fun x => u n x - f x) (fun x => v n x - g x)) atTop (𝓝 0) := by
  have := Nnorm_tendsto ha0.le ha4.le (l2_sub_tendsto hc.1) (l2_sub_tendsto hc.2)
  rwa [zero_rpow (by linarith), zero_mul] at this

/-- Joint continuity of `C₄` on `(H¹)⁴` (TeX lines 229-230, 281-283), in sequential form: under
`SquareBound Γ α R`, `R ≥ 0`, `0 < α < 4`, locally finite `Γ`, if `u_j n → f_j` in `H¹`
(functions and weak gradients in `L²`) then `C₄(u n) → C₄(f)`.  (Sequential continuity is
continuity for the `H¹` seminorm topology.) -/
theorem C4_tendsto {Γ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ] {alpha R : ℝ}
    (hB : SquareBound Γ alpha R) (hR0 : 0 ≤ R) (ha0 : 0 < alpha) (ha4 : alpha < 4)
    {u₁ u₂ u₃ u₄ : ℕ → Rd d → ℝ} {v₁ v₂ v₃ v₄ : ℕ → Rd d → Rd d}
    {f₁ f₂ f₃ f₄ : Rd d → ℝ} {g₁ g₂ g₃ g₄ : Rd d → Rd d}
    (hu₁ : ∀ n, IsH1Pair (u₁ n) (v₁ n)) (hu₂ : ∀ n, IsH1Pair (u₂ n) (v₂ n))
    (hu₃ : ∀ n, IsH1Pair (u₃ n) (v₃ n)) (hu₄ : ∀ n, IsH1Pair (u₄ n) (v₄ n))
    (hf₁ : IsH1Pair f₁ g₁) (hf₂ : IsH1Pair f₂ g₂) (hf₃ : IsH1Pair f₃ g₃)
    (hf₄ : IsH1Pair f₄ g₄)
    (hc₁ : H1Tendsto u₁ v₁ f₁ g₁) (hc₂ : H1Tendsto u₂ v₂ f₂ g₂) (hc₃ : H1Tendsto u₃ v₃ f₃ g₃)
    (hc₄ : H1Tendsto u₄ v₄ f₄ g₄) :
    Tendsto (fun n => C4 Γ (u₁ n) (u₂ n) (u₃ n) (u₄ n)) atTop (𝓝 (C4 Γ f₁ f₂ f₃ f₄)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (g := fun n =>
      R * (Nnorm alpha (fun x => u₁ n x - f₁ x) (fun x => v₁ n x - g₁ x) *
          Nnorm alpha (u₂ n) (v₂ n) *
          Nnorm alpha (u₃ n) (v₃ n) * Nnorm alpha (u₄ n) (v₄ n)) +
        R * (Nnorm alpha f₁ g₁ * Nnorm alpha (fun x => u₂ n x - f₂ x) (fun x => v₂ n x - g₂ x) *
          Nnorm alpha (u₃ n) (v₃ n) * Nnorm alpha (u₄ n) (v₄ n)) +
        (R * (Nnorm alpha f₁ g₁ * Nnorm alpha f₂ g₂ *
          Nnorm alpha (fun x => u₃ n x - f₃ x) (fun x => v₃ n x - g₃ x) *
            Nnorm alpha (u₄ n) (v₄ n)) +
        R * (Nnorm alpha f₁ g₁ * Nnorm alpha f₂ g₂ * Nnorm alpha f₃ g₃ *
          Nnorm alpha (fun x => u₄ n x - f₄ x) (fun x => v₄ n x - g₄ x))))
    (fun n => norm_nonneg _) (fun n => ?_) ?_
  · rw [Real.norm_eq_abs]
    exact C4_sub_le hB hR0 (hu₁ n) (hu₂ n) (hu₃ n) (hu₄ n) hf₁ hf₂ hf₃ hf₄
  · have t₂ := Nnorm_tendsto_of_H1 ha0.le ha4.le hu₂ hf₂ hc₂
    have t₃ := Nnorm_tendsto_of_H1 ha0.le ha4.le hu₃ hf₃ hc₃
    have t₄ := Nnorm_tendsto_of_H1 ha0.le ha4.le hu₄ hf₄ hc₄
    have s₁ := Nnorm_sub_tendsto_of_H1 ha0 ha4 hc₁
    have s₂ := Nnorm_sub_tendsto_of_H1 ha0 ha4 hc₂
    have s₃ := Nnorm_sub_tendsto_of_H1 ha0 ha4 hc₃
    have s₄ := Nnorm_sub_tendsto_of_H1 ha0 ha4 hc₄
    have c : ∀ (c : ℝ), Tendsto (fun _ : ℕ => c) atTop (𝓝 c) := fun c => tendsto_const_nhds
    have T := ((((c R).mul (((s₁.mul t₂).mul t₃).mul t₄)).add
      ((c R).mul ((((c (Nnorm alpha f₁ g₁)).mul s₂).mul t₃).mul t₄))).add
      (((c R).mul ((((c (Nnorm alpha f₁ g₁)).mul (c (Nnorm alpha f₂ g₂))).mul s₃).mul t₄)).add
      ((c R).mul ((((c (Nnorm alpha f₁ g₁)).mul (c (Nnorm alpha f₂ g₂))).mul
        (c (Nnorm alpha f₃ g₃))).mul s₄))))
    simpa using T

/-! ### Real values of the square pairings -/

/-- Auxiliary to the Lean proof route: the real value of the extended square pairing is the Bochner
integral `C₄(f,f,h,h)` (nonnegative integrand), for a.e.-strongly measurable `f, h` and locally
finite `Γ`; no finiteness is needed for the identity (a `⊤` value has real value `0` on both
sides). -/
theorem pairing_toReal_eq_C4 {Γ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ] {f h : Rd d → ℝ}
    (hf : AEStronglyMeasurable f volume) (hh : AEStronglyMeasurable h volume) :
    (pairing Γ (zE fun x => f x ^ 2) (zE fun x => h x ^ 2)).toReal = C4 Γ f f h h := by
  have hm : AEStronglyMeasurable (fun p : Rd d × Rd d =>
      f p.1 * f p.1 * h (p.1 - p.2) * h (p.1 - p.2)) (pairMeasure Γ) :=
    (((aesm_fst Γ hf).mul (aesm_fst Γ hf)).mul (aesm_sub Γ hh)).mul (aesm_sub Γ hh)
  unfold C4
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun p => by
      have : f p.1 * f p.1 * h (p.1 - p.2) * h (p.1 - p.2) = (f p.1 * h (p.1 - p.2)) ^ 2 := by
        ring
      simp only [Pi.zero_apply]
      rw [this]; positivity) hm]
  congr 1
  unfold pairing zE
  refine lintegral_congr fun p => ?_
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1; ring

/-- Auxiliary to the Lean proof route: for test functions, `C₄(φ,φ,ψ,ψ) = B_Γ(φ², ψ²)` (real
pairing). -/
theorem C4_test_eq {Γ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ] {φ ψ : Rd d → ℝ}
    (hφ : IsTestFunction φ) (hψ : IsTestFunction ψ) :
    C4 Γ φ φ ψ ψ = spatialPair Γ (fun x => φ x ^ 2) (fun x => ψ x ^ 2) := by
  rw [← pairing_toReal_eq_C4 hφ.1.continuous.aestronglyMeasurable
    hψ.1.continuous.aestronglyMeasurable]
  exact (SpatialStaticControls.pairing_eq_spatialPair (isTest_sq hφ).1.continuous (isTest_sq hφ).2
    (fun _ => sq_nonneg _) (isTest_sq hψ).1.continuous (isTest_sq hψ).2
    (fun _ => sq_nonneg _)).2.2

/-! ### Cauchy-Schwarz for square pairings on `H¹` -/

/-- The squared form of `E:spatial-square-CS` on `H¹` (TeX lines 225-227, 283-285): `C₄(f,f,h,h)² ≤
C₄(f,f,f,f) C₄(h,h,h,h)`.  Hypotheses: locally finite even `Γ` with spectral measure `μ`,
`SquareBound Γ α R`, `R ≥ 0`, `0 < α < 4`, and the density input `hdense`.  Lean route: the
smooth inequality `spatialPair_sq_le` is passed to the limit by the continuity of `C₄`; the TeX
instead passes positive semidefiniteness to finite combinations of `H¹` squares and applies
two-profile Cauchy-Schwarz (same ingredients). -/
theorem C4_square_CS {Γ μ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ] (hE : IsEven Γ)
    (hsp : IsSpectralMeasure Γ μ) {alpha R : ℝ} (hB : SquareBound Γ alpha R) (hR0 : 0 ≤ R)
    (ha0 : 0 < alpha) (ha4 : alpha < 4)
    (hdense : ∀ (f : Rd d → ℝ) (g : Rd d → Rd d), MemLp f 2 volume → MemLp g 2 volume →
      WeakSobolev.HasWeakGradient f g →
      ∃ φ : ℕ → Rd d → ℝ, (∀ n, WeakSobolev.IsTestFunction (φ n)) ∧
        Tendsto (fun n => eLpNorm (fun x => φ n x - f x) 2 volume) atTop (𝓝 0) ∧
        Tendsto (fun n => eLpNorm (fun x => VariationalFloor.grad (φ n) x - g x) 2 volume)
          atTop (𝓝 0))
    {f h : Rd d → ℝ} {g k : Rd d → Rd d} (hfg : IsH1Pair f g) (hhk : IsH1Pair h k) :
    C4 Γ f f h h ^ 2 ≤ C4 Γ f f f f * C4 Γ h h h h := by
  obtain ⟨φ, hφt, hφ1, hφ2⟩ := hdense f g hfg.1 hfg.2.1 hfg.2.2
  obtain ⟨ψ, hψt, hψ1, hψ2⟩ := hdense h k hhk.1 hhk.2.1 hhk.2.2
  have pφ : ∀ n, IsH1Pair (φ n) (grad (φ n)) := fun n => isH1Pair_test (hφt n)
  have pψ : ∀ n, IsH1Pair (ψ n) (grad (ψ n)) := fun n => isH1Pair_test (hψt n)
  have cφ : H1Tendsto φ (fun n => grad (φ n)) f g := ⟨hφ1, hφ2⟩
  have cψ : H1Tendsto ψ (fun n => grad (ψ n)) h k := ⟨hψ1, hψ2⟩
  have T1 := C4_tendsto hB hR0 ha0 ha4 pφ pφ pψ pψ hfg hfg hhk hhk cφ cφ cψ cψ
  have T2 := C4_tendsto hB hR0 ha0 ha4 pφ pφ pφ pφ hfg hfg hfg hfg cφ cφ cφ cφ
  have T3 := C4_tendsto hB hR0 ha0 ha4 pψ pψ pψ pψ hhk hhk hhk hhk cψ cψ cψ cψ
  refine le_of_tendsto_of_tendsto' (T1.pow 2) (T2.mul T3) (fun n => ?_)
  rw [C4_test_eq (hφt n) (hψt n), C4_test_eq (hφt n) (hφt n), C4_test_eq (hψt n) (hψt n)]
  exact spatialPair_sq_le hE hsp (isTest_sq (hφt n)) (isTest_sq (hψt n))

/-- `E:spatial-square-CS` (TeX lines 225-227) on `H¹` pairs, under the hypotheses of `C4_square_CS`:
`B_Γ(f², h²)` is finite and `0 ≤ B_Γ(f²,h²) ≤ √(A_sp(f) A_sp(h))` for the real values (all three
pairings finite). -/
theorem square_pairing_CS {Γ μ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ] (hE : IsEven Γ)
    (hsp : IsSpectralMeasure Γ μ) {alpha R : ℝ} (hB : SquareBound Γ alpha R) (hR0 : 0 ≤ R)
    (ha0 : 0 < alpha) (ha4 : alpha < 4)
    (hdense : ∀ (f : Rd d → ℝ) (g : Rd d → Rd d), MemLp f 2 volume → MemLp g 2 volume →
      WeakSobolev.HasWeakGradient f g →
      ∃ φ : ℕ → Rd d → ℝ, (∀ n, WeakSobolev.IsTestFunction (φ n)) ∧
        Tendsto (fun n => eLpNorm (fun x => φ n x - f x) 2 volume) atTop (𝓝 0) ∧
        Tendsto (fun n => eLpNorm (fun x => VariationalFloor.grad (φ n) x - g x) 2 volume)
          atTop (𝓝 0))
    {f h : Rd d → ℝ} {g k : Rd d → Rd d} (hfg : IsH1Pair f g) (hhk : IsH1Pair h k) :
    pairing Γ (zE fun x => f x ^ 2) (zE fun x => h x ^ 2) < ⊤ ∧
      0 ≤ (pairing Γ (zE fun x => f x ^ 2) (zE fun x => h x ^ 2)).toReal ∧
      (pairing Γ (zE fun x => f x ^ 2) (zE fun x => h x ^ 2)).toReal ≤
        Real.sqrt ((pairing Γ (zE fun x => f x ^ 2) (zE fun x => f x ^ 2)).toReal *
          (pairing Γ (zE fun x => h x ^ 2) (zE fun x => h x ^ 2)).toReal) := by
  refine ⟨(hB f h g k hfg hhk).trans_lt ENNReal.ofReal_lt_top, ENNReal.toReal_nonneg, ?_⟩
  rw [pairing_toReal_eq_C4 hfg.1.aestronglyMeasurable hhk.1.aestronglyMeasurable,
    pairing_toReal_eq_C4 hfg.1.aestronglyMeasurable hfg.1.aestronglyMeasurable,
    pairing_toReal_eq_C4 hhk.1.aestronglyMeasurable hhk.1.aestronglyMeasurable]
  exact (le_abs_self _).trans
    (Real.abs_le_sqrt (C4_square_CS hE hsp hB hR0 ha0 ha4 hdense hfg hhk))

/-! ### Multilinearity of `C₄` -/

/-- Multilinearity of `C₄` (TeX line 280), first argument: `C₄(a f + b f', f₂, f₃, f₄) = a C₄(f, …)
+ b C₄(f', …)` for `H¹` pairs under `SquareBound`, `R ≥ 0`. -/
theorem C4_linear_one {Γ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ] {alpha R : ℝ}
    (hB : SquareBound Γ alpha R) (hR0 : 0 ≤ R) {f f' f₂ f₃ f₄ : Rd d → ℝ}
    {g g' g₂ g₃ g₄ : Rd d → Rd d} (h : IsH1Pair f g) (h' : IsH1Pair f' g')
    (h₂ : IsH1Pair f₂ g₂) (h₃ : IsH1Pair f₃ g₃) (h₄ : IsH1Pair f₄ g₄) (a b : ℝ) :
    C4 Γ (fun x => a * f x + b * f' x) f₂ f₃ f₄ = a * C4 Γ f f₂ f₃ f₄ + b * C4 Γ f' f₂ f₃ f₄ := by
  have i1 : Integrable (fun p : Rd d × Rd d =>
      a * (f p.1 * f₂ p.1 * f₃ (p.1 - p.2) * f₄ (p.1 - p.2))) (pairMeasure Γ) :=
    (four_integrable hB hR0 h h₂ h₃ h₄).const_mul a
  have i2 : Integrable (fun p : Rd d × Rd d =>
      b * (f' p.1 * f₂ p.1 * f₃ (p.1 - p.2) * f₄ (p.1 - p.2))) (pairMeasure Γ) :=
    (four_integrable hB hR0 h' h₂ h₃ h₄).const_mul b
  simp only [C4]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add i1 i2]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only
  ring

/-- Multilinearity of `C₄` (TeX line 280), third argument, under the hypotheses of
`C4_linear_one`. -/
theorem C4_linear_three {Γ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ] {alpha R : ℝ}
    (hB : SquareBound Γ alpha R) (hR0 : 0 ≤ R) {f f' f₁ f₂ f₄ : Rd d → ℝ}
    {g g' g₁ g₂ g₄ : Rd d → Rd d} (h : IsH1Pair f g) (h' : IsH1Pair f' g')
    (h₁ : IsH1Pair f₁ g₁) (h₂ : IsH1Pair f₂ g₂) (h₄ : IsH1Pair f₄ g₄) (a b : ℝ) :
    C4 Γ f₁ f₂ (fun x => a * f x + b * f' x) f₄ = a * C4 Γ f₁ f₂ f f₄ + b * C4 Γ f₁ f₂ f' f₄ := by
  have i1 : Integrable (fun p : Rd d × Rd d =>
      a * (f₁ p.1 * f₂ p.1 * f (p.1 - p.2) * f₄ (p.1 - p.2))) (pairMeasure Γ) :=
    (four_integrable hB hR0 h₁ h₂ h h₄).const_mul a
  have i2 : Integrable (fun p : Rd d × Rd d =>
      b * (f₁ p.1 * f₂ p.1 * f' (p.1 - p.2) * f₄ (p.1 - p.2))) (pairMeasure Γ) :=
    (four_integrable hB hR0 h₁ h₂ h' h₄).const_mul b
  simp only [C4]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add i1 i2]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only
  ring

/-- Auxiliary to the Lean proof route: `C₄` is symmetric in its first two arguments. -/
theorem C4_comm_one_two (Γ : Measure (Rd d)) (f₁ f₂ f₃ f₄ : Rd d → ℝ) :
    C4 Γ f₁ f₂ f₃ f₄ = C4 Γ f₂ f₁ f₃ f₄ := by
  simp only [C4]; congr 1; funext p; ring

/-- Auxiliary to the Lean proof route: `C₄` is symmetric in its last two arguments. -/
theorem C4_comm_three_four (Γ : Measure (Rd d)) (f₁ f₂ f₃ f₄ : Rd d → ℝ) :
    C4 Γ f₁ f₂ f₃ f₄ = C4 Γ f₁ f₂ f₄ f₃ := by
  simp only [C4]; congr 1; funext p; ring

/-! ### Positivity of `A_sp` on nonzero profiles -/

/-- Last claim of `P:spatial-four-linear` (TeX line 236, proof lines 291-296): for a nonzero locally
finite `Γ` with the set scaling of `H:homog` and an a.e.-strongly measurable `f` that is not
a.e. zero, `A_sp(f) = B_Γ(f², f²) > 0`.  Route: a compact `K` of positive measure on which `|f|
≥ c > 0`; for `y` near `0`, `|K ∩ (y + K)| > 0` (Mathlib's continuity of the measure of
translates of a compact set, in place of the TeX's `L²` translation continuity of `1_E`); every
centred ball has positive `Γ` mass (`VariationalFloor.measure_ball_pos`).  No `H¹` membership is
used. -/
theorem pairing_sq_pos {alpha : ℝ} {Γ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ]
    (hS : VariationalDilation.SetScaling alpha Γ) (hΓ : Γ ≠ 0) {f : Rd d → ℝ}
    (hf : AEStronglyMeasurable f volume) (hne : ¬ f =ᵐ[volume] 0) :
    0 < pairing Γ (zE fun x => f x ^ 2) (zE fun x => f x ^ 2) := by
  have hFm : StronglyMeasurable (hf.mk f) := hf.stronglyMeasurable_mk
  have hfF : f =ᵐ[volume] hf.mk f := hf.ae_eq_mk
  have hz : (zE fun x => f x ^ 2) =ᵐ[volume] (zE fun x => hf.mk f x ^ 2) := by
    filter_upwards [hfF] with x hx
    simp only [zE, hx]
  rw [(OccupationKernelRow.spatial_physical_pair Γ).2.1 _ _ _ _ hz hz]
  set F := hf.mk f with hFdef
  have hpos : volume {x | F x ≠ 0} ≠ 0 := by
    intro h0
    apply hne
    have : F =ᵐ[volume] 0 := by
      rw [Filter.EventuallyEq, ae_iff]
      simpa using h0
    exact hfF.trans this
  let S : ℕ → Set (Rd d) := fun n => {x | ((n : ℝ) + 1)⁻¹ ≤ |F x|} ∩ ball 0 ((n : ℝ) + 1)
  have hSm : ∀ n, MeasurableSet (S n) := fun n =>
    (measurableSet_le measurable_const hFm.measurable.abs).inter measurableSet_ball
  have hcover : {x | F x ≠ 0} ⊆ ⋃ n, S n := by
    intro x hx
    have hax : 0 < |F x| := abs_pos.2 hx
    obtain ⟨n1, hn1⟩ := exists_nat_one_div_lt hax
    obtain ⟨n2, hn2⟩ := exists_nat_gt ‖x‖
    refine mem_iUnion.2 ⟨max n1 n2, ?_, ?_⟩
    · show ((max n1 n2 : ℕ) + 1 : ℝ)⁻¹ ≤ |F x|
      have h1 : ((n1 : ℝ) + 1)⁻¹ < |F x| := by simpa [one_div] using hn1
      refine le_trans ?_ h1.le
      gcongr
      exact_mod_cast le_max_left n1 n2
    · rw [mem_ball, dist_zero_right]
      have : (n2 : ℝ) ≤ (max n1 n2 : ℕ) := by exact_mod_cast le_max_right n1 n2
      linarith
  obtain ⟨n, hn⟩ : ∃ n, volume (S n) ≠ 0 := by
    by_contra h
    push Not at h
    exact hpos (measure_mono_null hcover (measure_iUnion_null h))
  have hfin : volume (S n) ≠ ⊤ :=
    ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne
  obtain ⟨K, hKS, hK, hKpos⟩ := (hSm n).exists_lt_isCompact_of_ne_top hfin (pos_iff_ne_zero.2 hn)
  have hKc : IsClosed K := hK.isClosed
  have hc : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
  have hcK : ∀ x ∈ K, (((n : ℝ) + 1)⁻¹) ^ 2 ≤ F x ^ 2 := fun x hx => by
    have h' : ((n : ℝ) + 1)⁻¹ ≤ |F x| := (hKS hx).1
    rw [← sq_abs (F x)]
    exact pow_le_pow_left₀ hc.le h' 2
  set T : Set (Rd d × Rd d) := {p | p.1 ∈ K ∧ p.1 - p.2 ∈ K} with hTdef
  have hTm : MeasurableSet T :=
    (measurable_fst hKc.measurableSet).inter ((measurable_fst.sub measurable_snd) hKc.measurableSet)
  have hνT : pairMeasure Γ T ≠ 0 := by
    rw [pairMeasure, Measure.prod_apply_symm hTm]
    have hGm : Measurable fun y => (volume : Measure (Rd d)) ((fun x => (x, y)) ⁻¹' T) :=
      measurable_measure_prodMk_right hTm
    have hev := eventually_nhds_zero_measure_vadd_sdiff_lt (μ := (volume : Measure (Rd d))) hK hKc
      (ε := volume K) hKpos.ne'
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
    have hGpos : ∀ y ∈ ball (0 : Rd d) r,
        (volume : Measure (Rd d)) ((fun x => (x, y)) ⁻¹' T) ≠ 0 := by
      intro y hy h0
      have hlt := hball y hy
      have hsub : (y +ᵥ K) ∩ K ⊆ (fun x => (x, y)) ⁻¹' T := by
        rintro x ⟨⟨k, hk, rfl⟩, hxK⟩
        refine ⟨hxK, ?_⟩
        simpa [vadd_eq_add] using hk
      have h1 : volume ((y +ᵥ K) ∩ K) = 0 := measure_mono_null hsub h0
      have h2 := measure_inter_add_sdiff (μ := (volume : Measure (Rd d))) (y +ᵥ K)
        hKc.measurableSet
      rw [h1, zero_add, measure_vadd] at h2
      rw [h2] at hlt
      exact lt_irrefl _ hlt
    intro h0
    rw [lintegral_eq_zero_iff hGm] at h0
    have hnull : Γ (ball (0 : Rd d) r) = 0 :=
      measure_mono_null (fun y hy => hGpos y hy) (ae_iff.1 h0)
    exact (VariationalFloor.measure_ball_pos hS hΓ hr).ne' hnull
  have hκ : (0 : ℝ≥0∞) < ENNReal.ofReal ((((n : ℝ) + 1)⁻¹) ^ 2) *
      ENNReal.ofReal ((((n : ℝ) + 1)⁻¹) ^ 2) :=
    ENNReal.mul_pos (ENNReal.ofReal_pos.2 (by positivity)).ne'
      (ENNReal.ofReal_pos.2 (by positivity)).ne'
  calc (0 : ℝ≥0∞) < ENNReal.ofReal ((((n : ℝ) + 1)⁻¹) ^ 2) *
        ENNReal.ofReal ((((n : ℝ) + 1)⁻¹) ^ 2) * pairMeasure Γ T := ENNReal.mul_pos hκ.ne' hνT
    _ = ∫⁻ p, T.indicator (fun _ => ENNReal.ofReal ((((n : ℝ) + 1)⁻¹) ^ 2) *
          ENNReal.ofReal ((((n : ℝ) + 1)⁻¹) ^ 2)) p ∂(pairMeasure Γ) :=
        (lintegral_indicator_const hTm _).symm
    _ ≤ pairing Γ (zE fun x => F x ^ 2) (zE fun x => F x ^ 2) := by
        unfold pairing zE
        refine lintegral_mono fun p => ?_
        by_cases hp : p ∈ T
        · rw [indicator_of_mem hp]
          exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hcK _ hp.1))
            (ENNReal.ofReal_le_ofReal (hcK _ hp.2))
        · rw [indicator_of_notMem hp]
          exact zero_le

/-! ### The `H¹` ratio supremum -/

/-- Auxiliary to the Lean proof route: `‖f‖₂ = √(∫ f²)` for real `f ∈ L²`. -/
theorem l2_eq_sqrt {f : Rd d → ℝ} (hf : MemLp f 2 volume) : l2 f = Real.sqrt (∫ x, f x ^ 2) := by
  rw [integral_sq_eq_l2_sq hf, Real.sqrt_sq (l2_nonneg f)]

/-- Auxiliary to the Lean proof route: `‖g‖₂ = √(∫ ‖g‖²)` for `g ∈ L²`. -/
theorem l2_eq_sqrt' {g : Rd d → Rd d} (hg : MemLp g 2 volume) :
    l2 g = Real.sqrt (∫ x, ‖g x‖ ^ 2) := by
  rw [← l2_sq hg, Real.sqrt_sq (l2_nonneg g)]

/-- Auxiliary to the Lean proof route: `N(f) = √(∫ f²)^{1-α/4} √(∫ ‖g‖²)^{α/4}` for `f, g ∈ L²` (the
spelling used by `OccupationPhysicalClass.Nnorm` of wave item L7-e). -/
theorem Nnorm_eq_sqrt (alpha : ℝ) {f : Rd d → ℝ} {g : Rd d → Rd d} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) :
    Nnorm alpha f g = Real.sqrt (∫ x, f x ^ 2) ^ (1 - alpha / 4) *
      Real.sqrt (∫ x, ‖g x‖ ^ 2) ^ (alpha / 4) := by
  rw [Nnorm, l2_eq_sqrt hf, l2_eq_sqrt' hg]

/-- Every real unit `H¹` profile has positive gradient energy (TeX lines 288-289): for `d ≥ 1` and a
unit `H¹` pair `(f, g)`, `∫ ‖g‖² > 0`.  Lean route: `g = 0` a.e. would make `0` a weak gradient
of `f`, so `f = 0` a.e. (`VariationalFloor.ae_eq_zero_of_hasWeakGradient_zero`, mollification),
contradicting `∫ f² = 1`; the TeX uses the Fourier support argument of lines 180-182. -/
theorem gradL2_pos (hd : 0 < d) {f : Rd d → ℝ} {g : Rd d → Rd d} (h : IsUnitH1 f g) :
    0 < ∫ x, ‖g x‖ ^ 2 := by
  obtain ⟨hf, hg, hw, h1⟩ := h
  have hi : Integrable (fun x => ‖g x‖ ^ 2) volume := by
    have := hg.integrable_norm_rpow (by norm_num) (by norm_num)
    simpa [ENNReal.toReal_ofNat, rpow_two] using this
  refine lt_of_le_of_ne (integral_nonneg fun _ => by positivity) (fun h0 => ?_)
  have hae : (fun x => ‖g x‖ ^ 2) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun _ => by positivity) hi).1 h0.symm
  have hg0 : HasWeakGradient f 0 := by
    intro φ hφ v
    rw [hw φ hφ v]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    have : g x = 0 := by simpa using hx
    simp [this]
  have hf0 := VariationalFloor.ae_eq_zero_of_hasWeakGradient_zero hd hf hg0
  have h2 : ∫ x, f x ^ 2 = 0 := by
    rw [integral_congr_ae (hf0.mono fun x hx => by simp [hx] :
      (fun x => f x ^ 2) =ᵐ[volume] fun _ => (0 : ℝ))]
    simp
  rw [h1] at h2
  exact one_ne_zero h2

/-- The `H¹` ratio set `{A_sp(g)/b(g)^{α/2}}` over real unit `H¹` pairs (TeX line 235), with `A_sp`
the real value of the extended pairing (finite by `E:spatial-homogeneous-bound`) and `b(g) = ∫
‖∇g‖²`. -/
def ratioSetH1 (Γ : Measure (Rd d)) (alpha : ℝ) : Set ℝ :=
  {r | ∃ (f : Rd d → ℝ) (g : Rd d → Rd d), IsUnitH1 f g ∧
    (pairing Γ (zE fun x => f x ^ 2) (zE fun x => f x ^ 2)).toReal /
      (∫ x, ‖g x‖ ^ 2) ^ (alpha / 2) = r}

/-- `R_sp = sup ratioSetH1` (TeX line 235); a genuine supremum where `Rsp_eq_R0` applies. -/
def Rsp (Γ : Measure (Rd d)) (alpha : ℝ) : ℝ := sSup (ratioSetH1 Γ alpha)

/-- Auxiliary to the Lean proof route: under `SquareBound Γ α R`, `R ≥ 0`, a unit `H¹` pair has
`A_sp(f) ≤ R b^{α/2}` (real value; `N(f)⁴ = b^{α/2}` when `‖f‖₂ = 1`). -/
theorem unitH1_A_le {Γ : Measure (Rd d)} {alpha R : ℝ} (hB : SquareBound Γ alpha R)
    (hR0 : 0 ≤ R) {f : Rd d → ℝ} {g : Rd d → Rd d} (h : IsUnitH1 f g) :
    (pairing Γ (zE fun x => f x ^ 2) (zE fun x => f x ^ 2)).toReal ≤
      R * (∫ x, ‖g x‖ ^ 2) ^ (alpha / 2) := by
  obtain ⟨hf, hg, hw, h1⟩ := h
  have hA := hB f f g g ⟨hf, hg, hw⟩ ⟨hf, hg, hw⟩
  have hN : R * Nnorm alpha f g ^ 2 * Nnorm alpha f g ^ 2 =
      R * (∫ x, ‖g x‖ ^ 2) ^ (alpha / 2) := by
    rw [mul_assoc, ← pow_add, Nnorm_pow_four, ← integral_sq_eq_l2_sq hf, h1, one_rpow, one_mul,
      l2_sq hg]
  rw [hN] at hA
  exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hR0 (rpow_nonneg
    (integral_nonneg fun _ => by positivity) _)) hA

/-- Auxiliary to the Lean proof route: for a real unit test `g`, the real value of the extended
`A_sp(g)` is `spatialEnergy Γ g` and `∫ ‖∇g‖² = b(g)`. -/
theorem unitTest_bridge {Γ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ] {g : Rd d → ℝ}
    (hg : IsUnitTest g) :
    (pairing Γ (zE fun x => g x ^ 2) (zE fun x => g x ^ 2)).toReal = spatialEnergy Γ g ∧
      ∫ x, ‖grad g x‖ ^ 2 = gradEnergy g := by
  have ht : IsTestFunction g := ⟨hg.1, hg.2.1⟩
  refine ⟨(SpatialStaticControls.pairing_eq_spatialPair (isTest_sq ht).1.continuous
    (isTest_sq ht).2 (fun _ => sq_nonneg _) (isTest_sq ht).1.continuous (isTest_sq ht).2
    (fun _ => sq_nonneg _)).2.2, ?_⟩
  rw [gradEnergy_eq_l2_sq ht, l2_sq (VariationalFloor.memLp_grad ht)]

/-- `R_sp = R_0` (TeX lines 235-236, 288-291): for `d ≥ 1`, locally finite `Γ`, `SquareBound Γ α
R_0`, a nonempty smooth ratio set and `R_0 ≥ 0`: every unit `H¹` pair has `b > 0` and ratio at
most `R_0`; the `H¹` ratio set is nonempty and bounded above; and its supremum is `R_0` (the
homogeneous bound gives `≤`, smooth inclusion `≥`). -/
theorem Rsp_eq_R0 {Γ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ] {alpha : ℝ} (hd : 0 < d)
    (hB : SquareBound Γ alpha (R0 Γ alpha)) (hne : (ratioSet Γ alpha).Nonempty)
    (hR0 : 0 ≤ R0 Γ alpha) :
    (∀ (f : Rd d → ℝ) (g : Rd d → Rd d), IsUnitH1 f g → 0 < ∫ x, ‖g x‖ ^ 2 ∧
      (pairing Γ (zE fun x => f x ^ 2) (zE fun x => f x ^ 2)).toReal /
        (∫ x, ‖g x‖ ^ 2) ^ (alpha / 2) ≤ R0 Γ alpha) ∧
      (ratioSetH1 Γ alpha).Nonempty ∧ BddAbove (ratioSetH1 Γ alpha) ∧
      Rsp Γ alpha = R0 Γ alpha := by
  have hall : ∀ (f : Rd d → ℝ) (g : Rd d → Rd d), IsUnitH1 f g → 0 < ∫ x, ‖g x‖ ^ 2 ∧
      (pairing Γ (zE fun x => f x ^ 2) (zE fun x => f x ^ 2)).toReal /
        (∫ x, ‖g x‖ ^ 2) ^ (alpha / 2) ≤ R0 Γ alpha := by
    intro f g h
    have hb := gradL2_pos hd h
    exact ⟨hb, (div_le_iff₀ (rpow_pos_of_pos hb _)).2 (unitH1_A_le hB hR0 h)⟩
  have hsub : ratioSet Γ alpha ⊆ ratioSetH1 Γ alpha := by
    rintro _ ⟨g, hg, rfl⟩
    refine ⟨g, grad g, SpatialStaticControls.isUnitH1_of_unitTest hg, ?_⟩
    rw [(unitTest_bridge (Γ := Γ) hg).1, (unitTest_bridge (Γ := Γ) hg).2]
    rfl
  have hbddH : BddAbove (ratioSetH1 Γ alpha) := by
    refine ⟨R0 Γ alpha, ?_⟩
    rintro _ ⟨f, g, h, rfl⟩
    exact (hall f g h).2
  refine ⟨hall, hne.mono hsub, hbddH, le_antisymm ?_ (csSup_le_csSup hbddH hne hsub)⟩
  refine csSup_le (hne.mono hsub) ?_
  rintro _ ⟨f, g, h, rfl⟩
  exact (hall f g h).2

/-! ### The spatial energy -/

/-- The value set `{A_sp(g) - b(g)/2}` over real unit `H¹` profiles (TeX lines 302-306). -/
def energySet (Γ : Measure (Rd d)) : Set ℝ :=
  {e | ∃ (f : Rd d → ℝ) (g : Rd d → Rd d), IsUnitH1 f g ∧
    (pairing Γ (zE fun x => f x ^ 2) (zE fun x => f x ^ 2)).toReal - (∫ x, ‖g x‖ ^ 2) / 2 = e}

/-- `𝓔_sp = sup energySet` (TeX lines 304-306); a genuine supremum where `energy_map` applies. -/
def Esp (Γ : Measure (Rd d)) : ℝ := sSup (energySet Γ)

/-- `(2-α)/2 · α^{α/(2-α)} · R^{2/(2-α)}`, the right side of `E:spatial-energy-map` at `R_sp = R`
(same body as `OccupationPhysicalClass.spEnergyVal` of wave item L7-e). -/
def energyValue (alpha R : ℝ) : ℝ :=
  (2 - alpha) / 2 * alpha ^ (alpha / (2 - alpha)) * R ^ (2 / (2 - alpha))

/-- Auxiliary to the Lean proof route: the scalar maximum (TeX lines 330-335, upper half): for `0 <
α < 2`, `R ≥ 0`, `β ≥ 0`, `R β^{α/2} - β/2 ≤ (2-α)/2 α^{α/(2-α)} R^{2/(2-α)}` (weighted AM-GM). -/
theorem young_bound {alpha R β : ℝ} (ha0 : 0 < alpha) (ha2 : alpha < 2) (hR : 0 ≤ R)
    (hβ : 0 ≤ β) : R * β ^ (alpha / 2) - β / 2 ≤ energyValue alpha R := by
  have h2a : 0 < 2 - alpha := by linarith
  have hp2 : 0 ≤ (alpha ^ (alpha / 2) * R) ^ (2 / (2 - alpha)) := by positivity
  have key := Real.geom_mean_le_arith_mean2_weighted (w₁ := alpha / 2) (w₂ := 1 - alpha / 2)
    (p₁ := β / alpha) (p₂ := (alpha ^ (alpha / 2) * R) ^ (2 / (2 - alpha))) (by positivity)
    (by linarith) (by positivity) hp2 (by ring)
  have hαα : 0 < alpha ^ (alpha / 2) := rpow_pos_of_pos ha0 _
  have e1 : (β / alpha) ^ (alpha / 2) = β ^ (alpha / 2) / alpha ^ (alpha / 2) :=
    div_rpow hβ ha0.le _
  have e2 : ((alpha ^ (alpha / 2) * R) ^ (2 / (2 - alpha))) ^ (1 - alpha / 2) =
      alpha ^ (alpha / 2) * R := by
    rw [← rpow_mul (by positivity)]
    rw [show 2 / (2 - alpha) * (1 - alpha / 2) = 1 by field_simp, rpow_one]
  have e3 : (alpha ^ (alpha / 2) * R) ^ (2 / (2 - alpha)) =
      alpha ^ (alpha / (2 - alpha)) * R ^ (2 / (2 - alpha)) := by
    rw [mul_rpow hαα.le hR, ← rpow_mul ha0.le]
    congr 2; field_simp
  rw [e1, e2, e3] at key
  have e4 : β ^ (alpha / 2) / alpha ^ (alpha / 2) * (alpha ^ (alpha / 2) * R) =
      R * β ^ (alpha / 2) := by
    field_simp
  rw [e4] at key
  unfold energyValue
  have e5 : alpha / 2 * (β / alpha) = β / 2 := by field_simp
  rw [e5] at key
  linarith

/-- Auxiliary to the Lean proof route: the scalar maximum is attained (TeX lines 330-335): for `0 <
α < 2`, `R > 0`, at `β = (αR)^{2/(2-α)}`. -/
theorem energy_attain {alpha R : ℝ} (ha0 : 0 < alpha) (ha2 : alpha < 2) (hR : 0 < R) :
    R * ((alpha * R) ^ (2 / (2 - alpha))) ^ (alpha / 2) - (alpha * R) ^ (2 / (2 - alpha)) / 2 =
      energyValue alpha R := by
  have h2a : 0 < 2 - alpha := by linarith
  have hαR : 0 < alpha * R := mul_pos ha0 hR
  set e := alpha / (2 - alpha) with he
  have e1 : ((alpha * R) ^ (2 / (2 - alpha))) ^ (alpha / 2) = (alpha * R) ^ e := by
    rw [← rpow_mul hαR.le, he]; congr 1; field_simp
  have e2 : (alpha * R) ^ (2 / (2 - alpha)) = (alpha * R) * (alpha * R) ^ e := by
    rw [show 2 / (2 - alpha) = 1 + e by rw [he]; field_simp; ring, rpow_add hαR, rpow_one]
  have e3 : energyValue alpha R = (2 - alpha) / 2 * R * (alpha * R) ^ e := by
    unfold energyValue
    rw [show 2 / (2 - alpha) = 1 + e by rw [he]; field_simp; ring, rpow_add hR, rpow_one,
      mul_rpow ha0.le hR.le]
    ring
  rw [e1, e2, e3]
  ring

/-- Auxiliary to the Lean proof route: `R ↦ energyValue α R` is continuous for `α < 2`. -/
theorem energyValue_continuous {alpha : ℝ} (ha2 : alpha < 2) :
    Continuous (energyValue alpha) :=
  continuous_const.mul (Real.continuous_rpow_const (div_nonneg zero_le_two (by linarith)))

/-- Auxiliary to the Lean proof route: for a real unit test `g` (`d ≥ 1`, `Γ ≠ 0` locally finite
with the set scaling, `0 < α < 2`), the dilation `U_ℓ g` with the optimal `ℓ` (TeX line 331,
`ℓ^{2-α} = α A/b`) is a unit `H¹` profile with energy `energyValue α (R(g))`; uses the smooth
`E:spatial-dilation` (`SpatialSmoothRatio.spatialEnergy_dilL2`, `gradEnergy_dilL2`). -/
theorem energyValue_mem {alpha : ℝ} {Γ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ]
    (hS : VariationalDilation.SetScaling alpha Γ) (hΓ : Γ ≠ 0) (hd : 0 < d) (ha0 : 0 < alpha)
    (ha2 : alpha < 2) {g : Rd d → ℝ} (hg : IsUnitTest g) :
    energyValue alpha (ratio Γ alpha g) ∈ energySet Γ := by
  have hb := SpatialFourierBound.gradEnergy_pos hd hg
  have hA := SpatialSmoothRatio.spatialEnergy_pos hS hΓ hg
  have hbα : 0 < gradEnergy g ^ (alpha / 2) := rpow_pos_of_pos hb _
  have hr : 0 < ratio Γ alpha g := div_pos hA hbα
  set r := ratio Γ alpha g with hrdef
  set β := (alpha * r) ^ (2 / (2 - alpha)) with hβ
  have hβ0 : 0 < β := rpow_pos_of_pos (mul_pos ha0 hr) _
  set ℓ := Real.sqrt (β / gradEnergy g) with hℓdef
  have hℓ : 0 < ℓ := Real.sqrt_pos.2 (div_pos hβ0 hb)
  have hU := SpatialSmoothRatio.isUnitTest_dilL2 hℓ hg
  refine ⟨_, grad (WeakSobolev.dilL2 ℓ g), SpatialStaticControls.isUnitH1_of_unitTest hU, ?_⟩
  rw [(unitTest_bridge (Γ := Γ) hU).1, (unitTest_bridge (Γ := Γ) hU).2,
    SpatialSmoothRatio.spatialEnergy_dilL2 hS hℓ hg.1.continuous hg.2.1,
    SpatialSmoothRatio.gradEnergy_dilL2 hℓ (hg.1.differentiable (by simp))]
  have hℓ2 : ℓ ^ 2 = β / gradEnergy g := Real.sq_sqrt (div_pos hβ0 hb).le
  have hℓα : ℓ ^ alpha = β ^ (alpha / 2) / gradEnergy g ^ (alpha / 2) := by
    rw [show ℓ ^ alpha = (ℓ ^ 2) ^ (alpha / 2) by
      rw [← rpow_natCast, ← rpow_mul hℓ.le]; congr 1; push_cast; ring, hℓ2,
      div_rpow hβ0.le hb.le]
  rw [hℓα, hℓ2, ← energy_attain ha0 ha2 hr]
  have hA' : spatialEnergy Γ g = r * gradEnergy g ^ (alpha / 2) := by
    rw [hrdef, ratio, div_mul_cancel₀ _ hbα.ne']
  rw [hA']
  field_simp
  rw [← hβ]
  ring

/-- `E:spatial-energy-map` with `R_0` (TeX lines 309-314, proof 327-338), general form: for `d ≥ 1`,
`Γ ≠ 0` locally finite with the set scaling, `0 < α < 2`, `SquareBound Γ α R_0`, nonempty
bounded smooth ratio set and `R_0 > 0`: the energy set is nonempty and bounded above, `𝓔_sp =
(2-α)/2 α^{α/(2-α)} R_0^{2/(2-α)}` and `𝓔_sp > 0`.  Lean route (differs from the TeX): the upper
bound applies `E:spatial-homogeneous-bound` and the scalar maximum to every unit `H¹` profile
(no dilation of `H¹` profiles); the lower bound dilates smooth unit tests and lets their ratios
increase to `R_0` along a sequence (continuity of the scalar map).  No optimizer is assumed. -/
theorem energy_map {Γ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ] {alpha : ℝ}
    (hS : VariationalDilation.SetScaling alpha Γ) (hΓ : Γ ≠ 0) (hd : 0 < d) (ha0 : 0 < alpha)
    (ha2 : alpha < 2) (hB : SquareBound Γ alpha (R0 Γ alpha)) (hne : (ratioSet Γ alpha).Nonempty)
    (hbdd : BddAbove (ratioSet Γ alpha)) (hR0 : 0 < R0 Γ alpha) :
    (energySet Γ).Nonempty ∧ BddAbove (energySet Γ) ∧
      Esp Γ = energyValue alpha (R0 Γ alpha) ∧ 0 < Esp Γ := by
  have hup : ∀ e ∈ energySet Γ, e ≤ energyValue alpha (R0 Γ alpha) := by
    rintro _ ⟨f, g, h, rfl⟩
    have h1 := unitH1_A_le hB hR0.le h
    have h2 := young_bound ha0 ha2 hR0.le (integral_nonneg fun x => by positivity :
      0 ≤ ∫ x, ‖g x‖ ^ 2)
    linarith
  have hneE : (energySet Γ).Nonempty := by
    obtain ⟨f, g, h⟩ := SpatialStaticControls.exists_isUnitH1 (d := d)
    exact ⟨_, f, g, h, rfl⟩
  have hbddE : BddAbove (energySet Γ) := ⟨_, hup⟩
  have hle : Esp Γ ≤ energyValue alpha (R0 Γ alpha) := csSup_le hneE hup
  have hge : energyValue alpha (R0 Γ alpha) ≤ Esp Γ := by
    obtain ⟨u, -, hu, hmem⟩ := exists_seq_tendsto_sSup hne hbdd
    refine le_of_tendsto' (((energyValue_continuous ha2).tendsto _).comp hu) (fun n => ?_)
    obtain ⟨g, hg, hgu⟩ := hmem n
    show energyValue alpha (u n) ≤ Esp Γ
    rw [← hgu]
    exact le_csSup hbddE (energyValue_mem hS hΓ hd ha0 ha2 hg)
  have heq := le_antisymm hle hge
  refine ⟨hneE, hbddE, heq, ?_⟩
  rw [heq]
  unfold energyValue
  have : 0 < 2 - alpha := by linarith
  have := rpow_pos_of_pos ha0 (alpha / (2 - alpha))
  have := rpow_pos_of_pos hR0 (2 / (2 - alpha))
  positivity

/-! ### The static energy score -/

/-- `F₀(z) = k [(2z/(2-α))^{(2-α)/2}/(8 q^{q/2})]^{1/k}`, `k = 3-α`, `q = 4-α` (TeX lines
319-321). -/
def F0 (alpha z : ℝ) : ℝ :=
  (3 - alpha) * ((2 * z / (2 - alpha)) ^ ((2 - alpha) / 2) /
    (8 * (4 - alpha) ^ ((4 - alpha) / 2))) ^ (1 / (3 - alpha))

/-- Auxiliary to the Lean proof route: the substitution of TeX lines 341-346: for `0 < α < 2`, `M_a
> 0`, `R ≥ 0`, `k [R α^{α/2}/(8 M_a q^{q/2})]^{1/k} = M_a^{-1/k} F₀((2-α)/2 α^{α/(2-α)}
R^{2/(2-α)})`. -/
theorem score_identity {alpha a R : ℝ} (ha0 : 0 < alpha) (ha2 : alpha < 2)
    (hM : 0 < TemporalEquilibrium.mass a) (hR : 0 ≤ R) :
    SpatialSmoothRatio.smoothScoreBound alpha a R =
      TemporalEquilibrium.mass a ^ (-(1 / (3 - alpha))) * F0 alpha (energyValue alpha R) := by
  have h2a : 0 < 2 - alpha := by linarith
  have hq : 0 < (4 - alpha) ^ ((4 - alpha) / 2) := rpow_pos_of_pos (by linarith) _
  have e1 : (2 * energyValue alpha R / (2 - alpha)) ^ ((2 - alpha) / 2) =
      alpha ^ (alpha / 2) * R := by
    have : 2 * energyValue alpha R / (2 - alpha) =
        alpha ^ (alpha / (2 - alpha)) * R ^ (2 / (2 - alpha)) := by
      unfold energyValue; field_simp
    rw [this, mul_rpow (by positivity) (by positivity), ← rpow_mul ha0.le, ← rpow_mul hR,
      show alpha / (2 - alpha) * ((2 - alpha) / 2) = alpha / 2 by field_simp,
      show 2 / (2 - alpha) * ((2 - alpha) / 2) = 1 by field_simp, rpow_one]
  unfold F0 SpatialSmoothRatio.smoothScoreBound
  rw [e1]
  have e2 : R * alpha ^ (alpha / 2) / (8 * TemporalEquilibrium.mass a *
      (4 - alpha) ^ ((4 - alpha) / 2)) = alpha ^ (alpha / 2) * R /
        (8 * (4 - alpha) ^ ((4 - alpha) / 2)) * (TemporalEquilibrium.mass a)⁻¹ := by
    field_simp
  rw [e2, mul_rpow (by positivity) (inv_nonneg.2 hM.le), inv_rpow hM.le, ← rpow_neg hM.le]
  ring

/-- Auxiliary to the Lean proof route: the right side of `E:spatial-smooth-score` is continuous in
`R` (`α < 3`). -/
theorem smoothScoreBound_continuous (alpha a : ℝ) (ha3 : alpha < 3) :
    Continuous (SpatialSmoothRatio.smoothScoreBound alpha a) := by
  unfold SpatialSmoothRatio.smoothScoreBound
  exact continuous_const.mul ((Real.continuous_rpow_const
    (div_nonneg zero_le_one (by linarith))).comp
    ((continuous_id.mul continuous_const).div_const _))

/-! ### The manuscript's statements under the section's standing assumptions -/

/-- Auxiliary to the Lean proof route: under the section's standing assumptions (`H:homog`, `Γ ≠ 0`)
and the density input: `d ≥ 1`, `0 < α < 2`, the smooth ratio set is nonempty and bounded above,
`R_0 > 0`, and `SquareBound Γ α R_0` (smooth bound from `P:spatial-smooth-ratio`, then
`squareBound_of_smooth`). -/
theorem squareBound_R0 {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0)
    (hdense : ∀ (f : Rd d → ℝ) (g : Rd d → Rd d), MemLp f 2 volume → MemLp g 2 volume →
      WeakSobolev.HasWeakGradient f g →
      ∃ φ : ℕ → Rd d → ℝ, (∀ n, WeakSobolev.IsTestFunction (φ n)) ∧
        Tendsto (fun n => eLpNorm (fun x => φ n x - f x) 2 volume) atTop (𝓝 0) ∧
        Tendsto (fun n => eLpNorm (fun x => VariationalFloor.grad (φ n) x - g x) 2 volume)
          atTop (𝓝 0)) :
    0 < d ∧ 0 < alpha ∧ alpha < 2 ∧ (ratioSet Γ alpha).Nonempty ∧
      BddAbove (ratioSet Γ alpha) ∧ 0 < R0 Γ alpha ∧ SquareBound Γ alpha (R0 Γ alpha) := by
  obtain ⟨hd, ha0, ha2, -⟩ := SpatialSmoothRatio.homog_consequences hH
  have := hH.Γ_radon
  obtain ⟨-, -, hne, hbdd, hR0, -, hle⟩ := SpatialSmoothRatio.spatial_smooth_ratio_R0_paper hH hΓ
  have hR : ∀ g, IsUnitTest g → spatialEnergy Γ g ≤ R0 Γ alpha * gradEnergy g ^ (alpha / 2) := by
    intro g hg
    have hb := SpatialFourierBound.gradEnergy_pos hd hg
    have h := hle g hg
    rwa [ratio, div_le_iff₀ (rpow_pos_of_pos hb _)] at h
  have hbd : ∀ φ, IsTestFunction φ → spatialEnergy Γ φ ≤ R0 Γ alpha * Nnorm alpha φ (grad φ) ^ 4 :=
    fun φ hφ => smooth_homog_bound (by linarith) hR hφ
  refine ⟨hd, ha0, ha2, hne, hbdd, hR0, squareBound_of_smooth ha0.le (by linarith) hdense
    fun φ ψ hφ hψ => smooth_pairing_bound hH.Γ_even hH.spectral hR0.le hbd hφ hψ⟩

/-- **`E:spatial-homogeneous-bound`** (TeX line 224) under the standing assumptions of Section
`S:spatial-occupation-foundation` (lines 4-10: `H:homog` with `a = α₀`, `Γ ≠ 0`) and the named
density input `hdense`: for every real `f ∈ H¹` (an `H¹` pair `(f, g)`), `A_sp(f) ≤ R_0 N(f)⁴`
in `[0,∞]`; in particular `A_sp(f) < ∞`. -/
theorem spatial_homogeneous_bound_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0)
    (hdense : ∀ (f : Rd d → ℝ) (g : Rd d → Rd d), MemLp f 2 volume → MemLp g 2 volume →
      WeakSobolev.HasWeakGradient f g →
      ∃ φ : ℕ → Rd d → ℝ, (∀ n, WeakSobolev.IsTestFunction (φ n)) ∧
        Tendsto (fun n => eLpNorm (fun x => φ n x - f x) 2 volume) atTop (𝓝 0) ∧
        Tendsto (fun n => eLpNorm (fun x => VariationalFloor.grad (φ n) x - g x) 2 volume)
          atTop (𝓝 0))
    {f : Rd d → ℝ} {g : Rd d → Rd d} (hfg : IsH1Pair f g) :
    pairing Γ (zE fun x => f x ^ 2) (zE fun x => f x ^ 2) ≤
      ENNReal.ofReal (R0 Γ alpha * Nnorm alpha f g ^ 4) := by
  obtain ⟨-, -, -, -, -, -, hB⟩ := squareBound_R0 hH hΓ hdense
  have h := hB f f g g hfg hfg
  rwa [mul_assoc, ← pow_add] at h

/-- **`E:spatial-square-CS`** (TeX lines 225-227) under the standing assumptions and `hdense`: for
real `f, h ∈ H¹`, `B_Γ(f², h²)` is finite and `0 ≤ B_Γ(f²,h²) ≤ √(A_sp(f) A_sp(h))` (real
values; all three are finite). -/
theorem spatial_square_CS_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0)
    (hdense : ∀ (f : Rd d → ℝ) (g : Rd d → Rd d), MemLp f 2 volume → MemLp g 2 volume →
      WeakSobolev.HasWeakGradient f g →
      ∃ φ : ℕ → Rd d → ℝ, (∀ n, WeakSobolev.IsTestFunction (φ n)) ∧
        Tendsto (fun n => eLpNorm (fun x => φ n x - f x) 2 volume) atTop (𝓝 0) ∧
        Tendsto (fun n => eLpNorm (fun x => VariationalFloor.grad (φ n) x - g x) 2 volume)
          atTop (𝓝 0))
    {f h : Rd d → ℝ} {g k : Rd d → Rd d} (hfg : IsH1Pair f g) (hhk : IsH1Pair h k) :
    pairing Γ (zE fun x => f x ^ 2) (zE fun x => h x ^ 2) < ⊤ ∧
      0 ≤ (pairing Γ (zE fun x => f x ^ 2) (zE fun x => h x ^ 2)).toReal ∧
      (pairing Γ (zE fun x => f x ^ 2) (zE fun x => h x ^ 2)).toReal ≤
        Real.sqrt ((pairing Γ (zE fun x => f x ^ 2) (zE fun x => f x ^ 2)).toReal *
          (pairing Γ (zE fun x => h x ^ 2) (zE fun x => h x ^ 2)).toReal) := by
  obtain ⟨-, ha0, ha2, -, -, hR0, hB⟩ := squareBound_R0 hH hΓ hdense
  have := hH.Γ_radon
  exact square_pairing_CS hH.Γ_even hH.spectral hB hR0.le ha0 (by linarith) hdense hfg hhk

/-- **`E:spatial-four-linear`** and absolute convergence of `C₄` (TeX lines 229-234) under the
standing assumptions and `hdense`: for four real `H¹` profiles, `∫ |f₁ f₂ f₃(·-y) f₄(·-y)| dν ≤
R_0 ∏ N(f_j)`, the integrand is `ν`-integrable, and `|C₄| ≤ R_0 ∏ N(f_j)`. -/
theorem spatial_four_linear_bound_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0)
    (hdense : ∀ (f : Rd d → ℝ) (g : Rd d → Rd d), MemLp f 2 volume → MemLp g 2 volume →
      WeakSobolev.HasWeakGradient f g →
      ∃ φ : ℕ → Rd d → ℝ, (∀ n, WeakSobolev.IsTestFunction (φ n)) ∧
        Tendsto (fun n => eLpNorm (fun x => φ n x - f x) 2 volume) atTop (𝓝 0) ∧
        Tendsto (fun n => eLpNorm (fun x => VariationalFloor.grad (φ n) x - g x) 2 volume)
          atTop (𝓝 0))
    {f₁ f₂ f₃ f₄ : Rd d → ℝ} {g₁ g₂ g₃ g₄ : Rd d → Rd d} (h₁ : IsH1Pair f₁ g₁)
    (h₂ : IsH1Pair f₂ g₂) (h₃ : IsH1Pair f₃ g₃) (h₄ : IsH1Pair f₄ g₄) :
    ∫⁻ p, ‖f₁ p.1 * f₂ p.1 * f₃ (p.1 - p.2) * f₄ (p.1 - p.2)‖ₑ ∂(pairMeasure Γ) ≤
        ENNReal.ofReal (R0 Γ alpha * (Nnorm alpha f₁ g₁ * Nnorm alpha f₂ g₂ *
          Nnorm alpha f₃ g₃ * Nnorm alpha f₄ g₄)) ∧
      Integrable (fun p : Rd d × Rd d => f₁ p.1 * f₂ p.1 * f₃ (p.1 - p.2) * f₄ (p.1 - p.2))
        (pairMeasure Γ) ∧
      |C4 Γ f₁ f₂ f₃ f₄| ≤ R0 Γ alpha * (Nnorm alpha f₁ g₁ * Nnorm alpha f₂ g₂ *
          Nnorm alpha f₃ g₃ * Nnorm alpha f₄ g₄) := by
  obtain ⟨-, -, -, -, -, hR0, hB⟩ := squareBound_R0 hH hΓ hdense
  have := hH.Γ_radon
  exact ⟨four_lintegral_le hB hR0.le h₁ h₂ h₃ h₄, four_integrable hB hR0.le h₁ h₂ h₃ h₄,
    abs_C4_le hB hR0.le h₁ h₂ h₃ h₄⟩

/-- Multilinearity of `C₄` (TeX line 280) under the standing assumptions and `hdense`: `C₄` is
linear in each of its four `H¹` arguments. -/
theorem spatial_four_linear_multilinear_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0)
    (hdense : ∀ (f : Rd d → ℝ) (g : Rd d → Rd d), MemLp f 2 volume → MemLp g 2 volume →
      WeakSobolev.HasWeakGradient f g →
      ∃ φ : ℕ → Rd d → ℝ, (∀ n, WeakSobolev.IsTestFunction (φ n)) ∧
        Tendsto (fun n => eLpNorm (fun x => φ n x - f x) 2 volume) atTop (𝓝 0) ∧
        Tendsto (fun n => eLpNorm (fun x => VariationalFloor.grad (φ n) x - g x) 2 volume)
          atTop (𝓝 0))
    {f f' f₁ f₂ f₃ f₄ : Rd d → ℝ} {g g' g₁ g₂ g₃ g₄ : Rd d → Rd d} (h : IsH1Pair f g)
    (h' : IsH1Pair f' g') (h₁ : IsH1Pair f₁ g₁) (h₂ : IsH1Pair f₂ g₂) (h₃ : IsH1Pair f₃ g₃)
    (h₄ : IsH1Pair f₄ g₄) (a b : ℝ) :
    C4 Γ (fun x => a * f x + b * f' x) f₂ f₃ f₄ = a * C4 Γ f f₂ f₃ f₄ + b * C4 Γ f' f₂ f₃ f₄ ∧
      C4 Γ f₁ (fun x => a * f x + b * f' x) f₃ f₄ =
        a * C4 Γ f₁ f f₃ f₄ + b * C4 Γ f₁ f' f₃ f₄ ∧
      C4 Γ f₁ f₂ (fun x => a * f x + b * f' x) f₄ =
        a * C4 Γ f₁ f₂ f f₄ + b * C4 Γ f₁ f₂ f' f₄ ∧
      C4 Γ f₁ f₂ f₃ (fun x => a * f x + b * f' x) =
        a * C4 Γ f₁ f₂ f₃ f + b * C4 Γ f₁ f₂ f₃ f' := by
  obtain ⟨-, -, -, -, -, hR0, hB⟩ := squareBound_R0 hH hΓ hdense
  have := hH.Γ_radon
  refine ⟨C4_linear_one hB hR0.le h h' h₂ h₃ h₄ a b, ?_,
    C4_linear_three hB hR0.le h h' h₁ h₂ h₄ a b, ?_⟩
  · rw [C4_comm_one_two, C4_linear_one hB hR0.le h h' h₁ h₃ h₄ a b, C4_comm_one_two Γ f,
      C4_comm_one_two Γ f']
  · rw [C4_comm_three_four, C4_linear_three hB hR0.le h h' h₁ h₂ h₃ a b,
      C4_comm_three_four Γ f₁ f₂ f,
      C4_comm_three_four Γ f₁ f₂ f']

/-- Joint continuity of `C₄` on `(H¹)⁴` (TeX lines 229-230, 281-283) under the standing assumptions
and `hdense`, in sequential form (`H¹` convergence of functions and weak gradients in `L²`).
Since `A_sp(f) = C₄(f,f,f,f)` and `B_Γ(f²,h²) = C₄(f,f,h,h)` as real values
(`pairing_toReal_eq_C4`), this gives the continuity of `A_sp` and of the square pairings (TeX
lines 282-283). -/
theorem spatial_four_linear_continuous_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0)
    (hdense : ∀ (f : Rd d → ℝ) (g : Rd d → Rd d), MemLp f 2 volume → MemLp g 2 volume →
      WeakSobolev.HasWeakGradient f g →
      ∃ φ : ℕ → Rd d → ℝ, (∀ n, WeakSobolev.IsTestFunction (φ n)) ∧
        Tendsto (fun n => eLpNorm (fun x => φ n x - f x) 2 volume) atTop (𝓝 0) ∧
        Tendsto (fun n => eLpNorm (fun x => VariationalFloor.grad (φ n) x - g x) 2 volume)
          atTop (𝓝 0))
    {u₁ u₂ u₃ u₄ : ℕ → Rd d → ℝ} {v₁ v₂ v₃ v₄ : ℕ → Rd d → Rd d}
    {f₁ f₂ f₃ f₄ : Rd d → ℝ} {g₁ g₂ g₃ g₄ : Rd d → Rd d}
    (hu₁ : ∀ n, IsH1Pair (u₁ n) (v₁ n)) (hu₂ : ∀ n, IsH1Pair (u₂ n) (v₂ n))
    (hu₃ : ∀ n, IsH1Pair (u₃ n) (v₃ n)) (hu₄ : ∀ n, IsH1Pair (u₄ n) (v₄ n))
    (hf₁ : IsH1Pair f₁ g₁) (hf₂ : IsH1Pair f₂ g₂) (hf₃ : IsH1Pair f₃ g₃)
    (hf₄ : IsH1Pair f₄ g₄)
    (hc₁ : H1Tendsto u₁ v₁ f₁ g₁) (hc₂ : H1Tendsto u₂ v₂ f₂ g₂) (hc₃ : H1Tendsto u₃ v₃ f₃ g₃)
    (hc₄ : H1Tendsto u₄ v₄ f₄ g₄) :
    Tendsto (fun n => C4 Γ (u₁ n) (u₂ n) (u₃ n) (u₄ n)) atTop (𝓝 (C4 Γ f₁ f₂ f₃ f₄)) := by
  obtain ⟨-, ha0, ha2, -, -, hR0, hB⟩ := squareBound_R0 hH hΓ hdense
  have := hH.Γ_radon
  exact C4_tendsto hB hR0.le ha0 (by linarith) hu₁ hu₂ hu₃ hu₄ hf₁ hf₂ hf₃ hf₄ hc₁ hc₂ hc₃ hc₄

/-- **`R_sp = R_0`** (TeX lines 235-236, 288-291) under the standing assumptions and `hdense`: every
real unit `H¹` profile has positive gradient energy and ratio at most `R_0`; the `H¹` ratio set
is nonempty and bounded above; `R_sp = R_0`. -/
theorem spatial_ratio_H1_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0)
    (hdense : ∀ (f : Rd d → ℝ) (g : Rd d → Rd d), MemLp f 2 volume → MemLp g 2 volume →
      WeakSobolev.HasWeakGradient f g →
      ∃ φ : ℕ → Rd d → ℝ, (∀ n, WeakSobolev.IsTestFunction (φ n)) ∧
        Tendsto (fun n => eLpNorm (fun x => φ n x - f x) 2 volume) atTop (𝓝 0) ∧
        Tendsto (fun n => eLpNorm (fun x => VariationalFloor.grad (φ n) x - g x) 2 volume)
          atTop (𝓝 0)) :
    (∀ (f : Rd d → ℝ) (g : Rd d → Rd d), IsUnitH1 f g → 0 < ∫ x, ‖g x‖ ^ 2 ∧
      (pairing Γ (zE fun x => f x ^ 2) (zE fun x => f x ^ 2)).toReal /
        (∫ x, ‖g x‖ ^ 2) ^ (alpha / 2) ≤ R0 Γ alpha) ∧
      (ratioSetH1 Γ alpha).Nonempty ∧ BddAbove (ratioSetH1 Γ alpha) ∧
      Rsp Γ alpha = R0 Γ alpha := by
  obtain ⟨hd, -, -, hne, -, hR0, hB⟩ := squareBound_R0 hH hΓ hdense
  have := hH.Γ_radon
  exact Rsp_eq_R0 hd hB hne hR0.le

/-- **Positivity** (TeX line 236, proof lines 291-296) under the standing assumptions: every nonzero
real `H¹` profile has `A_sp(f) > 0`.  The density input is not needed. -/
theorem spatial_Asp_pos_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) {f : Rd d → ℝ} {g : Rd d → Rd d}
    (hfg : IsH1Pair f g) (hne : ¬ f =ᵐ[volume] 0) :
    0 < pairing Γ (zE fun x => f x ^ 2) (zE fun x => f x ^ 2) := by
  have := hH.Γ_radon
  exact pairing_sq_pos hH.scaling hΓ hfg.1.aestronglyMeasurable hne

/-- **`P:spatial-four-linear`** (`integrated_spatial_occupation.tex` lines 219-298) under the
section's standing assumptions (lines 4-10: `H:homog`, `a = α₀`, `Γ ≠ 0`) and the named density
input `hdense` (TeX lines 262-268; the statement of wave item L7-c), for real `H¹` profiles
given as `H¹` pairs `(f, g)` (`g` an `L²` weak gradient): `E:spatial-homogeneous-bound`;
finiteness of every square pairing and `E:spatial-square-CS`; `E:spatial-four-linear` with
absolute convergence; joint continuity of `C₄` (sequential form); `R_sp = R_0`; positivity of
`A_sp` on nonzero profiles.  Multilinearity is `spatial_four_linear_multilinear_paper`; the
bound `|C₄| ≤ R_0 ∏ N` is in `spatial_four_linear_bound_paper`. -/
theorem spatial_four_linear_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0)
    (hdense : ∀ (f : Rd d → ℝ) (g : Rd d → Rd d), MemLp f 2 volume → MemLp g 2 volume →
      WeakSobolev.HasWeakGradient f g →
      ∃ φ : ℕ → Rd d → ℝ, (∀ n, WeakSobolev.IsTestFunction (φ n)) ∧
        Tendsto (fun n => eLpNorm (fun x => φ n x - f x) 2 volume) atTop (𝓝 0) ∧
        Tendsto (fun n => eLpNorm (fun x => VariationalFloor.grad (φ n) x - g x) 2 volume)
          atTop (𝓝 0)) :
    (∀ (f : Rd d → ℝ) (g : Rd d → Rd d), IsH1Pair f g →
      pairing Γ (zE fun x => f x ^ 2) (zE fun x => f x ^ 2) ≤
        ENNReal.ofReal (R0 Γ alpha * Nnorm alpha f g ^ 4)) ∧
    (∀ (f h : Rd d → ℝ) (g k : Rd d → Rd d), IsH1Pair f g → IsH1Pair h k →
      pairing Γ (zE fun x => f x ^ 2) (zE fun x => h x ^ 2) < ⊤ ∧
      0 ≤ (pairing Γ (zE fun x => f x ^ 2) (zE fun x => h x ^ 2)).toReal ∧
      (pairing Γ (zE fun x => f x ^ 2) (zE fun x => h x ^ 2)).toReal ≤
        Real.sqrt ((pairing Γ (zE fun x => f x ^ 2) (zE fun x => f x ^ 2)).toReal *
          (pairing Γ (zE fun x => h x ^ 2) (zE fun x => h x ^ 2)).toReal)) ∧
    (∀ (f₁ f₂ f₃ f₄ : Rd d → ℝ) (g₁ g₂ g₃ g₄ : Rd d → Rd d), IsH1Pair f₁ g₁ →
      IsH1Pair f₂ g₂ → IsH1Pair f₃ g₃ → IsH1Pair f₄ g₄ →
      ∫⁻ p, ‖f₁ p.1 * f₂ p.1 * f₃ (p.1 - p.2) * f₄ (p.1 - p.2)‖ₑ ∂(pairMeasure Γ) ≤
        ENNReal.ofReal (R0 Γ alpha * (Nnorm alpha f₁ g₁ * Nnorm alpha f₂ g₂ *
          Nnorm alpha f₃ g₃ * Nnorm alpha f₄ g₄)) ∧
      Integrable (fun p : Rd d × Rd d => f₁ p.1 * f₂ p.1 * f₃ (p.1 - p.2) * f₄ (p.1 - p.2))
        (pairMeasure Γ)) ∧
    (∀ (u₁ u₂ u₃ u₄ : ℕ → Rd d → ℝ) (v₁ v₂ v₃ v₄ : ℕ → Rd d → Rd d)
      (f₁ f₂ f₃ f₄ : Rd d → ℝ) (g₁ g₂ g₃ g₄ : Rd d → Rd d),
      (∀ n, IsH1Pair (u₁ n) (v₁ n)) → (∀ n, IsH1Pair (u₂ n) (v₂ n)) →
      (∀ n, IsH1Pair (u₃ n) (v₃ n)) → (∀ n, IsH1Pair (u₄ n) (v₄ n)) →
      IsH1Pair f₁ g₁ → IsH1Pair f₂ g₂ → IsH1Pair f₃ g₃ → IsH1Pair f₄ g₄ →
      H1Tendsto u₁ v₁ f₁ g₁ → H1Tendsto u₂ v₂ f₂ g₂ → H1Tendsto u₃ v₃ f₃ g₃ →
      H1Tendsto u₄ v₄ f₄ g₄ →
      Tendsto (fun n => C4 Γ (u₁ n) (u₂ n) (u₃ n) (u₄ n)) atTop (𝓝 (C4 Γ f₁ f₂ f₃ f₄))) ∧
    Rsp Γ alpha = R0 Γ alpha ∧
    (∀ (f : Rd d → ℝ) (g : Rd d → Rd d), IsH1Pair f g → ¬ f =ᵐ[volume] 0 →
      0 < pairing Γ (zE fun x => f x ^ 2) (zE fun x => f x ^ 2)) :=
  ⟨fun _ _ hfg => spatial_homogeneous_bound_paper hH hΓ hdense hfg,
    fun _ _ _ _ hfg hhk => spatial_square_CS_paper hH hΓ hdense hfg hhk,
    fun _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ =>
      ⟨(spatial_four_linear_bound_paper hH hΓ hdense h₁ h₂ h₃ h₄).1,
        (spatial_four_linear_bound_paper hH hΓ hdense h₁ h₂ h₃ h₄).2.1⟩,
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hu₁ hu₂ hu₃ hu₄ hf₁ hf₂ hf₃ hf₄ hc₁ hc₂ hc₃ hc₄ =>
      spatial_four_linear_continuous_paper hH hΓ hdense hu₁ hu₂ hu₃ hu₄ hf₁ hf₂ hf₃ hf₄
        hc₁ hc₂ hc₃ hc₄,
    (spatial_ratio_H1_paper hH hΓ hdense).2.2.2,
    fun _ _ hfg hne => spatial_Asp_pos_paper hH hΓ hfg hne⟩

/-- Interface for wave item L7-e (`OccupationPhysicalClass.SquarePairingBounds Γ α R_0`): the two
fields `homogeneous` and `squareCS` with exactly that structure's spelling of `sqPair` and
`Nnorm` unfolded, under the standing assumptions and `hdense`.  The first is
`E:spatial-homogeneous-bound` (TeX line 224), the second the squared `[0,∞]` form of
`E:spatial-square-CS` (lines 225-227). -/
theorem squarePairingBounds_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0)
    (hdense : ∀ (f : Rd d → ℝ) (g : Rd d → Rd d), MemLp f 2 volume → MemLp g 2 volume →
      WeakSobolev.HasWeakGradient f g →
      ∃ φ : ℕ → Rd d → ℝ, (∀ n, WeakSobolev.IsTestFunction (φ n)) ∧
        Tendsto (fun n => eLpNorm (fun x => φ n x - f x) 2 volume) atTop (𝓝 0) ∧
        Tendsto (fun n => eLpNorm (fun x => VariationalFloor.grad (φ n) x - g x) 2 volume)
          atTop (𝓝 0)) :
    (∀ (f : Rd d → ℝ) (gf : Rd d → Rd d), MemLp f 2 volume → MemLp gf 2 volume →
      HasWeakGradient f gf →
      pairing Γ (fun x => ENNReal.ofReal (f x ^ 2)) (fun x => ENNReal.ofReal (f x ^ 2)) ≤
        ENNReal.ofReal (R0 Γ alpha * (Real.sqrt (∫ x, f x ^ 2) ^ (1 - alpha / 4) *
          Real.sqrt (∫ x, ‖gf x‖ ^ 2) ^ (alpha / 4)) ^ 4)) ∧
    (∀ (f : Rd d → ℝ) (gf : Rd d → Rd d) (h : Rd d → ℝ) (gh : Rd d → Rd d),
      MemLp f 2 volume → MemLp gf 2 volume → HasWeakGradient f gf →
      MemLp h 2 volume → MemLp gh 2 volume → HasWeakGradient h gh →
      pairing Γ (fun x => ENNReal.ofReal (f x ^ 2)) (fun x => ENNReal.ofReal (h x ^ 2)) ^ 2 ≤
        pairing Γ (fun x => ENNReal.ofReal (f x ^ 2)) (fun x => ENNReal.ofReal (f x ^ 2)) *
          pairing Γ (fun x => ENNReal.ofReal (h x ^ 2)) (fun x => ENNReal.ofReal (h x ^ 2))) := by
  obtain ⟨-, ha0, ha2, -, -, hR0, hB⟩ := squareBound_R0 hH hΓ hdense
  have := hH.Γ_radon
  refine ⟨fun f gf hf hg hw => ?_, fun f gf h gh hf hg hw hh hk hw' => ?_⟩
  · have := spatial_homogeneous_bound_paper hH hΓ hdense ⟨hf, hg, hw⟩
    rwa [Nnorm_eq_sqrt alpha hf hg] at this
  · have hfh := hB f h gf gh ⟨hf, hg, hw⟩ ⟨hh, hk, hw'⟩
    have hff := hB f f gf gf ⟨hf, hg, hw⟩ ⟨hf, hg, hw⟩
    have hhh := hB h h gh gh ⟨hh, hk, hw'⟩ ⟨hh, hk, hw'⟩
    have hX := hfh.trans_lt ENNReal.ofReal_lt_top
    have hA := hff.trans_lt ENNReal.ofReal_lt_top
    have hC := hhh.trans_lt ENNReal.ofReal_lt_top
    have hcs := C4_square_CS hH.Γ_even hH.spectral hB hR0.le ha0 (by linarith) hdense
      (⟨hf, hg, hw⟩ : IsH1Pair f gf) (⟨hh, hk, hw'⟩ : IsH1Pair h gh)
    rw [← pairing_toReal_eq_C4 hf.aestronglyMeasurable hh.aestronglyMeasurable,
      ← pairing_toReal_eq_C4 hf.aestronglyMeasurable hf.aestronglyMeasurable,
      ← pairing_toReal_eq_C4 hh.aestronglyMeasurable hh.aestronglyMeasurable] at hcs
    show pairing Γ (zE fun x => f x ^ 2) (zE fun x => h x ^ 2) ^ 2 ≤
      pairing Γ (zE fun x => f x ^ 2) (zE fun x => f x ^ 2) *
        pairing Γ (zE fun x => h x ^ 2) (zE fun x => h x ^ 2)
    rw [← ENNReal.ofReal_toReal hX.ne, ← ENNReal.ofReal_toReal hA.ne, ← ENNReal.ofReal_toReal hC.ne,
      ← ENNReal.ofReal_pow ENNReal.toReal_nonneg, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_le_ofReal hcs

/-- **`P:spatial-energy-map`, `E:spatial-energy-map`** (TeX lines 300-325, display 309-314; proof
327-348, 327-338 for the display) under the standing assumptions and `hdense`: the energy set over
real unit `H¹` profiles is nonempty and bounded above,
`𝓔_sp = (2-α)/2 α^{α/(2-α)} R_sp^{2/(2-α)} ∈ (0,∞)`, and `R_sp = R_0`.  Proof route: see `energy_map`. -/
theorem spatial_energy_value_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0)
    (hdense : ∀ (f : Rd d → ℝ) (g : Rd d → Rd d), MemLp f 2 volume → MemLp g 2 volume →
      WeakSobolev.HasWeakGradient f g →
      ∃ φ : ℕ → Rd d → ℝ, (∀ n, WeakSobolev.IsTestFunction (φ n)) ∧
        Tendsto (fun n => eLpNorm (fun x => φ n x - f x) 2 volume) atTop (𝓝 0) ∧
        Tendsto (fun n => eLpNorm (fun x => VariationalFloor.grad (φ n) x - g x) 2 volume)
          atTop (𝓝 0)) :
    (energySet Γ).Nonempty ∧ BddAbove (energySet Γ) ∧
      Esp Γ = energyValue alpha (Rsp Γ alpha) ∧ 0 < Esp Γ ∧ Rsp Γ alpha = R0 Γ alpha := by
  obtain ⟨hd, ha0, ha2, hne, hbdd, hR0, hB⟩ := squareBound_R0 hH hΓ hdense
  have := hH.Γ_radon
  have hRsp := (spatial_ratio_H1_paper hH hΓ hdense).2.2.2
  obtain ⟨h1, h2, h3, h4⟩ := energy_map hH.scaling hΓ hd ha0 ha2 hB hne hbdd hR0
  exact ⟨h1, h2, by rw [hRsp]; exact h3, h4, hRsp⟩

/-- **`E:spatial-static-energy-score`** (TeX lines 316-322, proof 338-346) under the standing
assumptions and `hdense`, in the existential form used for `E:spatial-smooth-score` (Le's
decision 2): every `y < M_a^{-1/k} F₀(𝓔_sp)` (`k = 3-α`, `a = α₀`) is exceeded by `I_Ψ - v_Ψ/2`
for some `Ψ ∈ C_pos`.  This form is implied by the TeX's `S_1^pos ≥ …` and equivalent to it when
`S_1^pos < ∞`. -/
theorem spatial_static_energy_score_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0)
    (hdense : ∀ (f : Rd d → ℝ) (g : Rd d → Rd d), MemLp f 2 volume → MemLp g 2 volume →
      WeakSobolev.HasWeakGradient f g →
      ∃ φ : ℕ → Rd d → ℝ, (∀ n, WeakSobolev.IsTestFunction (φ n)) ∧
        Tendsto (fun n => eLpNorm (fun x => φ n x - f x) 2 volume) atTop (𝓝 0) ∧
        Tendsto (fun n => eLpNorm (fun x => VariationalFloor.grad (φ n) x - g x) 2 volume)
          atTop (𝓝 0)) :
    ∀ y < TemporalEquilibrium.mass alpha0 ^ (-(1 / (3 - alpha))) * F0 alpha (Esp Γ),
      ∃ Ψ ∈ VariationalDilation.CPos d,
        y < VariationalDilation.integratedRate alpha0 Γ Ψ -
          VariationalDilation.rawCost alpha0 Γ Ψ / 2 := by
  intro y hy
  obtain ⟨hd, ha0, ha2, hne, hbdd, hR0, hB⟩ := squareBound_R0 hH hΓ hdense
  have := hH.Γ_radon
  obtain ⟨-, -, hE, -⟩ := energy_map hH.scaling hΓ hd ha0 ha2 hB hne hbdd hR0
  have hM := TemporalEquilibrium.mass_pos hH.alpha0_pos hH.alpha0_lt_one
  rw [hE, ← score_identity ha0 ha2 hM hR0.le] at hy
  obtain ⟨u, -, hu, hmem⟩ := exists_seq_tendsto_sSup hne hbdd
  have hT := ((smoothScoreBound_continuous alpha alpha0 (by linarith)).tendsto _).comp hu
  obtain ⟨n, hn⟩ := (hT.eventually (lt_mem_nhds hy)).exists
  obtain ⟨g, hg, hgu⟩ := hmem n
  have hn' : y < SpatialSmoothRatio.smoothScoreBound alpha alpha0 (ratio Γ alpha g) := by
    rw [hgu]; exact hn
  exact SpatialOccupationCompleted.spatial_smooth_score_completed_paper hH hΓ hg y hn'

/-- **`E:spatial-static-energy-score`** in the TeX's `sSup` form (lines 316-322) under the standing
assumptions, `hdense` and the named input `S1Bdd α₀ Γ` (as in
`SpatialOccupationCompleted.spatial_smooth_score_sSup_completed_paper`): `S_1^pos ≥ M_a^{-1/k}
F₀(𝓔_sp)`. -/
theorem spatial_static_energy_score_sSup_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0)
    (hdense : ∀ (f : Rd d → ℝ) (g : Rd d → Rd d), MemLp f 2 volume → MemLp g 2 volume →
      WeakSobolev.HasWeakGradient f g →
      ∃ φ : ℕ → Rd d → ℝ, (∀ n, WeakSobolev.IsTestFunction (φ n)) ∧
        Tendsto (fun n => eLpNorm (fun x => φ n x - f x) 2 volume) atTop (𝓝 0) ∧
        Tendsto (fun n => eLpNorm (fun x => VariationalFloor.grad (φ n) x - g x) 2 volume)
          atTop (𝓝 0))
    (hB1 : VariationalRate.S1Bdd alpha0 Γ) :
    TemporalEquilibrium.mass alpha0 ^ (-(1 / (3 - alpha))) * F0 alpha (Esp Γ) ≤
      VariationalRate.S1pos alpha0 Γ := by
  obtain ⟨hd, ha0, ha2, hne, hbdd, hR0, hB⟩ := squareBound_R0 hH hΓ hdense
  have := hH.Γ_radon
  obtain ⟨-, -, hE, -⟩ := energy_map hH.scaling hΓ hd ha0 ha2 hB hne hbdd hR0
  have hM := TemporalEquilibrium.mass_pos hH.alpha0_pos hH.alpha0_lt_one
  rw [hE, ← score_identity ha0 ha2 hM hR0.le]
  obtain ⟨u, -, hu, hmem⟩ := exists_seq_tendsto_sSup hne hbdd
  have hT := ((smoothScoreBound_continuous alpha alpha0 (by linarith)).tendsto _).comp hu
  refine le_of_tendsto' hT (fun n => ?_)
  obtain ⟨g, hg, hgu⟩ := hmem n
  show SpatialSmoothRatio.smoothScoreBound alpha alpha0 (u n) ≤ _
  rw [← hgu]
  exact SpatialOccupationCompleted.spatial_smooth_score_sSup_completed_paper hH hΓ hB1 hg

end StratonovichHAMSecondMoment.SpatialFourLinear

