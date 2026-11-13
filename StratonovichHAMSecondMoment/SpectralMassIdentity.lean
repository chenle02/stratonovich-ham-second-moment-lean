module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

The spectral-mass constant `R_α` of `E:intro-spectral-mass` (main TeX
`notes/notes_stratonovich_ham_second_moment.tex`, revision a284420, lines
526-532: `B_1` the unit ball of `ℝ^d` and
`R_α = απ μ(B_1)/(2 sin(πα/2))`) is the resolvent at `1`:

  `R_Γ(1) = ∫ μ(dξ)/(1+|ξ|²) = R_α`,  and  `R_Γ(q) = q^{α-2} R_α`  for `q > 0`,

for a locally finite spectral measure `μ` with `μ(cA) = c^α μ(A)` and
`0 < α < 2` (`resolvent_one_eq_ralpha`, `resolvent_eq_ralpha`).  The second
identity is the display of the proof of `L:spatial-fourier-bound`
(`notes/integrated_spatial_occupation.tex`, lines 149-155 at a284420), which
cites "the deterministic resolvent calculation in the proof of
`L:damped-homogeneous-norms`" (main TeX lines 850-860:
`∫ μ(dξ)/(a²+|ξ|²) = αV a^{α-2} ∫_0^∞ u^{α-1}/(1+u²) du`, `V = μ(B_1)`)
together with `E:intro-spectral-mass`.  The value
`∫_0^∞ u^{α-1}/(1+u²) du = π/(2 sin(πα/2))` is not written in the TeX; it is
proved here.  `B_1` is the open unit ball `Metric.ball 0 1`, as in the
hypothesis `hRdef` of `IntervalScalar`.

Proof route (differs from the TeX, same conclusion): the layer-cake formula
(as in `SpectralHomog.integrable_inv_one_add_sq`, which proves finiteness)
with the level sets `{1/(1+|ξ|²) > t} = B_{√((1-t)/t)}` for `0 < t < 1`
(empty for `t ≥ 1`), `μ(B_r) = r^α V` (`SpectralHomog.measure_ball`), and the
real Beta integral `∫_0^1 t^{-a}(1-t)^a dt = aπ/sin(πa)` for `0 < a < 1`
(`beta_real`, from Mathlib's complex Beta function and the reflection
formula), at `a = α/2`.  The TeX uses polar coordinates instead.

Consequences:
* `spatial_fourier_bound_ralpha_paper`: `L:spatial-fourier-bound` with the
  manuscript's constant `R_α` (display `E:spatial-fourier-bound`,
  `integrated_spatial_occupation.tex` lines 101-111), under the lemma's own
  hypotheses (`H:homog`, allowing `Γ = 0`).  The general form with
  `R_Γ(1)` stays `SpatialFourierBound.spatial_fourier_bound(_paper)`.
* `hRdef_iff_resolvent(_paper)`: the hypothesis
  `R = απ μ(B_1)/(2 sin(πα/2))` carried by the `IntervalScalar` and
  `IntervalScalarCompleted` wrappers is equivalent to `R = R_Γ(1)`.

Supplied inputs: none.  The general theorems take `SpectralHomogeneous μ α`
(the supplied input of `SpectralHomog`, no stronger than the sentence of main
TeX lines 851-852); the `_paper` wrappers take `H:homog`
(`HomogHypothesis.HomogCovariance`) and discharge it by
`MaskedSpectralGrowth.spectralHomogeneous_of_homog`.  The integrability of
`(1+|ξ|²)^{-1}` (and of `(q²+|ξ|²)^{-1}`) against `μ` is part of each
conclusion, so no identity holds through the junk value of a non-integrable
Bochner integral; `μ(B_1) < ∞` by local finiteness, so its `toReal` is not
junk either; `sin(πα/2) > 0` for `0 < α < 2`, so the division is genuine.
No `Γ ≠ 0` is assumed: for `μ = 0` both sides are `0`.
-/

public import Mathlib
public import StratonovichHAMSecondMoment.HomogHypothesis
public import StratonovichHAMSecondMoment.SpectralHomog
public import StratonovichHAMSecondMoment.MaskedSpectralGrowth
public import StratonovichHAMSecondMoment.SpatialFourierBound

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Real Filter Metric
open scoped ENNReal

namespace StratonovichHAMSecondMoment.SpectralMassIdentity

open HomogHypothesis (Rd HomogCovariance)
open SpectralHomog (SpectralHomogeneous resolvent)

variable {d : ℕ}

/-- `R_α = απ μ(B_1)/(2 sin(πα/2))` with `B_1` the open unit ball
(`E:intro-spectral-mass`, main TeX lines 526-532; the same expression as the
hypothesis `hRdef` in `IntervalScalar`). -/
def ralpha (μ : Measure (Rd d)) (alpha : ℝ) : ℝ :=
  alpha * π * (μ (ball (0 : Rd d) 1)).toReal / (2 * Real.sin (π * alpha / 2))

/-- Auxiliary to the Lean proof route (the value of the radial integral of main TeX
lines 857-860, which the TeX does not compute): the real Beta integral
`∫_0^1 t^{-a} (1-t)^a dt = aπ/sin(πa)` for `0 < a < 1`. -/
theorem beta_real (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    ∫ t in (0 : ℝ)..1, t ^ (-a) * (1 - t) ^ a = a * π / Real.sin (π * a) := by
  have hc := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := ((1 - a : ℝ) : ℂ))
    (t := ((1 + a : ℝ) : ℂ)) (by simp; linarith) (by simp; linarith)
  have hB : Complex.betaIntegral ((1 - a : ℝ) : ℂ) ((1 + a : ℝ) : ℂ) =
      ((∫ t in (0 : ℝ)..1, t ^ (-a) * (1 - t) ^ a : ℝ) : ℂ) := by
    rw [Complex.betaIntegral, ← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le zero_le_one] at ht
    rw [Complex.ofReal_mul, Complex.ofReal_cpow ht.1, Complex.ofReal_cpow (by linarith [ht.2]),
      Complex.ofReal_sub, Complex.ofReal_one]
    congr 2 <;> push_cast <;> ring
  rw [hB, ← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    Complex.Gamma_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul] at hc
  have hr := Complex.ofReal_injective hc
  have h2 : (1 - a) + (1 + a) = 2 := by ring
  rw [h2, Real.Gamma_two, one_mul] at hr
  rw [← hr]
  have h1 : Real.Gamma (1 + a) = a * Real.Gamma a := by
    rw [add_comm]; exact Real.Gamma_add_one ha0.ne'
  have hr2 := Real.Gamma_mul_Gamma_one_sub a
  rw [h1]
  calc Real.Gamma (1 - a) * (a * Real.Gamma a) = a * (Real.Gamma a * Real.Gamma (1 - a)) := by
        ring
    _ = a * π / Real.sin (π * a) := by rw [hr2]; ring

/-- Auxiliary to the Lean proof route: for `t > 0` the level set
`{ξ : 1/(1+|ξ|²) > t}` is the open ball of radius `√((1-t)/t)` (empty for
`t ≥ 1`, where the radius is `√` of a nonpositive number, i.e. `0`). -/
theorem levelset_eq_ball (t : ℝ) (ht0 : 0 < t) :
    {ξ : Rd d | t < 1 / (1 + ‖ξ‖ ^ 2)} = ball (0 : Rd d) (Real.sqrt ((1 - t) / t)) := by
  ext ξ
  simp only [mem_ofPred_eq, mem_ball_zero_iff]
  have hpos : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  rw [lt_div_iff₀ hpos, Real.lt_sqrt (norm_nonneg _), lt_div_iff₀ ht0]
  constructor <;> intro h <;> nlinarith

/-- `R_Γ(1) = ∫ μ(dξ)/(1+|ξ|²) = R_α` for a locally finite `α`-homogeneous `μ`
with `0 < α < 2`, together with the integrability of `(1+|ξ|²)^{-1}`
(the resolvent calculation of main TeX lines 850-860 at `a = 1`, with the
radial integral evaluated, and `E:intro-spectral-mass`, lines 526-532).
Proof route: layer cake and the real Beta integral (module doc). -/
theorem resolvent_one_eq_ralpha {μ : Measure (Rd d)} {alpha : ℝ}
    (hI : SpectralHomogeneous μ alpha) [IsLocallyFiniteMeasure μ]
    (ha0 : 0 < alpha) (ha2 : alpha < 2) :
    Integrable (fun ξ : Rd d => 1 / (1 + ‖ξ‖ ^ 2)) μ ∧ resolvent μ 1 = ralpha μ alpha := by
  have hR := SpectralHomog.integrable_inv_one_add_sq hI ha2
  refine ⟨hR, ?_⟩
  set f : Rd d → ℝ := fun ξ => 1 / (1 + ‖ξ‖ ^ 2) with hf_def
  have hfm : Measurable f := by rw [hf_def]; fun_prop
  have hf0 : ∀ ξ, 0 ≤ f ξ := fun ξ => by rw [hf_def]; positivity
  have hres : resolvent μ 1 = ∫ ξ, f ξ ∂μ := by
    unfold SpectralHomog.resolvent; simp only [one_pow, hf_def]
  set V := μ (ball (0 : Rd d) 1) with hVdef
  have hV : V ≠ ⊤ := measure_ball_lt_top.ne
  set a := alpha / 2 with hadef
  have ha0' : 0 < a := by rw [hadef]; linarith
  have ha1' : a < 1 := by rw [hadef]; linarith
  set g : ℝ → ℝ := fun t => t ^ (-a) * (1 - t) ^ a with hg_def
  -- the level sets
  have hlevel : ∀ t ∈ Ioi (0 : ℝ), μ {ξ | t < f ξ} =
      (Iio (1 : ℝ)).indicator (fun t => ENNReal.ofReal (g t) * V) t := by
    intro t ht
    have ht0 : 0 < t := ht
    by_cases ht1 : t < 1
    · rw [indicator_of_mem (show t ∈ Iio (1 : ℝ) from ht1)]
      have hr : 0 < Real.sqrt ((1 - t) / t) := Real.sqrt_pos.2 (div_pos (by linarith) ht0)
      rw [hf_def, levelset_eq_ball t ht0, SpectralHomog.measure_ball hI _ hr]
      congr 2
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (div_pos (by linarith) ht0).le,
        Real.div_rpow (by linarith) ht0.le, hg_def]
      simp only
      rw [Real.rpow_neg ht0.le, show 1 / 2 * alpha = a by rw [hadef]; ring]
      ring
    · rw [indicator_of_notMem (show t ∉ Iio (1 : ℝ) from ht1)]
      have hempty : {ξ | t < f ξ} = ∅ := by
        ext ξ
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt, hf_def]
        rw [div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg ‖ξ‖]
      rw [hempty, measure_empty]
  -- the Beta integral and integrability of its integrand
  have hbeta := beta_real a ha0' ha1'
  have hsin : 0 < Real.sin (π * a) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hII : IntervalIntegrable g volume 0 1 := by
    refine intervalIntegral.intervalIntegrable_of_integral_ne_zero ?_
    rw [hg_def, hbeta]; positivity
  have hIoo : IntegrableOn g (Ioo 0 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 hII
  have hg0 : ∀ t ∈ Ioo (0 : ℝ) 1, 0 ≤ g t := fun t ht => by
    rw [hg_def]
    exact mul_nonneg (Real.rpow_nonneg ht.1.le _) (Real.rpow_nonneg (by linarith [ht.2]) _)
  have hB : ∫ t in Ioo (0 : ℝ) 1, g t = a * π / Real.sin (π * a) := by
    rw [← hbeta, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  -- the lintegral
  have hlin : ∫⁻ ξ, ENNReal.ofReal (f ξ) ∂μ = ENNReal.ofReal (a * π / Real.sin (π * a)) * V := by
    rw [lintegral_eq_lintegral_meas_lt μ (Eventually.of_forall hf0) hfm.aemeasurable,
      setLIntegral_congr_fun measurableSet_Ioi hlevel, lintegral_indicator measurableSet_Iio,
      Measure.restrict_restrict measurableSet_Iio]
    have hset : Iio (1 : ℝ) ∩ Ioi 0 = Ioo 0 1 := by
      ext t; simp [and_comm]
    rw [hset, lintegral_mul_const _ (by fun_prop), ← hB,
      ofReal_integral_eq_lintegral_ofReal hIoo
        ((ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall hg0))]
  rw [hres, integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf0)
    hfm.aestronglyMeasurable, hlin, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ralpha, ← hVdef, show π * alpha / 2 = π * a by rw [hadef]; ring, hadef]
  ring

/-- `R_Γ(q) = ∫ μ(dξ)/(q²+|ξ|²) = q^{α-2} R_α < ∞` for `q > 0`, a locally finite
`α`-homogeneous `μ` and `0 < α < 2` (the display of the proof of
`L:spatial-fourier-bound`, `integrated_spatial_occupation.tex` lines 149-155;
main TeX lines 850-860 with `E:intro-spectral-mass`).  The finiteness is the
integrability conjunct. -/
theorem resolvent_eq_ralpha {μ : Measure (Rd d)} {alpha : ℝ}
    (hI : SpectralHomogeneous μ alpha) [IsLocallyFiniteMeasure μ]
    (ha0 : 0 < alpha) (ha2 : alpha < 2) (q : ℝ) (hq : 0 < q) :
    Integrable (fun ξ : Rd d => 1 / (q ^ 2 + ‖ξ‖ ^ 2)) μ ∧
      resolvent μ q = q ^ (alpha - 2) * ralpha μ alpha := by
  obtain ⟨hR, h1⟩ := resolvent_one_eq_ralpha hI ha0 ha2
  exact ⟨SpectralHomog.resolvent_integrable hR q hq.ne',
    by rw [SpectralHomog.resolvent_homog hI q hq, h1]⟩

/-- Auxiliary to the Lean proof route: the numerical part of `H:homog` used here,
`0 < α < 2` (from `alpha_range`, and from `threshold` with `alpha0_pos`). -/
theorem alpha_mem_Ioo_of_homog {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) : 0 < alpha ∧ alpha < 2 := by
  refine ⟨?_, by linarith [hH.threshold, hH.alpha0_pos]⟩
  rcases hH.alpha_range with h | ⟨h, hd⟩
  · exact h.1
  · rw [h, hd]; norm_num

/-- **`R_Γ(q) = q^{α-2} R_α` under `H:homog`** (the display of the proof of
`L:spatial-fourier-bound`, `integrated_spatial_occupation.tex` lines 149-155,
with `R_α` of `E:intro-spectral-mass`, main TeX lines 526-532), for the
spectral measure `μ` of any covariance allowed by `H:homog`, including
`Γ = 0` (then `μ = 0` and both sides vanish): for every `q > 0`,
`(q²+|ξ|²)^{-1}` is `μ`-integrable and `R_Γ(q) = q^{α-2} R_α`; in particular
`R_Γ(1) = R_α`.  Fields of `HomogCovariance` used: `alpha_range`,
`alpha0_pos`, `threshold` (for `0 < α < 2`), `μ_radon`, and `μ_tempered`,
`spectral`, `scaling` (through `spectralHomogeneous_of_homog`). -/
theorem resolvent_eq_ralpha_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) :
    resolvent μ 1 = ralpha μ alpha ∧
      ∀ q : ℝ, 0 < q → Integrable (fun ξ : Rd d => 1 / (q ^ 2 + ‖ξ‖ ^ 2)) μ ∧
        resolvent μ q = q ^ (alpha - 2) * ralpha μ alpha := by
  have := hH.μ_radon
  obtain ⟨ha0, ha2⟩ := alpha_mem_Ioo_of_homog hH
  have hI := MaskedSpectralGrowth.spectralHomogeneous_of_homog hH
  exact ⟨(resolvent_one_eq_ralpha hI ha0 ha2).2, resolvent_eq_ralpha hI ha0 ha2⟩

/-- The `IntervalScalar` constant is the resolvent at `1`: for a locally finite
`α`-homogeneous `μ` and `0 < α < 2`, the hypothesis
`R = απ μ(B_1)/(2 sin(πα/2))` (`hRdef` of the `IntervalScalar` and
`IntervalScalarCompleted` wrappers) holds iff `R = R_Γ(1)`. -/
theorem hRdef_iff_resolvent {μ : Measure (Rd d)} {alpha : ℝ}
    (hI : SpectralHomogeneous μ alpha) [IsLocallyFiniteMeasure μ]
    (ha0 : 0 < alpha) (ha2 : alpha < 2) (R : ℝ) :
    R = alpha * π * (μ (ball (0 : Rd d) 1)).toReal / (2 * Real.sin (π * alpha / 2)) ↔
      R = resolvent μ 1 := by
  rw [(resolvent_one_eq_ralpha hI ha0 ha2).2, ralpha]

/-- `hRdef_iff_resolvent` under `H:homog`: the `IntervalScalar` hypothesis
`R = απ μ(B_1)/(2 sin(πα/2))` is equivalent to `R = R_Γ(1)` for the spectral
measure of any covariance allowed by `H:homog`.  Fields used as in
`resolvent_eq_ralpha_paper`. -/
theorem hRdef_iff_resolvent_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (R : ℝ) :
    R = alpha * π * (μ (ball (0 : Rd d) 1)).toReal / (2 * Real.sin (π * alpha / 2)) ↔
      R = resolvent μ 1 := by
  rw [(resolvent_eq_ralpha_paper hH).1, ralpha]

/-- **`L:spatial-fourier-bound` with the manuscript's constant `R_α`**
(`integrated_spatial_occupation.tex` lines 101-111 at a284420, display
`E:spatial-fourier-bound` at lines 106-109; `R_α` of `E:intro-spectral-mass`,
main TeX lines 526-532), under the lemma's hypothesis `H:homog`
(`HomogCovariance`, allowing `Γ = 0`; no `Γ ≠ 0` assumed), for every real unit
`g ∈ C_c^∞(ℝ^d)` (`IsUnitTest`): `b(g) > 0`, the autocorrelation of `g²` is
`Γ`-integrable, `|ĝ²|²` and `(1+|ξ|²)^{-1}` are `μ`-integrable,
`A_sp(g) = ∫ |ĝ²|² dμ`, and `0 ≤ A_sp(g) ≤ 2^{1+α} R_α b(g)^{α/2}`.
Obtained from `SpatialFourierBound.spatial_fourier_bound_paper` (constant
`R_Γ(1)`) and `R_Γ(1) = R_α` (`resolvent_eq_ralpha_paper`).  Fields of
`HomogCovariance` used: those of `spatial_fourier_bound_paper` (`dim`,
`alpha0_pos`, `threshold`, `Γ_radon`, `μ_radon`, `spectral`, `μ_tempered`,
`scaling`) and `alpha_range` (for `α > 0`). -/
theorem spatial_fourier_bound_ralpha_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) {g : Rd d → ℝ}
    (hg : SpatialFourierBound.IsUnitTest g) :
    0 < SpatialFourierBound.gradEnergy g ∧
      Integrable (SpatialFourierBound.autocorr (fun x => g x ^ 2)) Γ ∧
      Integrable (fun ξ => ‖SpatialFourierBound.fourierQ (fun x => g x ^ 2) ξ‖ ^ 2) μ ∧
      Integrable (fun ξ : Rd d => 1 / (1 + ‖ξ‖ ^ 2)) μ ∧
      SpatialFourierBound.spatialEnergy Γ g =
        ∫ ξ, ‖SpatialFourierBound.fourierQ (fun x => g x ^ 2) ξ‖ ^ 2 ∂μ ∧
      0 ≤ SpatialFourierBound.spatialEnergy Γ g ∧
      SpatialFourierBound.spatialEnergy Γ g ≤
        2 ^ (1 + alpha) * ralpha μ alpha * SpatialFourierBound.gradEnergy g ^ (alpha / 2) := by
  rw [← (resolvent_eq_ralpha_paper hH).1]
  exact SpatialFourierBound.spatial_fourier_bound_paper hH hg

end StratonovichHAMSecondMoment.SpectralMassIdentity
