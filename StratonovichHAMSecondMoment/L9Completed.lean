module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Integration of wave items L9-G (`WaveGreenFourier`), L9-L (`LowAlphaConvolution`) and L9-P
(`PhaseContractions`) for the main TeX file `notes/notes_stratonovich_ham_second_moment.tex`
(line numbers at revision a284420).  This module discharges the cross-item inputs of wave L9;
it defines no new object and modifies no existing module.

1. The supplied input `GreenFourier (waveGreen d)` of
   `LowAlphaConvolution.low_alpha_convolution_paper` (`L:low-alpha-convolution`, lines
   4702-4757; the display `Ĝ_h(ξ) = sin(h|ξ|)/|ξ|`, `G_h(ℝ^d) = h` at lines 4738-4744).
   `WaveGreenFourier.greenFourier d` proves it for `d ∈ {1,2,3}`, and `H:homog` carries
   `d ∈ {1,2,3}` (field `dim`).  `low_alpha_convolution_paper_completed` is the wrapper
   without it, in every dimension of `H:homog` (wave L9-L proved it unconditionally only in
   `d = 1`, `low_alpha_convolution_one`).
2. The supplied inputs `PhaseContractions.WaveFourierThree` (the `d = 3` case of
   `Ĝ_s(ξ) = sin(s|ξ|)/|ξ|`, lines 777-778, used at lines 2083 and 2107-2108) and
   `PhaseContractions.ArchimedesLaw` (Archimedes' law for `volume.toSphere`, behind the
   "direct integration over its normal coordinate" of lines 2125-2126).  They hold by
   `WaveGreenFourier.waveGreen_fourier_three` and `WaveGreenFourier.archimedes`, whose
   statements are those of the two `Prop`s (`waveFourierThree_holds`, `archimedesLaw_holds`).
   The public `PhaseContractions` declarations with a manuscript role that take them are
   re-issued as `<name>_completed` without them, every other hypothesis kept exactly:
   `phase_trace` (`E:phase-trace`), `traceT_fourier` (the Fourier form of `T_ε`) and
   `phase_contractions_paper` (`L:phase-contractions`, lines 2072-2138).  The route lemmas
   `lintegral_waveGreen_three`, `sphere_convolution`, `kernel_le_of_dist`, `three_regions`,
   `kernel_le_bAlpha` and `lintegral_gammaEps_le` are not re-issued (apply them to
   `archimedesLaw_holds`).  `phase_contractions_homog_completed` states the lemma under
   `H:homog` in `d = 3` (`PhaseContractions.PhaseCovariance.of_homog`).

After this module, `L:low-alpha-convolution` (`d ∈ {1,2,3}`) and `L:phase-contractions` rest on
their standing assumptions alone.  Every narrowing recorded in the source modules is unchanged;
in particular the `d = 3` Green measure is the recorded `toSphere` definitional choice of
`WaveGreen` (decision 4 of wave L6), not identified with a surface measure.

The other L9 items are not involved: `RawOccupationEnergy`, `OccupationCeilingExact`,
`GaussianHermite` and `HermiteFock` supply nothing; the named input `FockColumn` of `FockForm`
(the spatial half of `L:fock-form` and `E:interval-column`) is a bound for abstract operators on
an abstract Hilbert space and is not proved by any L9 item; the inputs of `ComplexPhaseScalar`
(Crouzeix-Palencia `E:cp-input`, the inverse-root integral and the propagator identification)
are not proved by any L9 item.  The application of `HermiteWord.cut_eq_raw` to the Fock model
of `FockForm` is `StratonovichHAMAudit.HermiteWordFock.cut_eq_raw_fock` (a non-`module` file,
since `HermiteWord` is not a `module`).
-/
public import Mathlib
public import StratonovichHAMSecondMoment.WaveGreenFourier
public import StratonovichHAMSecondMoment.LowAlphaConvolution
public import StratonovichHAMSecondMoment.PhaseContractions

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Real Metric

namespace StratonovichHAMSecondMoment.L9Completed

open HomogHypothesis (Rd HomogCovariance IsTempered IsSpectralMeasure)
open SpectralHomog (SpectralHomogeneous)
open WaveKernel (waveHat)
open WaveGreen (waveGreen)
open SpectralMassIdentity (ralpha)
open LowAlphaConvolution (specV lowKernel heatDens smoothedGreen)
open PhaseContractions (PhaseCovariance traceT dGam pdens WaveFourierThree ArchimedesLaw)

/-! ### The bridges -/

/-- **The supplied input `PhaseContractions.WaveFourierThree` holds**: the `d = 3` case of
`Ĝ_s(ξ) = sin(s|ξ|)/|ξ|` (value `s` at `ξ = 0`; main TeX lines 777-778 and 4738-4744 at
a284420) for the measure `waveGreen 3 s`, by `WaveGreenFourier.waveGreen_fourier_three`. -/
theorem waveFourierThree_holds : WaveFourierThree :=
  fun s hs ξ => (WaveGreenFourier.waveGreen_fourier_three s hs ξ).2

/-- **The supplied input `PhaseContractions.ArchimedesLaw` holds**: for every unit `e ∈ ℝ³` the
image of `volume.toSphere` under `ω ↦ ⟨e,ω⟩` is `2π` Lebesgue measure on `[-1,1]` (the "direct
integration over its normal coordinate" of main TeX lines 2125-2126 at a284420), by
`WaveGreenFourier.archimedes`. -/
theorem archimedesLaw_holds : ArchimedesLaw :=
  fun e he => WaveGreenFourier.archimedes e he

/-! ### `L:low-alpha-convolution` without `GreenFourier` -/

/-- **`L:low-alpha-convolution`** (main TeX lines 4702-4716, proof 4718-4757 at a284420;
displays `E:low-alpha-radial` and `E:low-alpha-convolution`) under `H:homog` and `α < 1` alone,
for `G_h = waveGreen d h` in every dimension `d ∈ {1,2,3}` of `H:homog`:
`LowAlphaConvolution.low_alpha_convolution_paper` with the input `GreenFourier (waveGreen d)`
discharged by `WaveGreenFourier.greenFourier` (the Fourier display at lines 4738-4744).
Conclusions: `0 < α`, `V = μ(B̄_1) < ∞`, `μ(B̄_R) = R^α V`, `min{h,|ξ|^{-1}}` is `μ`-integrable
with integral `V h^{1-α}/(1-α)`, `p_ε(x - ·)` is `Γ`-integrable, and for all `h, ε > 0`,
`η ≥ 0`, `z`: `y ↦ γ_ε(y + z)` is `G_{h,η}`-integrable with
`0 ≤ ∫ G_{h,η}(dy) γ_ε(y + z) ≤ V h^{1-α}/(1-α)`. -/
theorem low_alpha_convolution_paper_completed {d : ℕ} {alpha alpha0 : ℝ}
    {Γ μ : Measure (Rd d)} (hH : HomogCovariance d alpha alpha0 Γ μ) (ha1 : alpha < 1) :
    0 < alpha ∧ specV μ < ⊤ ∧
      (∀ R : ℝ, 0 < R → μ (closedBall 0 R) = ENNReal.ofReal (R ^ alpha) * specV μ) ∧
      (∀ h : ℝ, 0 < h → Integrable (lowKernel h) μ ∧
        ∫ ξ, lowKernel h ξ ∂μ = (specV μ).toReal / (1 - alpha) * h ^ (1 - alpha)) ∧
      (∀ ε : ℝ, 0 < ε → ∀ x, Integrable (fun y => heatDens ε (x - y)) Γ) ∧
      ∀ h : ℝ, 0 < h → ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 ≤ η → ∀ z : Rd d,
        Integrable (fun y => LowAlphaConvolution.gammaEps Γ ε (y + z))
            (smoothedGreen (waveGreen d) h η) ∧
        0 ≤ ∫ y, LowAlphaConvolution.gammaEps Γ ε (y + z) ∂(smoothedGreen (waveGreen d) h η) ∧
        ∫ y, LowAlphaConvolution.gammaEps Γ ε (y + z) ∂(smoothedGreen (waveGreen d) h η) ≤
          (specV μ).toReal / (1 - alpha) * h ^ (1 - alpha) :=
  LowAlphaConvolution.low_alpha_convolution_paper hH ha1
    (WaveGreenFourier.greenFourier d hH.dim)

/-! ### `PhaseContractions` without `WaveFourierThree` and `ArchimedesLaw` -/

/-- **`E:phase-trace`** (main TeX lines 2078-2082, proof 2108-2136 at a284420), general form,
without Archimedes' law: `PhaseContractions.phase_trace` with `ArchimedesLaw` discharged
(`archimedesLaw_holds`).  For a locally finite tempered `Γ` on `ℝ³` with `Γ(cA) = c^{3-α}Γ(A)`,
`0 < α < 2`, `ε, a > 0`, `q ∈ ℝ³`: the integrand of `T_ε(a,q)` is `G_a`-integrable,
`T_ε(a,0) = ∫ Γ_ε dG_a`, `|T_ε(a,q)| ≤ T_ε(a,0)` and `|T_ε(a,q)| ≤ D_Γ a^{1-α}`. -/
theorem phase_trace_completed {Γ : Measure (Rd 3)} [IsLocallyFiniteMeasure Γ]
    (hΓt : IsTempered Γ) {alpha : ℝ} (hΓs : SpectralHomogeneous Γ (3 - alpha))
    (ha0 : 0 < alpha) (ha2 : alpha < 2) (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : 0 < a) (q : Rd 3) :
    Integrable (fun x => Complex.exp (Complex.I * ((inner ℝ q x : ℝ) : ℂ)) *
        (PhaseContractions.gammaEps Γ ε x : ℂ)) (waveGreen 3 a) ∧
      traceT Γ ε a 0 = ((∫ x, PhaseContractions.gammaEps Γ ε x ∂(waveGreen 3 a) : ℝ) : ℂ) ∧
      ‖traceT Γ ε a q‖ ≤ ∫ x, PhaseContractions.gammaEps Γ ε x ∂(waveGreen 3 a) ∧
      ‖traceT Γ ε a q‖ ≤ dGam Γ alpha * a ^ (1 - alpha) :=
  PhaseContractions.phase_trace archimedesLaw_holds hΓt hΓs ha0 ha2 ε hε a ha q

/-- **The Fourier form of `T_ε`** (main TeX lines 2081-2084, proof 2107-2108 at a284420)
without the `d = 3` Fourier input: `PhaseContractions.traceT_fourier` with `WaveFourierThree`
discharged (`waveFourierThree_holds`).  For a locally finite tempered `μ` with the spectral
convention, `ε, a > 0` and `q ∈ ℝ³`, `ξ ↦ Ĝ_a(q+ξ) e^{-ε|ξ|²}` is `μ`-integrable and
`T_ε(a,q) = ∫ Ĝ_a(q+ξ) e^{-ε|ξ|²} μ(dξ)`. -/
theorem traceT_fourier_completed {Γ μ : Measure (Rd 3)} [IsLocallyFiniteMeasure μ]
    (hμt : IsTempered μ) (hsp : IsSpectralMeasure Γ μ) (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : 0 < a)
    (q : Rd 3) :
    Integrable (fun ξ : Rd 3 => (waveHat a (q + ξ) : ℂ) * (Real.exp (-(ε * ‖ξ‖ ^ 2)) : ℂ)) μ ∧
      traceT Γ ε a q =
        ∫ ξ, (waveHat a (q + ξ) : ℂ) * (Real.exp (-(ε * ‖ξ‖ ^ 2)) : ℂ) ∂μ :=
  PhaseContractions.traceT_fourier waveFourierThree_holds hμt hsp ε hε a ha q

/-- **`L:phase-contractions`** (Two static contraction bounds; main TeX lines 2072-2086, proof
2088-2138 at a284420) under the standing assumptions of `S:static-phase` (`PhaseCovariance`,
lines 2054-2057) alone: `PhaseContractions.phase_contractions_paper` with `WaveFourierThree` and
`ArchimedesLaw` discharged by wave item L9-G.  `E:phase-resolvent`: for `λ > 0`, `q ∈ ℝ³`,
`∫ μ(dξ)/(λ²+|q+ξ|²) ≤ R_α λ^{α-2}` with integrability; `E:phase-trace` and the definition of
`T_ε`: for `a, ε > 0`, `q ∈ ℝ³`, `p_{2ε}(x - ·)` is `Γ`-integrable and `Γ_ε ≥ 0`, both
integrands of `T_ε` are integrable, `T_ε(a,q) = ∫ Ĝ_a(q+ξ) e^{-ε|ξ|²} μ(dξ)` and
`|T_ε(a,q)| ≤ D_Γ a^{1-α}`. -/
theorem phase_contractions_paper_completed {alpha : ℝ} {Γ μ : Measure (Rd 3)}
    (h : PhaseCovariance alpha Γ μ) :
    (∀ lam : ℝ, 0 < lam → ∀ q : Rd 3,
      Integrable (fun ξ : Rd 3 => 1 / (lam ^ 2 + ‖q + ξ‖ ^ 2)) μ ∧
        ∫ ξ, 1 / (lam ^ 2 + ‖q + ξ‖ ^ 2) ∂μ ≤ ralpha μ alpha * lam ^ (alpha - 2)) ∧
    (∀ a : ℝ, 0 < a → ∀ ε : ℝ, 0 < ε → ∀ q : Rd 3,
      (∀ x : Rd 3, Integrable (fun y => pdens (2 * ε) (x - y)) Γ ∧
        0 ≤ PhaseContractions.gammaEps Γ ε x) ∧
      Integrable (fun x => Complex.exp (Complex.I * ((inner ℝ q x : ℝ) : ℂ)) *
          (PhaseContractions.gammaEps Γ ε x : ℂ)) (waveGreen 3 a) ∧
        Integrable (fun ξ : Rd 3 => (waveHat a (q + ξ) : ℂ) *
          (Real.exp (-(ε * ‖ξ‖ ^ 2)) : ℂ)) μ ∧
        traceT Γ ε a q = ∫ ξ, (waveHat a (q + ξ) : ℂ) * (Real.exp (-(ε * ‖ξ‖ ^ 2)) : ℂ) ∂μ ∧
        ‖traceT Γ ε a q‖ ≤ dGam Γ alpha * a ^ (1 - alpha)) :=
  PhaseContractions.phase_contractions_paper h waveFourierThree_holds archimedesLaw_holds

/-- **`L:phase-contractions` under `H:homog` in `d = 3`** (main TeX lines 2072-2138 at
a284420): `phase_contractions_paper_completed` with the section's class obtained from
`H:homog` by `PhaseContractions.PhaseCovariance.of_homog` (the parameter `α₀` is carried and
unused).  Same conclusions. -/
theorem phase_contractions_homog_completed {alpha alpha0 : ℝ} {Γ μ : Measure (Rd 3)}
    (hH : HomogCovariance 3 alpha alpha0 Γ μ) :
    (∀ lam : ℝ, 0 < lam → ∀ q : Rd 3,
      Integrable (fun ξ : Rd 3 => 1 / (lam ^ 2 + ‖q + ξ‖ ^ 2)) μ ∧
        ∫ ξ, 1 / (lam ^ 2 + ‖q + ξ‖ ^ 2) ∂μ ≤ ralpha μ alpha * lam ^ (alpha - 2)) ∧
    (∀ a : ℝ, 0 < a → ∀ ε : ℝ, 0 < ε → ∀ q : Rd 3,
      (∀ x : Rd 3, Integrable (fun y => pdens (2 * ε) (x - y)) Γ ∧
        0 ≤ PhaseContractions.gammaEps Γ ε x) ∧
      Integrable (fun x => Complex.exp (Complex.I * ((inner ℝ q x : ℝ) : ℂ)) *
          (PhaseContractions.gammaEps Γ ε x : ℂ)) (waveGreen 3 a) ∧
        Integrable (fun ξ : Rd 3 => (waveHat a (q + ξ) : ℂ) *
          (Real.exp (-(ε * ‖ξ‖ ^ 2)) : ℂ)) μ ∧
        traceT Γ ε a q = ∫ ξ, (waveHat a (q + ξ) : ℂ) * (Real.exp (-(ε * ‖ξ‖ ^ 2)) : ℂ) ∂μ ∧
        ‖traceT Γ ε a q‖ ≤ dGam Γ alpha * a ^ (1 - alpha)) :=
  phase_contractions_paper_completed (PhaseCovariance.of_homog hH)

end StratonovichHAMSecondMoment.L9Completed
