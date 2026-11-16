module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Integration of wave item L10-A1 (`AlphaOneConvolution`) with wave items L9-L
(`LowAlphaConvolution`) and L9-G (`WaveGreenFourier`) for the main TeX file
`notes/notes_stratonovich_ham_second_moment.tex` (line numbers at revision 39f2597a).  This
module discharges the two supplied inputs of `AlphaOneConvolution.alpha_one_convolution_paper`
(`L:alpha-one-convolution`, statement lines 5635-5643, proof lines 5645-5708); it defines no new
object.

1. `AlphaOneConvolution.SpectralPairing Γ μ`, the "Fourier Fubini" representation
   `∫ G_{h,η}(dy) γ_ε(y+z) = ∫ Ĝ_{h,η}(ξ) e^{iξ·z} e^{-ε|ξ|²/2} μ(dξ)` with the integrability
   of the left integrand (lines 5610-5612, used at line 5673).  `spectralPairing_holds`
   derives it from `LowAlphaConvolution.smoothed_pairing_spectral` (wave L9-L) applied to the
   finite measure `G_{h,η} = p_η * G_h`, for tempered `Γ`, `μ` with the spectral convention
   (`μ` s-finite); `γ_ε` of `AlphaOneConvolution` is definitionally L9-L's `gammaEps`
   (`AlphaOneConvolution.conv_heatK_eq_gammaEps`).  No dimension restriction is needed.
2. `AlphaOneConvolution.WaveGreenFourier d`, `∫ e^{iξ·y} G_s(dy) = sin(s|ξ|)/|ξ|` for `s > 0`
   (lines 5614-5618).  `waveGreenFourier_holds` is the second conjunct of
   `WaveGreenFourier.waveGreen_fourier` (wave L9-G) for `d ∈ {1,2,3}`.

`alpha_one_convolution_completed` (general form) and `alpha_one_convolution_paper_completed`
(under `H:homog` with `α = 1`) have the conclusions of `AlphaOneConvolution.alpha_one_convolution`
and `alpha_one_convolution_paper` with both inputs discharged.  After this module
`L:alpha-one-convolution` rests on its standing assumptions alone.  Every narrowing recorded in
the source modules is unchanged; in particular the `d = 3` Green measure is the recorded
`toSphere` definitional choice of `WaveGreen` (decision 4 of wave L6).

Fields of `H:homog` used by `alpha_one_convolution_paper_completed`: `dim`, `μ_radon`,
`μ_tempered`, `Γ_tempered`, `spectral`, `scaling` (the last through
`MaskedSpectralGrowth.spectralHomogeneous_of_homog`).  Carried, unused: `alpha0_pos`,
`alpha0_lt_one`, `Γ_radon`, `Γ_even`, `Γ_posdef`, `μ_even`, `threshold`, `alpha_range`.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.WaveGreenFourier
public import StratonovichHAMSecondMoment.LowAlphaConvolution
public import StratonovichHAMSecondMoment.AlphaOneConvolution

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Real Metric

namespace StratonovichHAMSecondMoment.L10Completed

open HomogHypothesis (Rd HomogCovariance IsTempered IsSpectralMeasure)
open SpectralHomog (SpectralHomogeneous)
open WaveGreen (waveGreen)
open VariationalDilation (conv)
open VariationalMean (heatK)
open LowAlphaConvolution (smoothedGreen)
open AlphaOneConvolution (Ia sphereMeasure SpectralPairing)

/-! ### The bridges -/

/-- **The supplied input `AlphaOneConvolution.SpectralPairing Γ μ` holds** for tempered `Γ`,
`μ` with `IsSpectralMeasure Γ μ` (`μ` s-finite), in every dimension: the "Fourier Fubini" step
of main TeX lines 5610-5612 (used at line 5673) at 39f2597a, by
`LowAlphaConvolution.smoothed_pairing_spectral` for the finite measure `G_{h,η}`. -/
theorem spectralPairing_holds {d : ℕ} {Γ μ : Measure (Rd d)} [SFinite μ]
    (hΓt : IsTempered Γ) (hμt : IsTempered μ) (hsp : IsSpectralMeasure Γ μ) :
    SpectralPairing Γ μ := by
  intro h _ ε hε η _ z
  have := WaveGreen.isFiniteMeasure_waveGreen d h
  have : IsFiniteMeasure (smoothedGreen (waveGreen d) h η) := by
    unfold smoothedGreen; infer_instance
  obtain ⟨-, hint, -, hrep⟩ :=
    LowAlphaConvolution.smoothed_pairing_spectral hΓt hμt hsp hε
      (smoothedGreen (waveGreen d) h η) z
  exact ⟨hint, hrep⟩

/-- **The supplied input `AlphaOneConvolution.WaveGreenFourier d` holds** for `d ∈ {1,2,3}`:
`∫ e^{iξ·y} G_s(dy) = sin(s|ξ|)/|ξ|` (value `s` at `ξ = 0`) for `s > 0` (main TeX lines
5614-5618 at 39f2597a), by `WaveGreenFourier.waveGreen_fourier` (wave L9-G). -/
theorem waveGreenFourier_holds (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) :
    AlphaOneConvolution.WaveGreenFourier d :=
  fun s hs ξ => (WaveGreenFourier.waveGreen_fourier d hd s hs ξ).2

/-! ### `L:alpha-one-convolution` without supplied inputs -/

/-- **`L:alpha-one-convolution`, general form, nothing supplied** (main TeX lines 5635-5708 at
39f2597a): `AlphaOneConvolution.alpha_one_convolution` with `SpectralPairing Γ μ` and
`WaveGreenFourier d` discharged.  Hypotheses: `d ∈ {1,2,3}`, `μ` locally finite with
`μ(cA) = cμ(A)`, `Γ` and `μ` tempered, `IsSpectralMeasure Γ μ`.  Conclusions: `V < ∞`, and for
`h > 0`, `ε > 0`, `η ≥ 0`, `z`, with `a = (ε+η)/2`: `y ↦ γ_ε(y+z)` is `G_{h,η}`-integrable, the
radial integrals `I_a(h,v)` converge absolutely, `θ ↦ I_a(h,θ·z)` is `σ`-integrable,
`E:alpha-one-polar`, and `0 ≤ ∫ G_{h,η}(dy) γ_ε(y+z) ≤ πV/2` (`E:alpha-one-convolution`). -/
theorem alpha_one_convolution_completed {d : ℕ} (hd : d = 1 ∨ d = 2 ∨ d = 3)
    {Γ μ : Measure (Rd d)} (hI : SpectralHomogeneous μ 1) [IsLocallyFiniteMeasure μ]
    (hΓt : IsTempered Γ) (hμt : IsTempered μ) (hsp : IsSpectralMeasure Γ μ) :
    μ (closedBall 0 1) < ⊤ ∧
      ∀ h : ℝ, 0 < h → ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 ≤ η → ∀ z : Rd d,
        Integrable (fun y => conv Γ (heatK ε) (y + z)) (smoothedGreen (waveGreen d) h η) ∧
        (∀ v : ℝ, IntegrableOn (fun r : ℝ => Real.exp (-((ε + η) / 2 * r ^ 2)) *
          (Real.sin (h * r) / r) * Real.cos (r * v)) (Ioi 0)) ∧
        Integrable (fun θ : Rd d => Ia ((ε + η) / 2) h (inner ℝ θ z)) (sphereMeasure μ) ∧
        ∫ y, conv Γ (heatK ε) (y + z) ∂(smoothedGreen (waveGreen d) h η) =
          ∫ θ, Ia ((ε + η) / 2) h (inner ℝ θ z) ∂(sphereMeasure μ) ∧
        0 ≤ ∫ y, conv Γ (heatK ε) (y + z) ∂(smoothedGreen (waveGreen d) h η) ∧
        ∫ y, conv Γ (heatK ε) (y + z) ∂(smoothedGreen (waveGreen d) h η) ≤
          π * (μ (closedBall 0 1)).toReal / 2 :=
  AlphaOneConvolution.alpha_one_convolution hI hμt (spectralPairing_holds hΓt hμt hsp)
    (waveGreenFourier_holds d hd)

/-- **`L:alpha-one-convolution`** (Degree-one convolution bound; main TeX lines 5635-5643,
proof 5645-5708 at 39f2597a) under `H:homog` with `α = 1` alone
(`HomogCovariance d 1 α₀ Γ μ`; no `Γ ≠ 0`, as in the TeX), for `G_h = waveGreen d h`,
`γ_ε = Γ * p_ε` and `G_{h,η} = p_η * G_h`: `AlphaOneConvolution.alpha_one_convolution_paper`
with `SpectralPairing Γ μ` (wave L9-L) and `WaveGreenFourier d` (wave L9-G) discharged.  Same
conclusions: `V = μ{|ξ| ≤ 1} < ∞`, and for `h > 0`, `ε > 0`, `η ≥ 0`, `z ∈ ℝ^d`, with
`a = (ε+η)/2`: integrability of `y ↦ γ_ε(y+z)` against `G_{h,η}`, absolute convergence of the
radial integrals defining `I_a(h,v)`, `σ`-integrability of `θ ↦ I_a(h,θ·z)`,
`E:alpha-one-polar`, and `0 ≤ ∫ G_{h,η}(dy) γ_ε(y+z) ≤ πV/2` (`E:alpha-one-convolution`). -/
theorem alpha_one_convolution_paper_completed {d : ℕ} {alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d 1 alpha0 Γ μ) :
    μ (closedBall 0 1) < ⊤ ∧
      ∀ h : ℝ, 0 < h → ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 ≤ η → ∀ z : Rd d,
        Integrable (fun y => conv Γ (heatK ε) (y + z)) (smoothedGreen (waveGreen d) h η) ∧
        (∀ v : ℝ, IntegrableOn (fun r : ℝ => Real.exp (-((ε + η) / 2 * r ^ 2)) *
          (Real.sin (h * r) / r) * Real.cos (r * v)) (Ioi 0)) ∧
        Integrable (fun θ : Rd d => Ia ((ε + η) / 2) h (inner ℝ θ z)) (sphereMeasure μ) ∧
        ∫ y, conv Γ (heatK ε) (y + z) ∂(smoothedGreen (waveGreen d) h η) =
          ∫ θ, Ia ((ε + η) / 2) h (inner ℝ θ z) ∂(sphereMeasure μ) ∧
        0 ≤ ∫ y, conv Γ (heatK ε) (y + z) ∂(smoothedGreen (waveGreen d) h η) ∧
        ∫ y, conv Γ (heatK ε) (y + z) ∂(smoothedGreen (waveGreen d) h η) ≤
          π * (μ (closedBall 0 1)).toReal / 2 := by
  have := hH.μ_radon
  exact AlphaOneConvolution.alpha_one_convolution_paper hH
    (spectralPairing_holds hH.Γ_tempered hH.μ_tempered hH.spectral)
    (waveGreenFourier_holds d hH.dim)

end StratonovichHAMSecondMoment.L10Completed
