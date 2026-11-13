module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

The wrappers of `P:clock-copy-obstruction` (main TeX file
`notes/notes_stratonovich_ham_second_moment.tex`, revision a284420, lines
7754-7905) and of the finiteness and nonnegativity parts of
`L:damped-homogeneous-norms` (lines 803-919), re-issued with the
manuscript's hypotheses only: the supplied input
`SpectralHomog.SpectralHomogeneous μ α` of `ClockCopy.clock_copy_obstruction_paper`,
`ClockCopy.damped_N2_nonneg_paper` and `DampedNorms.damped_norms_finite_paper`
is now derived from `H:homog` by
`MaskedSpectralGrowth.spectralHomogeneous_of_homog` (the sentence
"Scaling the Fourier representation of `Γ` and using Fourier uniqueness gives
`μ(cA) = c^α μ(A)`", lines 851-852).

Each theorem here has exactly the conclusion of the existing wrapper it
re-issues and is proved by applying that wrapper; the existing modules and
their statements are unchanged.
-/

public import Mathlib
public import StratonovichHAMSecondMoment.HomogHypothesis
public import StratonovichHAMSecondMoment.SpectralHomog
public import StratonovichHAMSecondMoment.WaveKernel
public import StratonovichHAMSecondMoment.DampedNorms
public import StratonovichHAMSecondMoment.ClockCopy
public import StratonovichHAMSecondMoment.MaskedSpectralGrowth

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Real Filter

namespace StratonovichHAMSecondMoment.ClockCopyHomog

open HomogHypothesis TimeFractional SpectralHomog WaveKernel DampedNorms ClockCopy
  MaskedSpectralGrowth

variable {d : ℕ}

/-- **`P:clock-copy-obstruction`** under `H:homog` (`HomogCovariance`, temporal
exponent `a = α₀`), `Γ ≠ 0`, `θ > 0` and `-1 ≤ ρ ≤ 1`, with no supplied
input: the conclusion of `ClockCopy.clock_copy_obstruction_paper` (positivity
and integrability of `w_θ`, `K_Γ(θ) = ∫_0^∞ w_θ`, integrability of the
candidate integrands, `0 < J_{Γ,ρ}(θ) ≤ J_{Γ,1}(θ)`,
`J_{Γ,1}(θ) = ∫_0^∞ 2θ/(2θ+λ) w_θ`, `E:clock-copy-obstruction`
`J_{Γ,1}(θ) < K_Γ(θ)`, and `E:degree-one-clock-loss` when `α = 1`). -/
theorem clock_copy_obstruction_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (h : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) (θ : ℝ) (hθ : 0 < θ) (ρ : ℝ)
    (hρ : -1 ≤ ρ ∧ ρ ≤ 1) :
    (∀ l : ℝ, 0 < l → 0 < weight alpha0 θ μ l) ∧ Integrable (weight alpha0 θ μ) L0 ∧
      Integrable (fun p : ℝ × ℝ => Real.exp (-(θ * (p.1 + p.2))) * |p.1 - p.2| ^ (-alpha0) *
        ∫ ξ, waveHat p.1 ξ * waveHat p.2 ξ ∂μ) P2 ∧
      N2sq alpha0 θ μ = ∫ l in Ioi (0 : ℝ), weight alpha0 θ μ l ∧
      Integrable (Jintegrand alpha0 θ μ ρ) P2 ∧ Integrable (Jintegrand alpha0 θ μ 1) P2 ∧
      0 < J alpha0 θ μ ρ ∧ J alpha0 θ μ ρ ≤ J alpha0 θ μ 1 ∧
      Integrable (filteredWeight alpha0 θ μ) L0 ∧
      J alpha0 θ μ 1 = ∫ l in Ioi (0 : ℝ), filteredWeight alpha0 θ μ l ∧
      J alpha0 θ μ 1 < N2sq alpha0 θ μ ∧
      (alpha = 1 → J alpha0 θ μ 1 = (2 - 2 ^ alpha0) * N2sq alpha0 θ μ) :=
  ClockCopy.clock_copy_obstruction_paper h (spectralHomogeneous_of_homog h) hΓ θ hθ ρ hρ

/-- `N₂(θ)² ≥ 0` under `H:homog` and `θ > 0` (the nonnegativity claim of
`L:damped-homogeneous-norms`), with no supplied input: the conclusion of
`ClockCopy.damped_N2_nonneg_paper`. -/
theorem damped_N2_nonneg_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (h : HomogCovariance d alpha alpha0 Γ μ) (θ : ℝ) (hθ : 0 < θ) : 0 ≤ N2sq alpha0 θ μ :=
  ClockCopy.damped_N2_nonneg_paper h (spectralHomogeneous_of_homog h) θ hθ

/-- The finiteness part of `L:damped-homogeneous-norms` under `H:homog` and
`θ > 0`, with no supplied input: the conclusion of
`DampedNorms.damped_norms_finite_paper` (absolute integrability of the spectral
formula for `N₂(θ)²` on `(0,∞)² × ℝ^d`, of its outer integrand, and of the
integrand of `N₁(θ)`). -/
theorem damped_norms_finite_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (h : HomogCovariance d alpha alpha0 Γ μ) (θ : ℝ) (hθ : 0 < θ) :
    Integrable (N2integrand (d := d) alpha0 θ) (P2.prod μ) ∧
      Integrable (fun p : ℝ × ℝ => Real.exp (-(θ * (p.1 + p.2))) * |p.1 - p.2| ^ (-alpha0) *
        ∫ ξ, waveHat p.1 ξ * waveHat p.2 ξ ∂μ) P2 ∧
      Integrable (fun l : ℝ => l ^ (alpha0 - 1) * resolvent μ (θ + l)) L0 :=
  DampedNorms.damped_norms_finite_paper h (spectralHomogeneous_of_homog h) θ hθ

end StratonovichHAMSecondMoment.ClockCopyHomog
