module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Hypothesis `H:homog` of the manuscript (main TeX file, Section `S:model`),
stated in full as a Lean predicate, and the two results that the manuscript
states under it, `E:kappa` and `E:driver-parameters`, restated with this
hypothesis. Their proofs use only the numerical part of `H:homog`
(`KappaRange.kappa_mem_Ioo`, `DriverParameters.parameters_nonempty`); the
covariance part is carried as hypotheses exactly as the manuscript states
them, so these wrappers have the manuscript's own hypotheses.
-/

public import Mathlib
public import StratonovichHAMSecondMoment.KappaRange
public import StratonovichHAMSecondMoment.DriverParameters

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory
open scoped Pointwise

namespace StratonovichHAMSecondMoment.HomogHypothesis

/-- Euclidean space `ℝ^d`. -/
abbrev Rd (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A tempered measure: `∫ (1 + ‖x‖)^(-k) dν < ∞` for some natural `k`. -/
def IsTempered {d : ℕ} (ν : Measure (Rd d)) : Prop :=
  ∃ k : ℕ, ∫⁻ x, ENNReal.ofReal ((1 + ‖x‖) ^ (-(k : ℝ))) ∂ν < ⊤

/-- An even measure: invariant under `x ↦ -x`. -/
def IsEven {d : ℕ} (ν : Measure (Rd d)) : Prop :=
  ν.map (fun x => -x) = ν

/-- Positive-definiteness of `Γ` as a tempered distribution:
`⟨Γ, φ ⋆ φ̃⟩` is a nonnegative real for every Schwartz `φ`, where
`(φ ⋆ φ̃)(x) = ∫ φ(x + y) conj(φ(y)) dy` and `φ̃(x) = conj(φ(-x))`. -/
def IsPosDefDistr {d : ℕ} (Γ : Measure (Rd d)) : Prop :=
  ∀ φ : SchwartzMap (Rd d) ℂ,
    (∫ x, (∫ y, φ (x + y) * (starRingEnd ℂ) (φ y)) ∂Γ).im = 0 ∧
      0 ≤ (∫ x, (∫ y, φ (x + y) * (starRingEnd ℂ) (φ y)) ∂Γ).re

/-- `μ` is the spectral measure of `Γ` in the manuscript's convention
`Γ = ∫ e^{i ξ·x} μ(dξ)` in the sense of tempered distributions:
`∫ φ dΓ = ∫ (∫ φ(x) e^{i ξ·x} dx) μ(dξ)` for every Schwartz `φ`. -/
def IsSpectralMeasure {d : ℕ} (Γ μ : Measure (Rd d)) : Prop :=
  ∀ φ : SchwartzMap (Rd d) ℂ,
    ∫ x, φ x ∂Γ =
      ∫ ξ, (∫ x, φ x * Complex.exp (Complex.I * (inner ℝ ξ x : ℝ))) ∂μ

/-- Hypothesis `H:homog`. Let `d ∈ {1,2,3}` and `0 < α₀ < 1`. The spatial
covariance is a nonnegative, even, positive-definite tempered Radon measure
`Γ` on `ℝ^d` with positive even tempered Radon spectral measure `μ`,
`Γ = ∫ e^{i ξ·x} μ(dξ)`; for every Borel set `A` and `c > 0`,
`Γ(cA) = c^{d-α} Γ(A)`; `α₀ + α < 2` (`E:threshold`), with `0 < α < d` or
`α = d = 1`. A Lean measure is nonnegative, and on `ℝ^d` a locally finite
Borel measure is a Radon measure. -/
structure HomogCovariance (d : ℕ) (alpha alpha0 : ℝ) (Γ μ : Measure (Rd d)) :
    Prop where
  dim : d = 1 ∨ d = 2 ∨ d = 3
  alpha0_pos : 0 < alpha0
  alpha0_lt_one : alpha0 < 1
  Γ_radon : IsLocallyFiniteMeasure Γ
  Γ_even : IsEven Γ
  Γ_tempered : IsTempered Γ
  Γ_posdef : IsPosDefDistr Γ
  μ_radon : IsLocallyFiniteMeasure μ
  μ_even : IsEven μ
  μ_tempered : IsTempered μ
  spectral : IsSpectralMeasure Γ μ
  scaling : ∀ A : Set (Rd d), MeasurableSet A → ∀ c : ℝ, 0 < c →
    Γ (c • A) = ENNReal.ofReal (c ^ ((d : ℝ) - alpha)) * Γ A
  threshold : alpha0 + alpha < 2
  alpha_range : (0 < alpha ∧ alpha < d) ∨ (alpha = d ∧ d = 1)

/-- The numerical part of `H:homog`, in the form used by `DriverParameters`
(with `a = α₀`). -/
theorem homog_params {d : ℕ} {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (h : HomogCovariance d alpha alpha0 Γ μ) :
    DriverParameters.Homog d alpha alpha0 :=
  ⟨h.dim, h.alpha0_pos, h.alpha0_lt_one, by linarith [h.threshold], h.alpha_range⟩

/-- `E:kappa` with the manuscript's hypothesis: under `H:homog`,
`κ = (4 - α - α₀)/(3 - α) ∈ (1, 2)`. -/
theorem kappa_mem_Ioo_paper {d : ℕ} {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (h : HomogCovariance d alpha alpha0 Γ μ) :
    KappaRange.kappa alpha alpha0 ∈ Set.Ioo 1 2 :=
  KappaRange.kappa_mem_Ioo d alpha alpha0 h.dim h.alpha0_pos h.alpha0_lt_one
    h.threshold h.alpha_range

/-- `E:driver-parameters` with the manuscript's hypothesis (the section
retains `H:homog` and sets `a = α₀`): its strict intervals are nonempty. -/
theorem parameters_nonempty_paper {d : ℕ} {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (h : HomogCovariance d alpha alpha0 Γ μ) :
    ∃ γ θ β : ℝ, (0 < γ ∧ γ < min (1 / 2) ((2 - alpha) / 2)) ∧
      (1 / 2 < θ ∧ θ < β ∧ β < min (1 - alpha0 / 2) ((3 - alpha0 - alpha) / 2)) :=
  DriverParameters.parameters_nonempty d alpha alpha0 (homog_params h)

end StratonovichHAMSecondMoment.HomogHypothesis
