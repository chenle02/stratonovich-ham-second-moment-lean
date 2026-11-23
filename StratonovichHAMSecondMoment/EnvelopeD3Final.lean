module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L17, item L17-E3, part 4: the `d = 3` results of `EnvelopeD3` with the frozen
`PairingEnvelopeTarget` discharged by `PairingEnvelope.pairing_product_envelope`
(`EnvelopeFinal.hPE`), for the Green-smoothed kernels `p_η * G_s`, uniformly in `η > 0` and the
noise width `ε > 0` (main TeX lines 1970-2041 and 2352-2394 at revision edf7085f
(book 1.1.3)).  The limit `η ↓ 0` is not formalized (L17 decision 5), so there are no `d = 3`
moment sentences through `MixedMoment`.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.EnvelopeFinal
public import StratonovichHAMSecondMoment.EnvelopeD3

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal Real Nat

namespace StratonovichHAMSecondMoment.EnvelopeD3Final

open HomogHypothesis (Rd HomogCovariance)
open LowAlphaConvolution (smoothedGreen)
open WaveGreen (waveGreen)
open DiagramModel (Pi2 diagram covEps)

/-- **`E:homogeneous-envelope` in `d = 3`** for the Green-smoothed kernels (TeX 2352-2394),
under `H:homog`, uniformly in `η > 0` and `ε > 0`. -/
theorem homogeneous_envelope_diagrams_three_l17 {alpha α₀ : ℝ} {Γ μ : Measure (Rd 3)}
    (hH : HomogCovariance 3 alpha α₀ Γ μ) :
    ∃ K : ℝ, 0 < K ∧ ∀ η : ℝ, 0 < η → ∀ ε : ℝ, 0 < ε → ∀ (m n k : ℕ), m + n = 2 * k → 1 ≤ k →
      ∀ t θ : ℝ, 0 < t → 0 < θ →
        ∑ D ∈ Pi2 m n, diagram (fun s => smoothedGreen (waveGreen 3) s η) (covEps Γ ε) α₀ m n D t ≤
          ENNReal.ofReal ((Pi2 m n).card * K ^ k * Real.exp (2 * θ * t) *
            θ ^ (-((4 - alpha - α₀) * k))) :=
  EnvelopeD3.homogeneous_envelope_diagrams_three hH (EnvelopeFinal.hPE 3)

/-- **`E:theta-envelope` in `d = 3`** for the Green-smoothed kernels (TeX: the display 2003-2006,
in Step 1 1993-2031), under
`H:homog`, uniformly in `η > 0` and `ε > 0`. -/
theorem theta_envelope_diagrams_three_l17 {alpha α₀ : ℝ} {Γ μ : Measure (Rd 3)}
    (hH : HomogCovariance 3 alpha α₀ Γ μ) :
    ∃ C θ₀ : ℝ, 0 < C ∧ 0 < θ₀ ∧ ∀ η : ℝ, 0 < η → ∀ ε : ℝ, 0 < ε → ∀ (n : ℕ) (t θ : ℝ),
      0 < t → θ₀ ≤ θ →
      ∑ D ∈ Pi2 n n, diagram (fun s => smoothedGreen (waveGreen 3) s η) (covEps Γ ε) α₀ n n D t ≤
        ENNReal.ofReal ((Pi2 n n).card * Real.exp (2 * θ * t) * C ^ n * θ ^ (-(2 * (n : ℝ)))) :=
  EnvelopeD3.theta_envelope_diagrams_three hH (EnvelopeFinal.hPE 3)

/-- **The first inequality of `E:crude-corrected` for the diagram sums, in `d = 3`** for the
Green-smoothed kernels (TeX: the display 1980-1984; its first inequality derived in Step 2,
2036-2041), under `H:homog`, uniformly in `η > 0` and `ε > 0`. -/
theorem crude_corrected_diagrams_three_l17 {alpha α₀ : ℝ} {Γ μ : Measure (Rd 3)}
    (hH : HomogCovariance 3 alpha α₀ Γ μ) :
    ∃ C θ₀ : ℝ, 0 < C ∧ 0 < θ₀ ∧ ∀ η : ℝ, 0 < η → ∀ ε : ℝ, 0 < ε → ∀ (n : ℕ) (t : ℝ),
      1 ≤ n → 0 < t →
      ∑ D ∈ Pi2 n n, diagram (fun s => smoothedGreen (waveGreen 3) s η) (covEps Γ ε) α₀ n n D t ≤
        ENNReal.ofReal (Real.exp (2 * θ₀ * t) * C ^ n * t ^ (2 * n) / (n ! : ℝ)) :=
  EnvelopeD3.crude_corrected_diagrams_three hH (EnvelopeFinal.hPE 3)

end StratonovichHAMSecondMoment.EnvelopeD3Final
