module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L17, integration: the results of item L17-E with the hypothesis
`PairingEnvelopeTarget` discharged by `PairingEnvelope.pairing_product_envelope`
(`L:pairing-product-envelope`, whole).  Main TeX file at revision edf7085f (book 1.1.3):
`L:crude-corrected` (lines 1978-2054, `E:theta-envelope` 2003) and `P:envelope`
(lines 2352-2433).  The remaining hypotheses are those of the TeX and of decision 5 of wave L17:
`H:homog`, `d ∈ {1, 2}` (`d = 3` is formalized at the diagram level for the Green-smoothed
kernel uniformly in `η > 0` in `GreenSmoothed3`, `PairingSmoothedNorms`, `EnvelopeD3` and
`EnvelopeD3Final`; in wave L17 (decision 5) the limit `η → 0` and the `d = 3` moment
(`_paper`) versions were not formalized in these modules; since wave L18 the pointwise
Green-width limit of the spatial diagram factor `wickJ` at fixed nonnegative gaps and fixed
positive vertexwise spatial widths is `EnvelopeD3Wave.tendsto_wickJ_greenS` (from the spectral
identity `SpectralSpatialWTarget`, proved by `WickSpectral.spectral_spatial_w`, and the
spectral-side limit `tendsto_spatialSpecW`) and the unsmoothed `d = 3`
diagram bounds are `WickFinal.homogeneous_envelope_diagrams_three_l18` and
`WickFinal.crude_corrected_diagrams_three_l18`; since wave L19 the `d = 3` moment sentences are
`SourceFinal.crude_corrected_paper_l19` and `SourceFinal.envelope_paper_l19`), and, for the
moment
sentences, the supplied input `DiagramModel.MixedMoment` (`P:mixed`; blocker D5 when this module
was written, the solution and its chaos not constructed; discharged in wave L19 for the chaos
terms `srcX` and their series `srcU` on every source field, `SourceFinal.mixed_terms_l19`).
-/
public import Mathlib
public import StratonovichHAMSecondMoment.PairingEnvelope
public import StratonovichHAMSecondMoment.CrudeCorrected

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal Real Nat

namespace StratonovichHAMSecondMoment.EnvelopeFinal

open HomogHypothesis (Rd HomogCovariance)
open WaveGreen (waveGreen)
open DiagramModel (Pi2 diagram covEps MixedMoment)
open HomogeneousEnvelope (BK)

variable {d : ℕ}

/-- `L:pairing-product-envelope` for every label type `Fin N`. -/
theorem hPE (d : ℕ) : ∀ N : ℕ, PairingInterface.PairingEnvelopeTarget d (Fin N) :=
  fun N => PairingEnvelope.pairing_product_envelope d (Fin N)

/-- **`E:theta-envelope`** for the model diagrams at every noise width (TeX: the display
2003-2006, in Step 1 1993-2031, at revision edf7085f (book 1.1.3)), `d = 1, 2`, under `H:homog`. -/
theorem theta_envelope_diagrams_l17 {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha α₀ Γ μ) (hd : d = 1 ∨ d = 2) :
    ∃ C θ₀ : ℝ, 0 < C ∧ 0 < θ₀ ∧ ∀ ε : ℝ, 0 < ε → ∀ (n : ℕ) (t θ : ℝ), 0 < t → θ₀ ≤ θ →
      ∑ D ∈ Pi2 n n, diagram (waveGreen d) (covEps Γ ε) α₀ n n D t ≤
        ENNReal.ofReal ((Pi2 n n).card * Real.exp (2 * θ * t) * C ^ n * θ ^ (-(2 * (n : ℝ)))) :=
  CrudeCorrected.theta_envelope_diagrams hH hd (hPE d)

/-- **The first inequality of `E:crude-corrected` for the diagram sums** (TeX: the display
1980-1984; its first inequality derived in Step 2, 2036-2041; at revision edf7085f (book 1.1.3)),
`d = 1, 2`, under `H:homog`. -/
theorem crude_corrected_diagrams_l17 {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha α₀ Γ μ) (hd : d = 1 ∨ d = 2) :
    ∃ C θ₀ : ℝ, 0 < C ∧ 0 < θ₀ ∧ ∀ ε : ℝ, 0 < ε → ∀ (n : ℕ) (t : ℝ), 1 ≤ n → 0 < t →
      ∑ D ∈ Pi2 n n, diagram (waveGreen d) (covEps Γ ε) α₀ n n D t ≤
        ENNReal.ofReal (Real.exp (2 * θ₀ * t) * C ^ n * t ^ (2 * n) / (n ! : ℝ)) :=
  CrudeCorrected.crude_corrected_diagrams hH hd (hPE d)

/-- **`L:crude-corrected`** (TeX lines 1978-2054 at revision edf7085f (book 1.1.3)), `d = 1, 2`,
under `H:homog`, for random variables with the supplied input `MixedMoment`. -/
theorem crude_corrected_paper_l17 {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha α₀ Γ μ) (hd : d = 1 ∨ d = 2) :
    ∃ C θ₀ : ℝ, 0 < C ∧ 0 < θ₀ ∧ ∀ t : ℝ, 0 < t → ∀ {Ω : Type} [MeasurableSpace Ω]
      {P : Measure Ω} {X : ℕ → Ω → ℝ} {u : Ω → ℝ}, MixedMoment d α₀ Γ P X u t →
      (∀ n : ℕ, 1 ≤ n → ∫ ω, X n ω ^ 2 ∂P ≤ Real.exp (2 * θ₀ * t) * C ^ n * t ^ (2 * n) / n !) ∧
      ∫ ω, u ω ^ 2 ∂P ≤ 2 * Real.exp (2 * θ₀ * t + 2 * C * t ^ 2) :=
  CrudeCorrected.crude_corrected_paper hH hd (hPE d)

/-- **`E:homogeneous-envelope`** for the model diagrams at every noise width (TeX lines
2352-2394 at revision edf7085f (book 1.1.3)), `d = 1, 2`, under `H:homog`. -/
theorem homogeneous_envelope_diagrams_l17 {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha α₀ Γ μ) (hd : d = 1 ∨ d = 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ∀ (m n k : ℕ), m + n = 2 * k → 1 ≤ k →
      ∀ t θ : ℝ, 0 < t → 0 < θ →
        ∑ D ∈ Pi2 m n, diagram (waveGreen d) (covEps Γ ε) α₀ m n D t ≤
          ENNReal.ofReal ((Pi2 m n).card * K ^ k * Real.exp (2 * θ * t) *
            θ ^ (-((4 - alpha - α₀) * k))) :=
  HomogeneousEnvelope.homogeneous_envelope_diagrams hH hd (hPE d)

/-- **`P:envelope`** (TeX lines 2352-2433 at revision edf7085f (book 1.1.3)), `d = 1, 2`, under
`H:homog`, for random variables with the supplied input `MixedMoment`; the growth of `B_K` is
`HomogeneousEnvelope.envelope_growth` (whole). -/
theorem envelope_paper_l17 {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha α₀ Γ μ) (hd : d = 1 ∨ d = 2) :
    ∃ K : ℝ, 0 < K ∧ (∀ t : ℝ, 0 < t → ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
      {X : ℕ → Ω → ℝ} {u : Ω → ℝ}, MixedMoment d α₀ Γ P X u t →
        (∀ m n k : ℕ, m + n = 2 * k → 1 ≤ k → ∀ θ : ℝ, 0 < θ →
          ∫ ω, X m ω * X n ω ∂P ≤ (Pi2 m n).card * K ^ k * Real.exp (2 * θ * t) *
            θ ^ (-((4 - alpha - α₀) * k))) ∧
        ∫ ω, u ω ^ 2 ∂P ≤ BK K (4 - alpha - α₀) t) :=
  HomogeneousEnvelope.envelope_paper hH hd (hPE d)

end StratonovichHAMSecondMoment.EnvelopeFinal
