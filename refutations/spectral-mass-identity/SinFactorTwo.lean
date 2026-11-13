/-
Refutation for `E:intro-spectral-mass` read as the resolvent identity, package
theorem `StratonovichHAMSecondMoment.SpectralMassIdentity.resolvent_one_eq_ralpha`
(`R_Γ(1) = απ μ(B_1)/(2 sin(πα/2))`; main TeX lines 526-532 and 850-860 at
a284420).

Wrong variant: the denominator `sin(πα/2)` in place of `2 sin(πα/2)`, same
binders and hypotheses.  Witness: `d = 1`, `μ` = Lebesgue measure on `ℝ¹`
(locally finite, homogeneous of degree `1`), `α = 1`.  The variant's right side
is twice the package's, so it would force `R_Γ(1) = 2 R_Γ(1)`, i.e.
`R_Γ(1) = 0`, while `R_Γ(1) > 0` (`SpectralHomog.resolvent_pos`, `μ ≠ 0`).
No junk-value reliance (`sin(π/2) = 1 ≠ 0`, `μ(B_1) < ∞`, integrability proved).
The contrast theorem applies the package theorem at the witness.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SpectralMassIdentity

set_option autoImplicit false

open MeasureTheory Set Module Real

namespace Refutations.SpectralMassIdentity

open StratonovichHAMSecondMoment.HomogHypothesis StratonovichHAMSecondMoment.SpectralHomog
  StratonovichHAMSecondMoment.SpectralMassIdentity

theorem volume_homog : SpectralHomogeneous (volume : Measure (Rd 1)) 1 := by
  intro A _ c hc
  rw [Measure.addHaar_smul, finrank_euclideanSpace_fin, pow_one, abs_of_pos hc,
    Real.rpow_one]

theorem volume_resolvent_pos : 0 < resolvent (volume : Measure (Rd 1)) 1 :=
  resolvent_pos (integrable_inv_one_add_sq volume_homog (by norm_num)) (NeZero.ne _) 1
    one_ne_zero

/-- The denominator `sin(πα/2)` (without the factor `2`) is false. -/
theorem sin_factor_two_refuted :
    ¬ (∀ (μ : Measure (Rd 1)) [IsLocallyFiniteMeasure μ] (alpha : ℝ),
        SpectralHomogeneous μ alpha → 0 < alpha → alpha < 2 →
        resolvent μ 1 =
          alpha * π * (μ (Metric.ball 0 1)).toReal / Real.sin (π * alpha / 2)) := by
  intro h
  have hv := h volume 1 volume_homog one_pos (by norm_num)
  have hp := (resolvent_one_eq_ralpha volume_homog one_pos (by norm_num)).2
  rw [ralpha] at hp
  have hs : Real.sin (π * 1 / 2) = 1 := by rw [mul_one]; exact Real.sin_pi_div_two
  rw [hs] at hv hp
  have hpos := volume_resolvent_pos
  linarith

/-- The package theorem at the witness: `R_Γ(1) = 1·π·μ(B_1)/(2 sin(π/2))`. -/
theorem sin_factor_two_contrast :
    resolvent (volume : Measure (Rd 1)) 1 =
      1 * π * ((volume : Measure (Rd 1)) (Metric.ball 0 1)).toReal /
        (2 * Real.sin (π * 1 / 2)) :=
  (resolvent_one_eq_ralpha volume_homog one_pos (by norm_num)).2

end Refutations.SpectralMassIdentity
