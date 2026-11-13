/-
Refutation for the resolvent scaling with `R_α`, package theorem
`StratonovichHAMSecondMoment.SpectralMassIdentity.resolvent_eq_ralpha`
(`R_Γ(q) = q^{α-2} R_α`; the display of the proof of `L:spatial-fourier-bound`,
`notes/integrated_spatial_occupation.tex` lines 149-155 at a284420).

Wrong variant: the exponent `2 - α` in place of `α - 2`, same binders and
hypotheses.  Witness: `d = 1`, `μ` = Lebesgue measure on `ℝ¹` (degree `1`),
`α = 1`, `q = 2`.  The package gives `R_Γ(2) = R_α/2`, the variant
`R_Γ(2) = 2 R_α`; with `R_α = R_Γ(1) > 0` these are incompatible.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SpectralMassIdentity

set_option autoImplicit false

open MeasureTheory Set Module Real

namespace Refutations.SpectralMassIdentity.ExponentSign

open StratonovichHAMSecondMoment.HomogHypothesis StratonovichHAMSecondMoment.SpectralHomog
  StratonovichHAMSecondMoment.SpectralMassIdentity

theorem volume_homog : SpectralHomogeneous (volume : Measure (Rd 1)) 1 := by
  intro A _ c hc
  rw [Measure.addHaar_smul, finrank_euclideanSpace_fin, pow_one, abs_of_pos hc,
    Real.rpow_one]

theorem ralpha_pos : 0 < ralpha (volume : Measure (Rd 1)) 1 := by
  rw [← (resolvent_one_eq_ralpha volume_homog one_pos (by norm_num)).2]
  exact resolvent_pos (integrable_inv_one_add_sq volume_homog (by norm_num)) (NeZero.ne _) 1
    one_ne_zero

/-- The exponent `2 - α` in `R_Γ(q) = q^{2-α} R_α` is false. -/
theorem exponent_sign_refuted :
    ¬ (∀ (μ : Measure (Rd 1)) [IsLocallyFiniteMeasure μ] (alpha : ℝ),
        SpectralHomogeneous μ alpha → 0 < alpha → alpha < 2 → ∀ q : ℝ, 0 < q →
        resolvent μ q = q ^ (2 - alpha) * ralpha μ alpha) := by
  intro h
  have hv := h volume 1 volume_homog one_pos (by norm_num) 2 two_pos
  have hp := (resolvent_eq_ralpha volume_homog one_pos (by norm_num) 2 two_pos).2
  rw [hp] at hv
  norm_num at hv
  have hr := ralpha_pos
  linarith

/-- The package theorem at the witness: `R_Γ(2) = 2^{-1} R_α`. -/
theorem exponent_sign_contrast :
    resolvent (volume : Measure (Rd 1)) 2 = 2 ^ ((1 : ℝ) - 2) * ralpha (volume : Measure (Rd 1)) 1 :=
  (resolvent_eq_ralpha volume_homog one_pos (by norm_num) 2 two_pos).2

end Refutations.SpectralMassIdentity.ExponentSign
