namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalMeanDerivatives
-- Statement written from the source structure field `Good.bdd` (a structure field: the printed type round-trips only up to definitional equality).
open MeasureTheory Set Metric
open scoped ContDiff
/-- Structure field: for every n there is B with |D^n Phi q| <= B for all q. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.VariationalMeanDerivatives.Good.bdd {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {S : Set E} {Φ : E → F} (self : Good S Φ) :
    ∀ n : ℕ, ∃ B : ℝ, ∀ q, ‖iteratedFDeriv ℝ n Φ q‖ ≤ B := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.VariationalMeanDerivatives.Good.bdd
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalMeanDerivatives
