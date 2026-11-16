namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ClassOBridge
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Set Real Filter Topology
open scoped ENNReal
open HomogHypothesis (Rd HomogCovariance)
variable {d : ℕ}
variable {E : Type*} [NormedAddCommGroup E]
/-- For a real complete normed space E, a finite measure nu on R and an a.e.-strongly measurable F : R -> L^2(R^d; E): there is a strongly measurable G on R x R^d with G(s, .) = F s a.e. for nu-a.e. s. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.ClassOBridge.exists_joint [NormedSpace ℝ E] [CompleteSpace E] {ν : Measure ℝ} [IsFiniteMeasure ν]
    {F : ℝ → Lp E 2 (volume : Measure (Rd d))} (hF : AEStronglyMeasurable F ν) :
    ∃ G : ℝ × Rd d → E, StronglyMeasurable G ∧
      ∀ᵐ s ∂ν, (fun x => G (s, x)) =ᵐ[volume] (F s : Rd d → E) := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.ClassOBridge.exists_joint
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ClassOBridge
