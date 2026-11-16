namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWickRegularization
-- Statement copied from the source (the printed type is only definitionally equal to the declaration's (an instance path differs: `SeminormedAddCommGroup.toIsTopologicalAddGroup` for `Lp`'s, or `WithLp.measurableSpace`); CheckFidelity requires Expr equality).
open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal Pointwise BoundedContinuousFunction
open TerminalWick TerminalWickInputs FiniteWick WaveGreen HomogHypothesis
variable {d : ℕ} {T : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : Pt d T → Ω → ℝ} {K : Pt d T → Pt d T → ℝ}
/-- Same hypotheses, m, n: E[Y_m^(eta1) Y_n^(eta2)] -> E[Y_m Y_n] as (eta1, eta2) -> (0+, 0+). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.TerminalWickRegularization.tendsto_mixed_moment_reg (hW : CenteredGaussianField W K P)
    (hVfin : BddAbove (Set.range fun p => K p p)) (hcell : MeanSquareCellContinuous K)
    (hT : 0 ≤ T) (x : Rd d) (m n : ℕ) :
    Tendsto (fun p : ℝ × ℝ =>
        ∫ ω, chainIntegral (fun n => chainMeasureReg d n T hT x p.1) hW m ω *
          chainIntegral (fun n => chainMeasureReg d n T hT x p.2) hW n ω ∂P)
      (𝓝[>] 0 ×ˢ 𝓝[>] 0)
      (𝓝 (∫ ω, chainIntegral (fun n => chainMeasure d n T hT x) hW m ω *
        chainIntegral (fun n => chainMeasure d n T hT x) hW n ω ∂P)) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWickRegularization
