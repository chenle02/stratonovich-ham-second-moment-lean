namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWickRegularization
-- Statement copied from the source (the printed type is only definitionally equal to the declaration's (an instance path differs: `SeminormedAddCommGroup.toIsTopologicalAddGroup` for `Lp`'s, or `WithLp.measurableSpace`); CheckFidelity requires Expr equality).
open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal Pointwise BoundedContinuousFunction
open TerminalWick TerminalWickInputs FiniteWick WaveGreen HomogHypothesis
/-- d in {1,2,3}, T > 0, x, probability P, CenteredGaussianField W K P on [0,T] x R^d, V < inf, MeanSquareCellContinuous K: same masses; weak convergence; Y_n^eta -> Y_n in L^2; two-width mixed moments converge (eta -> 0+). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.TerminalWickRegularization.terminal_wick_regularization_paper {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) (T : ℝ) (hT : 0 < T)
    (x : Rd d) (W : Pt d T → Ω → ℝ) (K : Pt d T → Pt d T → ℝ)
    (hW : CenteredGaussianField W K P) (hVfin : BddAbove (Set.range fun p => K p p))
    (hcell : MeanSquareCellContinuous K) :
    (∀ (η : ℝ) (n : ℕ), chainMeasureReg d n T hT.le x η univ = chainMass d n T) ∧
      (∀ (n : ℕ) (f : (Fin n → Pt d T) →ᵇ ℝ),
        Tendsto (fun η => ∫ z, f z ∂(chainMeasureReg d n T hT.le x η)) (𝓝[>] 0)
          (𝓝 (∫ z, f z ∂(chainMeasure d n T hT.le x)))) ∧
      (∀ n : ℕ, Tendsto (fun η => chainIntegral (fun n => chainMeasureReg d n T hT.le x η) hW n)
        (𝓝[>] 0) (𝓝 (chainIntegral (fun n => chainMeasure d n T hT.le x) hW n))) ∧
      (∀ m n : ℕ, Tendsto (fun p : ℝ × ℝ =>
          ∫ ω, chainIntegral (fun n => chainMeasureReg d n T hT.le x p.1) hW m ω *
            chainIntegral (fun n => chainMeasureReg d n T hT.le x p.2) hW n ω ∂P)
        (𝓝[>] 0 ×ˢ 𝓝[>] 0)
        (𝓝 (∫ ω, chainIntegral (fun n => chainMeasure d n T hT.le x) hW m ω *
          chainIntegral (fun n => chainMeasure d n T hT.le x) hW n ω ∂P))) := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.TerminalWickRegularization.terminal_wick_regularization_paper
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWickRegularization
