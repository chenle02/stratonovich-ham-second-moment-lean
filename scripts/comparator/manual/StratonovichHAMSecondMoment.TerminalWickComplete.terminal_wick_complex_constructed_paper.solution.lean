namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWickComplete
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Set Filter Topology Finset
open scoped ComplexConjugate
open TerminalWick TerminalWickInputs FiniteWick HomogHypothesis
/-- Probability P (unused), d in {1,2,3}, T > 0, x, centered Gaussian field W with bounded variance and cell continuity: for complex r, sum r^n toC(Y n) converges absolutely in Lp C 2 P; E|partial sum|^2 = sum r^m conj(r)^n E[Y m Y n]; its limit. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.TerminalWickComplete.terminal_wick_complex_constructed_paper {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) (T : ℝ)
    (hT : 0 < T) (x : Rd d) (W : Pt d T → Ω → ℝ) (K : Pt d T → Pt d T → ℝ)
    (hW : CenteredGaussianField W K P) (hVfin : BddAbove (Set.range fun p => K p p))
    (hcell : MeanSquareCellContinuous K) :
    let ν : ∀ n : ℕ, Measure (Fin n → Pt d T) := fun n => chainMeasure d n T hT.le x
    (∀ r : ℂ, Summable (fun n => ‖r ^ n • toC (chainIntegral ν hW n)‖) ∧
      Summable (fun n => r ^ n • toC (chainIntegral ν hW n))) ∧
    (∀ (r : ℂ) (N : ℕ),
      ((∫ ω, ‖(∑ n ∈ range (N + 1), r ^ n • toC (chainIntegral ν hW n) : Lp ℂ 2 P) ω‖ ^ 2
        ∂P : ℝ) : ℂ) =
        ∑ m ∈ range (N + 1), ∑ n ∈ range (N + 1), r ^ m * conj r ^ n *
          ((∫ ω, chainIntegral ν hW m ω * chainIntegral ν hW n ω ∂P : ℝ) : ℂ)) ∧
    ∀ r : ℂ, Tendsto (fun N => ∑ m ∈ range N, ∑ n ∈ range N, r ^ m * conj r ^ n *
        ((∫ ω, chainIntegral ν hW m ω * chainIntegral ν hW n ω ∂P : ℝ) : ℂ)) atTop
      (𝓝 ((∫ ω, ‖(∑' n, r ^ n • toC (chainIntegral ν hW n) : Lp ℂ 2 P) ω‖ ^ 2 ∂P : ℝ) : ℂ)) := by
  bridge_revert_all
  bridge_rw
  intro Ω _ P _ d hd T hT x W K hW hVfin hcell
  exact _root_.StratonovichHAMSecondMoment.TerminalWickComplete.terminal_wick_complex_constructed_paper P d hd T hT x W K
    (StratonovichHamSecondMomentLeanAuditBridge.FiniteWick.cgfToP hW) hVfin hcell
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWickComplete
