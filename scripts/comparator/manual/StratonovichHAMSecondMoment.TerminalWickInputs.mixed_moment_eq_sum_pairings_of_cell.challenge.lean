namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWickInputs
-- Statement copied from the source (the printed type is only definitionally equal to the declaration's (an instance path differs: `SeminormedAddCommGroup.toIsTopologicalAddGroup` for `Lp`'s, or `WithLp.measurableSpace`); CheckFidelity requires Expr equality).
open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise
open TerminalWick FiniteWick WaveGreen HomogHypothesis
open Finset
variable {d : ℕ} {T : ℝ}
/-- For CenteredGaussianField W K P, MeanSquareCellContinuous K, finite chain measures nu with TimeAtomless nu, 0 <= V with K x x <= V, and m, n: E[Y_m Y_n] = sum over pairings D of pairingIntegral nu K m n D. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.TerminalWickInputs.mixed_moment_eq_sum_pairings_of_cell {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {W : Pt d T → Ω → ℝ} {K : Pt d T → Pt d T → ℝ}
    (hW : CenteredGaussianField W K P) (hcell : MeanSquareCellContinuous K)
    (ν : ∀ n : ℕ, Measure (Fin n → Pt d T)) [∀ n, IsFiniteMeasure (ν n)]
    (hν : TimeAtomless ν) (V : ℝ) (hV0 : 0 ≤ V) (hV : ∀ x, K x x ≤ V) (m n : ℕ) :
    ∫ ω, chainIntegral ν hW m ω * chainIntegral ν hW n ω ∂P =
      ∑ D ∈ pairings (Finset.univ : Finset (Fin (m + n))), pairingIntegral ν K m n D := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWickInputs
