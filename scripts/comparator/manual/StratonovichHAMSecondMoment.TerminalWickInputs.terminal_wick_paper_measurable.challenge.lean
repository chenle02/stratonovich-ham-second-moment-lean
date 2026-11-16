namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWickInputs
-- Statement copied from the source (the printed type is only definitionally equal to the declaration's (an instance path differs: `SeminormedAddCommGroup.toIsTopologicalAddGroup` for `Lp`'s, or `WithLp.measurableSpace`); CheckFidelity requires Expr equality).
open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise
open TerminalWick FiniteWick WaveGreen HomogHypothesis
open Finset
variable {d : ℕ} {T : ℝ}
/-- d in {1,2,3}, T > 0, probability P, CenteredGaussianField W K P on [0,T] x R^d, V < inf, MeanSquareCellContinuous K, finite nu n with mass chainMass d n T and TimeAtomless nu: the nine conclusions of TerminalWick.terminal_wick_paper. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.TerminalWickInputs.terminal_wick_paper_measurable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) (T : ℝ) (hT : 0 < T)
    (W : Pt d T → Ω → ℝ) (K : Pt d T → Pt d T → ℝ) (hW : CenteredGaussianField W K P)
    (hVfin : BddAbove (Set.range fun p => K p p))
    (hcell : MeanSquareCellContinuous K)
    (ν : ∀ n : ℕ, Measure (Fin n → Pt d T)) [∀ n, IsFiniteMeasure (ν n)]
    (hmass : ∀ n, ν n univ = chainMass d n T)
    (hν : TimeAtomless ν) :
    (∀ n, Integrable (fun z : Fin n → Pt d T => prodL2 hW z) (ν n)) ∧
      ((chainIntegral ν hW 0 : Ω → ℝ) =ᵐ[P] fun _ => 1) ∧
      (∀ n, ‖chainIntegral ν hW n‖ ≤ Real.sqrt ((2 * n - 1).doubleFactorial) *
        (⨆ p, K p p) ^ ((n : ℝ) / 2) * (T ^ (2 * n) / (2 * n).factorial)) ∧
      (∀ m n, ∫ ω, chainIntegral ν hW m ω * chainIntegral ν hW n ω ∂P =
        ∑ D ∈ pairings (univ : Finset (Fin (m + n))), pairingIntegral ν K m n D) ∧
      (∀ m n (D : Fin (m + n) → Fin (m + n)),
        Integrable (fun q : (Fin m → Pt d T) × (Fin n → Pt d T) =>
          pairWeight (fun a b => K (Fin.append q.1 q.2 a) (Fin.append q.1 q.2 b)) univ D)
          ((ν m).prod (ν n))) ∧
      (∀ m n, Odd (m + n) → ∫ ω, chainIntegral ν hW m ω * chainIntegral ν hW n ω ∂P = 0) ∧
      ((∀ p q, 0 ≤ K p q) →
        (∀ m n (D : Fin (m + n) → Fin (m + n)), 0 ≤ pairingIntegral ν K m n D) ∧
        ∀ m n, 0 ≤ ∫ ω, chainIntegral ν hW m ω * chainIntegral ν hW n ω ∂P) ∧
      (∀ r : ℝ, Summable fun n => ‖r ^ n • chainIntegral ν hW n‖) ∧
      ((∀ p q, 0 ≤ K p q) → ∀ r : ℝ,
        UniformSeriesTail.TerminalWickInput P (fun n => chainIntegral ν hW n) r) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWickInputs
