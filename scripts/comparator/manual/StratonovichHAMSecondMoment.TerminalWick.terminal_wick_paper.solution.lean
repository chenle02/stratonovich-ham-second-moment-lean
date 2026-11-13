namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWick
open MeasureTheory Set
open scoped ENNReal
open WaveGreen
open FiniteWick Finset Filter Topology HomogHypothesis
-- Statement copied from the source (the printed type elaborates the `Lp` coercion's topological-group instance through `SeminormedAddCommGroup.toIsTopologicalAddGroup`, the declaration through `MeasureTheory.Lp._proof_4`).
/-- For d in {1,2,3}, T > 0, a CenteredGaussianField on [0,T] x R^d, sup K(p,p) finite, finite nu n of mass chainMass d n T, supplied hmeas, measurable K: Y_n exist, Y_0 = 1, the majorant, the Wick formula, odd case, positivity, real-r series, TerminalWickInput. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.TerminalWick.terminal_wick_paper {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) (T : ℝ) (hT : 0 < T)
    (W : Pt d T → Ω → ℝ) (K : Pt d T → Pt d T → ℝ) (hW : CenteredGaussianField W K P)
    (hVfin : BddAbove (Set.range fun p => K p p))
    (_hcell : MeanSquareCellContinuous K)
    (ν : ∀ n : ℕ, Measure (Fin n → Pt d T)) [∀ n, IsFiniteMeasure (ν n)]
    (hmass : ∀ n, ν n univ = chainMass d n T)
    (hmeas : ∀ n, AEStronglyMeasurable (fun z : Fin n → Pt d T => prodL2 hW z) (ν n))
    (hK : Measurable fun q : Pt d T × Pt d T => K q.1 q.2) :
    (∀ n, Integrable (fun z : Fin n → Pt d T => prodL2 hW z) (ν n)) ∧
      ((chainIntegral ν hW 0 : Ω → ℝ) =ᵐ[P] fun _ => 1) ∧
      (∀ n, ‖chainIntegral ν hW n‖ ≤ Real.sqrt ((2 * n - 1).doubleFactorial) *
        (⨆ p, K p p) ^ ((n : ℝ) / 2) * (T ^ (2 * n) / (2 * n).factorial)) ∧
      (∀ m n, ∫ ω, chainIntegral ν hW m ω * chainIntegral ν hW n ω ∂P =
        ∑ D ∈ pairings (univ : Finset (Fin (m + n))), pairingIntegral ν K m n D) ∧
      (∀ m n (D : Fin (m + n) → Fin (m + n)), Integrable (fun q : (Fin m → Pt d T) × (Fin n → Pt d T) =>
        pairWeight (fun a b => K (Fin.append q.1 q.2 a) (Fin.append q.1 q.2 b)) univ D)
        ((ν m).prod (ν n))) ∧
      (∀ m n, Odd (m + n) → ∫ ω, chainIntegral ν hW m ω * chainIntegral ν hW n ω ∂P = 0) ∧
      ((∀ p q, 0 ≤ K p q) →
        (∀ m n (D : Fin (m + n) → Fin (m + n)), 0 ≤ pairingIntegral ν K m n D) ∧
        ∀ m n, 0 ≤ ∫ ω, chainIntegral ν hW m ω * chainIntegral ν hW n ω ∂P) ∧
      (∀ r : ℝ, Summable fun n => ‖r ^ n • chainIntegral ν hW n‖) ∧
      ((∀ p q, 0 ≤ K p q) → ∀ r : ℝ,
        UniformSeriesTail.TerminalWickInput P (fun n => chainIntegral ν hW n) r) := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.TerminalWick.terminal_wick_paper
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWick
