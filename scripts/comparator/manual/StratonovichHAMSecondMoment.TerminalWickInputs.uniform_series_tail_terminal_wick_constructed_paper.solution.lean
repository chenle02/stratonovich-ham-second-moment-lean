namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWickInputs
-- Statement copied from the source (the printed type is only definitionally equal to the declaration's (an instance path differs: `SeminormedAddCommGroup.toIsTopologicalAddGroup` for `Lp`'s, or `WithLp.measurableSpace`); CheckFidelity requires Expr equality).
open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise
open TerminalWick FiniteWick WaveGreen HomogHypothesis
open Finset
/-- L8Completed.uniform_series_tail_terminal_wick_paper with nu = chainMeasure d n T x, hmass and hmeas replaced by MeanSquareCellContinuous (K eps delta) for eps, delta > 0; same other hypotheses and conclusions. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.TerminalWickInputs.uniform_series_tail_terminal_wick_constructed_paper {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (hd : d = 1 ∨ d = 2 ∨ d = 3)
    (T : ℝ) (hT : 0 < T) (x : Rd d) (W : ℝ → ℝ → Pt d T → Ω → ℝ)
    (K : ℝ → ℝ → Pt d T → Pt d T → ℝ)
    (hW : ∀ ε δ, CenteredGaussianField (W ε δ) (K ε δ) P)
    (hVfin : ∀ ε δ : ℝ, 0 < ε → 0 < δ → BddAbove (Set.range fun p => K ε δ p p))
    (hcell : ∀ ε δ : ℝ, 0 < ε → 0 < δ → MeanSquareCellContinuous (K ε δ))
    (hKpos : ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ p q, 0 ≤ K ε δ p q)
    (X : ℕ → Lp ℝ 2 P) (r B : ℝ) (hr : 1 < r)
    (hB : ∀ ε δ : ℝ, 0 < ε → 0 < δ →
      ∫ ω, ((∑' n, r ^ n • chainIntegral (fun n => chainMeasure d n T hT.le x) (hW ε δ) n :
        Lp ℝ 2 P) ω) ^ 2 ∂P ≤ B)
    (hX : ∀ n, Tendsto
      (fun p : ℝ × ℝ => chainIntegral (fun n => chainMeasure d n T hT.le x) (hW p.1 p.2) n)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (X n))) :
    (Summable fun n => ‖X n‖) ∧
      Tendsto (fun p : ℝ × ℝ =>
          ∑' n, chainIntegral (fun n => chainMeasure d n T hT.le x) (hW p.1 p.2) n)
        (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (∑' n, X n)) ∧
      (∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ n,
        ‖chainIntegral (fun n => chainMeasure d n T hT.le x) (hW ε δ) n‖ ≤
          Real.sqrt B * (r ^ n)⁻¹) ∧
      (∀ n, ‖X n‖ ≤ Real.sqrt B * (r ^ n)⁻¹) ∧
      (∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ N : ℕ,
        ‖∑' n, chainIntegral (fun n => chainMeasure d n T hT.le x) (hW ε δ) (n + (N + 1))‖ ≤
          Real.sqrt B * (r ^ (N + 1))⁻¹ / (1 - r⁻¹)) ∧
      (∀ N : ℕ, ‖∑' n, X (n + (N + 1))‖ ≤ Real.sqrt B * (r ^ (N + 1))⁻¹ / (1 - r⁻¹)) ∧
      (∀ ε δ : ℝ, 0 < ε → 0 < δ →
        Summable fun n => ‖chainIntegral (fun n => chainMeasure d n T hT.le x) (hW ε δ) n‖) := by
  bridge_revert_all
  bridge_rw
  intro d Ω _ P _ hd T hT x W K hW hVfin hcell hKpos X r B hr hB hX
  exact _root_.StratonovichHAMSecondMoment.TerminalWickInputs.uniform_series_tail_terminal_wick_constructed_paper P hd T hT x W K
    (fun ε δ => StratonovichHamSecondMomentLeanAuditBridge.FiniteWick.cgfToP (hW ε δ)) hVfin hcell hKpos X r B hr hB hX
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWickInputs
