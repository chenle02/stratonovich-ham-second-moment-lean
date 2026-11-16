namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWickInputs
-- Statement copied from the source (the printed type is only definitionally equal to the declaration's (an instance path differs: `SeminormedAddCommGroup.toIsTopologicalAddGroup` for `Lp`'s, or `WithLp.measurableSpace`); CheckFidelity requires Expr equality).
open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise
open TerminalWick FiniteWick WaveGreen HomogHypothesis
open Finset
/-- For chain integrals over chainMeasure d n T x of fields W eps delta with bounded variance, cell continuity and K >= 0 (eps, delta > 0), r > 1, the bound B, the L^2 limits X_n and E|u^(eps,delta)(1)|^2 <= B_1: E|sum_n X_n|^2 <= B_1. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.TerminalWickInputs.uniform_series_tail_second_moment_constructed_paper {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (hd : d = 1 ∨ d = 2 ∨ d = 3)
    (T : ℝ) (hT : 0 < T) (x : Rd d) (W : ℝ → ℝ → Pt d T → Ω → ℝ)
    (K : ℝ → ℝ → Pt d T → Pt d T → ℝ)
    (hW : ∀ ε δ, CenteredGaussianField (W ε δ) (K ε δ) P)
    (hVfin : ∀ ε δ : ℝ, 0 < ε → 0 < δ → BddAbove (Set.range fun p => K ε δ p p))
    (hcell : ∀ ε δ : ℝ, 0 < ε → 0 < δ → MeanSquareCellContinuous (K ε δ))
    (hKpos : ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ p q, 0 ≤ K ε δ p q)
    (X : ℕ → Lp ℝ 2 P) (r B B₁ : ℝ) (hr : 1 < r)
    (hB : ∀ ε δ : ℝ, 0 < ε → 0 < δ →
      ∫ ω, ((∑' n, r ^ n • chainIntegral (fun n => chainMeasure d n T hT.le x) (hW ε δ) n :
        Lp ℝ 2 P) ω) ^ 2 ∂P ≤ B)
    (hX : ∀ n, Tendsto
      (fun p : ℝ × ℝ => chainIntegral (fun n => chainMeasure d n T hT.le x) (hW p.1 p.2) n)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (X n)))
    (hB₁ : ∀ ε δ : ℝ, 0 < ε → 0 < δ →
      ∫ ω, ((∑' n, chainIntegral (fun n => chainMeasure d n T hT.le x) (hW ε δ) n :
        Lp ℝ 2 P) ω) ^ 2 ∂P ≤ B₁) :
    ∫ ω, ((∑' n, X n : Lp ℝ 2 P) ω) ^ 2 ∂P ≤ B₁ := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWickInputs
