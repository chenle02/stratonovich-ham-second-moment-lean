namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.L8Completed
open MeasureTheory
-- Statement copied from the source (the printed type is only definitionally equal to the declaration's; the statement has the `Lp` coercions of the `TerminalWick` and `UniformSeriesTail` statements copied for that reason).
-- The section variables used, written as binders: {d : ℕ}.
/-- L:uniform-series-tail with its L:terminal-wick input discharged: for the chain integrals Y_n of centered Gaussian fields with nonnegative covariance (per eps, delta), the conclusions of uniform_series_tail_paper hold; hB, hX, r > 1 and the terminal-wick hypotheses remain supplied. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.L8Completed.uniform_series_tail_terminal_wick_paper {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hd : d = 1 ∨ d = 2 ∨ d = 3) (T : ℝ)
    (hT : 0 < T) (W : ℝ → ℝ → TerminalWick.Pt d T → Ω → ℝ)
    (K : ℝ → ℝ → TerminalWick.Pt d T → TerminalWick.Pt d T → ℝ)
    (hW : ∀ ε δ, FiniteWick.CenteredGaussianField (W ε δ) (K ε δ) P)
    (hVfin : ∀ ε δ : ℝ, 0 < ε → 0 < δ → BddAbove (Set.range fun p => K ε δ p p))
    (ν : ℝ → ℝ → ∀ n : ℕ, Measure (Fin n → TerminalWick.Pt d T))
    [∀ ε δ n, IsFiniteMeasure (ν ε δ n)]
    (hmass : ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ n, ν ε δ n Set.univ = TerminalWick.chainMass d n T)
    (hmeas : ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ n,
      AEStronglyMeasurable (fun z : Fin n → TerminalWick.Pt d T => TerminalWick.prodL2 (hW ε δ) z)
        (ν ε δ n))
    (hKpos : ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ p q, 0 ≤ K ε δ p q)
    (X : ℕ → Lp ℝ 2 P) (r B : ℝ) (hr : 1 < r)
    (hB : ∀ ε δ : ℝ, 0 < ε → 0 < δ →
      ∫ ω, ((∑' n, r ^ n • TerminalWick.chainIntegral (ν ε δ) (hW ε δ) n : Lp ℝ 2 P) ω) ^ 2
        ∂P ≤ B)
    (hX : ∀ n, Filter.Tendsto
      (fun p : ℝ × ℝ => TerminalWick.chainIntegral (ν p.1 p.2) (hW p.1 p.2) n)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0) ×ˢ nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (X n))) :
    (Summable fun n => ‖X n‖) ∧
      Filter.Tendsto (fun p : ℝ × ℝ => ∑' n, TerminalWick.chainIntegral (ν p.1 p.2) (hW p.1 p.2) n)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0) ×ˢ nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (∑' n, X n)) ∧
      (∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ n,
        ‖TerminalWick.chainIntegral (ν ε δ) (hW ε δ) n‖ ≤ Real.sqrt B * (r ^ n)⁻¹) ∧
      (∀ n, ‖X n‖ ≤ Real.sqrt B * (r ^ n)⁻¹) ∧
      (∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ N : ℕ,
        ‖∑' n, TerminalWick.chainIntegral (ν ε δ) (hW ε δ) (n + (N + 1))‖ ≤
          Real.sqrt B * (r ^ (N + 1))⁻¹ / (1 - r⁻¹)) ∧
      (∀ N : ℕ, ‖∑' n, X (n + (N + 1))‖ ≤
        Real.sqrt B * (r ^ (N + 1))⁻¹ / (1 - r⁻¹)) ∧
      (∀ ε δ : ℝ, 0 < ε → 0 < δ →
        Summable fun n => ‖TerminalWick.chainIntegral (ν ε δ) (hW ε δ) n‖) := by
  rw [StratonovichHamSecondMomentLeanAuditBridge.TerminalWick.chainMass_eq] at hmass
  exact _root_.StratonovichHAMSecondMoment.L8Completed.uniform_series_tail_terminal_wick_paper P hd T hT W K
    (fun ε δ => StratonovichHamSecondMomentLeanAuditBridge.FiniteWick.cgfToP (hW ε δ)) hVfin ν hmass hmeas
    hKpos X r B hr hB hX
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.L8Completed
