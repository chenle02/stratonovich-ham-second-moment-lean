-- Printed type with the printed `ContDiff ℝ (↑⊤)` written as the source's `ContDiff ℝ ∞` (`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`, scope `ContDiff`).
open scoped ContDiff in
/-- psi_j is C^infinity. -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.CameronProducts.lpPsi_contDiff :
    ∀ {d : ℕ} (j : ℕ),
      ContDiff ℝ (E := StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.Rd d) ∞
        (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronProducts.lpPsi j) := by
  sorry
