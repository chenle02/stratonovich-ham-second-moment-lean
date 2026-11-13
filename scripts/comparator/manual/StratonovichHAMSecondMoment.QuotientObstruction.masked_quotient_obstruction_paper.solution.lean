namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.QuotientObstruction
open MeasureTheory Set Real Metric
open scoped ContDiff ENNReal Pointwise FourierTransform
open HomogHypothesis
-- Statement copied from the source (the printed type writes `ContDiff ℝ (↑⊤)` for the source's `ContDiff ℝ ∞` (`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`)).
/-- If 0 < a < 1, T > 0: HomogCovariance 2 1 a Gamma0 mu0, Gamma0 != 0, and some C^infinity compactly supported real zeta on R^2 has no real C with covW a Gamma0 (zeta F) <= C covW a Gamma0 F for all F with IsTest T F. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.QuotientObstruction.masked_quotient_obstruction_paper {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {T : ℝ}
    (hT : 0 < T) :
    HomogCovariance 2 1 a Gamma0 mu0 ∧ Gamma0 ≠ 0 ∧
      ∃ ζ : Rd 2 → ℝ, ContDiff ℝ ∞ ζ ∧ HasCompactSupport ζ ∧
        ¬ ∃ C : ℝ, ∀ F : ℝ → Rd 2 → ℝ, IsTest T F →
          covW a Gamma0 (fun t x => ζ x * F t x) ≤ C * covW a Gamma0 F := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.QuotientObstruction.masked_quotient_obstruction_paper
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.QuotientObstruction
