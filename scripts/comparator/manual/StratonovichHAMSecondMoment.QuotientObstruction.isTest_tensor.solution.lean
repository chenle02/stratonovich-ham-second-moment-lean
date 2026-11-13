namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.QuotientObstruction
open MeasureTheory Set Real Metric
open scoped ContDiff ENNReal Pointwise FourierTransform
open HomogHypothesis
-- Statement copied from the source (the printed type writes `ContDiff ℝ (↑⊤)` for the source's `ContDiff ℝ ∞` (`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`)).
/-- If tau : R -> R is C^infinity with compact support, tau(t) != 0 only for t in (0,T), and g : R^d -> R is C^infinity with compact support: IsTest T (t,x -> tau(t) g(x)). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.QuotientObstruction.isTest_tensor {d : ℕ} {T : ℝ} {τ : ℝ → ℝ} {g : Rd d → ℝ} (hτ : ContDiff ℝ ∞ τ)
    (hτc : HasCompactSupport τ) (hτs : ∀ t, τ t ≠ 0 → t ∈ Ioo 0 T) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) : IsTest T (fun t x => τ t * g x) := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.QuotientObstruction.isTest_tensor
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.QuotientObstruction
