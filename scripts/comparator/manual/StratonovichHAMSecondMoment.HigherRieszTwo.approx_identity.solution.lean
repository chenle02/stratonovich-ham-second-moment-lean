namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HigherRieszTwo
open MeasureTheory Set Real Metric Filter
open scoped ENNReal NNReal Pointwise Topology
open HomogHypothesis (Rd HomogCovariance)
open VariationalMean (heatK)
open WaveGreen (waveGreen)
-- Statement copied from the source (the printed type unfolds `Rd j` to `WithLp 2 (Fin j → ℝ)`, the declaration keeps `Rd`).
-- The section variables of the source, as there:
variable {d : ℕ}
/-- For 0 < lam < j and x != 0 in R^j: for every eps > 0, y -> heatK eps (x - y) |y|^(-lam) is integrable, and its integral tends to |x|^(-lam) as eps -> 0+. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.HigherRieszTwo.approx_identity {j : ℕ} {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < j) {x : Rd j}
    (hx : x ≠ 0) :
    (∀ ε : ℝ, 0 < ε → Integrable fun y : Rd j => heatK ε (x - y) * ‖y‖ ^ (-lam)) ∧
      Tendsto (fun ε => ∫ y : Rd j, heatK ε (x - y) * ‖y‖ ^ (-lam)) (𝓝[>] 0)
        (𝓝 (‖x‖ ^ (-lam))) := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.HigherRieszTwo.approx_identity
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HigherRieszTwo
