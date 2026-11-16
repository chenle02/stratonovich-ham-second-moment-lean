namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
open MeasureTheory Set Real Filter
open scoped ENNReal ComplexConjugate
open HomogHypothesis (Rd)
variable {d : ℕ}
variable {ν : Measure (Rd d)}
/-- For finite nu, psi in L^2(nu), f, g in L^2(Lebesgue) and F a.e. strongly measurable on R^d x R^d with |F p| <= |psi p.2| |f(p.1 - p.2)| |g p.1|: F is Lebesgue x nu-integrable. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FockColumnBound.integrable_of_triple_bound [IsFiniteMeasure ν] (ψ : Lp ℂ 2 ν)
    (f g : Lp ℂ 2 (volume : Measure (Rd d))) (F : Rd d × Rd d → ℂ)
    (hF : AEStronglyMeasurable F ((volume : Measure (Rd d)).prod ν))
    (hb : ∀ p, ‖F p‖ ≤ ‖ψ p.2‖ * ‖f (p.1 - p.2)‖ * ‖g p.1‖) :
    Integrable F ((volume : Measure (Rd d)).prod ν) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
