namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.H1Density
open MeasureTheory Filter Topology
open scoped ENNReal Pointwise ContDiff
open HomogHypothesis (Rd)
open WeakSobolev
open VariationalFloor (grad bumpN)
-- Statement copied from the source (the printed type writes `ContDiff ℝ (↑⊤)` for the source's `ContDiff ℝ ∞` (`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`)).
-- The section variables used, written as binders: {d : ℕ}.
/-- h : R^d -> R smooth with h and grad h in L^2: norm(cutoff n * h - h)_2 -> 0 and norm(grad (cutoff n * h) - grad h)_2 -> 0. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.H1Density.tendsto_cutoff_test {d : ℕ} {h : Rd d → ℝ} (hh : ContDiff ℝ ∞ h) (hL : MemLp h 2 volume)
    (hG : MemLp (grad h) 2 volume) :
    Tendsto (fun n => eLpNorm (fun x => cutoff n x * h x - h x) 2 volume) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (fun x => grad (fun y => cutoff n y * h y) x - grad h x) 2
        volume) atTop (𝓝 0) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.H1Density
