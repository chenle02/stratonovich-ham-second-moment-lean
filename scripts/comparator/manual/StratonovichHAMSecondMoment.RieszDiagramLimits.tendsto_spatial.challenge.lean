-- Printed type replaced by the source's statement in its scope (the printed one elaborates another instance path for the measurable space of `Rd 1`, so CheckFidelity's Expr equality fails).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszDiagramLimits
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal Nat
open HomogHypothesis (Rd)
open WaveGreen (waveGreen)
open HigherRieszTwo (riesz)
open DiagramModel
open TwoSimplexTime (Zc)
open D1Spatial (Ksp)
/-- For c >= 0, 0 <= alpha < 1, every m, D, h with the density spatial part finite: the spatial part with p_eps * Gamma converges as eps -> 0+ to the spatial part with c|.|^(-alpha) (dominated convergence over the Green box). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.RieszDiagramLimits.tendsto_spatial {c α : ℝ} (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα : α < 1)
    (m : ℕ) {N : ℕ} (D : Fin N → Fin N) (h : Fin N → ℝ)
    (hfin : spatial (waveGreen 1) (riesz c α) m D h ≠ ⊤) :
    Tendsto (fun ε => spatial (waveGreen 1)
        (covEps ((volume : Measure (Rd 1)).withDensity (riesz c α)) ε) m D h)
      (𝓝[>] 0) (𝓝 (spatial (waveGreen 1) (riesz c α) m D h)) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszDiagramLimits
