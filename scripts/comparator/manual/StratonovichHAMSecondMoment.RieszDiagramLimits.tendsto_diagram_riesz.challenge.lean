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
/-- Riesz diagrams converge, d = 1, every order: for c >= 0, 0 <= alpha < 1, 0 <= alpha0 < 1, D in Pi2 m n, t >= 0, the M4 diagram with covEps Gamma eps, Gamma = c|y|^(-alpha) dy, tends as eps -> 0+ to the density diagram. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.RieszDiagramLimits.tendsto_diagram_riesz {c α α₀ : ℝ} (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα : α < 1)
    (h0 : 0 ≤ α₀) (h1 : α₀ < 1) {m n : ℕ} {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n)
    {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun ε => diagram (waveGreen 1)
        (covEps ((volume : Measure (Rd 1)).withDensity (riesz c α)) ε) α₀ m n D t)
      (𝓝[>] 0) (𝓝 (diagram (waveGreen 1) (riesz c α) α₀ m n D t)) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszDiagramLimits
