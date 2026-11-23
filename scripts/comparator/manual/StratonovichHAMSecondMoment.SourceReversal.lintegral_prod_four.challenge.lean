-- Printed type replaced by the source's statement in its scope (the printed one elaborates another instance path or universe order, so CheckFidelity's Expr equality fails).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceReversal
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal
universe u
open HomogHypothesis (Rd HomogCovariance)
open WaveGreen (waveGreen)
open FiniteWick (pairWeight)
open TerminalWick (Pt chainWeightReal)
open TerminalWickInputs (chainMeasure chainMeasureRaw chainMap chainPoint timeMeasure gap toPt OpenSimplex)
open WickInterface (kerA capSet capDom wickF wickJ pairTime covW posOrthant horizon gapTime)
open LowAlphaConvolution (gammaEps)
open DiagramModel (Pi2 openers covEps rev revPairing SameChain pred predVal incr pos twoSimplex)
open SourceInterface SourceWick
variable {d : ℕ}
variable {α : Type*} [MeasurableSpace α]
/-- Tonelli for four s-finite measures and measurable F : (alpha x beta) x (gamma x delta) -> [0,infinity]: the integral over (mua x mub) x (muc x mud) equals the integral of F((a,b),(c,d)) over (mua x muc) x (mub x mud). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceReversal.lintegral_prod_four {β γ δ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] (μa : Measure α) (μb : Measure β) (μc : Measure γ) (μd : Measure δ)
    [SFinite μa] [SFinite μb] [SFinite μc] [SFinite μd] {F : (α × β) × (γ × δ) → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ p, F p ∂((μa.prod μb).prod (μc.prod μd)) =
      ∫⁻ q, F ((q.1.1, q.2.1), (q.1.2, q.2.2)) ∂((μa.prod μc).prod (μb.prod μd)) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceReversal
