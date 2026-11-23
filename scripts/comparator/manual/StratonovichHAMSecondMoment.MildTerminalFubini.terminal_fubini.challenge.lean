-- Printed type replaced by the source's statement in its scope (the printed type drops the universe of the .{u} targets, so it does not elaborate to the claimed type).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildTerminalFubini
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal Real Nat
universe u
open HomogHypothesis (Rd HomogCovariance)
open WaveGreen (waveGreen)
open FiniteWick (CenteredGaussianField)
open TerminalWick (Pt prodL2 chainWeightReal)
open TerminalWickInputs
open SourceInterface
open MildInterface
variable {d : ℕ}
/-- For every d, nothing supplied: TerminalFubiniTarget d: under H:homog, any source field, t > 0, x, widths b (m vertices), a: W_a Y_m^b in L^2 at every point, mild-integrable, and Y_(m+1)^(snoc b a)(t,x) = mildInt (W_a Y_m^b) t x. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildTerminalFubini.terminal_fubini (d : ℕ) : TerminalFubiniTarget.{u} d := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildTerminalFubini
