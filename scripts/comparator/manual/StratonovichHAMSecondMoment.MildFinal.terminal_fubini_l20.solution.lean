-- Printed type replaced by the source's statement in its scope (the printed type drops the universe of the .{u} targets, so it does not elaborate to the claimed type).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildFinal
set_option autoImplicit false
universe u v
open MildInterface
/-- For every d, nothing supplied: TerminalFubiniTarget d: under H:homog, t > 0: W_a Y_m^b is in L^2 pointwise, mild-integrable, and Y_(m+1)^(b,a)(t,x) = mildInt (W_a Y_m^b) (TeX 2257-2260 with 4276-4285). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildFinal.terminal_fubini_l20 (d : ℕ) : TerminalFubiniTarget.{u} d := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto20 _root_.StratonovichHAMSecondMoment.MildFinal.terminal_fubini_l20)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildFinal
