-- Printed type replaced by the source's statement in its scope (the printed type drops the universe of the .{u} targets, so it does not elaborate to the claimed type).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildFinal
set_option autoImplicit false
universe u v
open MildInterface
/-- For every d, nothing supplied: GreenWidthMildTarget d: under H:homog, t > 0, width a: the p_eta*G-smoothed mild integrals of W_a X_(n-1) (n >= 1) and of W_a u converge in L^2 to I_(n,a)(t,x), I_a(t,x) as eta -> 0+ (Step 4, TeX 2268-2287). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildFinal.green_width_mild_l20 (d : ℕ) : GreenWidthMildTarget.{u} d := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto20 _root_.StratonovichHAMSecondMoment.MildFinal.green_width_mild_l20)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildFinal
