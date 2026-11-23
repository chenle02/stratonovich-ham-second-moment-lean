-- Printed type replaced by the source's statement in its scope (the printed type drops the universe of the .{u} targets, so it does not elaborate to the claimed type).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildFinal
set_option autoImplicit false
universe u v
open MildInterface
/-- For every d, nothing supplied: PolyMemTarget d: under H:homog, every source field, t >= 0, x, n: every Y_n^a(t,x) and X_n(t,x) lies in PolyLE hW n (P_(<=n); TeX 2181-2185). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildFinal.poly_mem_l20 (d : ℕ) : PolyMemTarget.{u} d := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto20 _root_.StratonovichHAMSecondMoment.MildFinal.poly_mem_l20)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildFinal
