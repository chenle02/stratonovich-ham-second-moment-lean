module
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace StratonovichHAMAudit.OccupationForm

theorem potential_budget (A D N eps : ℝ) (heps : 0 < eps) :
    A*D*N+A*N^2 ≤ eps*D^2+(A+A^2/(4*eps))*N^2 := by
  have hden : 0 < 4*eps := by positivity
  have hid : eps*D^2+(A^2/(4*eps))*N^2-A*D*N
      = (2*eps*D-A*N)^2/(4*eps) := by
    field_simp
    ring
  have hn := div_nonneg (sq_nonneg (2*eps*D-A*N)) hden.le
  nlinarith

theorem shifted_coercivity (D N P C : ℝ)
    (hbound : P ≤ D^2/2+C*N^2) :
    (D^2+N^2)/2 ≤ D^2-P+(C+1)*N^2 := by
  nlinarith [sq_nonneg N]

end StratonovichHAMAudit.OccupationForm
