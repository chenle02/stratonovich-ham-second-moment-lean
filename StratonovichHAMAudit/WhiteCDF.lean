module
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace StratonovichHAMAudit.WhiteCDF

theorem cdf_square_bound (A b : ℝ)
    (h : ∀ z : ℝ, 0 ≤ b - 2 * z * A + z ^ 2 / 3) :
    3 * A ^ 2 ≤ b :=
by
  have hz := h (3 * A)
  nlinarith

theorem energy_upper (c A b : ℝ) (h : 3 * A ^ 2 ≤ b) :
    c * A - b / 2 ≤ c ^ 2 / 6 :=
by
  nlinarith [sq_nonneg (c - 3 * A)]

end StratonovichHAMAudit.WhiteCDF
