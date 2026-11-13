module
import StratonovichHAMAudit.WhiteCDF
set_option autoImplicit false
set_option pp.all true
#check @sq_nonneg
#check @StratonovichHAMAudit.WhiteCDF.cdf_square_bound
#print axioms StratonovichHAMAudit.WhiteCDF.cdf_square_bound
#check @StratonovichHAMAudit.WhiteCDF.energy_upper
#print axioms StratonovichHAMAudit.WhiteCDF.energy_upper
private theorem actual_energy_consumer (c A b : ℝ)
    (h : ∀ z : ℝ, 0 ≤ b - 2 * z * A + z ^ 2 / 3) :
    c * A - b / 2 ≤ c ^ 2 / 6 := by
  exact StratonovichHAMAudit.WhiteCDF.energy_upper c A b
    (StratonovichHAMAudit.WhiteCDF.cdf_square_bound A b h)
#check @actual_energy_consumer
#print axioms actual_energy_consumer
example : (1 : ℝ) * (1 / 3) - (1 / 3) / 2 ≤ 1 ^ 2 / 6 := by
  apply actual_energy_consumer
  intro z
  nlinarith [sq_nonneg (z - 1)]
example : 3 * ((1 : ℝ) / 3) ^ 2 ≤ (1 : ℝ) / 3 := by
  apply StratonovichHAMAudit.WhiteCDF.cdf_square_bound
  intro z
  nlinarith [sq_nonneg (z - 1)]
