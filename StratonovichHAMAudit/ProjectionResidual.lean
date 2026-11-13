module
public import Mathlib.Tactic
public import Mathlib.Analysis.Real.Sqrt
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace StratonovichHAMAudit.ProjectionResidual

def actualMeanCoeff : ℝ := 20000 / 1932951
def projectedLower : ℝ := 101 / (3200 * Real.sqrt 2)

theorem projection_gap : actualMeanCoeff + 1/96 < projectedLower := by
  have hs : 0 < Real.sqrt (2:ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hs2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hslt : Real.sqrt (2:ℝ) < 3/2 := by nlinarith
  have hp : (1:ℝ)/48 < projectedLower := by
    unfold projectedLower
    apply (lt_div_iff₀ (show (0:ℝ) < 3200 * Real.sqrt 2 by positivity)).2
    nlinarith
  have ha : actualMeanCoeff < (1:ℝ)/96 := by norm_num [actualMeanCoeff]
  linarith

theorem tilted_gap (p q : ℝ) (hp : projectedLower ≤ p) :
    actualMeanCoeff + (q-1)*p + 1/96 < q*p := by
  have h := projection_gap
  nlinarith

end StratonovichHAMAudit.ProjectionResidual
