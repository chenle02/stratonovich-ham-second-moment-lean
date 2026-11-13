module
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace StratonovichHAMAudit.AllAlphaMoment

theorem moment_lower (a D x y : ℝ) (ha : 0 < a) (hD : 0 < D)
    (hmean : x + y = a) (hcs : x^2 ≤ D*y/2) :
    2*a^2/(D+4*a) ≤ y := by
  have hden : 0 < D+4*a := by positivity
  apply (div_le_iff₀ hden).2
  have hx : x = a-y := by linarith
  rw [hx] at hcs
  nlinarith [sq_nonneg y]

theorem rational_gap (a D : ℝ) (ha : 0 < a) (hD : 0 < D) :
    a^2/(D*(D+4*a))-a^2/(2*D*(D+2*a))
      =a^2/(2*(D+4*a)*(D+2*a)) ∧
    0 < a^2/(2*(D+4*a)*(D+2*a)) := by
  constructor
  · have hD0 : D ≠ 0 := ne_of_gt hD
    have hfour : D+4*a ≠ 0 := ne_of_gt (by positivity)
    have htwo : D+2*a ≠ 0 := ne_of_gt (by positivity)
    field_simp [hD0,hfour,htwo]
    ring
  · positivity

end StratonovichHAMAudit.AllAlphaMoment
