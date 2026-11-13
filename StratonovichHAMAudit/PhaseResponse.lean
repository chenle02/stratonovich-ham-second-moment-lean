module
public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace StratonovichHAMAudit.PhaseResponse

def phaseIndex (alpha a : ℝ) : ℝ := 1-(alpha+a)/4

theorem rough_phase_choice (alpha a : ℝ) (hpos : 0 < alpha+a) (hsub : alpha+a < 2) :
    1/2 < phaseIndex alpha a ∧ phaseIndex alpha a < 1 ∧
    2*phaseIndex alpha a+alpha+a < 3 ∧
    2*phaseIndex alpha a+alpha+a-4 < -1 ∧ alpha+a-3 < -1 := by
  unfold phaseIndex
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem balanced_phase (alpha a : ℝ) (hsub : alpha+a < 2) :
    2*((1:ℝ)/2)+alpha+a < 3 ∧ alpha+a-3 < -1 := by
  constructor <;> linarith

theorem energy_boundary (alpha a : ℝ) :
    2*(1:ℝ)+alpha+a < 3 ↔ alpha+a < 1 := by
  constructor <;> intro h <;> linarith

theorem four_component_gram (r1 r2 k1 k2 : ℝ) :
    (Real.sin r1*Real.cos k1)*(Real.sin r2*Real.cos k2) +
    (Real.sin r1*Real.sin k1)*(Real.sin r2*Real.sin k2) +
    (Real.cos r1*Real.cos k1)*(Real.cos r2*Real.cos k2) +
    (Real.cos r1*Real.sin k1)*(Real.cos r2*Real.sin k2) =
      Real.cos (r1-r2)*Real.cos (k1-k2) := by
  rw [Real.cos_sub, Real.cos_sub]
  ring

theorem two_frequency_average (x y : ℝ) :
    Real.cos x*Real.cos y = (Real.cos (x-y)+Real.cos (x+y))/2 := by
  rw [Real.cos_sub, Real.cos_add]
  ring

theorem frequency_window (J A B t r a : ℝ) (hA : 0 < A) (_hB : 0 ≤ B)
    (ht : 0 < t) (hr : 0 < r) (hcut : 2*B/(A*t) ≤ r)
    (herr : |J-A*t*r^(a-1)| ≤ B*r^(a-2)) :
    (A*t/2)*r^(a-1) ≤ J ∧ J ≤ (3*A*t/2)*r^(a-1) := by
  have hAt : 0 < A*t := mul_pos hA ht
  have hbudget : B ≤ A*t*r/2 := by
    have h := (div_le_iff₀ hAt).mp hcut
    nlinarith
  have hp : 0 < r^(a-1) := Real.rpow_pos_of_pos hr _
  have hexp : r^(a-2) = r^(a-1)/r := by
    have he : a-2 = (a-1)-1 := by ring
    rw [he, Real.rpow_sub_one hr.ne']
  have hscaled := mul_le_mul_of_nonneg_right hbudget hp.le
  have herror : B*r^(a-2) ≤ (A*t/2)*r^(a-1) := by
    rw [hexp, ← mul_div_assoc]
    apply (div_le_iff₀ hr).2
    nlinarith
  rcases abs_le.mp herr with ⟨hl, hu⟩
  constructor <;> nlinarith

end StratonovichHAMAudit.PhaseResponse
