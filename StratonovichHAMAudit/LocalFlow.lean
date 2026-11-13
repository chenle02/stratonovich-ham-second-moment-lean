module
public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace StratonovichHAMAudit.LocalFlow

def noiseOrder (alpha : ℝ) : ℝ := (1-alpha)/2
def sourceSigma (alpha : ℝ) : ℝ := -(1+alpha)/4

theorem noise_order (alpha : ℝ) (ha0 : 0 < alpha) (ha1 : alpha ≤ 1) :
    0 ≤ noiseOrder alpha ∧ noiseOrder alpha < 1/2 ∧
    alpha-1 = -2*noiseOrder alpha := by
  unfold noiseOrder
  constructor
  · linarith
  constructor <;> linarith

theorem schur_row (q k b : ℝ) (_hq : 0 < q) (hk : 0 < k) :
    (q^(-b)*k^b)*k^(-b) = q^(-b) := by
  calc
    (q^(-b)*k^b)*k^(-b) = q^(-b)*(k^b*k^(-b)) := by ring
    _ = q^(-b) := by rw [← Real.rpow_add hk]; simp

theorem schur_column (q k b : ℝ) (hq : 0 < q) :
    (q^(-b)*k^b)*q^(-b) = k^b*q^(-2*b) := by
  calc
    (q^(-b)*k^b)*q^(-b) = k^b*(q^(-b)*q^(-b)) := by ring
    _ = k^b*q^(-2*b) := by rw [← Real.rpow_add hq]; congr 2; ring

theorem schur_rescale (k R b : ℝ) (hk : 0 < k) (hR : 0 < R) :
    (k/R)^(2*b)*R^(2*b) = k^(2*b) := by
  rw [Real.div_rpow hk.le hR.le]
  exact div_mul_cancel₀ _ (Real.rpow_pos_of_pos hR _).ne'

theorem source_overlap (alpha : ℝ) (ha : alpha < 1) :
    -(1:ℝ)/2 < sourceSigma alpha ∧ 2*sourceSigma alpha+alpha < 0 := by
  unfold sourceSigma
  constructor <;> linarith

theorem source_white_obstruction (s sigma : ℝ) (hleft : -s < sigma)
    (hright : s-1 < sigma) : ¬ sigma < -(1:ℝ)/2 := by
  intro h
  linarith

theorem source_tail_obstruction (alpha s sigma : ℝ) (hleft : -s < sigma)
    (hright : s-1 < sigma) (hHS : 2*sigma+alpha < 0) : alpha < 1 := by
  linarith

end StratonovichHAMAudit.LocalFlow
