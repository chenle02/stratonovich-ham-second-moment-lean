module
public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace StratonovichHAMAudit.DirectEvent

def kappa (alpha a : ℝ) : ℝ := (4-alpha-a)/(3-alpha)
def delta (T alpha a : ℝ) : ℝ := T ^ (-kappa alpha a)
def radius (T alpha a : ℝ) : ℝ := T * delta T alpha a

theorem kappa_gt_one (alpha a : ℝ) (ha : a < 1) (halpha : alpha < 3) :
    1 < kappa alpha a := by
  unfold kappa
  apply (lt_div_iff₀ (by linarith : (0:ℝ) < 3-alpha)).2
  linarith

theorem physical_scale (T alpha a : ℝ) (hT : 0 < T) (halpha : alpha < 3) :
    radius T alpha a = T ^ ((a-1)/(3-alpha)) := by
  have hd : 3-alpha ≠ 0 := by linarith
  unfold radius delta
  calc
    T * T ^ (-kappa alpha a) = T ^ ((1:ℝ)-kappa alpha a) := by
      rw [sub_eq_add_neg, Real.rpow_add hT]
      norm_num
    _ = _ := by
      congr 1
      unfold kappa
      field_simp [hd]
      ring

theorem noise_scale (T alpha a : ℝ) (hT : 0 < T) (halpha : alpha < 3) :
    T ^ (-a/2) * (radius T alpha a) ^ (2-alpha/2) = Real.sqrt (delta T alpha a) := by
  have hd : 3-alpha ≠ 0 := by linarith
  rw [physical_scale T alpha a hT halpha]
  unfold delta
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hT.le, ← Real.rpow_mul hT.le,
    ← Real.rpow_add hT]
  congr 1
  unfold kappa
  field_simp [hd]
  ring

theorem vertex_scale (T alpha a : ℝ) (hT : 0 < T) (halpha : alpha < 3) :
    T ^ (1-a/2) * (radius T alpha a) ^ (1-alpha/2) =
      (delta T alpha a) ^ (-(1:ℝ)/2) := by
  have hd : 3-alpha ≠ 0 := by linarith
  rw [physical_scale T alpha a hT halpha]
  unfold delta
  rw [← Real.rpow_mul hT.le, ← Real.rpow_mul hT.le, ← Real.rpow_add hT]
  congr 1
  unfold kappa
  field_simp [hd]
  ring

def gauge (w : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1,0;w,1]
def drift : Matrix (Fin 2) (Fin 2) ℝ := !![0,1;1,0]

theorem gauge_inverse (w : ℝ) : gauge (-w) * gauge w = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gauge, Matrix.mul_apply, Fin.sum_univ_two]

theorem gauge_drift (w : ℝ) :
    gauge (-w) * drift * gauge w = !![w,1;1-w^2,-w] := by
  simp only [gauge, drift, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  ring

def pulseZero : Matrix (Fin 2) (Fin 2) ℝ := !![1,1;0,1]
def pulseTwo (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a,b;2*b,a]

theorem monodromy (a b : ℝ) :
    pulseTwo a b * pulseZero = !![a,a+b;2*b,a+2*b] ∧
    Matrix.det (pulseTwo a b * pulseZero) = a^2-2*b^2 ∧
    Matrix.trace (pulseTwo a b * pulseZero) = 2*(a+b) := by
  have h : pulseTwo a b * pulseZero = !![a,a+b;2*b,a+2*b] := by
    simp [pulseTwo, pulseZero, add_comm]
  rw [h]
  constructor
  · rfl
  constructor
  · simp [Matrix.det_fin_two]
    ring
  · simp [Matrix.trace_fin_two]
    ring

end StratonovichHAMAudit.DirectEvent
