module
public import Mathlib.Tactic
public import Mathlib.LinearAlgebra.Matrix.Notation
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace StratonovichHAMAudit.DimensionalMatrix

def backward (cp sp p : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![cp,-sp/p;p*sp,cp]
def coupling (H : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0,0;H,0]
def forward (cq sq q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![cq,sq/q;-q*sq,cq]

theorem full_interaction (cp sp p H cq sq q : ℝ) :
    backward cp sp p * coupling H * forward cq sq q =
      !![-(sp/p)*H*cq,-(sp/p)*H*(sq/q);cp*H*cq,cp*H*(sq/q)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [backward,coupling,forward,Matrix.mul_apply,Fin.sum_univ_two]
  all_goals ring

end StratonovichHAMAudit.DimensionalMatrix
