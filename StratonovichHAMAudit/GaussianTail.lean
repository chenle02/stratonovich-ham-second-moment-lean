module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace StratonovichHAMAudit.GaussianTail

theorem cutoff_density_split (M x C nu : ℝ)
    (hM : 0 < M) (hx : M ≤ x) (hC : 0 ≤ C)
    (hnu : 1 < nu ∧ nu < 2) (hcut : 4 * C ≤ M ^ (2 - nu)) :
    C * x ^ nu - x ^ 2 / 2 ≤ -M ^ 2 / 8 - x ^ 2 / 8 := by
  have hxpos : 0 < x := lt_of_lt_of_le hM hx
  have hmono : M ^ (2 - nu) ≤ x ^ (2 - nu) :=
    Real.rpow_le_rpow hM.le hx (by linarith [hnu.2])
  have hs := mul_le_mul_of_nonneg_right (hcut.trans hmono)
    (Real.rpow_nonneg hxpos.le nu)
  have hr : x ^ (2 - nu) * x ^ nu = x ^ 2 := by
    calc
      _ = x ^ ((2 - nu) + nu) := (Real.rpow_add hxpos _ _).symm
      _ = x ^ (2 : ℝ) := by congr 1; ring
      _ = x ^ (2 : ℕ) := Real.rpow_natCast x 2
  rw [hr] at hs
  have hprod : 0 ≤ (x - M) * (x + M) :=
    mul_nonneg (sub_nonneg.mpr hx) (by linarith)
  have hCx : 0 ≤ C * x ^ nu := mul_nonneg hC (Real.rpow_nonneg hxpos.le nu)
  nlinarith [hs, hprod, hCx]

end StratonovichHAMAudit.GaussianTail
