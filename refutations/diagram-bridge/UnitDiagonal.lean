/-
Lean-route control for the determinant-one step of `DiagramBridge` (main TeX
line 5341 at edf7085f: "The spatial change of variables has determinant one"),
package theorem
`StratonovichHAMSecondMoment.DiagramBridge.measurePreserving_incrMatrix`.

Wrong variant: the triangular matrix with diagonal `2` instead of `1` (the
matrix `2 · incrMatrix`, determinant `4`).  Counterexample: `m = 1`, `N = 2`:
it maps Lebesgue measure to `¼` Lebesgue measure, so it is not measure
preserving (tested on the unit cube).  `unitDiagonal_contrast` is the package
measure preservation at the same size.
Class (b): Lean-route-only control (the matrix form of the change of variables
is the Lean route; the TeX states only the determinant).
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.DiagramBridge

set_option autoImplicit false

open MeasureTheory StratonovichHAMSecondMoment DiagramBridge

namespace Refutations.DiagramBridge

/-- The package: the unit-diagonal increment matrix preserves Lebesgue measure. -/
theorem unitDiagonal_contrast :
    MeasurePreserving (Matrix.toLin' (incrMatrix 1 2)) volume volume :=
  measurePreserving_incrMatrix 1 2

/-- With diagonal `2` the triangular map does not preserve Lebesgue measure. -/
theorem unitDiagonal_refuted :
    ¬ MeasurePreserving (Matrix.toLin' ((2 : ℝ) • incrMatrix 1 2)) volume volume := by
  intro h
  have hdet : ((2 : ℝ) • incrMatrix 1 2).det = 4 := by
    rw [Matrix.det_smul, det_incrMatrix]; norm_num
  have hmap := h.map_eq
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi (by rw [hdet]; norm_num), hdet] at hmap
  have hc := congrArg (fun μ : Measure (Fin 2 → ℝ) => μ (Set.Icc 0 1)) hmap
  simp only [Measure.smul_apply, smul_eq_mul, Real.volume_Icc_pi] at hc
  norm_num at hc

end Refutations.DiagramBridge
