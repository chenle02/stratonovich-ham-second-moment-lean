/-
Refutation for the positivity claim of part (i) of `L:spatial-static-controls`
(`notes/integrated_spatial_occupation.tex` lines 41-47 at a284420:
"for every nonnegative nonzero `z`, `λ_z(c)²` is positive"), package theorem
`StratonovichHAMSecondMoment.SpatialStaticControls.static_rate`.

Wrong variant: dropping `z ≠ 0`, i.e. `λ_z(c)² > 0` for every nonnegative test
function `z` and `c > 0` (covariance `Γ` = Lebesgue measure, outside `H:homog`
and not white noise, for which the floor input holds, `rayleighFloor_volume`).
Counterexample: `d = 1`, `z = 0`: `U_z = 0` and `λ_z(c)² = c · 0 = 0`
(`lamSq_const`).  `zero_profile_contrast` is the package value at the
counterexample.
Junk-value reliance: none (the Rayleigh set of the zero potential is nonempty
and bounded, its supremum `0` is genuine).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SpatialStaticControls

set_option autoImplicit false

open MeasureTheory
open StratonovichHAMSecondMoment HomogHypothesis SpatialStaticControls WeakSobolev

namespace Refutations.SpatialStaticControls

/-- Auxiliary: `U_0 = 0`. -/
theorem conv_zero_profile :
    VariationalDilation.conv (volume : Measure (Rd 1)) (fun _ => (0 : ℝ)) = fun _ => 0 := by
  funext x
  simp [VariationalDilation.conv]

/-- Positivity without `z ≠ 0` is false. -/
theorem zero_profile_refuted :
    ¬ (∀ z : Rd 1 → ℝ, IsTestFunction z → (∀ x, 0 ≤ z x) → ∀ c : ℝ, 0 < c →
        0 < lamSq (VariationalDilation.conv (volume : Measure (Rd 1)) z) c) := by
  intro h
  have := h (fun _ => 0) ⟨contDiff_const, HasCompactSupport.zero⟩ (fun _ => le_rfl) 1 one_pos
  rw [conv_zero_profile, lamSq_const] at this
  norm_num at this

/-- Contrast: the package value `λ_0(1)² = 0`. -/
theorem zero_profile_contrast :
    lamSq (VariationalDilation.conv (volume : Measure (Rd 1)) (fun _ => (0 : ℝ))) 1 = 0 := by
  rw [conv_zero_profile, lamSq_const, mul_zero]

end Refutations.SpatialStaticControls
