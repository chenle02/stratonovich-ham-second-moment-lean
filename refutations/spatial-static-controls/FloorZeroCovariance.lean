/-
Refutation for the named input of part (i) of `L:spatial-static-controls`
(`notes/integrated_spatial_occupation.tex` lines 40-49 at a284420), package
definition `StratonovichHAMSecondMoment.SpatialStaticControls.RayleighFloor`.

Wrong variant: the floor without `Γ ≠ 0`, i.e. `RayleighFloor 0`.
Counterexample: `d = 1`, `Γ = 0`: then `U_z = Γ * z = 0` for every `z`, and every
real Rayleigh value of the zero potential is `-‖∇g‖₂² ≤ 0`, whose supremum is
`0` (`rayleighSet_const`), so no positive value exists (the test `z` is a smooth
bump).  This shows that the input carries the content `Γ ≠ 0`, and the lemma
`rayleighFloor_volume` (`Γ` = Lebesgue measure, an unrestricted covariance
outside `H:homog`, not white noise) shows the input is satisfiable.
`floor_zero_covariance_contrast` is the package theorem `rayleighFloor_volume`.
Junk-value reliance: the Bochner integral against the zero measure is `0`
(a genuine value, not a junk value).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SpatialStaticControls

set_option autoImplicit false

open MeasureTheory
open StratonovichHAMSecondMoment HomogHypothesis SpatialStaticControls

namespace Refutations.SpatialStaticControls

/-- The floor fails for the zero covariance. -/
theorem floor_zero_covariance_refuted : ¬ RayleighFloor (0 : Measure (Rd 1)) := by
  intro h
  let b : ContDiffBump (0 : Rd 1) := ⟨1, 2, by norm_num, by norm_num⟩
  have hb0 : (b : Rd 1 → ℝ) 0 = 1 :=
    b.one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num))
  have hne : (b : Rd 1 → ℝ) ≠ 0 := by
    intro e
    have := congrFun e 0
    rw [hb0] at this
    exact one_ne_zero this
  obtain ⟨q, hq, hq0⟩ := h b ⟨b.contDiff, b.hasCompactSupport⟩ (fun _ => b.nonneg) hne
  have hU : VariationalDilation.conv (0 : Measure (Rd 1)) b = fun _ => (0 : ℝ) := by
    funext x
    simp [VariationalDilation.conv]
  rw [hU] at hq
  obtain ⟨-, hbdd, hsup⟩ := rayleighSet_const (d := 1) 0
  have := le_csSup hbdd hq
  rw [hsup] at this
  linarith

/-- Contrast: the package's satisfiability check (white noise). -/
theorem floor_zero_covariance_contrast : RayleighFloor (volume : Measure (Rd 1)) :=
  rayleighFloor_volume

end Refutations.SpatialStaticControls
