/-
Refutation for `rayleighFloor_of_homog` of the integration module
`StratonovichHAMSecondMoment.SpatialOccupationCompleted` (the discharge of the
input `RayleighFloor` of `L:spatial-static-controls`,
`notes/integrated_spatial_occupation.tex` lines 40-49 at a284420).

Wrong variant: the hypothesis `Γ ≠ 0` dropped, i.e. `H:homog` alone gives the
floor.  Counterexample: `d = 1`, `α = α₀ = 1/2`, `Γ = μ = 0`, which satisfies
`H:homog` (zero covariance is admitted by design); then `U_z = 0` and every
Rayleigh value of the zero potential is `≤ 0` (`rayleighSet_const`).
Junk-value reliance: the Bochner integral against the zero measure is `0`
(a genuine value).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SpatialOccupationCompleted

set_option autoImplicit false

open MeasureTheory
open StratonovichHAMSecondMoment HomogHypothesis SpatialStaticControls

namespace Refutations.SpatialOccupationCompleted

/-- The zero covariance satisfies `H:homog` (`d = 1`, `α = α₀ = 1/2`). -/
theorem zero_homog : HomogCovariance 1 (1 / 2) (1 / 2) (0 : Measure (Rd 1)) 0 := by
  refine ⟨Or.inl rfl, by norm_num, by norm_num, inferInstance, ?_, ⟨0, by simp⟩, ?_,
    inferInstance, ?_, ⟨0, by simp⟩, ?_, ?_, by norm_num, Or.inl ⟨by norm_num, by norm_num⟩⟩
  · exact Measure.map_zero _
  · intro φ; simp
  · exact Measure.map_zero _
  · intro φ; simp
  · intro A _ c _; simp

/-- Without `Γ ≠ 0`, `H:homog` does not give the floor. -/
theorem floor_needs_nonzero_refuted :
    ¬ (∀ (Γ μ : Measure (Rd 1)), HomogCovariance 1 (1 / 2) (1 / 2) Γ μ → RayleighFloor Γ) := by
  intro h
  have h0 := h 0 0 zero_homog
  let b : ContDiffBump (0 : Rd 1) := ⟨1, 2, by norm_num, by norm_num⟩
  have hb0 : (b : Rd 1 → ℝ) 0 = 1 :=
    b.one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num))
  have hne : (b : Rd 1 → ℝ) ≠ 0 := by
    intro e
    have := congrFun e 0
    rw [hb0] at this
    exact one_ne_zero this
  obtain ⟨q, hq, hq0⟩ := h0 b ⟨b.contDiff, b.hasCompactSupport⟩ (fun _ => b.nonneg) hne
  have hU : VariationalDilation.conv (0 : Measure (Rd 1)) b = fun _ => (0 : ℝ) := by
    funext x
    simp [VariationalDilation.conv]
  rw [hU] at hq
  obtain ⟨-, hbdd, hsup⟩ := rayleighSet_const (d := 1) 0
  have := le_csSup hbdd hq
  rw [hsup] at this
  linarith

end Refutations.SpatialOccupationCompleted
