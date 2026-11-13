/-
Refutation for `spatial_smooth_ratio_completed_paper` of the integration module
`StratonovichHAMSecondMoment.SpatialOccupationCompleted`
(`P:spatial-smooth-ratio`, `notes/integrated_spatial_occupation.tex` lines
166-176 at a284420: "`R_0` is a positive finite real number").

Wrong variant: the hypothesis `Γ ≠ 0` dropped, i.e. `R_0 > 0` under `H:homog`
alone.  Counterexample: `d = 1`, `α = α₀ = 1/2`, `Γ = μ = 0` (in `H:homog`);
every ratio is `A_sp(g)/b(g)^{α/2} = 0`, so `R_0 = sup ≤ 0`.  Junk-value
reliance: the Bochner integral against the zero measure is `0` (genuine), and
`sSup` of a set of nonpositive reals is `≤ 0` whether or not the set is empty.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SpatialOccupationCompleted

set_option autoImplicit false

open MeasureTheory
open StratonovichHAMSecondMoment HomogHypothesis SpatialSmoothRatio

namespace Refutations.SpatialOccupationCompleted

/-- The zero covariance satisfies `H:homog` (`d = 1`, `α = α₀ = 1/2`). -/
theorem zero_homog' : HomogCovariance 1 (1 / 2) (1 / 2) (0 : Measure (Rd 1)) 0 := by
  refine ⟨Or.inl rfl, by norm_num, by norm_num, inferInstance, ?_, ⟨0, by simp⟩, ?_,
    inferInstance, ?_, ⟨0, by simp⟩, ?_, ?_, by norm_num, Or.inl ⟨by norm_num, by norm_num⟩⟩
  · exact Measure.map_zero _
  · intro φ; simp
  · exact Measure.map_zero _
  · intro φ; simp
  · intro A _ c _; simp

/-- Without `Γ ≠ 0`, `R_0` need not be positive. -/
theorem R0_needs_nonzero_refuted :
    ¬ (∀ (Γ μ : Measure (Rd 1)), HomogCovariance 1 (1 / 2) (1 / 2) Γ μ →
        0 < R0 Γ (1 / 2)) := by
  intro h
  have h0 := h 0 0 zero_homog'
  have hle : R0 (0 : Measure (Rd 1)) (1 / 2) ≤ 0 := by
    refine Real.sSup_nonpos fun r hr => ?_
    obtain ⟨g, -, rfl⟩ := hr
    simp [ratio, SpatialFourierBound.spatialEnergy, SpatialFourierBound.spatialPair]
  linarith

end Refutations.SpatialOccupationCompleted
