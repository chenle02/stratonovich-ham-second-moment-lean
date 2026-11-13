/-
Refutation for the limit of the time trapezoids (Lean route of `L:occupation-rayleigh-selection`
and of the Cauchy-Schwarz bound `step_mean_le_sqrt`, `notes/integrated_occupation_ceiling.tex`
lines 38-41 and 149-193 at a284420), package theorem
`StratonovichHAMSecondMoment.OccupationCeilingExact.trap_tendsto`
(`trap n p q s → 1_{(p,q)}(s)`).

Wrong variant: the limit is the indicator of the CLOSED interval `[p,q]`.  Counterexample:
`p = 0`, `q = 1`, `s = 0`: every trapezoid vanishes at the endpoint, so the limit is `0`, while
`1_{[0,1]}(0) = 1`.  `trapezoid_limit_contrast` is the package statement at the same point.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.OccupationCeilingExact

set_option autoImplicit false

open Filter Topology

namespace Refutations.OccupationCeilingExact

open StratonovichHAMSecondMoment

/-- The trapezoids do not converge to the closed-interval indicator at an endpoint. -/
theorem trapezoid_limit_refuted :
    ¬ Tendsto (fun n => OccupationCeilingExact.trap n 0 1 0) atTop
        (𝓝 ((Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) 0)) := by
  intro h
  have h0 : (fun n => OccupationCeilingExact.trap n 0 1 0) = fun _ => (0 : ℝ) := by
    funext n
    exact OccupationCeilingExact.trap_eq_zero (by simp)
  rw [h0, Set.indicator_of_mem (by simp)] at h
  exact zero_ne_one (tendsto_nhds_unique tendsto_const_nhds h)

/-- The package statement at the same point. -/
theorem trapezoid_limit_contrast :
    Tendsto (fun n => OccupationCeilingExact.trap n 0 1 0) atTop
      (𝓝 ((Set.Ioo (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) 0)) :=
  OccupationCeilingExact.trap_tendsto 0 1 0

end Refutations.OccupationCeilingExact
