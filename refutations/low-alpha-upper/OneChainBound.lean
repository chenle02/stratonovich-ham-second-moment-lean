/-
Refutation for the increment-sum bound used by `P:low-alpha-upper` (through the
proof of `P:d1-upper`, main TeX lines 5483-5485 at 39f2597a: "the increments sum
to the two terminal times and therefore to at most `2t`").  Package theorem
`StratonovichHAMSecondMoment.TwoSimplexTime.sum_incr_le`.

Wrong variant: the one-chain bound `Σ_l h_l ≤ t` (main TeX line 5845) for two
chains.  Counterexample in the manuscript domain: `m = n = 1`, `t = 1`,
`s = (3/4, 3/4)` (one time in each chain): `Σ_l h_l = 3/2 > 1`.
`oneChainBound_contrast` is the package bound `≤ 2t` at the same point.
Class (a): manuscript-claim perturbation in the manuscript domain.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.TwoSimplexTime

set_option autoImplicit false

open StratonovichHAMSecondMoment TwoSimplexTime DiagramModel

namespace Refutations.LowAlphaUpper.OneChainBound

/-- The time vector `(3/4, 3/4)`. -/
noncomputable def s0 : Fin (1 + 1) → ℝ := fun _ => 3 / 4

/-- It lies in `[0,1]^1_< × [0,1]^1_<`. -/
theorem s0_mem : s0 ∈ twoSimplex 1 1 1 := by
  rw [mem_twoSimplex_iff]
  refine ⟨fun i => ⟨by norm_num [s0], by norm_num [s0]⟩, fun i j hij hjm => ?_⟩
  exfalso
  have := j.isLt
  have := i.isLt
  omega

/-- Its increments sum to `3/2`. -/
theorem s0_sum : ∑ i, incr 1 s0 i = 3 / 2 := by
  rw [sum_incr]
  simp [ext0, s0]
  norm_num

/-- The wrong variant `Σ h ≤ t` fails for two chains. -/
theorem oneChainBound_refuted :
    ¬ (∀ s ∈ twoSimplex 1 1 1, ∑ i, incr 1 s i ≤ 1) := by
  intro h
  have := h s0 s0_mem
  rw [s0_sum] at this
  norm_num at this

/-- The package bound `Σ h ≤ 2t` at the same point. -/
theorem oneChainBound_contrast : ∑ i, incr 1 s0 i ≤ 2 * 1 :=
  sum_incr_le zero_le_one s0_mem

end Refutations.LowAlphaUpper.OneChainBound
