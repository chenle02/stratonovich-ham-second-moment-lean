/-
Refutation for the potential identity of `L:temporal-equilibrium` (TeX lines
38 and 44--45, `E:temporal-equilibrium-potential`), package theorem
`StratonovichHAMSecondMoment.TemporalEquilibrium.potential_eq_one` and
package definition `StratonovichHAMSecondMoment.TemporalEquilibrium.density`.

Wrong variant: the hypothesis `a < 1` dropped (relaxed to `a ≤ 1`). At a = 1
the exponent is r = 0 and the normalizer Γ(0)Γ(1) is undefined.

Caveat (Lean junk value): the Lean refutation relies on Mathlib's
`Real.Gamma 0 = 0`, which makes the package density at a = 1 identically 0
(division by 0), so the potential is 0 ≠ 1. Mathematically the identity fails
at a = 1 for a different reason: the kernel |s-t|^{-1} is not locally
integrable. Either way the identity
"∫_0^1 |s-t|^{-a} f_a(t) dt = 1 for every s ∈ [0,1]" fails at a = 1.
`potential_at_a_one` is the statement at a = 1 (as before);
`potential_eq_one_fails_at_one` states the package theorem's shape with
`a < 1` relaxed to `a ≤ 1` and follows from it.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.TemporalEquilibrium

set_option autoImplicit false

open MeasureTheory Set Real

namespace Refutations.TemporalEquilibrium

/-- At `a = 1` the potential of the package density is not identically `1`
(through the junk value `Real.Gamma 0 = 0`). -/
theorem potential_at_a_one :
    ¬ (∀ s ∈ Icc (0:ℝ) 1, ∫ t in Ioo (0:ℝ) 1,
      |s - t| ^ (-(1:ℝ)) * StratonovichHAMSecondMoment.TemporalEquilibrium.density 1 t = 1) := by
  intro h
  have h0 := h 0 ⟨le_rfl, zero_le_one⟩
  simp [StratonovichHAMSecondMoment.TemporalEquilibrium.density, Gamma_zero] at h0

/-- `potential_eq_one` fails when `a < 1` is relaxed to `a ≤ 1`. -/
theorem potential_eq_one_fails_at_one :
    ¬ ∀ a : ℝ, 0 < a → a ≤ 1 → ∀ s ∈ Icc (0:ℝ) 1,
      IntegrableOn (fun t => |s - t| ^ (-a) *
          StratonovichHAMSecondMoment.TemporalEquilibrium.density a t) (Ioo 0 1) ∧
        ∫ t in Ioo (0:ℝ) 1,
          |s - t| ^ (-a) * StratonovichHAMSecondMoment.TemporalEquilibrium.density a t = 1 :=
  fun h => potential_at_a_one fun s hs => (h 1 one_pos le_rfl s hs).2

end Refutations.TemporalEquilibrium
