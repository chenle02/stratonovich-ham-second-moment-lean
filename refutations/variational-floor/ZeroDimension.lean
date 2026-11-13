/-
Refutation for (F5) of wave L6, package theorem
`StratonovichHAMSecondMoment.VariationalFloor.ae_eq_zero_of_hasWeakGradient_zero`
("zero weak gradient implies zero", used in `P:spatial-smooth-ratio`,
`notes/integrated_spatial_occupation.tex` lines 180-182 at a284420).

Wrong variant: the hypothesis `d ≥ 1` dropped.  Counterexample: `d = 0`.
`ℝ⁰` is one point of Lebesgue measure `1`; the constant `1` lies in `L²`, has
weak gradient `0` (every direction `v` is `0`, so `∂_v φ = 0`), and is not
a.e. zero.  No junk-value reliance: every integral is of a constant or zero
function against a finite measure.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.VariationalFloor

set_option autoImplicit false

open MeasureTheory
open StratonovichHAMSecondMoment HomogHypothesis WeakSobolev

namespace Refutations.VariationalFloor

/-- On `ℝ⁰` the constant `1` has weak gradient `0`. -/
theorem one_hasWeakGradient_zero : HasWeakGradient (fun _ : Rd 0 => (1 : ℝ)) 0 := by
  intro φ _ v
  have hv : v = 0 := Subsingleton.elim _ _
  subst hv
  simp

/-- Zero weak gradient does not force `f = 0` a.e. without `d ≥ 1`. -/
theorem zero_dimension_refuted :
    ¬ (∀ (d : ℕ) (f : Rd d → ℝ), MemLp f 2 volume → HasWeakGradient f 0 →
        f =ᵐ[volume] 0) := by
  intro h
  have hm : MemLp (fun _ : Rd 0 => (1 : ℝ)) 2 volume := memLp_const 1
  have h0 := h 0 _ hm one_hasWeakGradient_zero
  have hne : (volume : Measure (Rd 0)) ≠ 0 := NeZero.ne volume
  obtain ⟨x, hx⟩ := h0.exists
  simp at hx

end Refutations.VariationalFloor
