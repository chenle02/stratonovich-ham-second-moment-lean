/-
Refutation for `L:damped-homogeneous-norms` (main TeX
`notes/notes_stratonovich_ham_second_moment.tex`, revision a284420, lines
826 and 915-916: multipliers with values in `[0,1]`, closed under PRODUCTS),
package theorem `StratonovichHAMSecondMoment.DampedMultiplier.IsMultiplier.mul`.

Wrong variant: the class is closed under sums.  Counterexample: `d = 1`,
`g = h = 1`: `g + h = 2 > 1`.  `sum_contrast` is the package statement for the
product `1 · 1`.  No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.DampedMultiplier

set_option autoImplicit false

open StratonovichHAMSecondMoment StratonovichHAMSecondMoment.DampedMultiplier

namespace Refutations.DampedMultiplier

/-- The constant multiplier `1` is in the class. -/
theorem isMultiplier_one : IsMultiplier (fun _ : HomogHypothesis.Rd 1 => (1 : NNReal)) :=
  ⟨measurable_const, fun _ => le_rfl⟩

/-- Closure of the multiplier class under sums is false. -/
theorem sum_closed_refuted :
    ¬ (∀ g h : HomogHypothesis.Rd 1 → NNReal, IsMultiplier g → IsMultiplier h →
        IsMultiplier (g + h)) := by
  intro H
  have h1 := (H _ _ isMultiplier_one isMultiplier_one).2 0
  simp at h1

/-- The package statement for the product `1 · 1`. -/
theorem sum_contrast :
    IsMultiplier ((fun _ : HomogHypothesis.Rd 1 => (1 : NNReal)) * fun _ => 1) :=
  isMultiplier_one.mul isMultiplier_one

end Refutations.DampedMultiplier
