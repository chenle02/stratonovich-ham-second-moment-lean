/-
Refutation for the mask profile of `P:variational-remove-mask`
(`notes/integrated_unmasked_variational.tex` lines 184-189 at a284420),
package theorem `StratonovichHAMSecondMoment.RemoveMask.chi_eq_one`
(`χ = 1` on `r ≤ 1`).

Wrong variant: a wider plateau, `χ(r) = 1` for every `r ≤ 2`.
Counterexample: `r = 3/2`, where `χ(3/2) = F(1/2)/(F(1/2) + F(1/2)) = 1/2`
because `F(1/2) = e^{-2} > 0`.  `chi_plateau_contrast` is the package theorem
at `r = 1`.  No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.RemoveMask

set_option autoImplicit false

namespace Refutations.RemoveMask

open StratonovichHAMSecondMoment.RemoveMask

/-- `χ(3/2) = 1/2`. -/
theorem chi_three_halves : chi (3 / 2) = 1 / 2 := by
  rw [chi_eq, show (2 : ℝ) - 3 / 2 = 3 / 2 - 1 by norm_num]
  have h := expNegInvGlue.pos_of_pos (show (0 : ℝ) < 3 / 2 - 1 by norm_num)
  field_simp
  ring

/-- A plateau of `χ` up to `r = 2` is false. -/
theorem chi_plateau_two_refuted : ¬ (∀ r : ℝ, r ≤ 2 → chi r = 1) := by
  intro h
  have := h (3 / 2) (by norm_num)
  rw [chi_three_halves] at this
  norm_num at this

/-- The package plateau at its edge `r = 1`. -/
theorem chi_plateau_contrast : chi 1 = 1 := chi_eq_one le_rfl

end Refutations.RemoveMask
