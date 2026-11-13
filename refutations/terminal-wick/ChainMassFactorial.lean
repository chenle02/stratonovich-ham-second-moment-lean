/-
Refutation for the chain-measure mass of `L:terminal-wick` (main TeX lines
3648-3651 at a284420), package theorem
`StratonovichHAMSecondMoment.TerminalWick.chainMass_eq`.

Wrong variant: `M_n(T) = T^{2n}/(n!)²` (the product of a time-simplex volume
`T^n/n!` and a separate factor `T^n/n!` for the Green masses).
Counterexample: `d = 2`, `n = 1`, `T = 1`: the true value is `1/2! = 1/2`,
the variant gives `1`.  `chain_mass_factorial_contrast` is the package theorem at
the same point.  No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.TerminalWick

set_option autoImplicit false

open StratonovichHAMSecondMoment TerminalWick

namespace Refutations.TerminalWick

/-- The package value `M_1(1) = 1/2` in `d = 2`. -/
theorem chain_mass_factorial_contrast : chainMass 2 1 1 = ENNReal.ofReal (1 / 2) := by
  rw [chainMass_eq 2 (Or.inr (Or.inl rfl)) 1 1 zero_le_one]
  norm_num

/-- `M_n(T) = T^{2n}/(n!)²` is false. -/
theorem chain_mass_factorial_refuted :
    ¬ (∀ (n : ℕ) (T : ℝ), 0 ≤ T →
        chainMass 2 n T = ENNReal.ofReal (T ^ (2 * n) / (n.factorial : ℝ) ^ 2)) := by
  intro h
  have h1 := h 1 1 zero_le_one
  rw [chain_mass_factorial_contrast] at h1
  rw [ENNReal.ofReal_eq_ofReal_iff (by norm_num) (by norm_num)] at h1
  norm_num at h1

end Refutations.TerminalWick
