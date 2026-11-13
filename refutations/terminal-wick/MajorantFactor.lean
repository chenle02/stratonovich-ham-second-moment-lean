/-
Refutation for the comparison behind the absolute convergence in
`L:terminal-wick` (main TeX lines 3642-3644 and 3695-3698 at a284420), package
theorem `StratonovichHAMSecondMoment.TerminalWick.sqrt_doubleFactorial_div_le`
(auxiliary: `√((2n-1)!!)/(2n)! ≤ 1/n!`).

Wrong variant: the factor `√((2n-1)!!)` of `E:terminal-term-majorant` is at most
`1`, i.e. `√((2n-1)!!)/(2n)! ≤ 1/(2n)!` for all `n`.  Counterexample: `n = 2`:
`√3/24 > 1/24`.  `majorant_factor_contrast` is the package bound at `n = 2`:
`√3/24 ≤ 1/2`.  No junk-value reliance (`√3` of a positive number).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.TerminalWick

set_option autoImplicit false

open StratonovichHAMSecondMoment TerminalWick

namespace Refutations.TerminalWick

/-- The package bound at `n = 2`. -/
theorem majorant_factor_contrast :
    Real.sqrt ((2 * 2 - 1).doubleFactorial) / (2 * 2).factorial ≤ 1 / (2 : ℕ).factorial :=
  sqrt_doubleFactorial_div_le 2

/-- `√((2n-1)!!)/(2n)! ≤ 1/(2n)!` is false. -/
theorem majorant_factor_refuted :
    ¬ (∀ n : ℕ, Real.sqrt ((2 * n - 1).doubleFactorial) / (2 * n).factorial ≤
        1 / (2 * n).factorial) := by
  intro h
  have h2 := h 2
  have hdf : ((2 * 2 - 1).doubleFactorial : ℝ) = 3 := by norm_num [Nat.doubleFactorial]
  have hf : ((2 * 2).factorial : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [hdf, hf, div_le_div_iff_of_pos_right (by norm_num)] at h2
  have h3 : (1 : ℝ) < Real.sqrt 3 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

end Refutations.TerminalWick
