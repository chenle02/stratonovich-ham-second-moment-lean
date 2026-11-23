/-
Refutation for the masses of the regularized terminal-chain measures (main TeX lines 4393 and
4348-4351 at edf7085f), package theorem
`StratonovichHAMSecondMoment.TerminalWickRegularization.chainMeasureReg_univ`.

Wrong variant: the regularized measure built from the unit Green variables `V ~ G_1` alone
(forgetting the weights `s_{j+1} - s_j`, i.e. treating each `p_η * G_h` as a probability
measure) has mass `T^n/n!`.  Counterexample: `d = 1`, `n = 1`, `T = 1`, `x = 0`, `η = 1`:
the package mass is `1/2`, the variant gives `1`.  `reg_mass_no_green_mass_contrast` is the
package theorem at the same point.  No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.TerminalWickRegularization

set_option autoImplicit false

open StratonovichHAMSecondMoment TerminalWickRegularization

namespace Refutations.TerminalWickRegularization

/-- The package value: `g_1^{1,0,1}` has mass `1/2` in `d = 1`. -/
theorem reg_mass_no_green_mass_contrast :
    chainMeasureReg 1 1 1 zero_le_one 0 1 Set.univ = ENNReal.ofReal (1 / 2) := by
  rw [chainMeasureReg_univ 1 (Or.inl rfl) 1 1 zero_le_one 0 1]
  norm_num

/-- `g_n^{T,x,η}(total) = T^n/n!` is false. -/
theorem reg_mass_no_green_mass_refuted :
    ¬ (∀ (n : ℕ) (T : ℝ) (hT : 0 ≤ T),
      chainMeasureReg 1 n T hT 0 1 Set.univ = ENNReal.ofReal (T ^ n / n.factorial)) := by
  intro h
  have h1 := h 1 1 zero_le_one
  rw [reg_mass_no_green_mass_contrast] at h1
  rw [ENNReal.ofReal_eq_ofReal_iff (by norm_num) (by norm_num)] at h1
  norm_num at h1

end Refutations.TerminalWickRegularization
