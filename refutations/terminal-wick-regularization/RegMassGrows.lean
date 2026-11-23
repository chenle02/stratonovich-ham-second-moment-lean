/-
Refutation for the masses of the regularized terminal-chain measures (main TeX line 4393 at
edf7085f, "Those positive measures have the same masses"), package theorem
`StratonovichHAMSecondMoment.TerminalWickRegularization.chainMeasureReg_univ`.

Wrong variant: the Gaussian smoothing adds mass, `g_1^{T,x,η}(total) = T²/2 + η`.
Counterexample: `d = 1`, `T = 1`, `x = 0`, `η = 1`: the regularized measure has mass `1/2`
(the mass of `g_1^{1,0}`), the variant gives `3/2`.  `reg_mass_grows_contrast` is the package
theorem at the same point.  No junk-value reliance (`η = 1 > 0`, `T ≥ 0`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.TerminalWickRegularization

set_option autoImplicit false

open StratonovichHAMSecondMoment TerminalWickRegularization

namespace Refutations.TerminalWickRegularization

/-- The package value: `g_1^{1,0,1}` has mass `1/2` in `d = 1`. -/
theorem reg_mass_grows_contrast :
    chainMeasureReg 1 1 1 zero_le_one 0 1 Set.univ = ENNReal.ofReal (1 / 2) := by
  rw [chainMeasureReg_univ 1 (Or.inl rfl) 1 1 zero_le_one 0 1]
  norm_num

/-- `g_1^{T,x,η}(total) = T²/2 + η` is false. -/
theorem reg_mass_grows_refuted :
    ¬ (∀ (T η : ℝ) (hT : 0 ≤ T), 0 < η →
      chainMeasureReg 1 1 T hT 0 η Set.univ = ENNReal.ofReal (T ^ 2 / 2 + η)) := by
  intro h
  have h1 := h 1 1 zero_le_one one_pos
  rw [reg_mass_grows_contrast] at h1
  rw [ENNReal.ofReal_eq_ofReal_iff (by norm_num) (by norm_num)] at h1
  norm_num at h1

end Refutations.TerminalWickRegularization
