/-
Refutation for the total mass of the constructed terminal-chain measure
`g_n^{T,x}` (`E:terminal-chain-measure`, main TeX lines 4275-4288, mass lines
4348-4351 at 39f2597a), package theorem
`StratonovichHAMSecondMoment.TerminalWickInputs.chainMeasureRaw_univ`.

Wrong variant: `g_n^{T,x}(total) = T^n/n!`, the volume of the ordered simplex,
i.e. treating each Green measure `G_h` as a probability measure (forgetting
that its mass is `h`).  Counterexample: `d = 1`, `n = 1`, `T = 1`, `x = 0`:
the constructed measure has mass `∫_0^1 (1 - s) ds = 1/2`, the variant gives
`1`.  `chain_measure_no_green_mass_contrast` is the package theorem at the same
point.  No junk-value reliance (`T ≥ 0`, `ENNReal.ofReal` of nonnegative reals).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.TerminalWickInputs

set_option autoImplicit false

open StratonovichHAMSecondMoment TerminalWickInputs

namespace Refutations.TerminalWickInputs

/-- The package value: `g_1^{1,0}` has mass `1/2` in `d = 1`. -/
theorem chain_measure_no_green_mass_contrast :
    chainMeasureRaw 1 1 1 0 Set.univ = ENNReal.ofReal (1 / 2) := by
  rw [chainMeasureRaw_univ 1 (Or.inl rfl) 1 1 zero_le_one 0]
  norm_num

/-- `g_n^{T,x}(total) = T^n/n!` is false. -/
theorem chain_measure_no_green_mass_refuted :
    ¬ (∀ (n : ℕ) (T : ℝ), 0 ≤ T →
      chainMeasureRaw 1 n T 0 Set.univ = ENNReal.ofReal (T ^ n / n.factorial)) := by
  intro h
  have h1 := h 1 1 zero_le_one
  rw [chain_measure_no_green_mass_contrast] at h1
  rw [ENNReal.ofReal_eq_ofReal_iff (by norm_num) (by norm_num)] at h1
  norm_num at h1

end Refutations.TerminalWickInputs
