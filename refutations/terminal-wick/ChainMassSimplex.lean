/-
Refutation for the chain-measure mass of `L:terminal-wick` (main TeX lines
3648-3651 at a284420, `M_n(T) = T^{2n}/(2n)!`), package theorem
`StratonovichHAMSecondMoment.TerminalWick.chainMass_eq`.

Wrong variant: `M_n(T) = T^n/n!`, the volume of the ordered simplex, i.e.
forgetting that each Green measure `G_h` has mass `h` (not `1`).
Counterexample: `d = 1`, `n = 1`, `T = 1`: `M_1(1) = ∫_0^1 (1 - s) ds = 1/2`,
the variant gives `1`.  `chain_mass_simplex_contrast` is the package theorem at
the same point.  No junk-value reliance (`T ≥ 0`, `ENNReal.ofReal` of
nonnegative reals).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.TerminalWick

set_option autoImplicit false

open StratonovichHAMSecondMoment TerminalWick

namespace Refutations.TerminalWick

/-- The package value `M_1(1) = 1/2` in `d = 1`. -/
theorem chain_mass_simplex_contrast : chainMass 1 1 1 = ENNReal.ofReal (1 / 2) := by
  rw [chainMass_eq 1 (Or.inl rfl) 1 1 zero_le_one]
  norm_num

/-- `M_n(T) = T^n/n!` is false. -/
theorem chain_mass_simplex_refuted :
    ¬ (∀ (n : ℕ) (T : ℝ), 0 ≤ T → chainMass 1 n T = ENNReal.ofReal (T ^ n / n.factorial)) := by
  intro h
  have h1 := h 1 1 zero_le_one
  rw [chain_mass_simplex_contrast] at h1
  rw [ENNReal.ofReal_eq_ofReal_iff (by norm_num) (by norm_num)] at h1
  norm_num at h1

end Refutations.TerminalWick
