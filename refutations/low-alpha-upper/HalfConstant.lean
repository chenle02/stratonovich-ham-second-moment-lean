/-
Refutation for the calibration constant of `E:d1-first-calibration`
(`C:d1-first-calibration`, main TeX lines 5834-5839 at edf7085f).  Package
theorems `StratonovichHAMSecondMoment.LowAlphaUpper.C1_eq` and `two_C1_lt_C2`.

Wrong variant: `C_{1,*} = C_{2,*}/2` (the value that would make the Jensen
comparison `2C_1 ≤ C_2` an equality).  Counterexample in the manuscript domain:
`α = 1`, `α₀ = 1/2`, `K = 1` (`V = 1/π`, the degree-one case of
`P:low-alpha-upper`): the package gives `2C_1 < C_2`.
`halfConstant_contrast` is the package value `C_1 = C_2/2^{(4-α)/(3-α)}`.
Class (a): manuscript-claim perturbation in the manuscript domain.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.LowAlphaUpper

set_option autoImplicit false

open StratonovichHAMSecondMoment LowAlphaUpper

namespace Refutations.LowAlphaUpper.HalfConstant

/-- The wrong variant `C_1 = C_2/2` fails at `α = 1`, `α₀ = 1/2`, `K = 1`. -/
theorem halfConstant_refuted :
    ¬ (∀ α α₀ K : ℝ, 0 < α → α ≤ 1 → 0 < α₀ → α₀ < 1 → 0 < K →
      C1 α α₀ K = C2 α α₀ K / 2) := by
  intro h
  have h1 := h 1 (1 / 2) 1 one_pos le_rfl (by norm_num) (by norm_num) one_pos
  have h2 := two_C1_lt_C2 (α := 1) (α₀ := 1 / 2) (K := 1) (by norm_num) (by norm_num) one_pos
  rw [h1] at h2
  linarith

/-- The package value at the same point. -/
theorem halfConstant_contrast :
    C1 1 (1 / 2) 1 = C2 1 (1 / 2) 1 / 2 ^ ((4 - 1 : ℝ) / (3 - 1)) :=
  C1_eq (by norm_num) (by norm_num) zero_le_one

end Refutations.LowAlphaUpper.HalfConstant
