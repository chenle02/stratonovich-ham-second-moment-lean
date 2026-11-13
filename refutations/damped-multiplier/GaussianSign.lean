/-
Refutation for `L:damped-homogeneous-norms` (main TeX
`notes/notes_stratonovich_ham_second_moment.tex`, revision a284420, lines
845-846 and 915-916), package theorem
`StratonovichHAMSecondMoment.DampedMultiplier.isMultiplier_gaussMult`
(`e^{-η|ξ|²}` is in the multiplier class for `η ≥ 0`).

Wrong variant: dropped hypothesis `η ≥ 0`, i.e. `e^{-η|ξ|²}` is in the class for
every real `η`.  Counterexample: `d = 1`, `η = -1`, `ξ = e₀` (`|ξ| = 1`):
the value is `e > 1`.  `gaussian_sign_contrast` is the package statement at
`η = 1`.  No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.DampedMultiplier

set_option autoImplicit false

open StratonovichHAMSecondMoment StratonovichHAMSecondMoment.DampedMultiplier

namespace Refutations.DampedMultiplier

/-- `e^{-η|ξ|²}` in the class for every `η` (sign condition dropped) is false. -/
theorem gaussian_sign_refuted :
    ¬ (∀ η : ℝ, IsMultiplier (gaussMult (d := 1) η)) := by
  intro h
  have h1 := (h (-1)).2 (EuclideanSpace.single 0 1)
  have h2 : (gaussMult (d := 1) (-1) (EuclideanSpace.single 0 1) : ℝ) ≤ 1 := by
    exact_mod_cast h1
  rw [coe_gaussMult] at h2
  simp at h2
  linarith [Real.add_one_le_exp (1 : ℝ)]

/-- The package statement at `η = 1`. -/
theorem gaussian_sign_contrast : IsMultiplier (gaussMult (d := 1) 1) :=
  isMultiplier_gaussMult 1 zero_le_one

end Refutations.DampedMultiplier
