/-
Refutation for `L:damped-homogeneous-norms` (main TeX
`notes/notes_stratonovich_ham_second_moment.tex`, revision a284420, lines
809-810 and 881), package theorem
`StratonovichHAMSecondMoment.DampedNormsHomog.N0_eq` (`N₀(θ) = θ^{-2}` from the
mass identity `G_s(ℝ^d) = s`).

Wrong variant: exponent `-1` instead of `-2`, i.e. `N₀(θ) = θ^{-1}` for every
family with `G_s(ℝ^d) = s`.  Counterexample: `d = 1`, `G_s = s δ₀` (mass `s`)
and `θ = 2`: `N₀(2) = 1/4 ≠ 1/2`.  `green_exponent_contrast` is the package
value at the same point.  No junk-value reliance (`G_s` has finite mass, the
integrand is integrable by `N0_eq`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.DampedNormsHomog

set_option autoImplicit false

open MeasureTheory Set StratonovichHAMSecondMoment StratonovichHAMSecondMoment.DampedNormsHomog

namespace Refutations.DampedNormsHomog

/-- The family `G_s = s δ₀` on `ℝ¹`. -/
noncomputable def diracFamily : ℝ → Measure (HomogHypothesis.Rd 1) :=
  fun s => ENNReal.ofReal s • Measure.dirac 0

/-- `G_s = s δ₀` satisfies the mass identity. -/
theorem diracFamily_mass : GreenMass diracFamily :=
  ⟨fun s _ => by simp [diracFamily]⟩

/-- `N₀(θ) = θ^{-1}` (wrong exponent) is false. -/
theorem green_exponent_refuted :
    ¬ (∀ G : ℝ → Measure (HomogHypothesis.Rd 1), GreenMass G →
        ∀ θ : ℝ, 0 < θ → N0 G θ = θ ^ (-(1 : ℝ))) := by
  intro h
  have h1 := h diracFamily diracFamily_mass 2 two_pos
  rw [(N0_eq diracFamily diracFamily_mass 2 two_pos).2] at h1
  rw [Real.rpow_neg (by norm_num), Real.rpow_neg (by norm_num)] at h1
  norm_num at h1

/-- The package value at the same point: `N₀(2) = 2^{-2}`. -/
theorem green_exponent_contrast : N0 diracFamily 2 = (2 : ℝ) ^ (-(2 : ℝ)) :=
  (N0_eq diracFamily diracFamily_mass 2 two_pos).2

end Refutations.DampedNormsHomog
