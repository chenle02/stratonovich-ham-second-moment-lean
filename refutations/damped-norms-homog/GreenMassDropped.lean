/-
Refutation for `L:damped-homogeneous-norms` (main TeX
`notes/notes_stratonovich_ham_second_moment.tex`, revision a284420, lines
809-810 and 881), package theorem
`StratonovichHAMSecondMoment.DampedNormsHomog.N0_eq`.

Wrong variant: the supplied mass identity dropped, i.e. `N₀(θ) = θ^{-2}` for
every family `G` of measures.  Counterexample: `G_s = 0`, `θ = 1`:
`N₀(1) = 0 ≠ 1`.  `green_mass_contrast` is the package value at `θ = 1` for
`G_s = s δ₀`, which satisfies the input.  No junk-value reliance: the
integrand for `G_s = 0` is identically `0`.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.DampedNormsHomog

set_option autoImplicit false

open MeasureTheory Set StratonovichHAMSecondMoment StratonovichHAMSecondMoment.DampedNormsHomog

namespace Refutations.DampedNormsHomog

/-- `N₀(θ) = θ^{-2}` without the mass identity is false. -/
theorem green_mass_dropped_refuted :
    ¬ (∀ G : ℝ → Measure (HomogHypothesis.Rd 1), ∀ θ : ℝ, 0 < θ →
        N0 G θ = θ ^ (-(2 : ℝ))) := by
  intro h
  have h1 := h (fun _ => 0) 1 one_pos
  simp [N0] at h1

/-- The package value at `θ = 1` for `G_s = s δ₀`: `N₀(1) = 1`. -/
theorem green_mass_contrast :
    N0 (fun s : ℝ => ENNReal.ofReal s • Measure.dirac (0 : HomogHypothesis.Rd 1)) 1 = 1 := by
  rw [(N0_eq _ ⟨fun s _ => by simp⟩ 1 one_pos).2, Real.one_rpow]

end Refutations.DampedNormsHomog
