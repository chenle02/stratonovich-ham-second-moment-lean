/-
Refutation for `L:damped-homogeneous-norms` (main TeX
`notes/notes_stratonovich_ham_second_moment.tex`, revision a284420, lines
846-847 and 916-917), package theorem
`StratonovichHAMSecondMoment.DampedMultiplier.greenMass_conv` (convolution with
a PROBABILITY measure preserves the mass identity `G_s(ℝ^d) = s`).

Wrong variant: dropped hypothesis "probability", i.e. convolution with any
finite measure preserves the mass identity.  Counterexample: `d = 1`,
`ρ = 2 δ₀`, `G_s = s δ₀`: `(ρ * G_s)(ℝ) = 2s ≠ s` at `s = 1`.
`mass_contrast` is the package statement for `ρ = δ₀`.  No junk-value
reliance (all measures finite).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.DampedMultiplier

set_option autoImplicit false

open MeasureTheory StratonovichHAMSecondMoment StratonovichHAMSecondMoment.DampedNormsHomog
  StratonovichHAMSecondMoment.DampedMultiplier

namespace Refutations.DampedMultiplier

/-- The family `G_s = s δ₀` on `ℝ¹`. -/
noncomputable def diracMass : ℝ → Measure (HomogHypothesis.Rd 1) :=
  fun s => ENNReal.ofReal s • Measure.dirac 0

/-- `G_s = s δ₀` satisfies the mass identity. -/
theorem diracMass_greenMass : GreenMass diracMass :=
  ⟨fun s _ => by simp [diracMass]⟩

/-- Mass preservation under convolution with an arbitrary finite measure is
false. -/
theorem mass_nonprobability_refuted :
    ¬ (∀ ρ : Measure (HomogHypothesis.Rd 1), IsFiniteMeasure ρ →
        GreenMass (fun s => ρ ∗ diracMass s)) := by
  intro h
  have h1 := (h ((2 : NNReal) • Measure.dirac 0) inferInstance).mass 1 one_pos
  have := isFiniteMeasure_of_greenMass diracMass_greenMass 1 one_pos
  rw [Measure.conv, Measure.map_apply measurable_add MeasurableSet.univ, Set.preimage_univ,
    ← Set.univ_prod_univ, Measure.prod_prod] at h1
  simp [diracMass] at h1

/-- The package statement for `ρ = δ₀`. -/
theorem mass_contrast :
    GreenMass (fun s => (Measure.dirac (0 : HomogHypothesis.Rd 1)) ∗ diracMass s) :=
  greenMass_conv _ diracMass_greenMass

end Refutations.DampedMultiplier
