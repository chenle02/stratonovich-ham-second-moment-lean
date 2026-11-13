/-
Refutation for the positivity clause of `L:variational-heat-envelope`
(`notes/integrated_unmasked_variational.tex` line 34 at a284420), package
theorems `StratonovichHAMSecondMoment.VariationalMean.heat_conv_pos` and
`variational_heat_envelope_paper`.

Wrong variant: the hypothesis `Γ ≠ 0` dropped, i.e. for every tempered `Γ`,
`μ` with the spectral convention and every `ε > 0`, `(Γ * p_ε)(0) > 0`.
Counterexample: `d = 1`, `Γ = μ = 0` (tempered, and the spectral convention
holds with both sides `0`); then `(Γ * p_1)(0) = 0`.
`positivity_contrast` applies the package's general envelope
`heat_envelope` at the same counterexample: only `0 ≤ (Γ * p_1)(0)` holds.
Junk reliance: none (an integral against the zero measure is genuinely `0`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.VariationalMean

set_option autoImplicit false

open MeasureTheory
open StratonovichHAMSecondMoment HomogHypothesis VariationalDilation VariationalMean

namespace Refutations.VariationalMean.Positivity

/-- The zero measure is tempered. -/
theorem zero_tempered : IsTempered (0 : Measure (Rd 1)) := ⟨0, by simp⟩

/-- The zero measure is its own spectral measure. -/
theorem zero_spectral : IsSpectralMeasure (0 : Measure (Rd 1)) 0 := by
  intro φ; simp

/-- Without `Γ ≠ 0` the value at zero need not be positive. -/
theorem positivity_without_nonzero_false :
    ¬ (∀ (Γ μ : Measure (Rd 1)), IsTempered Γ → IsTempered μ → IsSpectralMeasure Γ μ →
        ∀ ε : ℝ, 0 < ε → 0 < conv Γ (heatK ε) 0) := by
  intro h
  have := h 0 0 zero_tempered zero_tempered zero_spectral 1 one_pos
  simp [conv] at this

/-- The package envelope at the counterexample gives only `0 ≤ (Γ * p_1)(0)`. -/
theorem positivity_contrast : 0 ≤ conv (0 : Measure (Rd 1)) (heatK 1) 0 :=
  ((heat_envelope zero_tempered zero_tempered zero_spectral one_pos).2.2.2 0).1

end Refutations.VariationalMean.Positivity
