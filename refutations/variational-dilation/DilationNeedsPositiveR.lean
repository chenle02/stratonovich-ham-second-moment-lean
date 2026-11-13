/-
Refutation for the bijection part of `L:variational-control-dilation`
(`notes/integrated_unmasked_variational.tex` lines 227-232), package theorem
`StratonovichHAMSecondMoment.VariationalDilation.dil_mapsTo` (and
`dil_bijOn`) and package definitions `CPos`, `dil`.

Wrong variant: the hypothesis `r > 0` dropped.  At `r = 0`, with `d = 1`,
`α = 1` (amplitude exponent `d + 2 - α = 2 ≠ 0`), `D_0 Ψ = 0^2 Ψ(s, 0) = 0`
for every `Ψ`, so `D_0` does not map the (nonempty, `CPos_nonempty`) class
into itself.  Junk reliance: none beyond Lean's `0 ^ 2 = 0` for the real
power, which is the true value.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.VariationalDilation

set_option autoImplicit false

namespace Refutations.VariationalDilation.Positive

open StratonovichHAMSecondMoment.VariationalDilation

/-- `D_0` collapses every control to zero (`d = 1`, `α = 1`). -/
theorem dil_zero (Ψ : ℝ × StratonovichHAMSecondMoment.HomogHypothesis.Rd 1 → ℝ) :
    dil 1 0 Ψ = 0 := by
  funext p
  simp [dil]

/-- `dil_mapsTo` fails without `r > 0`. -/
theorem mapsTo_without_pos_false :
    ¬ ∀ (d : ℕ) (alpha r : ℝ), Set.MapsTo (dil (d := d) alpha r) (CPos d) (CPos d) := by
  intro h
  obtain ⟨Ψ, hΨ⟩ := CPos_nonempty 1
  have := (h 1 1 0 hΨ).2.2.2.2
  exact this (dil_zero Ψ)

/-- Contrast: for `r = 1 > 0` the package theorem gives the inclusion. -/
theorem mapsTo_pos_contrast :
    Set.MapsTo (dil (d := 1) 1 1) (CPos 1) (CPos 1) :=
  dil_mapsTo 1 one_pos

end Refutations.VariationalDilation.Positive
