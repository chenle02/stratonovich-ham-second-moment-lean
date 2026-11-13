/-
Refutation for `StratonovichHAMSecondMoment.MaskedContinuousWave.bracket_add_le`
(`L:masked-continuous-wave`, TeX lines 413-416 at a284420: `⟨x+e⟩ ≤ (1+|e|)⟨x⟩`).

Wrong variant: the comparison with the factor `1 + |e|` dropped,
`⟨x+e⟩ ≤ ⟨x⟩`, in the binder shape of `bracket_add_le`. Witness `x = 0`,
`e = 1`: `⟨1⟩ = √2 > 1 = ⟨0⟩`. No junk value is involved (`√` of positive
reals). The contrast theorem applies `bracket_add_le` at the same point.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.MaskedContinuousWave

set_option autoImplicit false

namespace Refutations.MaskedContinuousWave

open StratonovichHAMSecondMoment.MaskedTrigProducts
  StratonovichHAMSecondMoment.MaskedContinuousWave

/-- Dropping the factor `1 + |e|` from `bracket_add_le` is false. -/
theorem bracket_add_no_factor : ¬ ∀ x e : ℝ, bracket (x + e) ≤ bracket x := by
  intro h
  have h1 := h 0 1
  simp only [bracket, zero_add] at h1
  norm_num at h1

/-- Contrast: the package comparison holds at the counterexample point. -/
theorem bracket_add_no_factor_contrast : bracket (0 + 1) ≤ (1 + |(1 : ℝ)|) * bracket 0 :=
  bracket_add_le 0 1

end Refutations.MaskedContinuousWave
