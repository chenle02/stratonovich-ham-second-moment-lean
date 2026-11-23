/-
Refutation for `StratonovichHAMSecondMoment.EndpointCorollaries.wsum_ne_zero` as used in
`three_finite_images_paper` (manuscript `C:three-finite-images`, main TeX lines 8000-8001 and
8030-8031 at edf7085f: "The target is nonzero because ... some weight is positive").

Wrong variant: the target `Σ w_i Γ_i` is nonzero for all nonnegative weights (the hypothesis
`Σ w_i > 0` dropped).  Counterexample: one component, weight `0`.  Control of the broader
Lean generalization, outside the manuscript's parameter class: the fixture is the exponent-1
Riesz measure, while the corollary requires `1 < α` (main TeX line 7992); `w_i ≥ 0` allows
zero.
`zero_weights_contrast` is the package lemma with weight `1` on `|x|^{-1} dx`.  The weights
enter through `ENNReal.ofReal`; weight `0` is a manuscript value, not a clamped junk value.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.EndpointCorollaries

set_option autoImplicit false

namespace Refutations.EndpointCorollaries

open MeasureTheory
open StratonovichHAMSecondMoment.EndpointCorollaries StratonovichHAMSecondMoment.EndpointLemmas

/-- The package lemma with weight `1`. -/
theorem zero_weights_contrast :
    wsum (fun _ : Fin 1 => (1 : ℝ)) (fun _ => rieszMeasure 1 1) ≠ 0 :=
  wsum_ne_zero (i := 0) one_pos (rieszMeasure_ne_zero one_pos 1)

/-- Without a positive weight the target can vanish. -/
theorem zero_weights_refuted :
    ¬ (∀ (w : Fin 1 → ℝ), (∀ i, 0 ≤ w i) →
      wsum w (fun _ => rieszMeasure 1 1) ≠ 0) := by
  intro h
  exact h (fun _ => 0) (fun _ => le_rfl) (by simp [wsum])

end Refutations.EndpointCorollaries
