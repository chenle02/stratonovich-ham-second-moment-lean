import StratonovichHAMSecondMoment.SourceHeatGram

/-!
Refutation for the decay hypothesis of
`StratonovichHAMSecondMoment.SourceHeatGram.rapid_mem_HGamma` (the Lean route to the
"includes Schwartz tests" conclusion of `L:source-spatial-heat`,
`integrated_source_convergence.tex` lines 175 and 189-192 at edf7085f).

Class (b): Lean-route-only control.  The route needs `IsRapid` (smooth and rapidly
decreasing); a smooth function without decay, the constant `1`, is not in this class, so the
cutoff argument does not apply to it (its transform is not an `L¹` integral).
`constant_not_rapid_contrast`: every real Schwartz test is in the class.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.SourceHeatGram

open StratonovichHAMSecondMoment
open StratonovichHAMSecondMoment.SourceHeatGram

/-- The constant `1` is not rapidly decreasing. -/
theorem constant_not_rapid_refuted : ¬ IsRapid (fun _ : HomogHypothesis.Rd 1 => (1 : ℝ)) := by
  rintro ⟨-, h⟩
  obtain ⟨C, hC⟩ := h 1
  have h1 := hC (EuclideanSpace.single 0 (|C| + 1))
  have hn : ‖(EuclideanSpace.single 0 (|C| + 1) : HomogHypothesis.Rd 1)‖ = |C| + 1 := by
    rw [PiLp.norm_single, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hn] at h1
  simp only [pow_one, abs_one, mul_one] at h1
  linarith [le_abs_self C]

/-- Contrast: real Schwartz tests are rapidly decreasing. -/
theorem constant_not_rapid_contrast (f : SchwartzMap (HomogHypothesis.Rd 1) ℝ) :
    IsRapid (f : HomogHypothesis.Rd 1 → ℝ) :=
  isRapid_schwartz f

end Refutations.SourceHeatGram
