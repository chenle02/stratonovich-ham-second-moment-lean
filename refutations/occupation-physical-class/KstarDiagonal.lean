/-
Refutation for the auxiliary kernel lower bound of the positivity step of
`P:occupation-physical-class` (`notes/integrated_spatial_occupation.tex` lines 434-439 at
a284420), package theorem `StratonovichHAMSecondMoment.OccupationPhysicalClass.Kstar_one_le`
(`K_⋆(1) ≤ K_⋆(s-t)` for distinct `s, t ∈ (0,1)`).

Wrong variant: the hypothesis `t ≠ s` dropped.  Counterexample: `a = 1/2`, `D = 1`,
`s = t = 1/2`: `K_⋆(0) = 0` by the manuscript's convention (line 359), while `K_⋆(1) > 0`.
This uses the manuscript's diagonal convention `K_⋆(0) = 0`, not a Lean junk value.
`kstar_diagonal_contrast` applies the package theorem at `s = 1/2`, `t = 1/4`.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.OccupationPhysicalClass

set_option autoImplicit false

open Set StratonovichHAMSecondMoment StratonovichHAMSecondMoment.OccupationPhysicalClass

namespace Refutations.OccupationPhysicalClass

/-- Dropping `t ≠ s` is false. -/
theorem kstar_diagonal_refuted :
    ¬ (∀ s t : ℝ, s ∈ Ioo (0 : ℝ) 1 → t ∈ Ioo (0 : ℝ) 1 →
        OccupationKernelRow.Kstar (1 / 2) 1 1 ≤ OccupationKernelRow.Kstar (1 / 2) 1 (s - t)) := by
  intro h
  have h1 := h (1 / 2) (1 / 2) ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
  have h0 : OccupationKernelRow.Kstar (1 / 2) 1 (1 / 2 - 1 / 2) = 0 := by
    simp [OccupationKernelRow.Kstar]
  have hp := OccupationKernelRow.Kstar_pos (1 / 2) 1 1 (by norm_num) one_pos one_ne_zero
  rw [h0] at h1
  linarith

/-- The package bound at distinct times. -/
theorem kstar_diagonal_contrast :
    OccupationKernelRow.Kstar (1 / 2) 1 1 ≤ OccupationKernelRow.Kstar (1 / 2) 1 (1 / 2 - 1 / 4) :=
  Kstar_one_le (by norm_num) one_pos ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    (by norm_num)

end Refutations.OccupationPhysicalClass
