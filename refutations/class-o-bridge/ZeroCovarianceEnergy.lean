/-
Refutation for the standing assumption `Γ ≠ 0` of `P:occupation-physical-class` (wave L14, item
O), package theorem
`StratonovichHAMSecondMoment.ClassOBridge.occupation_physical_class_whole_paper`.

Manuscript side: `notes/integrated_spatial_occupation.tex` (revision 39f2597a) assumes a nonzero
covariance (lines 4-5) and states `0 < 𝓔_⋆^𝒪` (`E:occupation-own-energy`, lines 516-520); the
remark of lines 577-582 says that for zero covariance the occupation energy is zero.

Wrong variant: `0 < 𝓔_⋆^𝒪` for every model of `H:homog` (dropping `Γ ≠ 0`). Counterexample:
the white model with amplitude `c = 0` (`WhiteModel.white_homogCovariance`, `d = α = 1`,
`a = 1/2`), whose covariance is the zero measure, where `𝓔_⋆^𝒪 = 0`
(`ClassOBridge.EstarClassO_zero`). Class (a): a perturbation of the manuscript claim (its
standing assumption removed) inside the manuscript's model class. The contrast is the package
positivity under `Γ ≠ 0`.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.ClassOBridge
import StratonovichHAMSecondMoment.WhiteModel

set_option autoImplicit false

namespace Refutations.ClassOBridge

open StratonovichHAMSecondMoment StratonovichHAMSecondMoment.ClassOBridge MeasureTheory
open HomogHypothesis (Rd HomogCovariance)

/-- Positivity of the occupation energy over `𝒪` fails without `Γ ≠ 0`. -/
theorem occupation_energy_pos_needs_nonzero :
    ¬ ∀ (a : ℝ) (Γ μ : Measure (Rd 1)), HomogCovariance 1 1 a Γ μ →
      0 < EstarClassO a ((4 - 1) - 2 * a) Γ := by
  intro H
  have h := H (1 / 2) _ _ (WhiteModel.white_homogCovariance (c := 0) le_rfl (by norm_num)
    (by norm_num))
  have hz : WhiteModel.whiteCov 0 = (0 : Measure (Rd 1)) := by simp [WhiteModel.whiteCov]
  rw [hz, EstarClassO_zero] at h
  exact lt_irrefl 0 h

/-- Contrast: with `Γ ≠ 0` the occupation energy over `𝒪` is positive. -/
theorem occupation_energy_pos_needs_nonzero_contrast :
    ∀ (a : ℝ) (Γ μ : Measure (Rd 1)), HomogCovariance 1 1 a Γ μ → Γ ≠ 0 →
      0 < EstarClassO a ((4 - 1) - 2 * a) Γ :=
  fun _ _ _ hH hΓ => (occupation_physical_class_whole_paper hH hΓ _ rfl).2.2.2.1

end Refutations.ClassOBridge
