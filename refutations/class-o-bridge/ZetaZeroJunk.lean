/-
Refutation for the totalized supremum at `ζ = 0` (wave L14, item O), package theorem
`StratonovichHAMSecondMoment.ClassOBridge.raw_occupation_energy_whole_paper` (the conjunct
`0 < 𝓔_ζ^𝒪`, stated for `ζ > 0`).

Manuscript side: `notes/integrated_occupation_ceiling.tex` (revision edf7085f), lines 10-18 and
129-130: `𝓔_ζ^𝒪` is defined and positive for `ζ > 0` only.

Wrong variant: `0 < 𝓔_0^𝒪` (the Lean object `EOO a Γ 0`). Lean's `sSup` of a set that is not
bounded above is `0`, so at `ζ = 0`, where the value set is unbounded
(`junk_white_not_bddAbove`, as in `ZetaZeroUnbounded.lean`), the Lean value is `0`, not positive.
Class (c): a control of Lean's totalized arithmetic outside the manuscript domain (`ζ = 0`).
The contrast is positivity for `ζ > 0`.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.ClassOBridge
import StratonovichHAMSecondMoment.WhiteModel

set_option autoImplicit false

namespace Refutations.ClassOBridge

open StratonovichHAMSecondMoment StratonovichHAMSecondMoment.ClassOBridge MeasureTheory
open HomogHypothesis (Rd HomogCovariance)

/-- Auxiliary: the white model with `c = 1` has a nonzero covariance. -/
theorem junk_whiteCov_one_ne_zero : WhiteModel.whiteCov 1 ≠ (0 : Measure (Rd 1)) := by
  simp [WhiteModel.whiteCov]

/-- Auxiliary: in the white model with `c = 1`, `a = 1/2`, the value set of `𝓔_0^𝒪` is not
bounded above. -/
theorem junk_white_not_bddAbove :
    ¬ BddAbove (rawEnergySetO (1 / 2) (WhiteModel.whiteCov 1) 0) := by
  have hH := WhiteModel.white_homogCovariance (c := 1) (a := 1 / 2) zero_le_one (by norm_num)
    (by norm_num)
  have hΓ := junk_whiteCov_one_ne_zero
  rintro ⟨M, hM⟩
  obtain ⟨hne, -, hC, -, hall, -, -⟩ := raw_occupation_energy_whole_paper hH hΓ
  obtain ⟨r, ⟨u, hu, rfl⟩, hr⟩ := exists_lt_of_lt_csSup hne hC
  obtain ⟨hT, -, hA0, -, hdil⟩ := hall u hu
  set A0 := RawOccupationEnergy.A (1 / 2) (WhiteModel.whiteCov 1) (gO u) with hA0def
  have hA : 0 < A0 := by
    rcases hA0.lt_or_eq with h | h
    · exact h
    · rw [← h, zero_div] at hr; exact absurd hr (lt_irrefl 0)
  set ℓ := (|M| + 1) / A0 + 1 with hℓdef
  have hℓ : 0 < ℓ := by positivity
  obtain ⟨u', hu', -, hA', -⟩ := hdil ℓ hℓ
  have hmem : RawOccupationEnergy.A (1 / 2) (WhiteModel.whiteCov 1) (gO u') -
      0 * OccupationPhysicalClass.T (dgO u') ∈
      rawEnergySetO (1 / 2) (WhiteModel.whiteCov 1) 0 := ⟨u', hu', rfl⟩
  have hle := hM hmem
  rw [zero_mul, sub_zero, hA', Real.rpow_one] at hle
  have e : ℓ * A0 = |M| + 1 + A0 := by
    rw [hℓdef, add_mul, div_mul_cancel₀ _ hA.ne', one_mul]
  rw [e] at hle
  linarith [le_abs_self M]

/-- `𝓔_0^𝒪 > 0` fails: the Lean supremum at `ζ = 0` is the junk value `0`. -/
theorem zeta_zero_energy_pos :
    ¬ ∀ (a : ℝ) (Γ μ : Measure (Rd 1)), HomogCovariance 1 1 a Γ μ → Γ ≠ 0 →
      0 < EOO a Γ 0 := by
  intro H
  have h := H _ _ _ (WhiteModel.white_homogCovariance (c := 1) (a := 1 / 2) zero_le_one
    (by norm_num) (by norm_num)) junk_whiteCov_one_ne_zero
  rw [EOO, Real.sSup_of_not_bddAbove junk_white_not_bddAbove] at h
  exact lt_irrefl 0 h

/-- Contrast: for every `ζ > 0`, `𝓔_ζ^𝒪 > 0`. -/
theorem zeta_zero_energy_pos_contrast :
    ∀ (a : ℝ) (Γ μ : Measure (Rd 1)), HomogCovariance 1 1 a Γ μ → Γ ≠ 0 →
      ∀ ζ : ℝ, 0 < ζ → 0 < EOO a Γ ζ :=
  fun _ _ _ hH hΓ ζ hζ =>
    ((raw_occupation_energy_whole_paper hH hΓ).2.2.2.2.2.2 ζ hζ).2.2.2.2.1

end Refutations.ClassOBridge
