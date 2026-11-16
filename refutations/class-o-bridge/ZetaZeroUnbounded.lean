/-
Refutation for the penalty range `ζ > 0` of `P:raw-occupation-energy` (wave L14, item O),
package theorem `StratonovichHAMSecondMoment.ClassOBridge.raw_occupation_energy_whole_paper`.

Manuscript side: `notes/integrated_occupation_ceiling.tex` (revision 39f2597a) defines
`𝓔_ζ^𝒪 = sup_{g ∈ 𝒪} {A(g) - ζ T(g)}` for `ζ > 0` (`E:raw-occupation-definitions`, lines
10-18) and states that it is finite (lines 129-130).

Wrong variant: the value set of `𝓔_0^𝒪` (penalty `ζ = 0`) is bounded above. Counterexample:
the white model with amplitude `c = 1` (`d = α = 1`, `a = 1/2`, `Γ = δ₀ ≠ 0`): a field of `𝒪`
with `A(g) > 0` exists (`C_occ > 0`) and its dilations have `A(U_ℓ g) = ℓ A(g) → ∞`. Control outside
the manuscript's parameter class (`ζ = 0`, outside the penalty domain `ζ > 0`, line 16), in the
manuscript's model class: a counterexample to extending the boundedness to zero penalty. The
contrast is the package boundedness for `ζ > 0`.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.ClassOBridge
import StratonovichHAMSecondMoment.WhiteModel

set_option autoImplicit false

namespace Refutations.ClassOBridge

open StratonovichHAMSecondMoment StratonovichHAMSecondMoment.ClassOBridge MeasureTheory
open HomogHypothesis (Rd HomogCovariance)

/-- Auxiliary: the white model with `c = 1` has a nonzero covariance. -/
theorem whiteCov_one_ne_zero : WhiteModel.whiteCov 1 ≠ (0 : Measure (Rd 1)) := by
  simp [WhiteModel.whiteCov]

/-- Auxiliary: in the white model with `c = 1`, `a = 1/2`, the value set of `𝓔_0^𝒪` is not
bounded above. -/
theorem white_zeta_zero_not_bddAbove :
    ¬ BddAbove (rawEnergySetO (1 / 2) (WhiteModel.whiteCov 1) 0) := by
  have hH := WhiteModel.white_homogCovariance (c := 1) (a := 1 / 2) zero_le_one (by norm_num)
    (by norm_num)
  have hΓ := whiteCov_one_ne_zero
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

/-- The value set of `𝓔_ζ^𝒪` at `ζ = 0` need not be bounded above. -/
theorem zeta_zero_bddAbove :
    ¬ ∀ (a : ℝ) (Γ μ : Measure (Rd 1)), HomogCovariance 1 1 a Γ μ → Γ ≠ 0 →
      BddAbove (rawEnergySetO a Γ 0) := fun H =>
  white_zeta_zero_not_bddAbove (H _ _ _ (WhiteModel.white_homogCovariance (c := 1)
    (a := 1 / 2) zero_le_one (by norm_num) (by norm_num)) whiteCov_one_ne_zero)

/-- Contrast: for every `ζ > 0` the value set is bounded above. -/
theorem zeta_zero_bddAbove_contrast :
    ∀ (a : ℝ) (Γ μ : Measure (Rd 1)), HomogCovariance 1 1 a Γ μ → Γ ≠ 0 →
      ∀ ζ : ℝ, 0 < ζ → BddAbove (rawEnergySetO a Γ ζ) :=
  fun _ _ _ hH hΓ ζ hζ => ((raw_occupation_energy_whole_paper hH hΓ).2.2.2.2.2.2 ζ hζ).2.1

end Refutations.ClassOBridge
