module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave item L10-W1: Theorem `T:white-moment-bounds` (Explicit white moment bounds) of
`notes/integrated_white_evaluation.tex` at revision 39f2597a (statement lines 140-151, proof
lines 153-167), stated for the variational value `S_2^pos` (not for `C_2(c,a)`), on the
spatial white-noise model of the same section (lines 4-9: `d = α = 1`, `Γ = c δ₀`, temporal
kernel `|s-t|^{-a}`, `0 < a < 1`).

Objects reused, not redefined: `Γ = WhiteModel.whiteCov c`, `μ = WhiteModel.whiteSpectral c`
(wave item L10-W0), `S_2^pos = sSup (VariationalRate.scoreSet a Γ 2)`,
`𝓔_sp = SpatialFourLinear.Esp`, `F₀ = SpatialFourLinear.F0`, `K₀ = SpatialBracket.K0`
(`= WhiteRelativeWidth.boundK0`), `M_a = WhiteRelativeWidth.boundMass`
(`= TemporalEquilibrium.mass`), the two formulas `WhiteRelativeWidth.lowerFormula c a =
(2/3)√(c/M_a)` and `upperFormula c a = (2/3)√(c K₀)` (lines 143-144), `C_occ =
RawOccupationEnergy.Cocc`, `𝓔_{1/2}^𝒪 = RawOccupationEnergy.EO a Γ (1/2)`.  New definition:
the named input `WhiteSpatialEnergy`.

Supplied input (named hypothesis `WhiteSpatialEnergy c`): `𝓔_sp(c δ₀) = c²/6`, the energy half
of `P:white-spatial-energy` (lines 79-133).  That proposition is reserved (package B9) and is
neither proved nor attempted here.  Each half of the bracket uses one inequality of it only:
the lower half uses `c²/6 ≤ 𝓔_sp` (attainment by the `sech` profile, lines 106-124), the upper
half uses `𝓔_sp ≤ c²/6` (the CDF square, lines 88-100 and 117-121); the one-sided theorems
`white_moment_lower_of_ge` and `white_moment_upper_of_le` record this.

Formalized:
* `whiteCov_ne_zero`: `c δ₀ ≠ 0` for `c > 0` (the standing assumption `Γ ≠ 0` of
  `integrated_occupation_ceiling.tex` lines 20-21 holds); `whiteCov_zero`: `0 δ₀ = 0`.
* `F0_mono` (monotonicity of `F₀` on `[0,∞)`), `ceilingValue_mono` (of `U_𝔠` in `C_occ`).
* `white_moment_lower_of_ge`, `white_moment_upper_of_le`: the two halves of
  `E:white-moment-bounds` for `S_2^pos`, each on its one-sided half of the input.
* `white_moment_bounds_paper` (headline): for `c > 0`, `0 < a < 1` and `WhiteSpatialEnergy c`,
  the coefficient-two value set is bounded above and
  `(2/3)√(c/M_a) ≤ S_2^pos ≤ (2/3)√(c K₀(a))`, with `K₀(a) = 2^a/(1-a)` and
  `M_a = Γ_E((1+a)/2)/(Γ_E(1+a)Γ_E((1-a)/2))` written out as in lines 143-147; and both
  formulas are positive and finite (`0 < lower ≤ upper` follows).
* `white_moment_upper_exact_paper`: the upper bound through the exact constant `C_occ` of wave
  item L9-A2 (`OccupationCeilingExact`): `S_2^pos ≤ 2^m F₀(𝓔_{1/2}^𝒪) ≤ (2/3)√(c K₀(a))` and
  `2^m F₀(𝓔_{1/2}^𝒪) < 2^m F_a(𝓔_{1/2}^𝒪)`, on the upper half of the input.  It is at least
  as sharp as the upper formula; whether it is strictly sharper for the white model is not
  decided (`C_occ` is not evaluated, only `C_occ ≤ K₀ R_sp`).

Narrower than the TeX (recorded):
* stated for `S_2^pos`, not for `C_2(c,a)`: the identification `C_2 = S_2^pos` is
  `T:intrinsic-second-moment` (stochastic, foundation D1), used in line 162 through
  `C:intrinsic-spatial-bracket`; the sentence "Its time exponent is `(3-a)/2`" (line 149) is a
  statement about `C_2` and is out with it;
* `c = 0` is out (decision 4 of wave L10): `c δ₀ = 0` violates the standing `Γ ≠ 0` of the
  bracket, and the TeX's argument there (lines 164-165) uses `T:intrinsic-second-moment`;
* `𝓔_sp = c²/6` is the named input above, not proved.
Route: as in the TeX (lines 153-163): `SpatialBracket`'s bracket at `α = 1`, `k = 2`,
`m = 3/2`, the white model `HomogCovariance 1 1 a` of `WhiteModel.white_homogCovariance`, and
the arithmetic `WhiteModel.white_bracket_lower`/`white_bracket_upper` at `z = c²/6`.

Reused from the integration module `L8Completed` (one copy): the named input
`SpatialBracket.OccupationCeilingK0` of the bracket's upper half
(`L8Completed.occupationCeilingK0_holds`), and the two halves of the bracket under the standing
assumptions alone (`L8Completed.spatial_bracket_lower_sSup_paper_completed`,
`L8Completed.spatial_bracket_upper_paper_completed`).

Implicit hypotheses made explicit: `Γ ≠ 0` (proved, `whiteCov_ne_zero`), `S1Bdd` (discharged
inside `L8Completed.spatial_bracket_lower_sSup_paper_completed`), `0 ≤ 𝓔_sp` (from
`spatial_energy_value_paper_completed`).  No hypothesis is carried unused: `0 < a` and `a < 1`
enter `H:homog` and the positivity of `M_a`, `c > 0` enters `Γ ≠ 0`.  Lemmas marked "Auxiliary
to the Lean proof route" have no manuscript label.  No fallback was needed.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.WhiteModel
public import StratonovichHAMSecondMoment.SpatialBracket
public import StratonovichHAMSecondMoment.L8Completed
public import StratonovichHAMSecondMoment.OccupationCeilingExact

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Real

namespace StratonovichHAMSecondMoment.WhiteMomentBounds

open HomogHypothesis (Rd HomogCovariance)
open WhiteModel (whiteCov whiteSpectral)
open VariationalRate (scoreSet)
open VariationalDilation (CPos)
open SpatialFourLinear (Esp Rsp F0 energyValue)
open WhiteRelativeWidth (boundMass boundK0 lowerFormula upperFormula)

variable {d : ℕ}

/-! ### The named input -/

/-- Supplied input (`P:white-spatial-energy`, `integrated_white_evaluation.tex` lines 79-133 at
39f2597a, reserved as package B9 and not proved here): the spatial energy of the white
covariance is `𝓔_sp(c δ₀) = c²/6`. -/
def WhiteSpatialEnergy (c : ℝ) : Prop := Esp (whiteCov c) = c ^ 2 / 6

/-! ### The standing assumption `Γ ≠ 0` and the ceiling -/

/-- `c δ₀ ≠ 0` for `c > 0`. -/
theorem whiteCov_ne_zero {c : ℝ} (hc : 0 < c) : whiteCov c ≠ 0 := by
  intro h
  have h1 := congrArg (fun ν : Measure (Rd 1) => ν Set.univ) h
  simp only [whiteCov, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one,
    Measure.coe_zero, Pi.zero_apply, ENNReal.ofReal_eq_zero] at h1
  linarith

/-- `0 δ₀ = 0`: at `c = 0` the standing assumption `Γ ≠ 0` fails. -/
theorem whiteCov_zero : whiteCov 0 = 0 := by
  simp [whiteCov]

/-! ### Monotonicity -/

/-- Auxiliary to the Lean proof route: `F₀` is monotone on `[0,∞)` for `α < 2`. -/
theorem F0_mono {alpha z w : ℝ} (ha2 : alpha < 2) (hz : 0 ≤ z) (hzw : z ≤ w) :
    F0 alpha z ≤ F0 alpha w := by
  have h2a : 0 < 2 - alpha := by linarith
  have hk : 0 < 3 - alpha := by linarith
  have hq : 0 < 8 * (4 - alpha) ^ ((4 - alpha) / 2) :=
    mul_pos (by norm_num) (rpow_pos_of_pos (by linarith) _)
  have hzz : 0 ≤ 2 * z / (2 - alpha) := div_nonneg (by linarith) h2a.le
  have hzw' : 2 * z / (2 - alpha) ≤ 2 * w / (2 - alpha) :=
    div_le_div_of_nonneg_right (by linarith) h2a.le
  unfold F0
  refine mul_le_mul_of_nonneg_left (rpow_le_rpow (div_nonneg (rpow_nonneg hzz _) hq.le) ?_
    (div_nonneg zero_le_one hk.le)) hk.le
  exact div_le_div_of_nonneg_right (rpow_le_rpow hzz hzw' (by linarith)) hq.le

/-- Auxiliary to the Lean proof route: `U_𝔠[C]` (`SpatialBracket.ceilingValue`) is monotone in
`C ≥ 0` for `0 < α < 2`, `𝔠 ≥ 0`. -/
theorem ceilingValue_mono {alpha c C D : ℝ} (ha0 : 0 < alpha) (ha2 : alpha < 2) (hc : 0 ≤ c)
    (hC : 0 ≤ C) (hCD : C ≤ D) :
    SpatialBracket.ceilingValue alpha c C ≤ SpatialBracket.ceilingValue alpha c D := by
  have hk : 0 < 3 - alpha := by linarith
  have hq : 0 < 8 * (4 - alpha) ^ ((4 - alpha) / 2) :=
    mul_pos (by norm_num) (rpow_pos_of_pos (by linarith) _)
  have hα : 0 ≤ alpha ^ (alpha / 2) := rpow_nonneg ha0.le _
  unfold SpatialBracket.ceilingValue
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (rpow_le_rpow
    (div_nonneg (mul_nonneg hα hC) hq.le) ?_ (div_nonneg zero_le_one hk.le)) hk.le)
    (rpow_nonneg hc _)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hCD hα) hq.le

/-! ### The two halves -/

/-- **Lower half of `E:white-moment-bounds` for `S_2^pos`** (`integrated_white_evaluation.tex`
lines 143, 153-163 at 39f2597a), on the lower half `c²/6 ≤ 𝓔_sp` of the input: for `c > 0`,
`0 < a < 1`, `(2/3)√(c/M_a) ≤ S_2^pos`.  Narrower: `S_2^pos`, not `C_2`. -/
theorem white_moment_lower_of_ge {c a : ℝ} (hc : 0 < c) (ha0 : 0 < a) (ha1 : a < 1)
    (hge : c ^ 2 / 6 ≤ Esp (whiteCov c)) :
    lowerFormula c a ≤ sSup (scoreSet a (whiteCov c) 2) := by
  have hH := WhiteModel.white_homogCovariance hc.le ha0 ha1
  have hΓ := whiteCov_ne_zero hc
  have hlow := L8Completed.spatial_bracket_lower_sSup_paper_completed hH hΓ
  have hM := TemporalEquilibrium.mass_pos ha0 ha1
  rw [← WhiteModel.white_bracket_lower hc.le ha0 ha1, mul_assoc]
  refine le_trans ?_ hlow
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (F0_mono (by norm_num) (by positivity) hge) (rpow_nonneg hM.le _))
    (rpow_nonneg zero_le_two _)

/-- **Upper half of `E:white-moment-bounds` for `S_2^pos`** (`integrated_white_evaluation.tex`
lines 144, 153-163 at 39f2597a), on the upper half `𝓔_sp ≤ c²/6` of the input: for `c > 0`,
`0 < a < 1`, the coefficient-two value set is bounded above and
`S_2^pos ≤ (2/3)√(c K₀(a))`.  Narrower: `S_2^pos`, not `C_2`. -/
theorem white_moment_upper_of_le {c a : ℝ} (hc : 0 < c) (ha0 : 0 < a) (ha1 : a < 1)
    (hle : Esp (whiteCov c) ≤ c ^ 2 / 6) :
    BddAbove (scoreSet a (whiteCov c) 2) ∧
      sSup (scoreSet a (whiteCov c) 2) ≤ upperFormula c a := by
  have hH := WhiteModel.white_homogCovariance hc.le ha0 ha1
  have hΓ := whiteCov_ne_zero hc
  obtain ⟨hbdd, hup⟩ := L8Completed.spatial_bracket_upper_paper_completed hH hΓ
  obtain ⟨-, -, -, hE0, -⟩ :=
    SpatialOccupationL7Completed.spatial_energy_value_paper_completed hH hΓ
  have hK := SpatialBracket.K0_pos ha1
  refine ⟨hbdd, hup.trans ?_⟩
  rw [← WhiteModel.white_bracket_upper hc.le ha1]
  exact mul_le_mul_of_nonneg_left (F0_mono (by norm_num) hE0.le hle)
    (mul_nonneg (rpow_nonneg zero_le_two _) (rpow_nonneg hK.le _))

/-! ### The theorem -/

/-- **`T:white-moment-bounds` for `S_2^pos`** (`integrated_white_evaluation.tex` lines 140-151,
proof 153-167, at 39f2597a): for the white model `Γ = c δ₀` (`d = α = 1`) with `c > 0`,
`0 < a < 1`, and the supplied input `WhiteSpatialEnergy c` (`𝓔_sp = c²/6`,
`P:white-spatial-energy`), the coefficient-two value set is bounded above,
`(2/3)√(c/M_a) ≤ S_2^pos ≤ (2/3)√(c K₀(a))` with `K₀(a) = 2^a/(1-a)` and
`M_a = Γ_E((1+a)/2)/(Γ_E(1+a)Γ_E((1-a)/2))` (`E:white-moment-bounds`), and `M_a`, `K₀(a)`
and both bound formulas are positive.  Narrower: `S_2^pos` in place of `C_2(c,a)`
(`T:intrinsic-second-moment`, D1); the time exponent sentence and `c = 0` are out. -/
theorem white_moment_bounds_paper {c a : ℝ} (hc : 0 < c) (ha0 : 0 < a) (ha1 : a < 1)
    (hE : WhiteSpatialEnergy c) :
    BddAbove (scoreSet a (whiteCov c) 2) ∧
      2 / 3 * √(c / (Gamma ((1 + a) / 2) / (Gamma (1 + a) * Gamma ((1 - a) / 2)))) ≤
        sSup (scoreSet a (whiteCov c) 2) ∧
      sSup (scoreSet a (whiteCov c) 2) ≤ 2 / 3 * √(c * (2 ^ a / (1 - a))) ∧
      0 < Gamma ((1 + a) / 2) / (Gamma (1 + a) * Gamma ((1 - a) / 2)) ∧
      0 < 2 ^ a / (1 - a) ∧
      0 < 2 / 3 * √(c / (Gamma ((1 + a) / 2) / (Gamma (1 + a) * Gamma ((1 - a) / 2)))) ∧
      0 < 2 / 3 * √(c * (2 ^ a / (1 - a))) := by
  have hM : 0 < boundMass a := WhiteRelativeWidth.boundMass_pos ha0 ha1
  have hK : 0 < boundK0 a := WhiteRelativeWidth.boundK0_pos ha1
  obtain ⟨hbdd, hup⟩ := white_moment_upper_of_le hc ha0 ha1 hE.le
  exact ⟨hbdd, white_moment_lower_of_ge hc ha0 ha1 hE.ge, hup, hM, hK,
    mul_pos (by norm_num) (sqrt_pos.2 (div_pos hc hM)),
    mul_pos (by norm_num) (sqrt_pos.2 (mul_pos hc hK))⟩

/-- **The upper bound through the exact `C_occ`** (wave item L9-A2,
`OccupationCeilingExact.intrinsic_spatial_comparison_paper`; the comparison of
`C:intrinsic-spatial-bracket`, `integrated_occupation_ceiling.tex` lines 328-332, at the white
model), on the upper half `𝓔_sp ≤ c²/6` of the input: for `c > 0`, `0 < a < 1`,
`S_2^pos ≤ 2^m F₀(𝓔_{1/2}^𝒪) ≤ (2/3)√(c K₀(a))` and `2^m F₀(𝓔_{1/2}^𝒪) < 2^m F_a(𝓔_{1/2}^𝒪)`
(`m = 3/2`).  The middle bound is at least as sharp as the upper formula of
`E:white-moment-bounds`; strict sharpness is not claimed (`C_occ` is not evaluated). -/
theorem white_moment_upper_exact_paper {c a : ℝ} (hc : 0 < c) (ha0 : 0 < a) (ha1 : a < 1)
    (hle : Esp (whiteCov c) ≤ c ^ 2 / 6) :
    sSup (scoreSet a (whiteCov c) 2) ≤
        2 ^ (((4 : ℝ) - 1) / (3 - 1)) *
          F0 1 (RawOccupationEnergy.EO a (whiteCov c) (1 / 2)) ∧
      2 ^ (((4 : ℝ) - 1) / (3 - 1)) * F0 1 (RawOccupationEnergy.EO a (whiteCov c) (1 / 2)) ≤
        upperFormula c a ∧
      2 ^ (((4 : ℝ) - 1) / (3 - 1)) * F0 1 (RawOccupationEnergy.EO a (whiteCov c) (1 / 2)) <
        2 ^ (((4 : ℝ) - 1) / (3 - 1)) *
          SpatialBracket.Fb 1 a (RawOccupationEnergy.EO a (whiteCov c) (1 / 2)) := by
  have hH := WhiteModel.white_homogCovariance hc.le ha0 ha1
  have hΓ := whiteCov_ne_zero hc
  obtain ⟨-, -, hS, hlt⟩ := OccupationCeilingExact.intrinsic_spatial_comparison_paper hH hΓ
  refine ⟨hS, ?_, hlt⟩
  obtain ⟨-, -, -, -, hU⟩ :=
    OccupationCeilingExact.intrinsic_occupation_ceiling_paper hH hΓ 2 two_pos
  have hU2 := hU (1 / 2) (by norm_num)
  rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_rpow, mul_one] at hU2
  obtain ⟨-, -, hC0, hCle, -⟩ := RawOccupationEnergy.raw_occupation_energy_paper hH hΓ
  obtain ⟨-, -, hEv, hE0, hRsp⟩ :=
    SpatialOccupationL7Completed.spatial_energy_value_paper_completed hH hΓ
  obtain ⟨-, -, -, -, hR0, -, -⟩ := SpatialSmoothRatio.spatial_smooth_ratio_R0_paper hH hΓ
  have hRs : 0 ≤ Rsp (whiteCov c) 1 := by rw [hRsp]; exact hR0.le
  have hK := SpatialBracket.K0_pos ha1
  rw [← hU2]
  calc SpatialBracket.ceilingValue 1 2 (RawOccupationEnergy.Cocc a 1 (whiteCov c))
      ≤ SpatialBracket.ceilingValue 1 2 (SpatialBracket.K0 a * Rsp (whiteCov c) 1) :=
        ceilingValue_mono one_pos (by norm_num) zero_le_two hC0.le hCle
    _ = 2 ^ (((4 : ℝ) - 1) / (3 - 1)) * SpatialBracket.K0 a ^ (1 / ((3 : ℝ) - 1)) *
          F0 1 (Esp (whiteCov c)) := by
        rw [SpatialBracket.ceilingValue_mul one_pos (by norm_num) hK.le hRs, hEv]
    _ ≤ 2 ^ (((4 : ℝ) - 1) / (3 - 1)) * boundK0 a ^ (1 / ((3 : ℝ) - 1)) *
          F0 1 (c ^ 2 / 6) :=
        mul_le_mul_of_nonneg_left (F0_mono (by norm_num) hE0.le hle)
          (mul_nonneg (rpow_nonneg zero_le_two _) (rpow_nonneg hK.le _))
    _ = upperFormula c a := WhiteModel.white_bracket_upper hc.le ha1

end StratonovichHAMSecondMoment.WhiteMomentBounds
