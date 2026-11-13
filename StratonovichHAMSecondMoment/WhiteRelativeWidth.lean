module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Corollary `C:white-relative-width` (Uniform relative width of the bound
formulas) of `notes/integrated_white_evaluation.tex` at revision `a284420`:
statement lines 130--138, proof lines 140--161.  The two formulas are those
displayed in `T:white-moment-bounds` (`E:white-moment-bounds`, lines 101--111):
`K_0(a) = 2^a/(1-a)` and `M_a = Γ_E((1+a)/2)/(Γ_E(1+a) Γ_E((1-a)/2))`, with
lower formula `(2/3) sqrt(c/M_a)` and upper formula `(2/3) sqrt(c K_0(a))`.
The section's standing parameters (lines 4--9) are `c ≥ 0` and `0 < a < 1`;
the corollary takes `c > 0`.

What is formalized, in full:
* for `c > 0` and `0 < a < 1` the ratio of the upper to the lower formula is
  `sqrt(K_0(a) M_a)`;
* `K_0(a) M_a = sqrt π / (2 Γ_E(1+a/2) Γ_E((3-a)/2))` (the proof's display,
  lines 148--152);
* `sqrt(K_0(a) M_a) ≤ [sqrt π / (2 Γ_E(5/4)²)]^{1/2}`, with equality at
  `a = 1/2`;
* the closing remark of the proof (lines 158--159): the ratio of the bound
  formulas is symmetric under `a ↦ 1-a`.
* `M_a` is also the mass of the temporal equilibrium density of
  `L:temporal-equilibrium`: `boundMass_eq_mass` identifies the displayed
  formula with `TemporalEquilibrium.mass a` for `0 < a < 1`.

Scope (what this module does not claim).  Lean proves the identities and the
inequality between the displayed formulas `K_0(a)` and `M_a` only.  That the
intrinsic moment constant `C_2(c,a)` lies between the lower and upper formulas
is `T:white-moment-bounds`, which is outside Lean and is neither used nor
proved here.  This module does not use or prove anything of
`P:white-spatial-energy` (the CDF square identity, `H^1` profiles, the spatial
energy constant; reserved package B9).

Conventions: `Γ_E` is Mathlib's `Real.Gamma`, `2^a` is `Real.rpow`, the square
roots are `Real.sqrt` and `[·]^{1/2}` is written `Real.sqrt`.  Every quantity
under a square root or in a denominator is shown positive for `0 < a < 1`
(`boundK0_pos`, `boundMass_pos`), so no statement relies on Lean's junk values
`sqrt(negative) = 0` or `x/0 = 0`.

Proof route.  The duplication and recurrence steps are those of the TeX
(`TemporalEquilibrium.gamma_beta_duplication`, `gamma_beta_recurrence`, i.e.
`L:equilibrium-gamma-beta`).  The inequality `Γ_E(5/4)² ≤ Γ_E(x) Γ_E(y)` for
`x + y = 5/2` is proved here from the log-convexity of `Γ_E` on `(0,∞)`
(Mathlib's `Real.convexOn_log_Gamma`), not from Cauchy--Schwarz in Euler's
integral as in the TeX (lines 153--157); the inequality proved is the same.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.TemporalEquilibrium

@[expose] public section

noncomputable section

set_option autoImplicit false

open Real

namespace StratonovichHAMSecondMoment.WhiteRelativeWidth

/-- The upper-bound factor `K_0(a) = 2^a/(1-a)` of `E:white-moment-bounds`
(TeX line 106). -/
def boundK0 (a : ℝ) : ℝ := 2 ^ a / (1 - a)

/-- The lower-bound mass `M_a = Γ_E((1+a)/2)/(Γ_E(1+a) Γ_E((1-a)/2))` of
`E:white-moment-bounds` (TeX lines 107--108). -/
def boundMass (a : ℝ) : ℝ := Gamma ((1 + a) / 2) / (Gamma (1 + a) * Gamma ((1 - a) / 2))

/-- The lower formula `(2/3) sqrt(c/M_a)` of `E:white-moment-bounds` (TeX line 104). -/
def lowerFormula (c a : ℝ) : ℝ := 2 / 3 * sqrt (c / boundMass a)

/-- The upper formula `(2/3) sqrt(c K_0(a))` of `E:white-moment-bounds` (TeX line 105). -/
def upperFormula (c a : ℝ) : ℝ := 2 / 3 * sqrt (c * boundK0 a)

/-- The constant `sqrt π / (2 Γ_E(5/4)²)` of `C:white-relative-width` (TeX
line 134), before the square root. -/
def widthConst : ℝ := sqrt π / (2 * Gamma (5 / 4) ^ 2)

/-- `K_0(a) > 0` for `a < 1` (the TeX's sign condition `0 < a < 1`, lines 124--125). -/
theorem boundK0_pos {a : ℝ} (ha1 : a < 1) : 0 < boundK0 a :=
  div_pos (rpow_pos_of_pos two_pos a) (by linarith)

/-- `M_a > 0` for `0 < a < 1` (TeX lines 124--125: "All Gamma factors are positive
finite for `0 < a < 1`"). -/
theorem boundMass_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 0 < boundMass a := by
  have := Gamma_pos_of_pos (by linarith : (0:ℝ) < (1 + a) / 2)
  have := Gamma_pos_of_pos (by linarith : (0:ℝ) < (1 - a) / 2)
  have := Gamma_pos_of_pos (by linarith : (0:ℝ) < 1 + a)
  unfold boundMass; positivity

/-- The displayed `M_a` is the mass `∫_0^1 f_a` of the temporal equilibrium
density of `L:temporal-equilibrium` (`TemporalEquilibrium.mass_eq`), for
`0 < a < 1`. -/
theorem boundMass_eq_mass {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    boundMass a = TemporalEquilibrium.mass a :=
  ((TemporalEquilibrium.mass_eq ha0 ha1).2).symm

/-- Proof step (TeX lines 141--147, duplication): for every real `a`,
`Γ_E(1+a) = 2^a Γ_E((1+a)/2) Γ_E(1+a/2)/sqrt π`
(`L:equilibrium-gamma-beta` at `x = (1+a)/2`). -/
theorem gamma_one_add_dup (a : ℝ) :
    Gamma (1 + a) = 2 ^ a * Gamma ((1 + a) / 2) * Gamma (1 + a / 2) / sqrt π := by
  have h := TemporalEquilibrium.gamma_beta_duplication_general ((1 + a) / 2)
  rw [show 2 * ((1 + a) / 2) = 1 + a by ring, show 1 + a - 1 = a by ring,
    show (1 + a) / 2 + 1 / 2 = 1 + a / 2 by ring] at h
  exact h

/-- Proof step (TeX lines 141--147, recurrence): for `a < 1`,
`(1-a) Γ_E((1-a)/2) = 2 Γ_E((3-a)/2)`. -/
theorem gamma_three_sub_rec {a : ℝ} (ha1 : a < 1) :
    (1 - a) * Gamma ((1 - a) / 2) = 2 * Gamma ((3 - a) / 2) := by
  have h := TemporalEquilibrium.gamma_beta_recurrence (x := (1 - a) / 2) (by linarith)
  rw [show (1 - a) / 2 + 1 = (3 - a) / 2 by ring] at h
  rw [h]; ring

/-- Proof display (TeX lines 148--152): for `0 < a < 1`,
`K_0(a) M_a = sqrt π / (2 Γ_E(1+a/2) Γ_E((3-a)/2))`. -/
theorem boundK0_mul_boundMass {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    boundK0 a * boundMass a = sqrt π / (2 * Gamma (1 + a / 2) * Gamma ((3 - a) / 2)) := by
  have hG1 := Gamma_pos_of_pos (by linarith : (0:ℝ) < (1 + a) / 2)
  have hG2 := Gamma_pos_of_pos (by linarith : (0:ℝ) < (1 - a) / 2)
  have hG3 := Gamma_pos_of_pos (by linarith : (0:ℝ) < 1 + a / 2)
  have hG4 := Gamma_pos_of_pos (by linarith : (0:ℝ) < (3 - a) / 2)
  have h2a : 0 < (2:ℝ) ^ a := rpow_pos_of_pos two_pos a
  have hpi : 0 < sqrt π := sqrt_pos.2 pi_pos
  have h1a : 0 < 1 - a := by linarith
  have hrec := gamma_three_sub_rec ha1
  unfold boundK0 boundMass
  rw [gamma_one_add_dup a]
  rw [div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]
  field_simp
  linear_combination -hrec

/-- Auxiliary (Lean route; replaces the TeX's Cauchy--Schwarz in Euler's
integral, lines 153--157): midpoint log-convexity of `Γ_E`,
`Γ_E((x+y)/2)² ≤ Γ_E(x) Γ_E(y)` for `x, y > 0`, from
`Real.convexOn_log_Gamma`. -/
theorem gamma_mid_sq_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Gamma ((x + y) / 2) ^ 2 ≤ Gamma x * Gamma y := by
  have h := convexOn_log_Gamma.2 (Set.mem_Ioi.2 hx) (Set.mem_Ioi.2 hy)
    (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul, Function.comp_apply] at h
  have hm : (1 / 2 : ℝ) * x + 1 / 2 * y = (x + y) / 2 := by ring
  rw [hm] at h
  have hg := Gamma_pos_of_pos (by linarith : 0 < (x + y) / 2)
  have := exp_le_exp.2 (by linarith : 2 * log (Gamma ((x + y) / 2)) ≤
      log (Gamma x) + log (Gamma y))
  rw [exp_add, exp_log (Gamma_pos_of_pos hx), exp_log (Gamma_pos_of_pos hy),
    ← log_rpow hg, exp_log (by positivity)] at this
  simpa using this

/-- Proof step (TeX lines 153--157): for `0 < a < 1`, with `x = 1+a/2`,
`y = (3-a)/2` (so `x + y = 5/2`), `Γ_E(5/4)² ≤ Γ_E(1+a/2) Γ_E((3-a)/2)`.  The
TeX proves it by Cauchy--Schwarz in Euler's integral; Lean proves it from the
auxiliary log-convexity lemma `gamma_mid_sq_le`. -/
theorem gamma_five_quarters_sq_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    Gamma (5 / 4) ^ 2 ≤ Gamma (1 + a / 2) * Gamma ((3 - a) / 2) := by
  have h := gamma_mid_sq_le (x := 1 + a / 2) (y := (3 - a) / 2) (by linarith) (by linarith)
  rwa [show (1 + a / 2 + (3 - a) / 2) / 2 = 5 / 4 by ring] at h

/-- The inequality of `C:white-relative-width` before the square root: for
`0 < a < 1`, `K_0(a) M_a ≤ sqrt π / (2 Γ_E(5/4)²)`. -/
theorem boundK0_mul_boundMass_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    boundK0 a * boundMass a ≤ widthConst := by
  rw [boundK0_mul_boundMass ha0 ha1, widthConst, mul_assoc]
  have hG := Gamma_pos_of_pos (by norm_num : (0:ℝ) < 5 / 4)
  have hpi : 0 < sqrt π := sqrt_pos.2 pi_pos
  exact div_le_div_of_nonneg_left hpi.le (by positivity)
    (by linarith [gamma_five_quarters_sq_le ha0 ha1])

/-- The inequality of `C:white-relative-width` (TeX lines 133--136): for
`0 < a < 1`, `sqrt(K_0(a) M_a) ≤ [sqrt π / (2 Γ_E(5/4)²)]^{1/2}`. -/
theorem relative_width_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    sqrt (boundK0 a * boundMass a) ≤ sqrt widthConst :=
  sqrt_le_sqrt (boundK0_mul_boundMass_le ha0 ha1)

/-- Equality at `a = 1/2` (TeX lines 137, 157--158):
`sqrt(K_0(1/2) M_{1/2}) = [sqrt π / (2 Γ_E(5/4)²)]^{1/2}`. -/
theorem relative_width_eq_half :
    sqrt (boundK0 (1 / 2) * boundMass (1 / 2)) = sqrt widthConst := by
  rw [boundK0_mul_boundMass (by norm_num) (by norm_num), widthConst]
  congr 1
  rw [show (1:ℝ) + 1 / 2 / 2 = 5 / 4 by norm_num, show ((3:ℝ) - 1 / 2) / 2 = 5 / 4 by norm_num]
  ring

/-- The closing remark of the proof (TeX lines 158--159): the ratio of the bound
formulas is symmetric under `a ↦ 1-a`, for `0 < a < 1`. -/
theorem boundK0_mul_boundMass_symm {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    boundK0 (1 - a) * boundMass (1 - a) = boundK0 a * boundMass a := by
  rw [boundK0_mul_boundMass (by linarith) (by linarith), boundK0_mul_boundMass ha0 ha1,
    show 1 + (1 - a) / 2 = (3 - a) / 2 by ring, show (3 - (1 - a)) / 2 = 1 + a / 2 by ring]
  ring

/-- For `c > 0` and `0 < a < 1` the ratio of the upper to the lower formula of
`E:white-moment-bounds` is `sqrt(K_0(a) M_a)` (TeX lines 132--133). -/
theorem ratio_eq {c a : ℝ} (hc : 0 < c) (ha0 : 0 < a) (ha1 : a < 1) :
    upperFormula c a / lowerFormula c a = sqrt (boundK0 a * boundMass a) := by
  have hK := boundK0_pos ha1
  have hM := boundMass_pos ha0 ha1
  unfold upperFormula lowerFormula
  rw [mul_div_mul_left _ _ (by norm_num : (2:ℝ) / 3 ≠ 0), sqrt_div' _ hM.le,
    div_div_eq_mul_div, sqrt_mul hc.le, sqrt_mul hK.le]
  have hsc : 0 < sqrt c := sqrt_pos.2 hc
  field_simp

/-- Corollary `C:white-relative-width` (TeX lines 130--138) under its exact
hypotheses (`c > 0`, line 132; the section's `0 < a < 1`, line 5): the ratio of
the upper formula `(2/3) sqrt(c K_0(a))` to the lower formula
`(2/3) sqrt(c/M_a)` of `E:white-moment-bounds` is `sqrt(K_0(a) M_a)`, it is at
most `[sqrt π/(2 Γ_E(5/4)²)]^{1/2}`, and equality holds at `a = 1/2`.  Lean
proves these statements about the displayed formulas only: that `C_2(c,a)` lies
between the two formulas is `T:white-moment-bounds`, outside Lean, and nothing
of `P:white-spatial-energy` (reserved package B9) is used or proved. -/
theorem white_relative_width_paper {c a : ℝ} (hc : 0 < c) (ha0 : 0 < a) (ha1 : a < 1) :
    upperFormula c a / lowerFormula c a = sqrt (boundK0 a * boundMass a) ∧
      sqrt (boundK0 a * boundMass a) ≤ sqrt (sqrt π / (2 * Gamma (5 / 4) ^ 2)) ∧
      (a = 1 / 2 → sqrt (boundK0 a * boundMass a) = sqrt (sqrt π / (2 * Gamma (5 / 4) ^ 2))) :=
  ⟨ratio_eq hc ha0 ha1, relative_width_le ha0 ha1, fun h => h ▸ relative_width_eq_half⟩

end StratonovichHAMSecondMoment.WhiteRelativeWidth
