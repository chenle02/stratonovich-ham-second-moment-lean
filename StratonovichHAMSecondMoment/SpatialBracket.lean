module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Corollary `C:intrinsic-spatial-bracket` (A common spatial-energy bracket) of
`notes/integrated_occupation_ceiling.tex` at revision a284420 (statement lines 252-266, proof
lines 268-300), together with the scalar map `E:occupation-scalar-map` (lines 195-203) and the
second form of `E:occupation-score-ceiling` (lines 208-216), stated for the variational value
`S_2^pos` (not for `C_2`).

Standing assumptions (section setup, lines 4-21 of the same file): `H:homog` via
`HomogHypothesis.HomogCovariance d α α₀ Γ μ`, `a = α₀`, `q = 4-α`, `k = 3-α`, `m = q/k`,
and `Γ ≠ 0` (lines 20-21: "Assume `Γ ≠ 0` until the direct zero case below").

Objects reused, not redefined: `S_c^pos = sSup (VariationalRate.scoreSet α₀ Γ c)`
(`P:variational-positive-scores`, `integrated_unmasked_variational.tex` lines 270-284; every
other line number in this module is in `integrated_occupation_ceiling.tex`),
`VariationalRate.S1Bdd`, `VariationalRate.S1pos`, `C_pos = VariationalDilation.CPos`,
`I_Ψ = VariationalDilation.integratedRate`, `v_Ψ = VariationalDilation.rawCost`,
`R_sp = SpatialFourLinear.Rsp`, `𝓔_sp = SpatialFourLinear.Esp`, `F₀ = SpatialFourLinear.F0`,
`M_a = TemporalEquilibrium.mass`, the energy map value `SpatialFourLinear.energyValue`.
New definitions: `K0` (`K_0 = 2^a/(1-a)`, line 94), `coef` and `Fb` (`F_b`,
`E:occupation-scalar-map`, lines 195-201), `logGap` (`Δ`, lines 276-279), `Dzeta`
(`D_ζ`, `E:raw-occupation-energy`, lines 99-104), `ceilingValue` (`U_𝔠` of
`E:occupation-score-ceiling` with `C_occ` replaced by a real argument `C`, lines 208-213), and
the named input `OccupationCeilingK0`.

Formalized:
* scalar facts (general, no covariance): `Fb_zero` (`F_b(0) = 0`), `Fb_zero_eq_F0` (`F_0` of
  line 202 is `SpatialFourLinear.F0`), `logGap_pos` (`Δ > 0` for `a > 0`, `q - 2a > 0`, lines
  276-283, by strict convexity of `x log x`), `log_Fb_ratio` (`log(F_a(z)/F_0(z)) = Δ/k`, line
  286), `F0_lt_Fa`, `ceilingValue_eq_zeta` (second form of `E:occupation-score-ceiling`, lines
  214-215, for every `ζ > 0` with `𝓔_ζ^𝒪` replaced by `D_ζ C^{2/(2-α)}`, i.e. the right side of
  `E:raw-occupation-energy` at `C_occ = C`), `ceiling_ratio_exp` (lines 287-288), and the
  numerical counterexample at `ζ = 1`, `α = 5/4`, `a = 1/2` (lines 290-298):
  `counterexample_integers` (the two integers and their order, `norm_num`), `counterexample_log`,
  `counterexample_ratio`;
* `spatial_bracket_lower_paper` (lower half of `E:intrinsic-spatial-bracket` for `S_2^pos`,
  existential form), `spatial_bracket_lower_sSup_paper` (`sSup` form on `S1Bdd`),
  `spatial_bracket_upper_paper` (upper half on the named input), and
  `intrinsic_spatial_bracket_paper` (both halves, the comparison and `Δ > 0`, on the named
  input alone; `S1Bdd` is derived from it by `S1Bdd_of_ceiling`).

Supplied input (named hypothesis `OccupationCeilingK0 α α₀ Γ`): for every `c > 0` and every
`Ψ ∈ C_pos`, `c I_Ψ - v_Ψ/2 ≤ U_c` with `C_occ` replaced by `K_0 R_sp`.  It stands for
`T:intrinsic-occupation-ceiling` (`E:occupation-score-ceiling`, lines 205-220) combined with
`C_occ ≤ K_0 R_sp` of `P:raw-occupation-energy` (lines 92-97), exactly as the corollary's proof
uses them (lines 269-271), and is no stronger: `U_c` is increasing in `C_occ`, and the pointwise
form is equivalent to "the value set is bounded above and `S_c^pos ≤ U_c`" because the value
sets are nonempty.  Wave item L8-c (steps (a)-(d) of the feasibility report R2, section 3, with
step (e) at integration) proves it; the integrator instantiates it.

Narrower than the TeX (recorded):
* the corollary is stated for `S_2^pos`, not for `C_2(Γ,a)`: the identification `C_2 = S_2^pos`
  is `T:intrinsic-second-moment` (stochastic, decision 4 of wave L8), used in lines 269-273;
* the comparison `C_2 ≤ 2^m F_0(𝓔_{1/2}^𝒪) < 2^m F_a(𝓔_{1/2}^𝒪)` (lines 261-265) is stated
  with `𝓔_{1/2}^𝒪 = D_{1/2} C_occ^{2/(2-α)}` replaced by `D_{1/2}(K_0R_sp)^{2/(2-α)} =
  energyValue α (K_0 R_sp)`: the class `𝒪` with the original kernel, `A(g)`, `C_occ` and
  `𝓔_ζ^𝒪` are not formalized (decision 4); the scalar identities are stated for every
  real `C ≥ 0` (`C > 0` in the ratio identity) in place of `C_occ`;
* the lower half in the `sSup` form needs `S1Bdd` (`spatial_bracket_lower_sSup_paper`) or the
  named input (`intrinsic_spatial_bracket_paper`, which derives `S1Bdd`); the existential form
  needs neither;
* the direct zero case `Γ = 0` (lines 302-307, after the corollary) is not formalized: every
  wrapper carries `Γ ≠ 0`, the section's standing assumption of lines 20-21.
`HomogCovariance` is passed whole to the cited package wrappers; no field is claimed unused.
Proof route: as in the TeX (lines 268-300) for `S_2^pos`.  The lower half multiplies
`E:spatial-static-energy-score` by `2^m`: the existential form through
`E:variational-score-set-scaling` (dilating one control), the `sSup` form through
`E:variational-score-homogeneity` (`S_2^pos = 2^m S_1^pos`); the TeX's further step to `C_2`
(`T:intrinsic-second-moment`, lines 271-272) is out of scope.  `Δ > 0` uses the strict midpoint
convexity of `x log x` (one of the two arguments the TeX names, lines 280-283).
Lemmas marked "Auxiliary to the Lean proof route" have no manuscript label.  The fallback
scope was not needed.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.SpatialOccupationL7Completed
public import StratonovichHAMSecondMoment.VariationalRate

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Real Filter

namespace StratonovichHAMSecondMoment.SpatialBracket

open HomogHypothesis (Rd HomogCovariance)
open VariationalDilation (CPos integratedRate rawCost dil)
open VariationalRate (scoreSet score1Set S1Bdd S1pos)
open SpatialFourLinear (Rsp Esp energyValue F0)

variable {d : ℕ}

/-! ### Scalar objects -/

/-- `K_0 = 2^a/(1-a)` (TeX line 94, `P:raw-occupation-energy`). -/
def K0 (a : ℝ) : ℝ := 2 ^ a / (1 - a)

/-- The coefficient `(q-2b)^{(q-2b)/2}/(8(q-b)^{q-b})` of `E:occupation-scalar-map` (TeX lines
197-200), `q = 4-α`. -/
def coef (alpha b : ℝ) : ℝ :=
  (4 - alpha - 2 * b) ^ ((4 - alpha - 2 * b) / 2) / (8 * (4 - alpha - b) ^ (4 - alpha - b))

/-- `F_b(z) = k[(q-2b)^{(q-2b)/2}/(8(q-b)^{q-b}) (2z/(2-α))^{(2-α)/2}]^{1/k}`, `k = 3-α`,
`q = 4-α` (`E:occupation-scalar-map`, TeX lines 195-201).  The TeX defines it for `z > 0` with
`F_b(0) = 0`; the formula gives `F_b(0) = 0` (`Fb_zero`); it is used only for `z ≥ 0`. -/
def Fb (alpha b z : ℝ) : ℝ :=
  (3 - alpha) * (coef alpha b * (2 * z / (2 - alpha)) ^ ((2 - alpha) / 2)) ^ (1 / (3 - alpha))

/-- `Δ = ½[q log q + (q-2a) log(q-2a)] - (q-a) log(q-a)`, `q = 4-α` (TeX lines 276-279). -/
def logGap (alpha a : ℝ) : ℝ :=
  ((4 - alpha) * log (4 - alpha) + (4 - alpha - 2 * a) * log (4 - alpha - 2 * a)) / 2 -
    (4 - alpha - a) * log (4 - alpha - a)

/-- `D_ζ = (2-α)/2 (α/(2ζ))^{α/(2-α)}` (`E:raw-occupation-energy`, TeX lines 99-104). -/
def Dzeta (alpha ζ : ℝ) : ℝ := (2 - alpha) / 2 * (alpha / (2 * ζ)) ^ (alpha / (2 - alpha))

/-- `U_𝔠 = 𝔠^m k[α^{α/2} C/(8q^{q/2})]^{1/k}` (`E:occupation-score-ceiling`, TeX lines 208-213),
`m = q/k`, with the constant `C_occ` replaced by the real argument `C`. -/
def ceilingValue (alpha c C : ℝ) : ℝ :=
  c ^ ((4 - alpha) / (3 - alpha)) * ((3 - alpha) *
    (alpha ^ (alpha / 2) * C / (8 * (4 - alpha) ^ ((4 - alpha) / 2))) ^ (1 / (3 - alpha)))

/-- The named input: the ceiling `E:occupation-score-ceiling` (TeX lines 205-220) with `C_occ`
replaced by `K_0 R_sp` (`C_occ ≤ K_0 R_sp`, `P:raw-occupation-energy`, lines 92-97), in
pointwise form: for every `c > 0` and `Ψ ∈ C_pos`, `c I_Ψ - v_Ψ/2 ≤ U_c[K_0 R_sp]`.  Wave item
L8-c proves it; see the module doc comment for why it is no stronger than its sources. -/
def OccupationCeilingK0 (alpha a : ℝ) (Γ : Measure (Rd d)) : Prop :=
  ∀ c : ℝ, 0 < c → ∀ Ψ ∈ CPos d,
    c * integratedRate a Γ Ψ - rawCost a Γ Ψ / 2 ≤ ceilingValue alpha c (K0 a * Rsp Γ alpha)

/-! ### Scalar facts -/

/-- `K_0 > 0` for `a < 1`. -/
theorem K0_pos {a : ℝ} (ha : a < 1) : 0 < K0 a :=
  div_pos (rpow_pos_of_pos two_pos _) (by linarith)

/-- `coef α b > 0` when `q - 2b > 0` and `q - b > 0`. -/
theorem coef_pos {alpha b : ℝ} (h2 : 0 < 4 - alpha - 2 * b) (h1 : 0 < 4 - alpha - b) :
    0 < coef alpha b :=
  div_pos (rpow_pos_of_pos h2 _) (mul_pos (by norm_num) (rpow_pos_of_pos h1 _))

/-- `F_b(0) = 0` (TeX line 195) for `α < 2`. -/
theorem Fb_zero {alpha : ℝ} (ha2 : alpha < 2) (b : ℝ) : Fb alpha b 0 = 0 := by
  unfold Fb
  rw [mul_zero, zero_div, zero_rpow (by linarith), mul_zero,
    zero_rpow (one_div_ne_zero (by linarith)), mul_zero]

/-- `F_b(z) > 0` for `z > 0`, `α < 2`, `q - 2b > 0`, `q - b > 0`. -/
theorem Fb_pos {alpha b z : ℝ} (ha2 : alpha < 2) (h2 : 0 < 4 - alpha - 2 * b)
    (h1 : 0 < 4 - alpha - b) (hz : 0 < z) : 0 < Fb alpha b z := by
  unfold Fb
  have hw : 0 < 2 * z / (2 - alpha) := div_pos (by linarith) (by linarith)
  exact mul_pos (by linarith) (rpow_pos_of_pos (mul_pos (coef_pos h2 h1)
    (rpow_pos_of_pos hw _)) _)

/-- At `b = 0` the map `F_b` is `F_0` of `E:spatial-static-energy-score` (TeX lines 202-203), i.e.
`SpatialFourLinear.F0`, for `α < 4`. -/
theorem Fb_zero_eq_F0 {alpha : ℝ} (ha4 : alpha < 4) (z : ℝ) : Fb alpha 0 z = F0 alpha z := by
  have hq : 0 < 4 - alpha := by linarith
  have hh : 0 < (4 - alpha) ^ ((4 - alpha) / 2) := rpow_pos_of_pos hq _
  have e : (4 - alpha) ^ (4 - alpha) =
      (4 - alpha) ^ ((4 - alpha) / 2) * (4 - alpha) ^ ((4 - alpha) / 2) := by
    rw [← rpow_add hq]; congr 1; ring
  unfold Fb F0 coef
  simp only [mul_zero, sub_zero]
  rw [e]
  congr 2
  field_simp

/-- Auxiliary to the Lean proof route: `log coef = (q-2b)/2 log(q-2b) - log 8 - (q-b) log(q-b)`. -/
theorem log_coef {alpha b : ℝ} (h2 : 0 < 4 - alpha - 2 * b) (h1 : 0 < 4 - alpha - b) :
    log (coef alpha b) = (4 - alpha - 2 * b) / 2 * log (4 - alpha - 2 * b) - log 8 -
      (4 - alpha - b) * log (4 - alpha - b) := by
  unfold coef
  rw [log_div (rpow_pos_of_pos h2 _).ne' (mul_pos (by norm_num) (rpow_pos_of_pos h1 _)).ne',
    log_mul (by norm_num) (rpow_pos_of_pos h1 _).ne', log_rpow h2, log_rpow h1]
  ring

/-- **`Δ > 0`** (TeX lines 275-283): for `a > 0` and `q - 2a > 0` (`q = 4-α`), by strict midpoint
convexity of `x ↦ x log x` on `[0,∞)`. -/
theorem logGap_pos {alpha a : ℝ} (ha : 0 < a) (h2 : 0 < 4 - alpha - 2 * a) :
    0 < logGap alpha a := by
  have hx : (4 - alpha) ∈ Ici (0 : ℝ) := by simp only [mem_Ici]; linarith
  have hy : (4 - alpha - 2 * a) ∈ Ici (0 : ℝ) := by simp only [mem_Ici]; linarith
  have hne : 4 - alpha ≠ 4 - alpha - 2 * a := by intro h; linarith
  have key := Real.strictConvexOn_mul_log.2 hx hy hne (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (0 : ℝ) < 1 / 2 by norm_num) (by norm_num)
  simp only [smul_eq_mul] at key
  have e : 1 / 2 * (4 - alpha) + 1 / 2 * (4 - alpha - 2 * a) = 4 - alpha - a := by ring
  rw [e] at key
  unfold logGap
  linarith

/-- **`log(F_a(z)/F_0(z)) = Δ/k`** (TeX line 286), `k = 3-α`, for `α < 2`, `q - 2a > 0`, `z > 0`. -/
theorem log_Fb_ratio {alpha a z : ℝ} (ha2 : alpha < 2)
    (h2 : 0 < 4 - alpha - 2 * a) (hz : 0 < z) :
    log (Fb alpha a z / Fb alpha 0 z) = logGap alpha a / (3 - alpha) := by
  have h1 : 0 < 4 - alpha - a := by linarith
  have hq : 0 < 4 - alpha - 2 * 0 := by linarith
  have hq' : 0 < 4 - alpha - 0 := by linarith
  have hw : 0 < (2 * z / (2 - alpha)) ^ ((2 - alpha) / 2) :=
    rpow_pos_of_pos (div_pos (by linarith) (by linarith)) _
  have hca := coef_pos h2 h1
  have hc0 := coef_pos hq hq'
  have hk : (3 - alpha) ≠ 0 := by intro h; linarith
  unfold Fb
  rw [mul_div_mul_left _ _ hk, ← div_rpow (mul_pos hca hw).le (mul_pos hc0 hw).le,
    mul_div_mul_right _ _ hw.ne', log_rpow (div_pos hca hc0), log_div hca.ne' hc0.ne',
    log_coef h2 h1, log_coef hq hq']
  unfold logGap
  simp only [mul_zero, sub_zero]
  field_simp
  ring

/-- **`F_0(z) < F_a(z)`** (TeX lines 261-265, 286): for `0 < α < 2`, `a > 0`, `q - 2a > 0`, `z > 0`,
with `F_0 = SpatialFourLinear.F0`. -/
theorem F0_lt_Fa {alpha a z : ℝ} (ha2 : alpha < 2) (ha : 0 < a)
    (h2 : 0 < 4 - alpha - 2 * a) (hz : 0 < z) : F0 alpha z < Fb alpha a z := by
  rw [← Fb_zero_eq_F0 (by linarith)]
  have h0 : 0 < Fb alpha 0 z := Fb_pos ha2 (by linarith) (by linarith) hz
  have hr : 0 < Fb alpha a z / Fb alpha 0 z := div_pos (Fb_pos ha2 h2 (by linarith) hz) h0
  have hlog := log_Fb_ratio ha2 h2 hz
  have hpos : 0 < log (Fb alpha a z / Fb alpha 0 z) := by
    rw [hlog]; exact div_pos (logGap_pos ha h2) (by linarith)
  have h1 : 1 < Fb alpha a z / Fb alpha 0 z := by
    rw [← exp_log hr]; exact one_lt_exp_iff.2 hpos
  rwa [one_lt_div h0] at h1

/-- Auxiliary to the Lean proof route: homogeneity of `F₀`: for `0 < α < 2`, `t ≥ 0`, `E ≥ 0`,
`F₀(tE) = t^{(2-α)/(2k)} F₀(E)`, `k = 3-α`. -/
theorem F0_mul {alpha t E : ℝ} (ha2 : alpha < 2) (ht : 0 ≤ t) (hE : 0 ≤ E) :
    F0 alpha (t * E) = t ^ ((2 - alpha) / 2 * (1 / (3 - alpha))) * F0 alpha E := by
  have h2a : 0 < 2 - alpha := by linarith
  have hq : 0 < 8 * (4 - alpha) ^ ((4 - alpha) / 2) :=
    mul_pos (by norm_num) (rpow_pos_of_pos (by linarith) _)
  unfold F0
  have e : 2 * (t * E) / (2 - alpha) = t * (2 * E / (2 - alpha)) := by ring
  have hw : 0 ≤ 2 * E / (2 - alpha) := div_nonneg (by linarith) h2a.le
  rw [e, mul_rpow ht hw, mul_div_assoc,
    mul_rpow (rpow_nonneg ht _) (div_nonneg (rpow_nonneg hw _) hq.le), ← rpow_mul ht]
  ring

/-- Auxiliary to the Lean proof route: for `0 < α < 2` and `C ≥ 0`,
`(2 E/(2-α))^{(2-α)/2} = α^{α/2} C` at `E = (2-α)/2 α^{α/(2-α)} C^{2/(2-α)}` (as in
`SpatialFourLinear.score_identity`). -/
theorem energyValue_pow {alpha C : ℝ} (ha0 : 0 < alpha) (ha2 : alpha < 2) (hC : 0 ≤ C) :
    (2 * energyValue alpha C / (2 - alpha)) ^ ((2 - alpha) / 2) = alpha ^ (alpha / 2) * C := by
  have h2a : 0 < 2 - alpha := by linarith
  have : 2 * energyValue alpha C / (2 - alpha) =
      alpha ^ (alpha / (2 - alpha)) * C ^ (2 / (2 - alpha)) := by
    unfold energyValue; field_simp
  rw [this, mul_rpow (by positivity) (by positivity), ← rpow_mul ha0.le, ← rpow_mul hC,
    show alpha / (2 - alpha) * ((2 - alpha) / 2) = alpha / 2 by field_simp,
    show 2 / (2 - alpha) * ((2 - alpha) / 2) = 1 by field_simp, rpow_one]

/-- The ceiling at `ζ = 1/2`: for `0 < α < 2`, `C ≥ 0`,
`U_𝔠[C] = 𝔠^m F₀(D_{1/2} C^{2/(2-α)})`, where `D_{1/2} C^{2/(2-α)} = energyValue α C`
(TeX lines 214-215 at `ζ = 1/2`). -/
theorem ceilingValue_eq_half {alpha c C : ℝ} (ha0 : 0 < alpha) (ha2 : alpha < 2) (hC : 0 ≤ C) :
    ceilingValue alpha c C =
      c ^ ((4 - alpha) / (3 - alpha)) * F0 alpha (energyValue alpha C) := by
  unfold ceilingValue F0
  rw [energyValue_pow ha0 ha2 hC]

/-- `D_{1/2} C^{2/(2-α)} = energyValue α C` (`E:raw-occupation-energy` at `ζ = 1/2` is the right
side of `E:spatial-energy-map`). -/
theorem Dzeta_half (alpha C : ℝ) :
    Dzeta alpha (1 / 2) * C ^ (2 / (2 - alpha)) = energyValue alpha C := by
  unfold Dzeta energyValue
  norm_num

/-- The ceiling with `C = K R`: for `0 < α < 2`, `K, R ≥ 0`,
`U_𝔠[K R] = 𝔠^m K^{1/k} F₀(energyValue α R)` (TeX lines 269-270: inserting `C_occ ≤ K_0 R_sp` and
`E:spatial-energy-map`). -/
theorem ceilingValue_mul {alpha c K R : ℝ} (ha0 : 0 < alpha) (ha2 : alpha < 2) (hK : 0 ≤ K)
    (hR : 0 ≤ R) :
    ceilingValue alpha c (K * R) =
      c ^ ((4 - alpha) / (3 - alpha)) * K ^ (1 / (3 - alpha)) *
        F0 alpha (energyValue alpha R) := by
  have hq : 0 < 8 * (4 - alpha) ^ ((4 - alpha) / 2) :=
    mul_pos (by norm_num) (rpow_pos_of_pos (by linarith) _)
  unfold ceilingValue F0
  rw [energyValue_pow ha0 ha2 hR]
  have e : alpha ^ (alpha / 2) * (K * R) / (8 * (4 - alpha) ^ ((4 - alpha) / 2)) =
      K * (alpha ^ (alpha / 2) * R / (8 * (4 - alpha) ^ ((4 - alpha) / 2))) := by ring
  rw [e, mul_rpow hK (div_nonneg (mul_nonneg (rpow_nonneg ha0.le _) hR) hq.le)]
  ring

/-- **Second form of `E:occupation-score-ceiling`** (TeX lines 214-215): for `0 < α < 2`, `ζ > 0`,
`C ≥ 0`, `U_𝔠[C] = 𝔠^m (2ζ)^{α/(2k)} F₀(D_ζ C^{2/(2-α)})`, `k = 3-α`.  In the TeX
`D_ζ C_occ^{2/(2-α)} = 𝓔_ζ^𝒪` (`E:raw-occupation-energy`); here `C` is any real `C ≥ 0`. -/
theorem ceilingValue_eq_zeta {alpha c C ζ : ℝ} (ha0 : 0 < alpha) (ha2 : alpha < 2)
    (hC : 0 ≤ C) (hζ : 0 < ζ) :
    ceilingValue alpha c C = c ^ ((4 - alpha) / (3 - alpha)) *
      (2 * ζ) ^ (alpha / (2 * (3 - alpha))) * F0 alpha (Dzeta alpha ζ * C ^ (2 / (2 - alpha))) := by
  have h2a : 0 < 2 - alpha := by linarith
  have h2ζ : 0 < 2 * ζ := by linarith
  have hD : Dzeta alpha ζ * C ^ (2 / (2 - alpha)) =
      (2 * ζ) ^ (-(alpha / (2 - alpha))) * energyValue alpha C := by
    unfold Dzeta energyValue
    rw [div_rpow ha0.le h2ζ.le, rpow_neg h2ζ.le]
    field_simp
  have hE : 0 ≤ energyValue alpha C := by unfold energyValue; positivity
  rw [hD, F0_mul ha2 (rpow_nonneg h2ζ.le _) hE, ← rpow_mul h2ζ.le, ceilingValue_eq_half ha0 ha2 hC,
    mul_assoc (c ^ _), ← mul_assoc ((2 * ζ) ^ _), ← rpow_add h2ζ]
  have e : alpha / (2 * (3 - alpha)) +
      -(alpha / (2 - alpha)) * ((2 - alpha) / 2 * (1 / (3 - alpha))) = 0 := by
    field_simp; ring
  rw [e, rpow_zero, one_mul]

/-- **The ratio identity** (TeX lines 287-288): for `0 < α < 2`, `q - 2a > 0`, `𝔠 > 0`,
`C > 0`, `ζ > 0`, with `E = D_ζ C^{2/(2-α)}` (in the TeX `𝓔_ζ^𝒪` at `C = C_occ`):
`𝔠^m F_a(E)/U_𝔠[C] = exp((Δ - (α/2) log(2ζ))/k)`. -/
theorem ceiling_ratio_exp {alpha a c C ζ : ℝ} (ha0 : 0 < alpha) (ha2 : alpha < 2)
    (h2 : 0 < 4 - alpha - 2 * a) (hc : 0 < c) (hC : 0 < C) (hζ : 0 < ζ) :
    c ^ ((4 - alpha) / (3 - alpha)) * Fb alpha a (Dzeta alpha ζ * C ^ (2 / (2 - alpha))) /
        ceilingValue alpha c C =
      exp ((logGap alpha a - alpha / 2 * log (2 * ζ)) / (3 - alpha)) := by
  have h2a : 0 < 2 - alpha := by linarith
  have h2ζ : 0 < 2 * ζ := by linarith
  set E := Dzeta alpha ζ * C ^ (2 / (2 - alpha)) with hEdef
  have hEpos : 0 < E := by
    rw [hEdef]; unfold Dzeta
    exact mul_pos (mul_pos (by linarith) (rpow_pos_of_pos (div_pos ha0 h2ζ) _))
      (rpow_pos_of_pos hC _)
  have h0 : 0 < Fb alpha 0 E := Fb_pos ha2 (by linarith) (by linarith) hEpos
  have hFa : Fb alpha a E = exp (logGap alpha a / (3 - alpha)) * F0 alpha E := by
    rw [← log_Fb_ratio ha2 h2 hEpos,
      exp_log (div_pos (Fb_pos ha2 h2 (by linarith) hEpos) h0), Fb_zero_eq_F0 (by linarith)]
    rw [← Fb_zero_eq_F0 (by linarith)]
    field_simp
  rw [ceilingValue_eq_zeta ha0 ha2 hC.le hζ, ← hEdef, hFa, ← Fb_zero_eq_F0 (by linarith),
    rpow_def_of_pos h2ζ]
  have hcm : 0 < c ^ ((4 - alpha) / (3 - alpha)) := rpow_pos_of_pos hc _
  field_simp
  rw [← exp_add]
  congr 1
  field_simp
  ring

/-! ### The numerical counterexample at `ζ = 1` (TeX lines 290-298) -/

/-- The two integers of TeX lines 297-298 and their order: `11^11 7^7 = 234966429149994773`,
`2^5 9^18 = 4803028329503971872`, and the first is smaller. -/
theorem counterexample_integers :
    (11 : ℕ) ^ 11 * 7 ^ 7 = 234966429149994773 ∧ (2 : ℕ) ^ 5 * 9 ^ 18 = 4803028329503971872 ∧
      (11 : ℕ) ^ 11 * 7 ^ 7 < 2 ^ 5 * 9 ^ 18 := by
  norm_num

/-- **TeX lines 290-295**: at `α = 5/4`, `a = 1/2`,
`8[Δ - (α/2) log 2] = log(11^{11} 7^7/(2^5 9^{18})) < 0`.  (The TeX also fixes `d = 2`; the
scalar identity does not depend on `d`.) -/
theorem counterexample_log :
    8 * (logGap (5 / 4) (1 / 2) - (5 / 4) / 2 * log 2) =
        log ((11 : ℝ) ^ 11 * 7 ^ 7 / (2 ^ 5 * 9 ^ 18)) ∧
      8 * (logGap (5 / 4) (1 / 2) - (5 / 4) / 2 * log 2) < 0 := by
  have hid : 8 * (logGap (5 / 4) (1 / 2) - (5 / 4) / 2 * log 2) =
      log ((11 : ℝ) ^ 11 * 7 ^ 7 / (2 ^ 5 * 9 ^ 18)) := by
    have l4 : log (4 : ℝ) = 2 * log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; norm_num
    have l11 : log (11 / 4 : ℝ) = log 11 - log 4 := log_div (by norm_num) (by norm_num)
    have l7 : log (7 / 4 : ℝ) = log 7 - log 4 := log_div (by norm_num) (by norm_num)
    have l9 : log (9 / 4 : ℝ) = log 9 - log 4 := log_div (by norm_num) (by norm_num)
    rw [log_div (by norm_num) (by norm_num), log_mul (by norm_num) (by norm_num),
      log_mul (by norm_num) (by norm_num), log_pow, log_pow, log_pow, log_pow]
    unfold logGap
    norm_num
    rw [l11, l7, l9, l4]
    ring
  refine ⟨hid, ?_⟩
  rw [hid]
  exact log_neg (by norm_num) (by norm_num)

/-- **At `ζ = 1` the comparison is not universally favorable** (TeX lines 290-298): at
`α = 5/4`, `a = 1/2`, for every `𝔠 > 0` and `C > 0`, `𝔠^m F_a(D_1 C^{2/(2-α)}) < U_𝔠[C]`
(in the TeX `D_1 C_occ^{2/(2-α)} = 𝓔_1^𝒪`). -/
theorem counterexample_ratio {c C : ℝ} (hc : 0 < c) (hC : 0 < C) :
    c ^ (((4 : ℝ) - 5 / 4) / (3 - 5 / 4)) *
        Fb (5 / 4) (1 / 2) (Dzeta (5 / 4) 1 * C ^ ((2 : ℝ) / (2 - 5 / 4))) <
      ceilingValue (5 / 4) c C := by
  have hr := ceiling_ratio_exp (alpha := 5 / 4) (a := 1 / 2) (ζ := 1) (by norm_num) (by norm_num)
    (by norm_num) hc hC one_pos
  have hU : 0 < ceilingValue (5 / 4) c C := by
    unfold ceilingValue
    exact mul_pos (rpow_pos_of_pos hc _) (mul_pos (by norm_num) (rpow_pos_of_pos
      (div_pos (mul_pos (rpow_pos_of_pos (by norm_num) _) hC)
        (mul_pos (by norm_num) (rpow_pos_of_pos (by norm_num) _))) _))
  have hneg := counterexample_log.2
  have hlt : exp ((logGap (5 / 4) (1 / 2) - (5 / 4) / 2 * log (2 * 1)) / (3 - 5 / 4)) < 1 := by
    rw [exp_lt_one_iff, mul_one]
    exact div_neg_of_neg_of_pos (by linarith) (by norm_num)
  rw [← hr, div_lt_one hU] at hlt
  exact hlt

/-! ### The bracket for `S_2^pos` -/

/-- Auxiliary to the Lean proof route: the named input gives `S1Bdd` (its case `c = 1`). -/
theorem S1Bdd_of_ceiling {alpha a : ℝ} {Γ : Measure (Rd d)} (hC : OccupationCeilingK0 alpha a Γ) :
    S1Bdd a Γ := by
  refine ⟨ceilingValue alpha 1 (K0 a * Rsp Γ alpha), ?_⟩
  rintro _ ⟨Ψ, hΨ, rfl⟩
  simpa only [one_mul] using hC 1 one_pos Ψ hΨ

/-- **Lower half of `E:intrinsic-spatial-bracket` for `S_2^pos`, existential form** (TeX lines
256-260, 271-272) under the standing assumptions (`H:homog`, `a = α₀`, `Γ ≠ 0`): every
`y < 2^m M_a^{-1/k} F₀(𝓔_sp)` (`m = q/k`, `k = 3-α`, `q = 4-α`) is exceeded by
`2 I_Ψ - v_Ψ/2` for some `Ψ ∈ C_pos`.  Narrower: `S_2^pos`, not `C_2`; this form is implied by
`2^m M_a^{-1/k} F₀(𝓔_sp) ≤ S_2^pos` and needs no boundedness. -/
theorem spatial_bracket_lower_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) :
    ∀ y < 2 ^ ((4 - alpha) / (3 - alpha)) *
        (TemporalEquilibrium.mass alpha0 ^ (-(1 / (3 - alpha))) * F0 alpha (Esp Γ)),
      ∃ Ψ ∈ CPos d, y < 2 * integratedRate alpha0 Γ Ψ - rawCost alpha0 Γ Ψ / 2 := by
  intro y hy
  obtain ⟨-, -, ha2, -⟩ := SpatialSmoothRatio.homog_consequences hH
  have hk : 0 < 3 - alpha := by linarith
  have hm : 0 < (2 : ℝ) ^ ((4 - alpha) / (3 - alpha)) := rpow_pos_of_pos two_pos _
  have hy' : y / 2 ^ ((4 - alpha) / (3 - alpha)) <
      TemporalEquilibrium.mass alpha0 ^ (-(1 / (3 - alpha))) * F0 alpha (Esp Γ) := by
    rwa [div_lt_iff₀' hm]
  obtain ⟨Ψ₀, hΨ₀, hlt⟩ :=
    SpatialOccupationL7Completed.spatial_static_energy_score_paper_completed hH hΓ _ hy'
  have hr : 0 < (2 : ℝ) ^ (3 - alpha)⁻¹ := rpow_pos_of_pos two_pos _
  refine ⟨dil alpha ((2 : ℝ) ^ (3 - alpha)⁻¹) Ψ₀, VariationalDilation.dil_mapsTo alpha hr hΨ₀, ?_⟩
  rw [VariationalRate.score_set_scaling hH.scaling hk two_pos hΨ₀.1.continuous alpha0]
  rwa [div_lt_iff₀' hm] at hlt

/-- **Lower half of `E:intrinsic-spatial-bracket` for `S_2^pos`, `sSup` form** (TeX lines
256-260, 271-272) under the standing assumptions and `S1Bdd α₀ Γ` (which the named input
`OccupationCeilingK0` implies, `S1Bdd_of_ceiling`): `2^m M_a^{-1/k} F₀(𝓔_sp) ≤ S_2^pos`.
Narrower: `S_2^pos`, not `C_2`. -/
theorem spatial_bracket_lower_sSup_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) (hB1 : S1Bdd alpha0 Γ) :
    2 ^ ((4 - alpha) / (3 - alpha)) *
        (TemporalEquilibrium.mass alpha0 ^ (-(1 / (3 - alpha))) * F0 alpha (Esp Γ)) ≤
      sSup (scoreSet alpha0 Γ 2) := by
  rw [((VariationalRate.variational_positive_scores_sSup_paper hH hΓ hB1).2 2 two_pos).2.2.2]
  exact mul_le_mul_of_nonneg_left
    (SpatialOccupationL7Completed.spatial_static_energy_score_sSup_paper_completed hH hΓ hB1)
    (rpow_pos_of_pos two_pos _).le

/-- **Upper half of `E:intrinsic-spatial-bracket` for `S_2^pos`** (TeX lines 256-260, 269-271)
under the standing assumptions and the named input `OccupationCeilingK0 α α₀ Γ`: the
coefficient-two value set is bounded above and `S_2^pos ≤ 2^m K_0^{1/k} F₀(𝓔_sp)`.
Narrower: `S_2^pos`, not `C_2`. -/
theorem spatial_bracket_upper_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0)
    (hC : OccupationCeilingK0 alpha alpha0 Γ) :
    BddAbove (scoreSet alpha0 Γ 2) ∧
      sSup (scoreSet alpha0 Γ 2) ≤
        2 ^ ((4 - alpha) / (3 - alpha)) * K0 alpha0 ^ (1 / (3 - alpha)) * F0 alpha (Esp Γ) := by
  obtain ⟨-, ha0, ha2, -⟩ := SpatialSmoothRatio.homog_consequences hH
  obtain ⟨-, -, hE, -, hRsp⟩ :=
    SpatialOccupationL7Completed.spatial_energy_value_paper_completed hH hΓ
  obtain ⟨-, -, -, -, hR0, -, -⟩ := SpatialSmoothRatio.spatial_smooth_ratio_R0_paper hH hΓ
  have hRs : 0 ≤ Rsp Γ alpha := by rw [hRsp]; exact hR0.le
  have hK := K0_pos hH.alpha0_lt_one
  have hU : ceilingValue alpha 2 (K0 alpha0 * Rsp Γ alpha) =
      2 ^ ((4 - alpha) / (3 - alpha)) * K0 alpha0 ^ (1 / (3 - alpha)) * F0 alpha (Esp Γ) := by
    rw [ceilingValue_mul ha0 ha2 hK.le hRs, hE]
  have hub : ∀ y ∈ scoreSet alpha0 Γ 2,
      y ≤ ceilingValue alpha 2 (K0 alpha0 * Rsp Γ alpha) := by
    rintro _ ⟨Ψ, hΨ, rfl⟩
    exact hC 2 two_pos Ψ hΨ
  have hne := (VariationalRate.variational_positive_scores_paper hH hΓ).1 2
  exact ⟨⟨_, hub⟩, hU ▸ csSup_le hne hub⟩

/-- **`C:intrinsic-spatial-bracket` for `S_2^pos`** (`integrated_occupation_ceiling.tex` lines
252-300) under the section's standing assumptions (lines 4-21: `H:homog`, `a = α₀`, `Γ ≠ 0`)
and the named input `OccupationCeilingK0 α α₀ Γ` (`E:occupation-score-ceiling` with `C_occ`
replaced by `K_0 R_sp`): `S1Bdd α₀ Γ` holds and the coefficient-two value set is bounded above;
`2^m M_a^{-1/k} F₀(𝓔_sp) ≤ S_2^pos ≤ 2^m K_0^{1/k} F₀(𝓔_sp)` (`E:intrinsic-spatial-bracket`);
the comparison `S_2^pos ≤ 2^m F₀(E) < 2^m F_a(E)` at `E = energyValue α (K_0 R_sp) =
D_{1/2}(K_0R_sp)^{2/(2-α)}`, which equals the upper bracket; and `Δ > 0`.  Narrower: `S_2^pos`
in place of `C_2` and `E` in place of `𝓔_{1/2}^𝒪` (module doc comment). -/
theorem intrinsic_spatial_bracket_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0)
    (hC : OccupationCeilingK0 alpha alpha0 Γ) :
    S1Bdd alpha0 Γ ∧ BddAbove (scoreSet alpha0 Γ 2) ∧
      2 ^ ((4 - alpha) / (3 - alpha)) *
          (TemporalEquilibrium.mass alpha0 ^ (-(1 / (3 - alpha))) * F0 alpha (Esp Γ)) ≤
        sSup (scoreSet alpha0 Γ 2) ∧
      sSup (scoreSet alpha0 Γ 2) ≤
        2 ^ ((4 - alpha) / (3 - alpha)) * K0 alpha0 ^ (1 / (3 - alpha)) * F0 alpha (Esp Γ) ∧
      2 ^ ((4 - alpha) / (3 - alpha)) * F0 alpha (energyValue alpha (K0 alpha0 * Rsp Γ alpha)) =
        2 ^ ((4 - alpha) / (3 - alpha)) * K0 alpha0 ^ (1 / (3 - alpha)) * F0 alpha (Esp Γ) ∧
      2 ^ ((4 - alpha) / (3 - alpha)) * F0 alpha (energyValue alpha (K0 alpha0 * Rsp Γ alpha)) <
        2 ^ ((4 - alpha) / (3 - alpha)) *
          Fb alpha alpha0 (energyValue alpha (K0 alpha0 * Rsp Γ alpha)) ∧
      0 < logGap alpha alpha0 := by
  obtain ⟨-, ha0, ha2, -⟩ := SpatialSmoothRatio.homog_consequences hH
  obtain ⟨-, -, hE, -, hRsp⟩ :=
    SpatialOccupationL7Completed.spatial_energy_value_paper_completed hH hΓ
  obtain ⟨-, -, -, -, hR0, -, -⟩ := SpatialSmoothRatio.spatial_smooth_ratio_R0_paper hH hΓ
  have hRs : 0 < Rsp Γ alpha := by rw [hRsp]; exact hR0
  have hK := K0_pos hH.alpha0_lt_one
  have hB1 := S1Bdd_of_ceiling hC
  have h2 : 0 < 4 - alpha - 2 * alpha0 := by linarith [hH.alpha0_lt_one]
  have hm : 0 < (2 : ℝ) ^ ((4 - alpha) / (3 - alpha)) := rpow_pos_of_pos two_pos _
  have hEpos : 0 < energyValue alpha (K0 alpha0 * Rsp Γ alpha) := by
    unfold energyValue
    exact mul_pos (mul_pos (by linarith) (rpow_pos_of_pos ha0 _))
      (rpow_pos_of_pos (mul_pos hK hRs) _)
  have heq : 2 ^ ((4 - alpha) / (3 - alpha)) *
      F0 alpha (energyValue alpha (K0 alpha0 * Rsp Γ alpha)) =
      2 ^ ((4 - alpha) / (3 - alpha)) * K0 alpha0 ^ (1 / (3 - alpha)) * F0 alpha (Esp Γ) := by
    rw [← ceilingValue_eq_half ha0 ha2 (mul_pos hK hRs).le,
      ceilingValue_mul ha0 ha2 hK.le hRs.le, hE]
  obtain ⟨hbdd, hup⟩ := spatial_bracket_upper_paper hH hΓ hC
  exact ⟨hB1, hbdd, spatial_bracket_lower_sSup_paper hH hΓ hB1, hup, heq,
    mul_lt_mul_of_pos_left (F0_lt_Fa ha2 hH.alpha0_pos h2 hEpos) hm,
    logGap_pos hH.alpha0_pos h2⟩

end StratonovichHAMSecondMoment.SpatialBracket
