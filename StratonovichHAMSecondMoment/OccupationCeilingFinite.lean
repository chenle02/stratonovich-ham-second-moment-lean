module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave item L8-c2: the deterministic discharge of the named input `VariationalRate.S1Bdd`
(the boundedness claim of `P:variational-positive-scores`,
`notes/integrated_unmasked_variational.tex` lines 272-274 at revision a284420) and the
occupation ceiling of `T:intrinsic-occupation-ceiling` (`notes/integrated_occupation_ceiling.tex`
lines 205-220, proof 222-250) with the constant `K_0 R_sp` in the place of `C_occ`
(`P:raw-occupation-energy`, line 96: `C_occ ≤ K_0 R_sp`, `K_0 = 2^a/(1-a)`), over one named
input `SpaceTimeCS` (step (c), proved by wave item L8-c1).  Standing assumptions (occupation file
lines 4-21; unmasked file line 4): a nonzero covariance satisfying `H:homog`
(`HomogHypothesis.HomogCovariance`), `a = α₀`, `Γ ≠ 0` (the TeX assumes `Γ ≠ 0` at line 20).

Route (not the TeX's; Le's decision 3 of wave L8): the TeX proves `S1Bdd` stochastically
(unmasked file lines 309-325, through `T:full-upper`), and the ceiling through the countable
measurable selection `L:occupation-rayleigh-selection` (occupation file lines 149-193), the map
`Q` and `ρ_g ∈ H_I` of `L:occupation-raw-square` (lines 23-90) and the class `𝒪`.  Here:
(a) `exists_unitTest_gt`: near-optimal real unit TEST functions for the Rayleigh supremum
    `λ_s² = sup R_{h_s}` of the bounded potential `h_s` (`H1Density.h1TestDense`);
(b) `exists_near_field`: a finite partition of unity `χ_i` in time (finite subcover of `[0,1]`)
    and the field `G(s,x) = ∑_i χ_i(s) f_i(x)²` (`fieldG`) with
    `∫_0^1 λ_s² - ε ≤ ∫_0^1 ∫ h_s G_s - T(G)`, `T(G) = ∫_0^1 ∑_i χ_i b(f_i)` (`fieldT`), from
    the uniform Lipschitz bounds in `s` of `∫ h_s f²` and of `λ_s²`;
(c) the named input `SpaceTimeCS`: for the space-time form
    `F(Φ,Φ') = ∫_0^1∫_0^1 |s-t|^{-a} B_Γ(Φ_s,Φ'_t)` (`stForm`), Cauchy-Schwarz
    `F(Ψ,Φ)² ≤ F(Ψ,Ψ)F(Φ,Φ)`, `F(Ψ,Ψ) = v_Ψ` and `∫∫ h_s Φ_s = F(Ψ,Φ)` for `Ψ ∈ C_pos` and
    nonnegative continuous compactly supported `Φ` (provenance: `L:positive-raw-embedding`,
    `integrated_intrinsic_constant.tex` lines 22-39, and `E:occupation-raw-identities`,
    occupation file lines 33-37);
(d) `field_energy_le`: `F(G,G) ≤ K_0 R_0 T(G)^{α/2}` (smooth square bound with `R_0`, the sharp
    Schur row `∫_0^1 |s-t|^{-a} dt ≤ K_0` of `integrated_intrinsic_constant.tex` lines 42-46,
    discrete and integral Jensen);
(e) `integratedRate_sq_le`, `score_le_ceiling`: `I_Ψ² ≤ (q/4)(α/4)^{α/q}(v_Ψ K_0R_0)^{2/q}`
    (TeX lines 224-234), then `c I_Ψ - v_Ψ/2 ≤ U_c` (lines 235-243), by weighted AM-GM.

Formalized (exact-hypothesis wrappers over `hH`, `hΓ0` and `SpaceTimeCS α₀ Γ`):
* `occupation_ceiling_K0_paper`: `c I_Ψ - v_Ψ/2 ≤ U_c` with `C_occ := K_0 R_sp` for all `c > 0`,
  `Ψ ∈ C_pos` (literally `SpatialBracket.OccupationCeilingK0 α α₀ Γ` of wave item L8-d, with the
  same `K0` and `ceilingValue` bodies); `occupation_ceiling_sSup_K0_paper`: `S_c^pos ≤ U_c`.
* `s1Bdd_paper`: `S1Bdd α₀ Γ`.
* Re-issued without `S1Bdd`: `variational_positive_scores_sSup_st_paper`,
  `spatial_static_score_sSup_st_paper`, `spatial_smooth_score_sSup_st_paper`,
  `R0_le_of_st_paper`, `spatial_static_energy_score_sSup_st_paper` (the originals in
  `VariationalRate`, `SpatialStaticControls`, `SpatialOccupationCompleted`,
  `SpatialOccupationL7Completed`, unchanged).

Supplied input (named, one): `SpaceTimeCS a Γ` (see its doc comment); it is deterministic and
much weaker than `S1Bdd`.  `S1Bdd` is never assumed.

Narrower than the TeX: the ceiling constant is `K_0 R_sp` (an upper bound of `C_occ`), not
`C_occ`; the class `𝒪`, `A(g)`, `C_occ`, `𝓔_ζ^𝒪`, `L:occupation-raw-square`,
`P:raw-occupation-energy` and the selection lemma are not formalized; the second form
`c^m (2ζ)^{α/(2k)} F_0(𝓔_ζ^𝒪)` of `E:occupation-score-ceiling` and the moment statement
`C_2 ≤ U_2` (which needs `T:intrinsic-second-moment`, foundation D1) are not formalized.
`v_Ψ` is the integral form `VariationalDilation.rawCost`; `λ` is the square root of the real
Rayleigh supremum (`VariationalDilation.rate`).

Implicit hypotheses made explicit: measurability, continuity and compact support of the
partition functions and of the field; the iterated Bochner form `stForm` is bounded from above
only for nonnegative integrands (`integral_le_toReal_lintegral`), so no junk value enters the
upper bound; `S_c^pos` is used only with nonemptiness and boundedness proved.
Lemmas marked "Auxiliary to the Lean proof route" have no manuscript label; the fallback scope
was not needed.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.SpatialOccupationL7Completed
public import StratonovichHAMSecondMoment.SpatialStaticControls
public import StratonovichHAMSecondMoment.TimeSchur

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Metric Topology
open scoped ContDiff ENNReal

namespace StratonovichHAMSecondMoment.OccupationCeilingFinite

open HomogHypothesis (Rd HomogCovariance IsSpectralMeasure IsEven)
open WeakSobolev (IsTestFunction rayleighSet rayleighValue IsRayleighTrial)
open SpatialFourierBound (spatialPair spatialEnergy gradEnergy IsUnitTest)
open TimeSchur (kern kern_nonneg measurable_kern kern_sub_comm)
open VariationalDilation (CPos mean rawCost rate integratedRate)
open VariationalRate (S1Bdd S1pos scoreSet score1Set)
open VariationalFloor (grad)
open SpatialFourLinear (Nnorm l2 Rsp)
open SpatialSmoothRatio (R0)

variable {d : ℕ}

/-! ### The constant `K_0` and the sharp Schur row -/

/-- `K_0 = 2^a/(1-a)` (`E:positive-bochner-inclusion`, `integrated_intrinsic_constant.tex`
line 29; `P:raw-occupation-energy`, `integrated_occupation_ceiling.tex` line 94). -/
def K0 (a : ℝ) : ℝ := 2 ^ a / (1 - a)

/-- Auxiliary to the Lean proof route: `K_0 > 0` for `a < 1`. -/
theorem K0_pos {a : ℝ} (ha : a < 1) : 0 < K0 a :=
  div_pos (Real.rpow_pos_of_pos two_pos _) (by linarith)

/-- Auxiliary to the Lean proof route: concavity of `x ↦ x^p` (`0 ≤ p ≤ 1`) gives
`s^p + (1-s)^p ≤ 2^{1-p}` for `s ∈ [0,1]`. -/
theorem rpow_add_rpow_le {p s : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    s ^ p + (1 - s) ^ p ≤ 2 ^ (1 - p) := by
  have h := (Real.concaveOn_rpow hp0 hp1).2 (show s ∈ Ici (0 : ℝ) from hs.1)
    (show 1 - s ∈ Ici (0 : ℝ) from by simp only [mem_Ici]; linarith [hs.2])
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  simp only [smul_eq_mul] at h
  have e : 1 / 2 * s + 1 / 2 * (1 - s) = (1 / 2 : ℝ) := by ring
  rw [e] at h
  have e2 : (2 : ℝ) ^ (1 - p) = 2 * (1 / 2 : ℝ) ^ p := by
    rw [Real.rpow_sub two_pos, Real.rpow_one, Real.div_rpow (by norm_num) (by norm_num),
      Real.one_rpow]
    ring
  rw [e2]
  linarith

/-- The sharp row bound (`integrated_intrinsic_constant.tex` lines 42-46, in the proof of
`L:positive-raw-embedding`): for `0 ≤ a < 1` and `s ∈ [0,1]`,
`∫_0^1 |s-t|^{-a} dt = (s^{1-a} + (1-s)^{1-a})/(1-a) ≤ K_0`, in `[0,∞]`. -/
theorem row_le {a s : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (kern a (s - t)) ≤ ENNReal.ofReal (K0 a) := by
  obtain ⟨hi, he⟩ := TimeSchur.integral_row (T := 1) ha1 hs
  rw [Measure.restrict_congr_set Ioo_ae_eq_Icc,
    ← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun t => kern_nonneg _ _), he]
  apply ENNReal.ofReal_le_ofReal
  unfold K0
  rw [div_le_div_iff_of_pos_right (by linarith)]
  have := rpow_add_rpow_le (p := 1 - a) (by linarith) (by linarith) hs
  rwa [sub_sub_cancel] at this

/-- The sharp Schur bound on `(0,1)²` in iterated `[0,∞]` form (TeX: `L:positive-raw-embedding`,
lines 47-49, with row constant `K_0`): for `0 ≤ a < 1` and measurable `g ≥ 0`,
`∫∫ g(s) g(t) |s-t|^{-a} ≤ K_0 ∫ g²`. -/
theorem schur_sharp {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ s in Ioo (0 : ℝ) 1, ∫⁻ t in Ioo (0 : ℝ) 1,
        g s * g t * ENNReal.ofReal (kern a (s - t)) ≤
      ENNReal.ofReal (K0 a) * ∫⁻ s in Ioo (0 : ℝ) 1, g s ^ 2 := by
  set μ := volume.restrict (Ioo (0 : ℝ) 1)
  set R := ENNReal.ofReal (K0 a)
  have hk : ∀ s : ℝ, Measurable fun t : ℝ => ENNReal.ofReal (kern a (s - t)) := fun s =>
    ENNReal.measurable_ofReal.comp ((measurable_kern a).comp (measurable_const.sub measurable_id))
  have hk2 : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (kern a (p.1 - p.2)) :=
    ENNReal.measurable_ofReal.comp ((measurable_kern a).comp (measurable_fst.sub measurable_snd))
  have hA : ∫⁻ s, ∫⁻ t, g s ^ 2 * ENNReal.ofReal (kern a (s - t)) ∂μ ∂μ ≤
      R * ∫⁻ s, g s ^ 2 ∂μ := by
    calc ∫⁻ s, ∫⁻ t, g s ^ 2 * ENNReal.ofReal (kern a (s - t)) ∂μ ∂μ
        = ∫⁻ s, g s ^ 2 * ∫⁻ t, ENNReal.ofReal (kern a (s - t)) ∂μ ∂μ :=
          lintegral_congr fun s => lintegral_const_mul _ (hk s)
      _ ≤ ∫⁻ s, g s ^ 2 * R ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
          gcongr
          exact row_le ha0 ha1 (Ioo_subset_Icc_self hs)
      _ = R * ∫⁻ s, g s ^ 2 ∂μ := by
          rw [lintegral_mul_const _ (hg.pow_const 2), mul_comm]
  have hB : ∫⁻ s, ∫⁻ t, g t ^ 2 * ENNReal.ofReal (kern a (s - t)) ∂μ ∂μ ≤
      R * ∫⁻ s, g s ^ 2 ∂μ := by
    rw [lintegral_lintegral_swap (((hg.comp measurable_snd).pow_const 2).mul hk2).aemeasurable]
    calc ∫⁻ t, ∫⁻ s, g t ^ 2 * ENNReal.ofReal (kern a (s - t)) ∂μ ∂μ
        = ∫⁻ t, g t ^ 2 * ∫⁻ s, ENNReal.ofReal (kern a (t - s)) ∂μ ∂μ := by
          refine lintegral_congr fun t => ?_
          simp_rw [kern_sub_comm a _ t]
          exact lintegral_const_mul _ (hk t)
      _ ≤ ∫⁻ t, g t ^ 2 * R ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
          gcongr
          exact row_le ha0 ha1 (Ioo_subset_Icc_self ht)
      _ = R * ∫⁻ s, g s ^ 2 ∂μ := by
          rw [lintegral_mul_const _ (hg.pow_const 2), mul_comm]
  have h2 : 2 * ∫⁻ s, ∫⁻ t, g s * g t * ENNReal.ofReal (kern a (s - t)) ∂μ ∂μ ≤
      2 * (R * ∫⁻ s, g s ^ 2 ∂μ) := by
    rw [← lintegral_const_mul' _ _ (by norm_num)]
    calc ∫⁻ s, 2 * ∫⁻ t, g s * g t * ENNReal.ofReal (kern a (s - t)) ∂μ ∂μ
        = ∫⁻ s, ∫⁻ t, 2 * (g s * g t * ENNReal.ofReal (kern a (s - t))) ∂μ ∂μ :=
          lintegral_congr fun s => (lintegral_const_mul' _ _ (by norm_num)).symm
      _ ≤ ∫⁻ s, ∫⁻ t, (g s ^ 2 * ENNReal.ofReal (kern a (s - t)) +
            g t ^ 2 * ENNReal.ofReal (kern a (s - t))) ∂μ ∂μ := by
          refine lintegral_mono fun s => lintegral_mono fun t => ?_
          rw [← add_mul, ← mul_assoc, ← mul_assoc]
          gcongr
          exact TimeSchur.two_mul_le_add_sq_ennreal _ _
      _ = ∫⁻ s, (∫⁻ t, g s ^ 2 * ENNReal.ofReal (kern a (s - t)) ∂μ +
            ∫⁻ t, g t ^ 2 * ENNReal.ofReal (kern a (s - t)) ∂μ) ∂μ :=
          lintegral_congr fun s => lintegral_add_left (measurable_const.mul (hk s)) _
      _ = ∫⁻ s, ∫⁻ t, g s ^ 2 * ENNReal.ofReal (kern a (s - t)) ∂μ ∂μ +
            ∫⁻ s, ∫⁻ t, g t ^ 2 * ENNReal.ofReal (kern a (s - t)) ∂μ ∂μ := by
          refine lintegral_add_left ?_ _
          exact (((hg.comp measurable_fst).pow_const 2).mul hk2).lintegral_prod_right'
      _ ≤ R * ∫⁻ s, g s ^ 2 ∂μ + R * ∫⁻ s, g s ^ 2 ∂μ := add_le_add hA hB
      _ = 2 * (R * ∫⁻ s, g s ^ 2 ∂μ) := by rw [two_mul]
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp h2

/-! ### Scalar maxima -/

/-- Auxiliary to the Lean proof route (the first scalar maximum of the proof of
`T:intrinsic-occupation-ceiling`, TeX lines 224-231, by weighted AM-GM): for `0 < α < 4`,
`X ≥ 0`, `T ≥ 0`, `√X T^{α/4} - T ≤ (q/4)(α/4)^{α/q} X^{2/q}` with `q = 4 - α`. -/
theorem young_quarter {alpha X T : ℝ} (ha0 : 0 < alpha) (ha4 : alpha < 4) (hX : 0 ≤ X)
    (hT : 0 ≤ T) :
    Real.sqrt X * T ^ (alpha / 4) - T ≤
      (4 - alpha) / 4 * (alpha / 4) ^ (alpha / (4 - alpha)) * X ^ (2 / (4 - alpha)) := by
  have hq : 0 < 4 - alpha := by linarith
  have hβ0 : 0 < alpha / 4 := by positivity
  set Y := (alpha / 4) ^ (alpha / (4 - alpha)) * X ^ (2 / (4 - alpha)) with hY
  have hY0 : 0 ≤ Y := by positivity
  have hAM := Real.geom_mean_le_arith_mean2_weighted (w₁ := alpha / 4) (w₂ := 1 - alpha / 4)
    (p₁ := T / (alpha / 4)) (p₂ := Y) hβ0.le (by linarith) (by positivity) hY0 (by ring)
  have e1 : (T / (alpha / 4)) ^ (alpha / 4) = T ^ (alpha / 4) / (alpha / 4) ^ (alpha / 4) :=
    Real.div_rpow hT hβ0.le _
  have e2 : Y ^ (1 - alpha / 4) = (alpha / 4) ^ (alpha / 4) * Real.sqrt X := by
    rw [hY, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hβ0.le,
      ← Real.rpow_mul hX, Real.sqrt_eq_rpow]
    have i1 : alpha / (4 - alpha) * (1 - alpha / 4) = alpha / 4 := by field_simp
    have i2 : 2 / (4 - alpha) * (1 - alpha / 4) = 1 / 2 := by field_simp; ring
    rw [i1, i2]
  rw [e1, e2] at hAM
  have hpos : 0 < (alpha / 4) ^ (alpha / 4) := Real.rpow_pos_of_pos hβ0 _
  have e3 : T ^ (alpha / 4) / (alpha / 4) ^ (alpha / 4) * ((alpha / 4) ^ (alpha / 4) *
      Real.sqrt X) = Real.sqrt X * T ^ (alpha / 4) := by field_simp
  have e4 : alpha / 4 * (T / (alpha / 4)) = T := by field_simp
  rw [e3, e4] at hAM
  have e5 : (4 - alpha) / 4 * (alpha / 4) ^ (alpha / (4 - alpha)) * X ^ (2 / (4 - alpha)) =
      (1 - alpha / 4) * Y := by rw [hY]; ring
  rw [e5]
  linarith

/-- Auxiliary to the Lean proof route (the second scalar maximum, TeX lines 235-237, by
weighted AM-GM): for `α < 3`, `E ≥ 0`, `v ≥ 0`, with `q = 4 - α`, `k = 3 - α`:
`E v^{1/q} - v/2 ≤ (k/2)(2E/q)^{q/k}`. -/
theorem young_q {alpha E v : ℝ} (ha3 : alpha < 3) (hE : 0 ≤ E) (hv : 0 ≤ v) :
    E * v ^ (1 / (4 - alpha)) - v / 2 ≤
      (3 - alpha) / 2 * (2 * E / (4 - alpha)) ^ ((4 - alpha) / (3 - alpha)) := by
  have hk : 0 < 3 - alpha := by linarith
  have hq : 0 < 4 - alpha := by linarith
  set Z := (2 * E / (4 - alpha)) ^ ((4 - alpha) / (3 - alpha)) with hZ
  have hZ0 : 0 ≤ Z := by positivity
  have hAM := Real.geom_mean_le_arith_mean2_weighted (w₁ := 1 / (4 - alpha))
    (w₂ := (3 - alpha) / (4 - alpha)) (p₁ := (4 - alpha) / 2 * v) (p₂ := (4 - alpha) / 2 * Z)
    (by positivity) (by positivity) (by positivity) (by positivity) (by field_simp; ring)
  have e1 : ((4 - alpha) / 2 * v) ^ (1 / (4 - alpha)) =
      ((4 - alpha) / 2) ^ (1 / (4 - alpha)) * v ^ (1 / (4 - alpha)) :=
    Real.mul_rpow (by positivity) hv
  have e2 : ((4 - alpha) / 2 * Z) ^ ((3 - alpha) / (4 - alpha)) =
      ((4 - alpha) / 2) ^ ((3 - alpha) / (4 - alpha)) * (2 * E / (4 - alpha)) := by
    rw [Real.mul_rpow (by positivity) hZ0, hZ, ← Real.rpow_mul (by positivity),
      show (4 - alpha) / (3 - alpha) * ((3 - alpha) / (4 - alpha)) = 1 by field_simp,
      Real.rpow_one]
  have e3 : ((4 - alpha) / 2) ^ (1 / (4 - alpha)) * ((4 - alpha) / 2) ^
      ((3 - alpha) / (4 - alpha)) = (4 - alpha) / 2 := by
    rw [← Real.rpow_add (by positivity),
      show 1 / (4 - alpha) + (3 - alpha) / (4 - alpha) = 1 by field_simp; ring, Real.rpow_one]
  rw [e1, e2] at hAM
  have e4 : ((4 - alpha) / 2) ^ (1 / (4 - alpha)) * v ^ (1 / (4 - alpha)) *
      (((4 - alpha) / 2) ^ ((3 - alpha) / (4 - alpha)) * (2 * E / (4 - alpha))) =
      E * v ^ (1 / (4 - alpha)) := by
    calc _ = (((4 - alpha) / 2) ^ (1 / (4 - alpha)) * ((4 - alpha) / 2) ^
          ((3 - alpha) / (4 - alpha))) * (2 * E / (4 - alpha)) * v ^ (1 / (4 - alpha)) := by
          ring
      _ = _ := by rw [e3]; field_simp
  rw [e4] at hAM
  have e5 : 1 / (4 - alpha) * ((4 - alpha) / 2 * v) = v / 2 := by field_simp
  have e6 : (3 - alpha) / (4 - alpha) * ((4 - alpha) / 2 * Z) = (3 - alpha) / 2 * Z := by
    field_simp
  rw [e5, e6] at hAM
  linarith

/-- The ceiling `U_c = c^m k [α^{α/2} C / (8 q^{q/2})]^{1/k}` of `E:occupation-score-ceiling`
(`integrated_occupation_ceiling.tex` lines 209-212), `q = 4 - α`, `k = 3 - α`, `m = q/k`,
with a real constant `C` in the place of `C_occ` (the definition agreed with wave item L8-d,
`SpatialBracket.ceilingValue`, verbatim). -/
def ceilingValue (alpha c C : ℝ) : ℝ :=
  c ^ ((4 - alpha) / (3 - alpha)) *
    ((3 - alpha) * (alpha ^ (alpha / 2) * C / (8 * (4 - alpha) ^ ((4 - alpha) / 2))) ^
      (1 / (3 - alpha)))

/-- Auxiliary to the Lean proof route ("direct positive-power algebra", TeX lines 237-243):
for `0 < α < 2`, `C > 0`, `c > 0`, with `D = √(q/4) (α/4)^{α/(2q)} C^{1/q}` written as
`√((q/4)(α/4)^{α/q}) C^{1/q}`: `(k/2)(2cD/q)^{q/k} = U_c`. -/
theorem ceilingValue_eq {alpha C c : ℝ} (ha0 : 0 < alpha) (ha2 : alpha < 2) (hC : 0 < C)
    (hc : 0 < c) :
    (3 - alpha) / 2 * (2 * (c * Real.sqrt ((4 - alpha) / 4 * (alpha / 4) ^ (alpha / (4 - alpha))) *
      C ^ (1 / (4 - alpha))) / (4 - alpha)) ^ ((4 - alpha) / (3 - alpha)) =
      ceilingValue alpha c C := by
  have hk : 0 < 3 - alpha := by linarith
  have hq : 0 < 4 - alpha := by linarith
  set P := (4 - alpha) / 4 * (alpha / 4) ^ (alpha / (4 - alpha)) with hPdef
  have hP : 0 < P := by positivity
  set E := c * Real.sqrt P * C ^ (1 / (4 - alpha)) with hEdef
  have hE : 0 < E := by positivity
  set X := alpha ^ (alpha / 2) * C / (8 * (4 - alpha) ^ ((4 - alpha) / 2)) with hXdef
  have hX : 0 < X := by positivity
  have hL : 0 < (3 - alpha) / 2 * (2 * E / (4 - alpha)) ^ ((4 - alpha) / (3 - alpha)) := by
    positivity
  have hR : 0 < ceilingValue alpha c C := by unfold ceilingValue; rw [← hXdef]; positivity
  refine Real.log_injOn_pos hL hR ?_
  have l4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have l8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have hlogP : Real.log P = Real.log (4 - alpha) - 2 * Real.log 2 +
      alpha / (4 - alpha) * (Real.log alpha - 2 * Real.log 2) := by
    rw [hPdef, Real.log_mul (by positivity) (by positivity), Real.log_div hq.ne' (by norm_num),
      Real.log_rpow (by positivity), Real.log_div ha0.ne' (by norm_num), l4]
  have hlogE : Real.log E = Real.log c + Real.log P / 2 + Real.log C / (4 - alpha) := by
    rw [hEdef, Real.log_mul (by positivity) (by positivity),
      Real.log_mul hc.ne' (by positivity), Real.log_sqrt hP.le, Real.log_rpow hC]
    ring
  have hlogX : Real.log X = alpha / 2 * Real.log alpha + Real.log C -
      (3 * Real.log 2 + (4 - alpha) / 2 * Real.log (4 - alpha)) := by
    rw [hXdef, Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) hC.ne', Real.log_rpow ha0,
      Real.log_mul (by norm_num) (by positivity), Real.log_rpow hq, l8]
  have hlhs : Real.log ((3 - alpha) / 2 * (2 * E / (4 - alpha)) ^ ((4 - alpha) / (3 - alpha))) =
      Real.log (3 - alpha) - Real.log 2 + (4 - alpha) / (3 - alpha) *
        (Real.log 2 + Real.log E - Real.log (4 - alpha)) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_div hk.ne' (by norm_num),
      Real.log_rpow (by positivity), Real.log_div (by positivity) hq.ne',
      Real.log_mul (by norm_num) hE.ne']
  have hrhs : Real.log (ceilingValue alpha c C) = (4 - alpha) / (3 - alpha) * Real.log c +
      (Real.log (3 - alpha) + 1 / (3 - alpha) * Real.log X) := by
    unfold ceilingValue
    rw [← hXdef, Real.log_mul (by positivity) (by positivity), Real.log_rpow hc,
      Real.log_mul hk.ne' (by positivity), Real.log_rpow hX]
  rw [hlhs, hrhs, hlogE, hlogP, hlogX]
  field_simp
  ring

/-! ### Step (a): near-optimal unit tests for a bounded potential -/

/-- Step (a) of the route (TeX: `L:occupation-rayleigh-selection`, lines 159-168, where a
countable dense family is used instead): for a continuous potential `0 ≤ V ≤ M` with a nonempty
real Rayleigh set and `q < sup R_V`, there is a real unit test `f ∈ C_c^∞` (`IsUnitTest`) with
`q < ∫ V f² - b(f)`.  Proof: a trial `(f,g)` with value above `q`, test functions `φ_n → f`,
`∇φ_n → g` in `L²` (`H1Density.h1TestDense`), `∫ V φ_n² → ∫ V f²` (through `√V φ_n → √V f` in
`L²`), and normalization of `φ_n`. -/
theorem exists_unitTest_gt {V : Rd d → ℝ} (hV : Continuous V) (hV0 : ∀ x, 0 ≤ V x) {M : ℝ}
    (hVM : ∀ x, V x ≤ M) (hne : (rayleighSet V).Nonempty) {q : ℝ}
    (hq : q < sSup (rayleighSet V)) :
    ∃ f, IsUnitTest f ∧ q < (∫ x, V x * f x ^ 2) - gradEnergy f := by
  obtain ⟨_, ⟨f, g, htr, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hne hq
  obtain ⟨φ, hφt, h1, h2⟩ := H1Density.h1TestDense d f g htr.memLp_f htr.memLp_g htr.weakGrad
  have hm : Tendsto (fun n => ∫ x, φ n x ^ 2) atTop (𝓝 1) := by
    have h := (SpatialFourLinear.l2_tendsto (fun n => VariationalFloor.memLp_test (hφt n))
      htr.memLp_f h1).pow 2
    rw [← SpatialFourLinear.integral_sq_eq_l2_sq htr.memLp_f, htr.unit] at h
    refine h.congr fun n => ?_
    exact (SpatialFourLinear.integral_sq_eq_l2_sq (VariationalFloor.memLp_test (hφt n))).symm
  have hB : Tendsto (fun n => gradEnergy (φ n)) atTop (𝓝 (∫ x, ‖g x‖ ^ 2)) := by
    have h := (SpatialFourLinear.l2_tendsto (fun n => VariationalFloor.memLp_grad (hφt n))
      htr.memLp_g h2).pow 2
    rw [SpatialFourLinear.l2_sq htr.memLp_g] at h
    refine h.congr fun n => ?_
    exact (SpatialFourLinear.gradEnergy_eq_l2_sq (hφt n)).symm
  have hsVc : Continuous fun x => Real.sqrt (V x) := hV.sqrt
  have hbd : ∀ x, ‖Real.sqrt (V x)‖ ≤ Real.sqrt M := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (hVM x)
  have hmemφ : ∀ n, MemLp (fun x => Real.sqrt (V x) * φ n x) 2 volume := fun n =>
    (hsVc.mul (hφt n).1.continuous).memLp_of_hasCompactSupport (hφt n).2.mul_left
  have hmemf : MemLp (fun x => Real.sqrt (V x) * f x) 2 volume :=
    htr.memLp_f.of_le_mul (c := Real.sqrt M)
      (hsVc.aestronglyMeasurable.mul htr.memLp_f.aestronglyMeasurable)
      (ae_of_all _ fun x => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hbd x) (norm_nonneg _))
  have hconv : Tendsto (fun n => eLpNorm (fun x => Real.sqrt (V x) * φ n x -
      Real.sqrt (V x) * f x) 2 volume) atTop (𝓝 0) := by
    have hM : Tendsto (fun n => ENNReal.ofReal (Real.sqrt M) *
        eLpNorm (fun x => φ n x - f x) 2 volume) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul h1 (Or.inr (ENNReal.ofReal_ne_top (r := Real.sqrt M)))
      rwa [mul_zero] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hM
      (fun _ => zero_le) fun n => ?_
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul ((hmemφ n).sub hmemf).aestronglyMeasurable
      (ae_of_all _ fun x => ?_) 2
    show ‖Real.sqrt (V x) * φ n x - Real.sqrt (V x) * f x‖ ≤ _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul_of_nonneg_right (hbd x) (norm_nonneg _)
  have e : ∀ u : Rd d → ℝ, (fun x => (Real.sqrt (V x) * u x) ^ 2) = fun x => V x * u x ^ 2 :=
    fun u => funext fun x => by rw [mul_pow, Real.sq_sqrt (hV0 x)]
  have hA : Tendsto (fun n => ∫ x, V x * φ n x ^ 2) atTop (𝓝 (∫ x, V x * f x ^ 2)) := by
    have h := (SpatialFourLinear.l2_tendsto hmemφ hmemf hconv).pow 2
    rw [← SpatialFourLinear.integral_sq_eq_l2_sq hmemf, e] at h
    refine h.congr fun n => ?_
    rw [← SpatialFourLinear.integral_sq_eq_l2_sq (hmemφ n), e]
  have hval : Tendsto (fun n => ((∫ x, V x * φ n x ^ 2) - gradEnergy (φ n)) /
      ∫ x, φ n x ^ 2) atTop (𝓝 (rayleighValue V f g)) := by
    have := (hA.sub hB).div hm one_ne_zero
    rwa [div_one] at this
  obtain ⟨n, hn1, hn2⟩ :=
    ((hval.eventually (lt_mem_nhds hlt)).and (hm.eventually (lt_mem_nhds one_pos))).exists
  set m := ∫ x, φ n x ^ 2 with hmdef
  have hm0 : 0 < m := hn2
  refine ⟨fun x => (Real.sqrt m)⁻¹ * φ n x, ⟨contDiff_const.mul (hφt n).1, (hφt n).2.mul_left,
    ?_⟩, ?_⟩
  · simp_rw [mul_pow]
    rw [integral_const_mul, inv_pow, Real.sq_sqrt hm0.le, ← hmdef, inv_mul_cancel₀ hm0.ne']
  · rw [SpatialFourLinear.gradEnergy_const_mul ((hφt n).1.differentiable (by simp))]
    have h3 : ∫ x, V x * ((Real.sqrt m)⁻¹ * φ n x) ^ 2 =
        (Real.sqrt m)⁻¹ ^ 2 * ∫ x, V x * φ n x ^ 2 := by
      rw [← integral_const_mul]; congr 1; funext x; ring
    rw [h3, inv_pow, Real.sq_sqrt hm0.le]
    calc q < ((∫ x, V x * φ n x ^ 2) - gradEnergy (φ n)) / m := hn1
      _ = _ := by field_simp

/-! ### General integral comparisons for nonnegative integrands -/

/-- Auxiliary to the Lean proof route: for `f ≥ 0`, `∫ f ≤ (∫⁻ ofReal f).toReal` (equality when
`f` is integrable; otherwise the Bochner integral is `0`). -/
theorem integral_le_toReal_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∫ x, f x ∂μ ≤ (∫⁻ x, ENNReal.ofReal (f x) ∂μ).toReal := by
  by_cases hi : Integrable f μ
  · rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf) hi.aestronglyMeasurable]
  · rw [integral_undef hi]; exact ENNReal.toReal_nonneg

/-- Auxiliary to the Lean proof route: for `f ≥ 0`, `ofReal (∫ f) ≤ ∫⁻ ofReal f`. -/
theorem ofReal_integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : ∀ x, 0 ≤ f x) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases hi : Integrable f μ
  · rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hf)]
  · rw [integral_undef hi, ENNReal.ofReal_zero]; exact zero_le

/-! ### The space-time form and the finite fields -/

/-- The space-time form `F(Φ,Φ') = ∫_0^1 ∫_0^1 |s-t|^{-a} B_Γ(Φ_s, Φ'_t) dt ds`
(`integrated_occupation_ceiling.tex` line 12 and `E:positive-bochner-inclusion` with
`G = H_sp`, on the original kernel `K(s,t) = |s-t|^{-a}`), as an iterated Bochner integral with
the real pairing `B_Γ = SpatialFourierBound.spatialPair`.  It is the manuscript's object only
where the integrands are integrable; every statement about it below either bounds it from above
for nonnegative integrands (where non-integrability gives the value `0`) or takes its values from
the named hypothesis `SpaceTimeCS`. -/
def stForm (a : ℝ) (Γ : Measure (Rd d)) (Φ Φ' : ℝ × Rd d → ℝ) : ℝ :=
  ∫ s in Ioo (0 : ℝ) 1, ∫ t in Ioo (0 : ℝ) 1,
    kern a (s - t) * spatialPair Γ (fun x => Φ (s, x)) (fun x => Φ' (t, x))

/-- The finite space-time field `G(s,x) = ∑_i χ_i(s) f_i(x)²` of step (b) (a Lean route object:
the TeX's selected occupation `g_ε` of `L:occupation-rayleigh-selection` is replaced by this
finite partition-of-unity field, a squared profile field). -/
def fieldG {ι : Type*} [Fintype ι] (χ : ι → ℝ → ℝ) (f : ι → Rd d → ℝ) : ℝ × Rd d → ℝ :=
  fun p => ∑ i, χ i p.1 * f i p.2 ^ 2

/-- The gradient budget `T(G) = ∫_0^1 ∑_i χ_i(s) b(f_i) ds` of the finite field (Lean route
object; for the TeX's `T(g) = ∫ b(g_s) ds` of a profile field). -/
def fieldT {ι : Type*} [Fintype ι] (χ : ι → ℝ → ℝ) (f : ι → Rd d → ℝ) : ℝ :=
  ∫ s in Ioo (0 : ℝ) 1, ∑ i, χ i s * gradEnergy (f i)

/-- Auxiliary to the Lean proof route: the finite field is continuous, compactly supported and
nonnegative when the `χ_i` are continuous, compactly supported and nonnegative and the `f_i` are
test functions. -/
theorem fieldG_props {ι : Type*} [Fintype ι] {χ : ι → ℝ → ℝ} {f : ι → Rd d → ℝ}
    (hχc : ∀ i, Continuous (χ i)) (hχs : ∀ i, HasCompactSupport (χ i))
    (hχ0 : ∀ i s, 0 ≤ χ i s) (hf : ∀ i, IsTestFunction (f i)) :
    Continuous (fieldG χ f) ∧ HasCompactSupport (fieldG χ f) ∧ ∀ p, 0 ≤ fieldG χ f p := by
  refine ⟨continuous_finsetSum _ fun i _ => ((hχc i).comp continuous_fst).mul
      (((hf i).1.continuous.comp continuous_snd).pow 2), ?_,
    fun p => Finset.sum_nonneg fun i _ => mul_nonneg (hχ0 i _) (sq_nonneg _)⟩
  refine HasCompactSupport.intro ((isCompact_iUnion fun i => hχs i).prod
    (isCompact_iUnion fun i => (hf i).2)) fun p hp => ?_
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [mem_prod, not_and_or] at hp
  rcases hp with hp | hp
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hp (mem_iUnion.2 ⟨i, h⟩)), zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hp (mem_iUnion.2 ⟨i, h⟩))]; ring

/-- Auxiliary to the Lean proof route: `B_Γ(F,G) ≥ 0` for nonnegative `F, G`. -/
theorem spatialPair_nonneg (Γ : Measure (Rd d)) {F G : Rd d → ℝ} (hF : ∀ x, 0 ≤ F x)
    (hG : ∀ x, 0 ≤ G x) : 0 ≤ spatialPair Γ F G :=
  integral_nonneg fun _ => integral_nonneg fun _ => mul_nonneg (hF _) (hG _)

/-- Auxiliary to the Lean proof route: bilinear expansion of `B_Γ` over finite sums of
continuous compactly supported profiles (locally finite `Γ`). -/
theorem spatialPair_fsum (Γ : Measure (Rd d)) [IsLocallyFiniteMeasure Γ] {ι : Type*}
    [Fintype ι] (c e : ι → ℝ) {φ ψ : ι → Rd d → ℝ} (hφ : ∀ i, Continuous (φ i))
    (hφs : ∀ i, HasCompactSupport (φ i)) (hψ : ∀ i, Continuous (ψ i))
    (hψs : ∀ i, HasCompactSupport (ψ i)) :
    spatialPair Γ (fun x => ∑ i, c i * φ i x) (fun x => ∑ j, e j * ψ j x) =
      ∑ i, ∑ j, c i * e j * spatialPair Γ (φ i) (ψ j) := by
  have hpt : ∀ y x, (∑ i, c i * φ i x) * (∑ j, e j * ψ j (x - y)) =
      ∑ i, ∑ j, c i * e j * (φ i x * ψ j (x - y)) := by
    intro y x
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hin : ∀ y, ∫ x, (∑ i, c i * φ i x) * (∑ j, e j * ψ j (x - y)) =
      ∑ i, ∑ j, c i * e j * ∫ x, φ i x * ψ j (x - y) := by
    intro y
    simp_rw [hpt y]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (SpatialFourLinear.inner_integrable (hφ i) (hφs i) (hψ j) y).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ =>
      (SpatialFourLinear.inner_integrable (hφ i) (hφs i) (hψ j) y).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
  unfold spatialPair
  simp_rw [hin]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (SpatialFourLinear.cross_integrable Γ (hφ i) (hφs i) (hψ j) (hψs j)).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ =>
    (SpatialFourLinear.cross_integrable Γ (hφ i) (hφs i) (hψ j) (hψs j)).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]

/-- Auxiliary to the Lean proof route: for a real unit test `f`, `N(f)² = b(f)^{α/4}`. -/
theorem Nnorm_sq_unit (alpha : ℝ) {f : Rd d → ℝ} (hf : IsUnitTest f) :
    Nnorm alpha f (grad f) ^ 2 = gradEnergy f ^ (alpha / 4) := by
  have ht : IsTestFunction f := ⟨hf.1, hf.2.1⟩
  have h1 : l2 f = 1 := by
    have h := SpatialFourLinear.integral_sq_eq_l2_sq (VariationalFloor.memLp_test ht)
    rw [hf.2.2] at h
    have h0 := SpatialFourLinear.l2_nonneg f
    nlinarith
  have hg0 := SpatialFourLinear.l2_nonneg (grad f)
  rw [Nnorm, h1, Real.one_rpow, one_mul, SpatialFourLinear.gradEnergy_eq_l2_sq ht,
    ← Real.rpow_natCast, ← Real.rpow_mul hg0, ← Real.rpow_natCast, ← Real.rpow_mul hg0]
  norm_num
  ring_nf

/-- Step (d), the square bound for unit tests (`E:spatial-square-CS` with
`E:spatial-homogeneous-bound` at `R`, TeX `P:raw-occupation-energy` lines 117-118): for a locally
finite even `Γ` with spectral measure `μ`, `α < 4`, `R ≥ 0` with `A_sp(g) ≤ R b(g)^{α/2}` for
every real unit test `g`: `B_Γ(f², h²) ≤ R b(f)^{α/4} b(h)^{α/4}` for real unit tests `f, h`. -/
theorem pair_unit_le {Γ μ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ] (hE : IsEven Γ)
    (hsp : IsSpectralMeasure Γ μ) {alpha R : ℝ} (ha4 : alpha < 4) (hR0 : 0 ≤ R)
    (hR : ∀ g, IsUnitTest g → spatialEnergy Γ g ≤ R * gradEnergy g ^ (alpha / 2))
    {f h : Rd d → ℝ} (hf : IsUnitTest f) (hh : IsUnitTest h) :
    spatialPair Γ (fun x => f x ^ 2) (fun x => h x ^ 2) ≤
      R * gradEnergy f ^ (alpha / 4) * gradEnergy h ^ (alpha / 4) := by
  have hbd : ∀ φ, IsTestFunction φ → spatialEnergy Γ φ ≤ R * Nnorm alpha φ (grad φ) ^ 4 :=
    fun φ hφ => SpatialFourLinear.smooth_homog_bound ha4 hR hφ
  have := SpatialFourLinear.smooth_square_bound hE hsp hR0 hbd ⟨hf.1, hf.2.1⟩ ⟨hh.1, hh.2.1⟩
  rwa [Nnorm_sq_unit alpha hf, Nnorm_sq_unit alpha hh] at this

/-- Step (d) (TeX `P:raw-occupation-energy`, lines 117-122, for the finite field; Lean route):
under the hypotheses of `pair_unit_le` with `0 < α < 2`, `0 ≤ a < 1`, for continuous compactly
supported `χ_i ≥ 0` with `∑_i χ_i = 1` on `[0,1]` and real unit tests `f_i`:
`F(G,G) ≤ K_0 R T(G)^{α/2}` for `G = fieldG χ f`, `T(G) = fieldT χ f`.  Route: bilinear
expansion and `pair_unit_le`, the sharp Schur bound `schur_sharp`, discrete Jensen for
`x ↦ x^{α/4}` and integral Jensen for `x ↦ x^{α/2}` on `(0,1)`. -/
theorem field_energy_le {Γ μ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ] (hE : IsEven Γ)
    (hsp : IsSpectralMeasure Γ μ) {alpha R a : ℝ} (ha0 : 0 < alpha) (ha2 : alpha < 2)
    (hR0 : 0 ≤ R)
    (hR : ∀ g, IsUnitTest g → spatialEnergy Γ g ≤ R * gradEnergy g ^ (alpha / 2))
    (hb0 : 0 ≤ a) (hb1 : a < 1) {ι : Type*} [Fintype ι] {χ : ι → ℝ → ℝ} {f : ι → Rd d → ℝ}
    (hχc : ∀ i, Continuous (χ i)) (hχ0 : ∀ i s, 0 ≤ χ i s)
    (hχ1 : ∀ s ∈ Icc (0 : ℝ) 1, ∑ i, χ i s = 1) (hf : ∀ i, IsUnitTest (f i)) :
    stForm a Γ (fieldG χ f) (fieldG χ f) ≤ K0 a * R * fieldT χ f ^ (alpha / 2) := by
  set b : ι → ℝ := fun i => gradEnergy (f i) with hbdef
  have hb : ∀ i, 0 ≤ b i := fun i => SpatialFourierBound.gradEnergy_nonneg _
  set w : ℝ → ℝ := fun s => ∑ i, χ i s * b i ^ (alpha / 4) with hwdef
  set e : ℝ → ℝ := fun s => ∑ i, χ i s * b i with hedef
  have hw0 : ∀ s, 0 ≤ w s := fun s => Finset.sum_nonneg fun i _ =>
    mul_nonneg (hχ0 i s) (Real.rpow_nonneg (hb i) _)
  have he0 : ∀ s, 0 ≤ e s := fun s => Finset.sum_nonneg fun i _ => mul_nonneg (hχ0 i s) (hb i)
  have hwc : Continuous w := continuous_finsetSum _ fun i _ => (hχc i).mul continuous_const
  have hec : Continuous e := continuous_finsetSum _ fun i _ => (hχc i).mul continuous_const
  have hsq : ∀ i, Continuous fun x => f i x ^ 2 := fun i => (hf i).1.continuous.pow 2
  have hsqs : ∀ i, HasCompactSupport fun x => f i x ^ 2 := fun i =>
    (hf i).2.1.comp_left (g := fun r : ℝ => r ^ 2) (by norm_num)
  have hG0 : ∀ p, 0 ≤ fieldG χ f p := fun p =>
    Finset.sum_nonneg fun i _ => mul_nonneg (hχ0 i _) (sq_nonneg _)
  set P : ℝ → ℝ → ℝ := fun s t => kern a (s - t) *
    spatialPair Γ (fun x => fieldG χ f (s, x)) (fun x => fieldG χ f (t, x)) with hPdef
  have hP0 : ∀ s t, 0 ≤ P s t := fun s t =>
    mul_nonneg (kern_nonneg _ _) (spatialPair_nonneg Γ (fun x => hG0 _) (fun x => hG0 _))
  have hpair : ∀ s t, spatialPair Γ (fun x => fieldG χ f (s, x)) (fun x => fieldG χ f (t, x)) ≤
      R * w s * w t := by
    intro s t
    show spatialPair Γ (fun x => ∑ i, χ i s * f i x ^ 2) (fun x => ∑ j, χ j t * f j x ^ 2) ≤ _
    rw [spatialPair_fsum Γ (fun i => χ i s) (fun j => χ j t) hsq hsqs hsq hsqs]
    calc _ ≤ ∑ i, ∑ j, χ i s * χ j t * (R * b i ^ (alpha / 4) * b j ^ (alpha / 4)) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (pair_unit_le hE hsp (by linarith) hR0 hR (hf i) (hf j))
              (mul_nonneg (hχ0 i s) (hχ0 j t))
      _ = R * w s * w t := by
          simp only [hwdef]
          rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
  have hwe : ∀ s ∈ Icc (0 : ℝ) 1, w s ^ 2 ≤ e s ^ (alpha / 2) := by
    intro s hs
    have hj := (Real.concaveOn_rpow (p := alpha / 4) (by positivity) (by linarith)).le_map_sum
      (t := Finset.univ) (w := fun i => χ i s) (p := b) (fun i _ => hχ0 i s) (hχ1 s hs)
      (fun i _ => hb i)
    simp only [smul_eq_mul] at hj
    calc w s ^ 2 ≤ (e s ^ (alpha / 4)) ^ 2 := pow_le_pow_left₀ (hw0 s) hj 2
      _ = e s ^ (alpha / 2) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (he0 s)]; norm_num; ring_nf
  have : IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := ⟨by simp⟩
  have hint : IntegrableOn e (Ioo 0 1) := hec.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hint2 : IntegrableOn (fun s => e s ^ (alpha / 2)) (Ioo 0 1) :=
    (hec.rpow_const fun _ => Or.inr (by positivity)).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  have hT : fieldT χ f = ∫ s in Ioo (0 : ℝ) 1, e s := rfl
  have hT0 : 0 ≤ fieldT χ f := by
    rw [hT]; exact setIntegral_nonneg measurableSet_Ioo fun s _ => he0 s
  have hJ : ∫ s in Ioo (0 : ℝ) 1, e s ^ (alpha / 2) ≤ fieldT χ f ^ (alpha / 2) := by
    rw [hT]
    exact (Real.concaveOn_rpow (by positivity) (by linarith)).le_map_integral
      (Real.continuous_rpow_const (by positivity)).continuousOn isClosed_Ici
      (ae_of_all _ fun s => he0 s) hint hint2
  have step1 : stForm a Γ (fieldG χ f) (fieldG χ f) ≤
      (∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (∫ t in Ioo (0 : ℝ) 1, P s t)).toReal :=
    integral_le_toReal_lintegral fun s => integral_nonneg fun t => hP0 s t
  have step2 : ∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (∫ t in Ioo (0 : ℝ) 1, P s t) ≤
      ENNReal.ofReal R * (ENNReal.ofReal (K0 a) * ENNReal.ofReal (fieldT χ f ^ (alpha / 2))) := by
    calc _ ≤ ∫⁻ s in Ioo (0 : ℝ) 1, ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (P s t) :=
          lintegral_mono fun s => ofReal_integral_le (hP0 s)
      _ ≤ ∫⁻ s in Ioo (0 : ℝ) 1, ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal R *
            (ENNReal.ofReal (w s) * ENNReal.ofReal (w t) * ENNReal.ofReal (kern a (s - t))) := by
          refine lintegral_mono fun s => lintegral_mono fun t => ?_
          rw [← ENNReal.ofReal_mul (hw0 s), ← ENNReal.ofReal_mul (mul_nonneg (hw0 s) (hw0 t)),
            ← ENNReal.ofReal_mul hR0]
          apply ENNReal.ofReal_le_ofReal
          calc P s t ≤ kern a (s - t) * (R * w s * w t) :=
                mul_le_mul_of_nonneg_left (hpair s t) (kern_nonneg _ _)
            _ = _ := by ring
      _ = ENNReal.ofReal R * ∫⁻ s in Ioo (0 : ℝ) 1, ∫⁻ t in Ioo (0 : ℝ) 1,
            ENNReal.ofReal (w s) * ENNReal.ofReal (w t) * ENNReal.ofReal (kern a (s - t)) := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun s => ?_
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal R * (ENNReal.ofReal (K0 a) *
            ∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (w s) ^ 2) := by
          gcongr
          exact schur_sharp hb0 hb1 (ENNReal.measurable_ofReal.comp hwc.measurable)
      _ ≤ _ := by
          gcongr
          calc ∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (w s) ^ 2
              ≤ ∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (e s ^ (alpha / 2)) := by
                refine lintegral_mono_ae ?_
                filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
                rw [← ENNReal.ofReal_pow (hw0 s)]
                exact ENNReal.ofReal_le_ofReal (hwe s (Ioo_subset_Icc_self hs))
            _ = ENNReal.ofReal (∫ s in Ioo (0 : ℝ) 1, e s ^ (alpha / 2)) :=
                (ofReal_integral_eq_lintegral_ofReal hint2
                  (ae_of_all _ fun s => Real.rpow_nonneg (he0 s) _)).symm
            _ ≤ _ := ENNReal.ofReal_le_ofReal hJ
  calc stForm a Γ (fieldG χ f) (fieldG χ f) ≤ _ := step1
    _ ≤ (ENNReal.ofReal R * (ENNReal.ofReal (K0 a) *
          ENNReal.ofReal (fieldT χ f ^ (alpha / 2)))).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)) step2
    _ = K0 a * R * fieldT χ f ^ (alpha / 2) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hR0,
          ENNReal.toReal_ofReal (K0_pos hb1).le, ENNReal.toReal_ofReal (Real.rpow_nonneg hT0 _)]
        ring

/-! ### Step (b): the finite hat partition in time -/

/-- Auxiliary to the Lean proof route: a function `C`-Lipschitz on `[0,1]` is continuous there. -/
theorem continuousOn_of_lip {f : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, |f s - f t| ≤ C * |s - t|) :
    ContinuousOn f (Icc 0 1) := by
  refine (LipschitzOnWith.of_dist_le_mul (K := Real.toNNReal C) fun s hs t ht => ?_).continuousOn
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hC]
  exact h s hs t ht

/-- Step (b) of the route (TeX: `L:occupation-rayleigh-selection`, lines 149-193, whose countable
measurable selection is replaced here by a finite partition of unity in time): under the
section's standing assumptions (`H:homog`, `Γ ≠ 0`, `a = α₀`), for `Ψ ∈ C_pos` and `ε > 0` there
are a finite index type, continuous compactly supported `χ_i ≥ 0` with `∑_i χ_i = 1` on `[0,1]`
and real unit tests `f_i` such that, for `G = ∑_i χ_i(s) f_i²` and `T(G) = ∫_0^1 ∑_i χ_i b(f_i)`,
`∫_0^1 λ_s² ds - ε ≤ ∫_0^1 ∫ h_s G_s dx ds - T(G)` (with `λ_s² = sup R_{h_s}`).  Route: near-optimal
unit tests at finitely many nodes (`exists_unitTest_gt`), the uniform Lipschitz bounds in `s` of
`∫ h_s f²` (from `E:variational-global-mean`) and of `λ_s²` (`P:variational-unmasked-rate`), a
finite subcover of `[0,1]` by balls and a subordinate partition of unity. -/
theorem exists_near_field {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ0 : Γ ≠ 0) {Ψ : ℝ × Rd d → ℝ}
    (hΨ : Ψ ∈ CPos d) {ε : ℝ} (hε : 0 < ε) :
    ∃ (ι : Type) (_ : Fintype ι) (χ : ι → ℝ → ℝ) (f : ι → Rd d → ℝ),
      (∀ i, Continuous (χ i)) ∧ (∀ i, HasCompactSupport (χ i)) ∧ (∀ i s, 0 ≤ χ i s) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∑ i, χ i s = 1) ∧ (∀ i, IsUnitTest (f i)) ∧
      (∫ s in Ioo (0 : ℝ) 1, sSup (rayleighSet (mean alpha0 Γ Ψ s))) - ε ≤
        (∫ s in Ioo (0 : ℝ) 1, ∫ x, mean alpha0 Γ Ψ s x * fieldG χ f (s, x)) - fieldT χ f := by
  obtain ⟨ε0, M, C, -, -, hC, hbd, hlipx, hR, hsupLip, -⟩ :=
    VariationalRate.variational_unmasked_rate_paper hH hΓ0 hΨ
  obtain ⟨-, -, -, -, -, -, -, -, hcont, hpot⟩ :=
    VariationalMean.variational_global_mean_paper hH hΓ0 hΨ
  set L : ℝ → ℝ := fun s => sSup (rayleighSet (mean alpha0 Γ Ψ s)) with hLdef
  set m : (Rd d → ℝ) → ℝ → ℝ := fun g s => ∫ x, mean alpha0 Γ Ψ s x * g x ^ 2 with hmdef
  have hL2 : ∀ g : Rd d → ℝ, IsUnitTest g → MemLp g 2 volume := fun g hg =>
    VariationalFloor.memLp_test ⟨hg.1, hg.2.1⟩
  have hmlip : ∀ g : Rd d → ℝ, IsUnitTest g → ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |m g s - m g t| ≤ C * |s - t| := by
    intro g hg s hs t ht
    have hsqt := SpatialFourLinear.isTest_sq (φ := g) ⟨hg.1, hg.2.1⟩
    have hsq : Integrable (fun x => g x ^ 2) volume :=
      hsqt.1.continuous.integrable_of_hasCompactSupport hsqt.2
    have e : m g s - m g t = ∫ x, (mean alpha0 Γ Ψ s x - mean alpha0 Γ Ψ t x) * g x ^ 2 := by
      simp only [hmdef]
      rw [← integral_sub (hpot s hs g (hL2 g hg)) (hpot t ht g (hL2 g hg))]
      congr 1; funext x; ring
    rw [e, ← Real.norm_eq_abs]
    calc _ ≤ ∫ x, C * |s - t| * g x ^ 2 :=
          norm_integral_le_of_norm_le (hsq.const_mul _) (ae_of_all _ fun x => by
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (g x))]
            exact mul_le_mul_of_nonneg_right (hlipx s hs t ht x) (sq_nonneg _))
      _ = C * |s - t| := by rw [integral_const_mul, hg.2.2, mul_one]
  have hLcont : ContinuousOn L (Icc 0 1) := continuousOn_of_lip hC hsupLip
  set δ := ε / (4 * (C + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  have h2Cδ : 2 * (C * δ) ≤ ε / 2 := by
    rw [hδdef, show 2 * (C * (ε / (4 * (C + 1)))) = ε / 2 * (C / (C + 1)) by field_simp; ring]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one (by positivity)).2 (by linarith))
  have hsel : ∀ c : Icc (0 : ℝ) 1, ∃ g, IsUnitTest g ∧ L c - ε / 2 < m g c - gradEnergy g :=
    fun c => exists_unitTest_gt (hcont c c.2) (fun x => (hbd c c.2 x).1)
      (fun x => (hbd c c.2 x).2) (hR c c.2).1 (by linarith)
  choose g hgU hgv using hsel
  obtain ⟨t, ht⟩ := isCompact_Icc.elim_finite_subcover
    (fun c : Icc (0 : ℝ) 1 => ball (c : ℝ) δ) (fun _ => isOpen_ball)
    (fun s hs => mem_iUnion.2 ⟨⟨s, hs⟩, mem_ball_self hδ⟩)
  have hcov : Icc (0 : ℝ) 1 ⊆ ⋃ i : t, ball ((i.1 : Icc (0 : ℝ) 1) : ℝ) δ := by
    intro s hs
    obtain ⟨c, hc, hsc⟩ := mem_iUnion₂.1 (ht hs)
    exact mem_iUnion.2 ⟨⟨c, hc⟩, hsc⟩
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_Icc
    (fun i : t => ball ((i.1 : Icc (0 : ℝ) 1) : ℝ) δ) (fun _ => isOpen_ball) hcov
  have hsum : ∀ s ∈ Icc (0 : ℝ) 1, ∑ i, ρ i s = 1 := fun s hs => by
    rw [← finsum_eq_sum_of_fintype]; exact ρ.sum_eq_one hs
  have hkey : ∀ s ∈ Icc (0 : ℝ) 1,
      L s - ε ≤ ∑ i : t, ρ i s * (m (g i.1) s - gradEnergy (g i.1)) := by
    intro s hs
    have h1 : ∑ i : t, ρ i s * (L s - ε) = L s - ε := by
      rw [← Finset.sum_mul, hsum s hs, one_mul]
    rw [← h1]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases h0 : ρ i s = 0
    · rw [h0, zero_mul, zero_mul]
    refine mul_le_mul_of_nonneg_left ?_ (ρ.nonneg i s)
    have hsb : s ∈ ball ((i.1 : Icc (0 : ℝ) 1) : ℝ) δ := hρ i (subset_tsupport _ h0)
    rw [mem_ball, Real.dist_eq] at hsb
    have h2 := abs_le.mp (hmlip (g i.1) (hgU i.1) s hs i.1 i.1.2)
    have h3 := abs_le.mp (hsupLip s hs i.1 i.1.2)
    have h4 := hgv i.1
    have hCδ : C * |s - i.1| ≤ C * δ := mul_le_mul_of_nonneg_left hsb.le hC
    simp only [hLdef] at h3 h4 ⊢
    linarith [h2.1, h2.2, h3.1, h3.2]
  have hmeq : ∀ s ∈ Icc (0 : ℝ) 1, ∫ x, mean alpha0 Γ Ψ s x *
      fieldG (fun i : t => ⇑(ρ i)) (fun i => g i.1) (s, x) = ∑ i : t, ρ i s * m (g i.1) s := by
    intro s hs
    show ∫ x, mean alpha0 Γ Ψ s x * ∑ i : t, ρ i s * g i.1 x ^ 2 = _
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum _ fun i _ =>
      ((hpot s hs _ (hL2 _ (hgU i.1))).const_mul (ρ i s)).congr (ae_of_all _ fun x => by ring)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hmdef]
    rw [← integral_const_mul]; congr 1; funext x; ring
  have hsumcont : ContinuousOn (fun s => ∑ i : t, ρ i s * m (g i.1) s) (Icc 0 1) :=
    continuousOn_finsetSum _ fun i _ => (ρ i).continuous.continuousOn.mul
      (continuousOn_of_lip hC (hmlip _ (hgU i.1)))
  have hI1 : IntegrableOn (fun s => L s - ε) (Ioo 0 1) :=
    (hLcont.sub continuousOn_const).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hI2 : IntegrableOn (fun s => ∫ x, mean alpha0 Γ Ψ s x *
      fieldG (fun i : t => ⇑(ρ i)) (fun i => g i.1) (s, x)) (Ioo 0 1) :=
    (hsumcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self).congr_fun
      (fun s hs => (hmeq s (Ioo_subset_Icc_self hs)).symm) measurableSet_Ioo
  have hI3 : IntegrableOn (fun s => ∑ i : t, ρ i s * gradEnergy (g i.1)) (Ioo 0 1) :=
    (continuous_finsetSum _ fun i _ => (ρ i).continuous.mul continuous_const).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  have hvol : (volume : Measure ℝ).real (Ioo 0 1) = 1 := by simp
  refine ⟨t, inferInstance, fun i => ρ i, fun i => g i.1, fun i => (ρ i).continuous,
    fun i => IsCompact.of_isClosed_subset (isCompact_closedBall _ δ) (isClosed_tsupport _)
      ((hρ i).trans ball_subset_closedBall), fun i s => ρ.nonneg i s, hsum,
    fun i => hgU i.1, ?_⟩
  calc (∫ s in Ioo (0 : ℝ) 1, L s) - ε = ∫ s in Ioo (0 : ℝ) 1, (L s - ε) := by
        rw [integral_sub (hLcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
          (continuousOn_const.integrableOn_Icc.mono_set Ioo_subset_Icc_self), setIntegral_const,
          hvol, one_smul]
    _ ≤ ∫ s in Ioo (0 : ℝ) 1, ((∫ x, mean alpha0 Γ Ψ s x *
          fieldG (fun i : t => ⇑(ρ i)) (fun i => g i.1) (s, x)) -
          ∑ i : t, ρ i s * gradEnergy (g i.1)) := by
        refine setIntegral_mono_on hI1 (hI2.sub hI3) measurableSet_Ioo fun s hs => ?_
        rw [hmeq s (Ioo_subset_Icc_self hs), ← Finset.sum_sub_distrib]
        refine (hkey s (Ioo_subset_Icc_self hs)).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = _ := integral_sub hI2 hI3

/-! ### The named input: space-time positivity (step (c), wave item L8-c1) -/

/-- **Named input (step (c) of the route, proved by wave item L8-c1).**  Three facts about the
space-time form `stForm` (`F`) for the section's controls `Ψ ∈ C_pos` and nonnegative continuous
compactly supported space-time fields `Φ` on `ℝ × ℝ^d` (such as `fieldG`):
* `cs`: Cauchy-Schwarz `F(Ψ,Φ)² ≤ F(Ψ,Ψ) F(Φ,Φ)` (positive semidefiniteness of the form: the
  Hilbert inclusion `J_{H_sp}` of `L:positive-raw-embedding`,
  `integrated_intrinsic_constant.tex` lines 22-39, `E:positive-bochner-inclusion`);
* `self`: `F(Ψ,Ψ) = v_Ψ` (the first identity of `E:positive-raw-mean`, line 34, with `v_Ψ` the
  integral form `VariationalDilation.rawCost` of `E:compact-raw-cost`);
* `mean`: `∫_0^1 ∫ h_{Ψ,s} Φ_s dx ds = F(Ψ,Φ)` (the second identity of
  `E:occupation-raw-identities`, `integrated_occupation_ceiling.tex` lines 34-37, for a squared
  field in the place of `g_s²`).
All three are deterministic and follow from positive-definiteness of `|s-t|^{-a}` and of `Γ`
and Fubini; they are no stronger than the manuscript statements named.  The hypothesis is
assumed only for the fields listed (it carries no statement about other fields). -/
structure SpaceTimeCS (a : ℝ) (Γ : Measure (Rd d)) : Prop where
  cs : ∀ Ψ ∈ CPos d, ∀ Φ : ℝ × Rd d → ℝ, Continuous Φ → HasCompactSupport Φ →
    (∀ p, 0 ≤ Φ p) → stForm a Γ Ψ Φ ^ 2 ≤ stForm a Γ Ψ Ψ * stForm a Γ Φ Φ
  self : ∀ Ψ ∈ CPos d, stForm a Γ Ψ Ψ = rawCost a Γ Ψ
  mean : ∀ Ψ ∈ CPos d, ∀ Φ : ℝ × Rd d → ℝ, Continuous Φ → HasCompactSupport Φ →
    (∀ p, 0 ≤ Φ p) → ∫ s in Ioo (0 : ℝ) 1, ∫ x, mean a Γ Ψ s x * Φ (s, x) = stForm a Γ Ψ Φ

/-! ### Step (e): assembly -/

/-- Auxiliary to the Lean proof route: under `H:homog` and `Γ ≠ 0`: `0 < α < 2`, `R_0 > 0`, and `A_sp(g) ≤ R_0 b(g)^{α/2}` for every real unit test `g`
(`P:spatial-smooth-ratio`, `SpatialSmoothRatio.spatial_smooth_ratio_R0_paper`). -/
theorem R0_bound {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ0 : Γ ≠ 0) :
    0 < alpha ∧ alpha < 2 ∧ 0 < R0 Γ alpha ∧
      ∀ g, IsUnitTest g → spatialEnergy Γ g ≤ R0 Γ alpha * gradEnergy g ^ (alpha / 2) := by
  obtain ⟨-, ha0, ha2, -⟩ := SpatialSmoothRatio.homog_consequences hH
  obtain ⟨hpos, -, -, -, hR0, -, hle⟩ := SpatialSmoothRatio.spatial_smooth_ratio_R0_paper hH hΓ0
  refine ⟨ha0, ha2, hR0, fun g hg => ?_⟩
  have hb := (hpos g hg).1
  have h := hle g hg
  rwa [SpatialSmoothRatio.ratio, div_le_iff₀ (Real.rpow_pos_of_pos hb _)] at h

/-- **Step (e), first half (TeX `L:occupation-rayleigh-selection` and the proof of
`T:intrinsic-occupation-ceiling`, lines 175-193 and 222-234, with `C_occ` replaced by
`K_0 R_0`):** under the standing assumptions (`H:homog`, `Γ ≠ 0`, `a = α₀`) and the named input
`SpaceTimeCS α₀ Γ`, every `Ψ ∈ C_pos` satisfies
`I_Ψ² ≤ (q/4)(α/4)^{α/q} (v_Ψ K_0 R_0)^{2/q}`, `q = 4 - α`, i.e. `I_Ψ ≤ D v_Ψ^{1/q}` with
`D = √(q/4)(α/4)^{α/(2q)} (K_0R_0)^{1/q}` (TeX line 233).  Route: `I_Ψ² ≤ ∫_0^1 λ_s²` (Jensen),
`exists_near_field`, the named input (`mean`, `cs`, `self`), `field_energy_le`, and
`young_quarter`, then `ε → 0`. -/
theorem integratedRate_sq_le {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ0 : Γ ≠ 0) (hST : SpaceTimeCS alpha0 Γ)
    {Ψ : ℝ × Rd d → ℝ} (hΨ : Ψ ∈ CPos d) :
    integratedRate alpha0 Γ Ψ ^ 2 ≤ (4 - alpha) / 4 * (alpha / 4) ^ (alpha / (4 - alpha)) *
      (rawCost alpha0 Γ Ψ * (K0 alpha0 * R0 Γ alpha)) ^ (2 / (4 - alpha)) := by
  obtain ⟨ha0, ha2, hR0, hR⟩ := R0_bound hH hΓ0
  have := hH.Γ_radon
  have hv : 0 < rawCost alpha0 Γ Ψ :=
    ((VariationalRate.variational_positive_scores_paper hH hΓ0).2.1 Ψ hΨ).2.2.2.2
  obtain ⟨ε0, M, C, -, -, hC, -, -, hRs, hsupLip, -, hint, -, -⟩ :=
    VariationalRate.variational_unmasked_rate_paper hH hΓ0 hΨ
  have hLcont := continuousOn_of_lip hC hsupLip
  have : IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := ⟨by simp⟩
  have hI2 : integratedRate alpha0 Γ Ψ ^ 2 ≤
      ∫ s in Ioo (0 : ℝ) 1, sSup (rayleighSet (mean alpha0 Γ Ψ s)) := by
    have heq : EqOn (fun s => rate alpha0 Γ Ψ s ^ 2)
        (fun s => sSup (rayleighSet (mean alpha0 Γ Ψ s))) (Ioo 0 1) := fun s hs =>
      (hRs s (Ioo_subset_Icc_self hs)).2.2.2.2.1
    have hsq : IntegrableOn (fun s => rate alpha0 Γ Ψ s ^ 2) (Ioo 0 1) :=
      (hLcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self).congr_fun
        (fun s hs => (heq hs).symm) measurableSet_Ioo
    have hj := (convexOn_pow 2).map_integral_le (μ := volume.restrict (Ioo (0 : ℝ) 1))
      (continuous_pow 2).continuousOn isClosed_Ici
      (ae_of_all _ fun s => (Real.sqrt_nonneg _ : (0 : ℝ) ≤ rate alpha0 Γ Ψ s)) hint hsq
    calc integratedRate alpha0 Γ Ψ ^ 2 ≤ ∫ s in Ioo (0 : ℝ) 1, rate alpha0 Γ Ψ s ^ 2 := hj
      _ = _ := setIntegral_congr_fun measurableSet_Ioo heq
  set X := rawCost alpha0 Γ Ψ * (K0 alpha0 * R0 Γ alpha) with hXdef
  have hX : 0 ≤ X := mul_nonneg hv.le (mul_nonneg (K0_pos hH.alpha0_lt_one).le hR0.le)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨ι, _, χ, f, hχc, hχs, hχ0, hχ1, hf, hnear⟩ := exists_near_field hH hΓ0 hΨ hε
  obtain ⟨hGc, hGs, hG0⟩ := fieldG_props hχc hχs hχ0 fun i => ⟨(hf i).1, (hf i).2.1⟩
  have hFGG := field_energy_le hH.Γ_even hH.spectral ha0 ha2 hR0.le hR hH.alpha0_pos.le
    hH.alpha0_lt_one hχc hχ0 hχ1 hf
  have hmean := hST.mean Ψ hΨ _ hGc hGs hG0
  have hcs := hST.cs Ψ hΨ _ hGc hGs hG0
  rw [hST.self Ψ hΨ] at hcs
  have hT0 : 0 ≤ fieldT χ f := setIntegral_nonneg measurableSet_Ioo fun s _ =>
    Finset.sum_nonneg fun i _ => mul_nonneg (hχ0 i s) (SpatialFourierBound.gradEnergy_nonneg _)
  have hF : stForm alpha0 Γ Ψ (fieldG χ f) ≤ Real.sqrt X * fieldT χ f ^ (alpha / 4) := by
    calc stForm alpha0 Γ Ψ (fieldG χ f) ≤ |stForm alpha0 Γ Ψ (fieldG χ f)| := le_abs_self _
      _ = Real.sqrt (stForm alpha0 Γ Ψ (fieldG χ f) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (rawCost alpha0 Γ Ψ * (K0 alpha0 * R0 Γ alpha * fieldT χ f ^ (alpha / 2))) :=
          Real.sqrt_le_sqrt (hcs.trans (mul_le_mul_of_nonneg_left hFGG hv.le))
      _ = Real.sqrt X * fieldT χ f ^ (alpha / 4) := by
          rw [show rawCost alpha0 Γ Ψ * (K0 alpha0 * R0 Γ alpha * fieldT χ f ^ (alpha / 2)) =
            X * fieldT χ f ^ (alpha / 2) by rw [hXdef]; ring, Real.sqrt_mul hX,
            Real.sqrt_eq_rpow (fieldT χ f ^ (alpha / 2)), ← Real.rpow_mul hT0]
          ring_nf
  have hY := young_quarter ha0 (by linarith) hX hT0
  rw [hmean] at hnear
  linarith

/-- **Step (e), second half: the occupation ceiling with `K_0 R_0`** (TeX
`T:intrinsic-occupation-ceiling`, lines 205-220, proof 222-245, with `C_occ` replaced by
`C = K_0 R_0`): under the standing assumptions and `SpaceTimeCS α₀ Γ`, for every `c > 0` and
`Ψ ∈ C_pos`, `c I_Ψ - v_Ψ/2 ≤ U_c = c^m k [α^{α/2} K_0 R_0/(8 q^{q/2})]^{1/k}`.  Route:
`integratedRate_sq_le`, `young_q` and `ceilingValue_eq`. -/
theorem score_le_ceiling {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ0 : Γ ≠ 0) (hST : SpaceTimeCS alpha0 Γ)
    {c : ℝ} (hc : 0 < c) {Ψ : ℝ × Rd d → ℝ} (hΨ : Ψ ∈ CPos d) :
    c * integratedRate alpha0 Γ Ψ - rawCost alpha0 Γ Ψ / 2 ≤
      ceilingValue alpha c (K0 alpha0 * R0 Γ alpha) := by
  obtain ⟨ha0, ha2, hR0, -⟩ := R0_bound hH hΓ0
  have := hH.Γ_radon
  have hv : 0 < rawCost alpha0 Γ Ψ :=
    ((VariationalRate.variational_positive_scores_paper hH hΓ0).2.1 Ψ hΨ).2.2.2.2
  set C := K0 alpha0 * R0 Γ alpha with hCdef
  have hC : 0 < C := mul_pos (K0_pos hH.alpha0_lt_one) hR0
  have hq : 0 < 4 - alpha := by linarith
  have hP : 0 < (4 - alpha) / 4 * (alpha / 4) ^ (alpha / (4 - alpha)) := by positivity
  have hsq := integratedRate_sq_le hH hΓ0 hST hΨ
  rw [← hCdef] at hsq
  have hIle : integratedRate alpha0 Γ Ψ ≤ Real.sqrt ((4 - alpha) / 4 *
      (alpha / 4) ^ (alpha / (4 - alpha))) * C ^ (1 / (4 - alpha)) *
      rawCost alpha0 Γ Ψ ^ (1 / (4 - alpha)) := by
    have h1 := (le_abs_self _).trans (Real.abs_le_sqrt hsq)
    rw [Real.sqrt_mul hP.le, Real.sqrt_eq_rpow ((rawCost alpha0 Γ Ψ * C) ^ _),
      ← Real.rpow_mul (mul_nonneg hv.le hC.le), Real.mul_rpow hv.le hC.le] at h1
    rw [show 2 / (4 - alpha) * (1 / 2) = 1 / (4 - alpha) by field_simp] at h1
    linarith
  have hY := young_q (alpha := alpha) (by linarith)
    (E := c * Real.sqrt ((4 - alpha) / 4 * (alpha / 4) ^ (alpha / (4 - alpha))) *
      C ^ (1 / (4 - alpha))) (by positivity) hv.le
  rw [ceilingValue_eq ha0 ha2 hC hc] at hY
  nlinarith [mul_le_mul_of_nonneg_left hIle hc.le]

/-! ### The manuscript's statements over the named input `SpaceTimeCS` -/

/-- **`T:intrinsic-occupation-ceiling`, `E:occupation-score-ceiling` with `C_occ` replaced by
`K_0 R_sp`** (`integrated_occupation_ceiling.tex` lines 205-220 at a284420; `K_0 R_sp` is the
upper bound of `C_occ` in `P:raw-occupation-energy`, line 96), under the section's standing
assumptions (lines 4-21: `H:homog`, `a = α₀`, `Γ ≠ 0`) and the named input
`SpaceTimeCS α₀ Γ`: for every `c > 0` and `Ψ ∈ C_pos`,
`c I_Ψ - v_Ψ/2 ≤ U_c = c^m k [α^{α/2} K_0 R_sp/(8 q^{q/2})]^{1/k}`.  The conclusion is
literally the proposition `SpatialBracket.OccupationCeilingK0 α α₀ Γ` of wave item L8-d.
Narrower than the TeX: the constant is `K_0 R_sp ≥ C_occ`, not `C_occ` (the class `𝒪` with the
original kernel, `A(g)` and `C_occ` are not formalized); the second form
`c^m (2ζ)^{α/(2k)} F_0(𝓔_ζ^𝒪)` and the moment statement `C_2 ≤ U_2` (which needs
`T:intrinsic-second-moment`, foundation D1) are not formalized.  Route difference: a finite
partition of unity in time (`exists_near_field`) instead of the countable measurable selection
of `L:occupation-rayleigh-selection`, and the named input `SpaceTimeCS` in the place of
`L:occupation-raw-square`. -/
theorem occupation_ceiling_K0_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ0 : Γ ≠ 0) (hST : SpaceTimeCS alpha0 Γ) :
    ∀ c : ℝ, 0 < c → ∀ Ψ ∈ CPos d, c * integratedRate alpha0 Γ Ψ - rawCost alpha0 Γ Ψ / 2 ≤
      ceilingValue alpha c (K0 alpha0 * Rsp Γ alpha) := by
  intro c hc Ψ hΨ
  rw [(SpatialOccupationL7Completed.spatial_ratio_H1_paper_completed hH hΓ0).2.2.2]
  exact score_le_ceiling hH hΓ0 hST hc hΨ

/-- **`P:variational-positive-scores`, the boundedness claim** (`S1Bdd`,
`integrated_unmasked_variational.tex` lines 272-274 at a284420), proved deterministically under
the standing assumptions (`H:homog`, `Γ ≠ 0`, `a = α₀`) and the named input `SpaceTimeCS α₀ Γ`:
the coefficient-one set `{I_Ψ - v_Ψ/2}` is bounded above by `U_1` (with `K_0 R_0`).  Route
difference: the TeX's proof (lines 309-325) is stochastic (`T:full-upper` and
`E:variational-unmasked-point-lower`); here it is the ceiling `score_le_ceiling` at `c = 1`. -/
theorem s1Bdd_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ0 : Γ ≠ 0) (hST : SpaceTimeCS alpha0 Γ) :
    S1Bdd alpha0 Γ := by
  refine ⟨ceilingValue alpha 1 (K0 alpha0 * R0 Γ alpha), ?_⟩
  rintro _ ⟨Ψ, hΨ, rfl⟩
  have := score_le_ceiling hH hΓ0 hST one_pos hΨ
  rwa [one_mul] at this

/-- **`T:intrinsic-occupation-ceiling` for the suprema** (TeX lines 209-212, "take the supremum
over the smooth positive-control class", line 245), with `C_occ` replaced by `K_0 R_sp`, under the
standing assumptions and `SpaceTimeCS α₀ Γ`: for every `c > 0` the set `{c I_Ψ - v_Ψ/2}` is
nonempty and bounded above and `S_c^pos ≤ U_c`.  Narrower as in
`occupation_ceiling_K0_paper`. -/
theorem occupation_ceiling_sSup_K0_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ0 : Γ ≠ 0) (hST : SpaceTimeCS alpha0 Γ) :
    ∀ c : ℝ, 0 < c → (scoreSet alpha0 Γ c).Nonempty ∧ BddAbove (scoreSet alpha0 Γ c) ∧
      sSup (scoreSet alpha0 Γ c) ≤ ceilingValue alpha c (K0 alpha0 * Rsp Γ alpha) := by
  intro c hc
  have hne := (VariationalRate.variational_positive_scores_paper hH hΓ0).1 c
  have hb : ∀ y ∈ scoreSet alpha0 Γ c, y ≤ ceilingValue alpha c (K0 alpha0 * Rsp Γ alpha) := by
    rintro _ ⟨Ψ, hΨ, rfl⟩
    exact occupation_ceiling_K0_paper hH hΓ0 hST c hc Ψ hΨ
  exact ⟨hne, ⟨_, hb⟩, csSup_le hne hb⟩

/-- **`P:variational-positive-scores`, supremum part, without `S1Bdd`**
(`integrated_unmasked_variational.tex` lines 272-277 and 327-332 at a284420):
`VariationalRate.variational_positive_scores_sSup_paper` with `S1Bdd` discharged by
`s1Bdd_paper` over the named input `SpaceTimeCS α₀ Γ`.  `S_1^pos > 0` and for every `c > 0`
the value set is nonempty, bounded above, with `S_c^pos = c^{(4-α)/(3-α)} S_1^pos > 0`.
Narrower as the source: `Q_2 ≥ S_2^pos` is not formalized. -/
theorem variational_positive_scores_sSup_st_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ0 : Γ ≠ 0) (hST : SpaceTimeCS alpha0 Γ) :
    0 < S1pos alpha0 Γ ∧
    ∀ c, 0 < c → (scoreSet alpha0 Γ c).Nonempty ∧ BddAbove (scoreSet alpha0 Γ c) ∧
      0 < sSup (scoreSet alpha0 Γ c) ∧
      sSup (scoreSet alpha0 Γ c) = c ^ ((4 - alpha) / (3 - alpha)) * S1pos alpha0 Γ :=
  VariationalRate.variational_positive_scores_sSup_paper hH hΓ0 (s1Bdd_paper hH hΓ0 hST)

/-- `E:spatial-static-score` in the `sSup` form (`integrated_spatial_occupation.tex` lines 50-53
at a284420): `SpatialStaticControls.spatial_static_score_sSup_paper` with `S1Bdd` discharged
over `SpaceTimeCS α₀ Γ`: `S_1^pos ≥ λ_z(1) - (M_a/2) B_Γ(z,z)` for every nonnegative nonzero
test function `z`. -/
theorem spatial_static_score_sSup_st_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ0 : Γ ≠ 0) (hST : SpaceTimeCS alpha0 Γ)
    {z : Rd d → ℝ} (hz : IsTestFunction z) (hz0 : ∀ x, 0 ≤ z x) (hzne : z ≠ 0) :
    SpatialStaticControls.lamZ Γ z 1 - TemporalEquilibrium.mass alpha0 / 2 *
        (OccupationKernelRow.pairing Γ (SpatialStaticControls.zE z)
          (SpatialStaticControls.zE z)).toReal ≤ S1pos alpha0 Γ :=
  SpatialStaticControls.spatial_static_score_sSup_paper hH hΓ0 (s1Bdd_paper hH hΓ0 hST) hz hz0
    hzne

/-- `E:spatial-smooth-score` in the `sSup` form (`integrated_spatial_occupation.tex` lines
171-176 at a284420): `SpatialOccupationCompleted.spatial_smooth_score_sSup_completed_paper` with
`S1Bdd` discharged over `SpaceTimeCS α₀ Γ`: `S_1^pos ≥ k [R(g) α^{α/2}/(8 M_a q^{q/2})]^{1/k}` for
every real unit test `g`. -/
theorem spatial_smooth_score_sSup_st_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ0 : Γ ≠ 0) (hST : SpaceTimeCS alpha0 Γ)
    {g : Rd d → ℝ} (hg : IsUnitTest g) :
    SpatialSmoothRatio.smoothScoreBound alpha alpha0 (SpatialSmoothRatio.ratio Γ alpha g) ≤
      S1pos alpha0 Γ :=
  SpatialOccupationCompleted.spatial_smooth_score_sSup_completed_paper hH hΓ0
    (s1Bdd_paper hH hΓ0 hST) hg

/-- "`S1Bdd ⇒ R_0` finite" (the manuscript's route before revision a284420):
`SpatialOccupationCompleted.R0_finite_of_S1Bdd_completed_paper` with `S1Bdd` discharged over
`SpaceTimeCS α₀ Γ`: the ratio set is bounded above and
`R_0 ≤ 8 M_a q^{q/2} (S_1^pos/k)^k / α^{α/2}`. -/
theorem R0_le_of_st_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ0 : Γ ≠ 0) (hST : SpaceTimeCS alpha0 Γ) :
    BddAbove (SpatialSmoothRatio.ratioSet Γ alpha) ∧
      R0 Γ alpha ≤ 8 * TemporalEquilibrium.mass alpha0 * (4 - alpha) ^ ((4 - alpha) / 2) *
        (S1pos alpha0 Γ / (3 - alpha)) ^ (3 - alpha) / alpha ^ (alpha / 2) :=
  SpatialOccupationCompleted.R0_finite_of_S1Bdd_completed_paper hH hΓ0 (s1Bdd_paper hH hΓ0 hST)

/-- `E:spatial-static-energy-score` in the `sSup` form (`integrated_spatial_occupation.tex`
lines 316-322 at a284420):
`SpatialOccupationL7Completed.spatial_static_energy_score_sSup_paper_completed` with `S1Bdd`
discharged over `SpaceTimeCS α₀ Γ`: `S_1^pos ≥ M_a^{-1/k} F₀(𝓔_sp)`. -/
theorem spatial_static_energy_score_sSup_st_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ0 : Γ ≠ 0) (hST : SpaceTimeCS alpha0 Γ) :
    TemporalEquilibrium.mass alpha0 ^ (-(1 / (3 - alpha))) *
        SpatialFourLinear.F0 alpha (SpatialFourLinear.Esp Γ) ≤ S1pos alpha0 Γ :=
  SpatialOccupationL7Completed.spatial_static_energy_score_sSup_paper_completed hH hΓ0
    (s1Bdd_paper hH hΓ0 hST)

end StratonovichHAMSecondMoment.OccupationCeilingFinite
