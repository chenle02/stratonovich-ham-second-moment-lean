module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L18, item A, decision 5 add-on (approved by Le on 2026-11-21): the `d = 1` classification
of `H:homog` and `DiagramLimits` for every `d = 1` covariance of `H:homog`.  TeX lines at
revision edf7085f (book 1.1.3), main file `notes/notes_stratonovich_ham_second_moment.tex`:
* `H:homog`, lines 384-401 (`Γ(cA) = c^{d-α}Γ(A)`, `0 < α < d` or `α = d = 1`, "the last case
  includes spatial white noise `Γ = δ_0`");
* `E:d1-covariances` (lines 5317-5322): its Riesz case (5319) is the covariance of
  `P:riesz-small` (5125-5172), and both its Riesz and white cases (5319, 5320) are used in
  `P:d1-upper` (5454-5466);
* `L:joint-fixed-order`, lines 1853-1966 (the TeX's source of the diagram limits).

Results:
* `homogCovariance_one_eq`: in `d = 1`, a covariance of `H:homog` is `Γ = c|y|^{-α} dy`
  (`volume.withDensity (riesz c α)`, `c ≥ 0`) when `0 < α < 1`, and `Γ = c δ_0`
  (`whiteCov c`, `c ≥ 0`) when `α = 1`.  Only local finiteness, evenness and the scaling of
  `H:homog` are used (not positive-definiteness or the spectral measure).  The constants are
  explicit: `c = (1 - α) Γ{0 < y ≤ 1}` and `c = Γ{0}` (`homogCovariance_one_riesz`,
  `homogCovariance_one_white`);
* `diagramLimits_homog_one`: `D1Upper.DiagramLimits 1 Γ α₀ t` for every `HomogCovariance 1`
  and `t > 0`, from `RieszDiagramLimits.diagramLimits_riesz` and `D1Upper.diagramLimits_white`.

**Route difference (disclosed).**  The TeX obtains the limits from the Wick-measure route of
`L:joint-fixed-order` (conventions 825-832).  Here, in `d = 1` only, they come from the
classification and the domination route of `RieszDiagramLimits` (Riesz) and the white-noise
collapse of `D1Upper.diagramLimits_white` (white).

Proof of the classification: push `Γ` forward to `ℝ` by the coordinate (`WaveGreen.coordOne`);
there `ν(r • A) = r^{1-α} ν(A)` and `ν` is even.  For `α < 1`: `ν{0} = 0`,
`ν(0, x] = x^{1-α} ν(0, 1]`, which determines `ν` on `(0, ∞)` (`Measure.ext_of_Ioc'`), and
evenness determines it on `(-∞, 0)`; the density measure `c|y|^{-α} dy` has the same values.
For `α = 1`: `ν(0, x] = ν(0, 1]` for all `x > 0`, and continuity from above gives
`ν(0, ∞) = 0`; by evenness `ν = ν{0} δ_0`.
-/

public import Mathlib
public import StratonovichHAMSecondMoment.RieszDiagramLimits

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise

namespace StratonovichHAMSecondMoment.RieszDiagramLimitsHomog

open HomogHypothesis (Rd HomogCovariance)
open HigherRieszTwo (riesz)
open WhiteModel (whiteCov)
open WaveGreen (coordOne coordOne_apply coordOne_mp norm_coord_one)

/-! ### Homogeneous even measures on `ℝ` -/

/-- The Riesz density on `ℝ`: `c|y|^{-α}`. -/
def rieszR (c α : ℝ) (y : ℝ) : ℝ≥0∞ := ENNReal.ofReal (c * |y| ^ (-α))

theorem measurable_rieszR (c α : ℝ) : Measurable (rieszR c α) :=
  (measurable_const.mul (continuous_abs.measurable.pow_const _)).ennreal_ofReal

/-- `ν(0, x] = x^β ν(0, 1]` for `x > 0`, from the scaling. -/
theorem measure_Ioc_of_scaling {ν : Measure ℝ} {β : ℝ}
    (hs : ∀ A : Set ℝ, MeasurableSet A → ∀ r : ℝ, 0 < r →
      ν (r • A) = ENNReal.ofReal (r ^ β) * ν A) {x : ℝ} (hx : 0 < x) :
    ν (Ioc 0 x) = ENNReal.ofReal (x ^ β) * ν (Ioc 0 1) := by
  have h := hs (Ioc 0 1) measurableSet_Ioc x hx
  rwa [LinearOrderedField.smul_Ioc hx, mul_zero, mul_one] at h

/-- `ν{0} = 0` when the degree is positive and `ν{0}` is finite. -/
theorem measure_zero_of_scaling {ν : Measure ℝ} {β : ℝ}
    (hs : ∀ A : Set ℝ, MeasurableSet A → ∀ r : ℝ, 0 < r →
      ν (r • A) = ENNReal.ofReal (r ^ β) * ν A) (hβ : 0 < β) (hfin : ν {0} ≠ ∞) :
    ν {0} = 0 := by
  have h := hs {0} (measurableSet_singleton 0) 2 two_pos
  rw [Set.smul_set_singleton, smul_zero] at h
  have h2 : (1 : ℝ) < 2 ^ β := Real.one_lt_rpow (by norm_num) hβ
  have hr := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hr
  have h0 : 0 ≤ (ν {0}).toReal := ENNReal.toReal_nonneg
  have hx : (ν {0}).toReal = 0 := by nlinarith
  exact ((ENNReal.toReal_eq_zero_iff _).1 hx).resolve_right hfin

/-- Two measures with the same finite values `G x` on every `(0, x]`, `x ≥ 0`, agree on
`(0, ∞)`. -/
theorem restrict_Ioi_eq {ν ν' : Measure ℝ} {G : ℝ → ℝ≥0∞} (hG : ∀ x, 0 ≤ x → G x ≠ ∞)
    (hν : ∀ x, 0 ≤ x → ν (Ioc 0 x) = G x) (hν' : ∀ x, 0 ≤ x → ν' (Ioc 0 x) = G x) :
    ν.restrict (Ioi 0) = ν'.restrict (Ioi 0) := by
  have hI : ∀ a b : ℝ, Ioc a b ∩ Ioi 0 = Ioc (max a 0) b := by
    intro a b
    ext y
    simp only [mem_inter_iff, mem_Ioc, mem_Ioi, max_lt_iff]
    tauto
  -- the value on `(a', b]`, `0 ≤ a'`, is determined by `G`
  have key : ∀ m : Measure ℝ, (∀ x, 0 ≤ x → m (Ioc 0 x) = G x) → ∀ a' b : ℝ, 0 ≤ a' →
      a' ≤ b → G a' + m (Ioc a' b) = G b := by
    intro m hm a' b ha hab
    rw [← hm a' ha, ← hm b (ha.trans hab), ← measure_union (Ioc_disjoint_Ioc_of_le le_rfl)
      measurableSet_Ioc, Ioc_union_Ioc_eq_Ioc ha hab]
  refine Measure.ext_of_Ioc' _ _ (fun a b _ => ?_) (fun a b _ => ?_)
  · rw [Measure.restrict_apply measurableSet_Ioc, hI]
    refine ne_top_of_le_ne_top (hG (max b 0) (le_max_right _ _)) ?_
    rw [← hν _ (le_max_right _ _)]
    exact measure_mono fun y hy => ⟨(le_max_right a 0).trans_lt hy.1, hy.2.trans (le_max_left _ _)⟩
  · rw [Measure.restrict_apply measurableSet_Ioc, Measure.restrict_apply measurableSet_Ioc, hI]
    set a' := max a 0
    have ha : 0 ≤ a' := le_max_right _ _
    rcases le_or_gt a' b with hab | hab
    · have h1 := key ν hν a' b ha hab
      have h2 := key ν' hν' a' b ha hab
      exact (ENNReal.add_right_inj (hG a' ha)).1 (h1.trans h2.symm)
    · rw [Ioc_eq_empty (not_lt.2 hab.le), measure_empty, measure_empty]

/-- For an even measure, the part on `(-∞, 0)` is the reflection of the part on `(0, ∞)`. -/
theorem restrict_Iio_of_even {m : Measure ℝ} (h : m.map (fun x : ℝ => -x) = m) :
    m.restrict (Iio 0) = (m.restrict (Ioi 0)).map (fun x : ℝ => -x) := by
  conv_lhs => rw [← h]
  rw [Measure.restrict_map measurable_neg measurableSet_Iio]
  congr 2
  ext x
  simp

/-- A measure with no atom at `0` is the sum of its parts on `(-∞, 0)` and `(0, ∞)`. -/
theorem eq_restrict_add {m : Measure ℝ} (h0 : m {0} = 0) :
    m = m.restrict (Iio 0) + m.restrict (Ioi 0) := by
  have hu := Measure.restrict_union (μ := m)
    (Set.disjoint_left.2 fun x (hx : x ∈ Iio (0 : ℝ)) (hx' : x ∈ Ioi 0) => lt_asymm hx hx')
    (measurableSet_Ioi (a := (0 : ℝ)))
  rw [Iio_union_Ioi] at hu
  rw [← hu]
  exact (Measure.restrict_eq_self_of_ae_mem
    ((measure_eq_zero_iff_ae_notMem.1 h0).mono fun _ hx => hx)).symm

/-! ### The Riesz density measure on `ℝ` -/

/-- `∫_{(0,x]} c|y|^{-α} dy = c x^{1-α}/(1-α)` for `x ≥ 0`, `c ≥ 0`, `α < 1`. -/
theorem withDensity_rieszR_Ioc {c α : ℝ} (hc : 0 ≤ c) (hα : α < 1) {x : ℝ} (hx : 0 ≤ x) :
    volume.withDensity (rieszR c α) (Ioc 0 x) = ENNReal.ofReal (c * x ^ (1 - α) / (1 - α)) := by
  rw [withDensity_apply _ measurableSet_Ioc]
  have hcongr : ∫⁻ y in Ioc 0 x, rieszR c α y = ∫⁻ y in Ioc 0 x, ENNReal.ofReal (c * y ^ (-α)) :=
    setLIntegral_congr_fun measurableSet_Ioc fun y hy => by
      rw [rieszR, abs_of_pos hy.1]
  have hint : IntervalIntegrable (fun y : ℝ => c * y ^ (-α)) volume 0 x :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul c
  rw [hcongr, ← ofReal_integral_eq_lintegral_ofReal
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hx).1 hint)
    ((ae_restrict_mem measurableSet_Ioc).mono fun y hy =>
      mul_nonneg hc (Real.rpow_nonneg hy.1.le _)),
    ← intervalIntegral.integral_of_le hx, intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by linarith)),
    Real.zero_rpow (by linarith : -α + 1 ≠ 0), sub_zero, show -α + 1 = 1 - α by ring,
    mul_div_assoc]

theorem withDensity_rieszR_zero (c α : ℝ) : volume.withDensity (rieszR c α) {0} = 0 := by
  rw [withDensity_apply _ (measurableSet_singleton 0)]
  exact setLIntegral_measure_zero _ _ Real.volume_singleton

theorem withDensity_rieszR_even (c α : ℝ) :
    (volume.withDensity (rieszR c α)).map (fun x : ℝ => -x) = volume.withDensity (rieszR c α) := by
  ext S hS
  rw [Measure.map_apply measurable_neg hS, withDensity_apply _ (measurable_neg hS),
    withDensity_apply _ hS]
  have hmp : MeasurePreserving (fun x : ℝ => -x) volume volume := Measure.measurePreserving_neg _
  have := hmp.setLIntegral_comp_preimage_emb (MeasurableEquiv.neg ℝ).measurableEmbedding
    (rieszR c α) S
  rw [← this]
  refine lintegral_congr fun y => ?_
  simp [rieszR, abs_neg]

/-! ### The transfer to `ℝ¹` -/

theorem coordOne_neg (x : Rd 1) : coordOne (-x) = -coordOne x := by
  simp [coordOne_apply]

theorem preimage_coordOne_smul {r : ℝ} (hr : 0 < r) (A : Set ℝ) :
    coordOne ⁻¹' (r • A) = r • (coordOne ⁻¹' A) := by
  ext x
  rw [mem_preimage, mem_smul_set_iff_inv_smul_mem₀ hr.ne', mem_smul_set_iff_inv_smul_mem₀ hr.ne',
    mem_preimage, coordOne_apply, coordOne_apply]
  simp

/-- The pushforward of a `d = 1` covariance of `H:homog` to `ℝ`: scaling. -/
theorem map_scaling {alpha α₀ : ℝ} {Γ μ : Measure (Rd 1)} (h : HomogCovariance 1 alpha α₀ Γ μ)
    (A : Set ℝ) (hA : MeasurableSet A) (r : ℝ) (hr : 0 < r) :
    Γ.map coordOne (r • A) = ENNReal.ofReal (r ^ (1 - alpha)) * Γ.map coordOne A := by
  rw [Measure.map_apply coordOne.measurable (hA.const_smul_of_ne_zero hr.ne'),
    Measure.map_apply coordOne.measurable hA, preimage_coordOne_smul hr,
    h.scaling _ (coordOne.measurable hA) r hr, Nat.cast_one]

/-- The pushforward is even. -/
theorem map_even {alpha α₀ : ℝ} {Γ μ : Measure (Rd 1)} (h : HomogCovariance 1 alpha α₀ Γ μ) :
    (Γ.map coordOne).map (fun x : ℝ => -x) = Γ.map coordOne := by
  rw [Measure.map_map measurable_neg coordOne.measurable]
  have he : (fun x : ℝ => -x) ∘ coordOne = coordOne ∘ fun x : Rd 1 => -x :=
    funext fun x => (coordOne_neg x).symm
  rw [he, ← Measure.map_map coordOne.measurable measurable_neg]
  have h2 := h.Γ_even
  unfold HomogHypothesis.IsEven at h2
  rw [h2]

/-- The pushforward is finite on `[-1, 1]`. -/
theorem map_Icc_ne_top {alpha α₀ : ℝ} {Γ μ : Measure (Rd 1)} (h : HomogCovariance 1 alpha α₀ Γ μ) :
    Γ.map coordOne (Icc (-1) 1) ≠ ∞ := by
  have := h.Γ_radon
  rw [Measure.map_apply coordOne.measurable measurableSet_Icc]
  refine ne_top_of_le_ne_top (measure_closedBall_lt_top (x := (0 : Rd 1)) (r := 1)).ne
    (measure_mono fun x hx => ?_)
  rw [mem_closedBall_zero_iff, norm_coord_one, abs_le]
  exact hx

/-- `(c|·|^{-α} dy)` on `ℝ¹` pushed to `ℝ`. -/
theorem map_withDensity_riesz (c α : ℝ) :
    (volume.withDensity (riesz c α) : Measure (Rd 1)).map coordOne =
      volume.withDensity (rieszR c α) := by
  ext S hS
  rw [Measure.map_apply coordOne.measurable hS, withDensity_apply _ (coordOne.measurable hS),
    withDensity_apply _ hS,
    ← coordOne_mp.setLIntegral_comp_preimage_emb coordOne.measurableEmbedding (rieszR c α) S]
  refine lintegral_congr fun x => ?_
  rw [riesz, rieszR, norm_coord_one, coordOne_apply]

theorem map_whiteCov (c : ℝ) : (whiteCov c).map coordOne = ENNReal.ofReal c • Measure.dirac 0 := by
  rw [whiteCov, Measure.map_smul, Measure.map_dirac' coordOne.measurable]
  · congr 2
  · exact coordOne.measurable.aemeasurable

/-! ### The classification -/

/-- **`d = 1`, `0 < α < 1`**: a covariance of `H:homog` is `Γ = c|y|^{-α} dy` with
`c = (1 - α) Γ{0 < y ≤ 1} ≥ 0` (TeX 384-401; `E:d1-covariances`, Riesz case). -/
theorem homogCovariance_one_riesz {alpha α₀ : ℝ} {Γ μ : Measure (Rd 1)}
    (h : HomogCovariance 1 alpha α₀ Γ μ) (hα : alpha < 1) :
    Γ = volume.withDensity
      (riesz ((1 - alpha) * (Γ (coordOne ⁻¹' Ioc 0 1)).toReal) alpha) := by
  set ν := Γ.map coordOne with hνdef
  have hβ : 0 < 1 - alpha := by linarith
  have hs : ∀ A : Set ℝ, MeasurableSet A → ∀ r : ℝ, 0 < r →
      ν (r • A) = ENNReal.ofReal (r ^ (1 - alpha)) * ν A := map_scaling h
  have hfin : ν (Icc (-1) 1) ≠ ∞ := map_Icc_ne_top h
  have hfin1 : ν (Ioc 0 1) ≠ ∞ :=
    ne_top_of_le_ne_top hfin (measure_mono fun y hy => ⟨by linarith [hy.1], hy.2⟩)
  have hfin0 : ν {0} ≠ ∞ :=
    ne_top_of_le_ne_top hfin (measure_mono fun y hy => by
      rw [mem_singleton_iff.1 hy]; exact ⟨by norm_num, by norm_num⟩)
  have hK : ν (Ioc 0 1) = Γ (coordOne ⁻¹' Ioc 0 1) :=
    Measure.map_apply coordOne.measurable measurableSet_Ioc
  set K := (ν (Ioc 0 1)).toReal with hKdef
  have hK0 : 0 ≤ K := ENNReal.toReal_nonneg
  set c := (1 - alpha) * K with hcdef
  have hc : 0 ≤ c := mul_nonneg hβ.le hK0
  rw [← hK, ← hKdef]
  set ν' := volume.withDensity (rieszR c alpha) with hν'def
  -- the common values on `(0, x]`
  set G : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (K * x ^ (1 - alpha)) with hG
  have hνG : ∀ x, 0 ≤ x → ν (Ioc 0 x) = G x := by
    intro x hx
    rcases hx.lt_or_eq with hx | hx
    · show _ = ENNReal.ofReal (K * x ^ (1 - alpha))
      rw [measure_Ioc_of_scaling hs hx, ← ENNReal.ofReal_toReal hfin1, ← hKdef,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hx.le _), mul_comm]
    · subst hx
      show _ = ENNReal.ofReal (K * (0 : ℝ) ^ (1 - alpha))
      rw [Ioc_self, measure_empty, Real.zero_rpow hβ.ne', mul_zero, ENNReal.ofReal_zero]
  have hν'G : ∀ x, 0 ≤ x → ν' (Ioc 0 x) = G x := by
    intro x hx
    show volume.withDensity (rieszR c alpha) (Ioc 0 x) = ENNReal.ofReal (K * x ^ (1 - alpha))
    rw [withDensity_rieszR_Ioc hc hα hx, hcdef]
    congr 1
    field_simp
  have hpos : ν.restrict (Ioi 0) = ν'.restrict (Ioi 0) :=
    restrict_Ioi_eq (fun _ _ => ENNReal.ofReal_ne_top) hνG hν'G
  have hev : ν.map (fun x : ℝ => -x) = ν := map_even h
  have hev' : ν'.map (fun x : ℝ => -x) = ν' := withDensity_rieszR_even c alpha
  have h0 : ν {0} = 0 := measure_zero_of_scaling hs hβ hfin0
  have h0' : ν' {0} = 0 := withDensity_rieszR_zero c alpha
  have hνeq : ν = ν' :=
    calc ν = ν.restrict (Iio 0) + ν.restrict (Ioi 0) := eq_restrict_add h0
      _ = ν'.restrict (Iio 0) + ν'.restrict (Ioi 0) := by
        rw [restrict_Iio_of_even hev, restrict_Iio_of_even hev', hpos]
      _ = ν' := (eq_restrict_add h0').symm
  apply coordOne.map_measurableEquiv_injective
  rw [← hνdef, hνeq]
  exact (map_withDensity_riesz _ _).symm

/-- **`d = 1`, `α = 1`**: a covariance of `H:homog` is `Γ = c δ_0` with `c = Γ{0} ≥ 0`
(TeX 384-401: "the last case includes spatial white noise"). -/
theorem homogCovariance_one_white {α₀ : ℝ} {Γ μ : Measure (Rd 1)}
    (h : HomogCovariance 1 1 α₀ Γ μ) : Γ = whiteCov (Γ {0}).toReal := by
  set ν := Γ.map coordOne with hνdef
  have hs : ∀ A : Set ℝ, MeasurableSet A → ∀ r : ℝ, 0 < r → ν (r • A) = ν A := by
    intro A hA r hr
    rw [hνdef, map_scaling h A hA r hr, sub_self, Real.rpow_zero, ENNReal.ofReal_one, one_mul]
  have hfin : ν (Icc (-1) 1) ≠ ∞ := map_Icc_ne_top h
  have hfin1 : ν (Ioc 0 1) ≠ ∞ :=
    ne_top_of_le_ne_top hfin (measure_mono fun y hy => ⟨by linarith [hy.1], hy.2⟩)
  -- `ν(0, x] = ν(0, 1]` for every `x > 0`
  have hconst : ∀ x : ℝ, 0 < x → ν (Ioc 0 x) = ν (Ioc 0 1) := by
    intro x hx
    have := hs (Ioc 0 1) measurableSet_Ioc x hx
    rwa [LinearOrderedField.smul_Ioc hx, mul_zero, mul_one] at this
  -- continuity from above: `ν(0, 1] = 0`
  have h1 : ν (Ioc 0 1) = 0 := by
    have hanti : Antitone fun n : ℕ => Ioc (0 : ℝ) (1 / (n + 1)) := by
      intro i j hij
      refine Ioc_subset_Ioc_right ?_
      gcongr
    have hT := tendsto_measure_iInter_atTop (μ := ν) (fun n => measurableSet_Ioc.nullMeasurableSet)
      hanti ⟨0, by simpa using hfin1⟩
    have hemp : (⋂ n : ℕ, Ioc (0 : ℝ) (1 / (n + 1))) = ∅ := by
      refine eq_empty_of_forall_notMem fun y hy => ?_
      rw [mem_iInter] at hy
      have hy0 : 0 < y := (hy 0).1
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hy0
      exact absurd (hy n).2 (not_le.2 hn)
    rw [hemp, measure_empty] at hT
    have hc : (ν ∘ fun n : ℕ => Ioc (0 : ℝ) (1 / (n + 1))) = fun _ => ν (Ioc 0 1) :=
      funext fun n => hconst _ (by positivity)
    rw [hc] at hT
    exact tendsto_nhds_unique tendsto_const_nhds hT
  have hIoi : ν (Ioi 0) = 0 := by
    refine measure_mono_null (t := ⋃ n : ℕ, Ioc (0 : ℝ) n)
      (fun y (hy : 0 < y) => mem_iUnion.2 ⟨⌈y⌉₊ + 1, ?_⟩) (measure_iUnion_null fun n : ℕ => ?_)
    · exact ⟨hy, (Nat.le_ceil y).trans (by norm_cast; omega)⟩
    · rcases (Nat.cast_nonneg n : (0 : ℝ) ≤ n).lt_or_eq with hn | hn
      · rw [hconst _ hn, h1]
      · rw [← hn, Ioc_self, measure_empty]
  have hIio : ν (Iio 0) = 0 := by
    have he : ν.map (fun x : ℝ => -x) = ν := map_even h
    rw [← he, Measure.map_apply measurable_neg measurableSet_Iio]
    have : (fun x : ℝ => -x) ⁻¹' Iio 0 = Ioi 0 := by ext x; simp
    rw [this, hIoi]
  have hνd : ν = ENNReal.ofReal (Γ {0}).toReal • Measure.dirac 0 := by
    have hcompl : ν {0}ᶜ = 0 := by
      rw [← Iio_union_Ioi]
      exact measure_union_null hIio hIoi
    have h0 : ν {0} = Γ {0} := by
      rw [hνdef, Measure.map_apply coordOne.measurable (measurableSet_singleton 0)]
      congr 1
      ext x
      simp only [mem_preimage, mem_singleton_iff]
      constructor
      · intro hx
        apply coordOne.injective
        rw [hx]
        simp [coordOne_apply]
      · rintro rfl
        simp [coordOne_apply]
    have hfin0 : Γ {0} ≠ ∞ := by
      rw [← h0]
      exact ne_top_of_le_ne_top hfin (measure_mono fun y hy => by
        rw [mem_singleton_iff.1 hy]; exact ⟨by norm_num, by norm_num⟩)
    rw [ENNReal.ofReal_toReal hfin0, ← h0, ← Measure.restrict_singleton]
    exact (Measure.restrict_eq_self_of_ae_mem (measure_eq_zero_iff_ae_notMem.1 hcompl |>.mono
      fun _ hx => by simpa using hx)).symm
  apply coordOne.map_measurableEquiv_injective
  rw [← hνdef, hνd, map_whiteCov]

/-- **The `d = 1` classification of `H:homog`** (TeX 384-401): `Γ = c|y|^{-α} dy` with `c ≥ 0`
when `0 < α < 1`, and `Γ = c δ_0` with `c ≥ 0` when `α = 1`. -/
theorem homogCovariance_one_eq {alpha α₀ : ℝ} {Γ μ : Measure (Rd 1)}
    (h : HomogCovariance 1 alpha α₀ Γ μ) :
    (0 < alpha ∧ alpha < 1 ∧ ∃ c : ℝ, 0 ≤ c ∧ Γ = volume.withDensity (riesz c alpha)) ∨
      (alpha = 1 ∧ ∃ c : ℝ, 0 ≤ c ∧ Γ = whiteCov c) := by
  rcases h.alpha_range with ⟨h0, h1⟩ | ⟨h1, -⟩
  · rw [Nat.cast_one] at h1
    exact Or.inl ⟨h0, h1, _, mul_nonneg (by linarith) ENNReal.toReal_nonneg,
      homogCovariance_one_riesz h h1⟩
  · rw [Nat.cast_one] at h1
    subst h1
    exact Or.inr ⟨rfl, _, ENNReal.toReal_nonneg, homogCovariance_one_white h⟩

/-- **`DiagramLimits` for every `d = 1` covariance of `H:homog`** (decision 5): every diagram
converges as `ε ↓ 0`.  Route difference (disclosed): the classification
`homogCovariance_one_eq` and the domination route (`RieszDiagramLimits.diagramLimits_riesz`) or
the white collapse (`D1Upper.diagramLimits_white`), not the Wick-measure route of TeX 825-832 and
`L:joint-fixed-order` (1853-1966). -/
theorem diagramLimits_homog_one {alpha α₀ : ℝ} {Γ μ : Measure (Rd 1)}
    (h : HomogCovariance 1 alpha α₀ Γ μ) : ∀ t : ℝ, 0 < t → D1Upper.DiagramLimits 1 Γ α₀ t := by
  intro t ht
  rcases homogCovariance_one_eq h with ⟨h0, h1, c, hc, rfl⟩ | ⟨-, c, -, rfl⟩
  · exact RieszDiagramLimits.diagramLimits_riesz hc h0.le h1 h.alpha0_pos.le h.alpha0_lt_one ht.le
  · exact D1Upper.diagramLimits_white c h.alpha0_lt_one t

end StratonovichHAMSecondMoment.RieszDiagramLimitsHomog
