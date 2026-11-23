module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L16, item L16-C (part 5): `P:cameron-temporal-map` whole
(`integrated_cameron_mean.tex` lines 225-237, proof 239-314, at revision edf7085f (book
1.1.3)).

* Compactness (Steps 1-3): `K` (B1's `L²`-kernel lemma `isCompactOperator_of_L2_kernel` for the
  truncations `K_ε`), `K^{1/2}` (`S† S = S S = K`, B1's `isCompactOperator_of_adjoint_comp_self`),
  and `C_t : H_t → L^r(I)` by interpolation (lines 293-296): `‖u‖_r ≤ ‖u‖₂^τ ‖u‖_{r₂}^{1-τ}`,
  `r < r₂ < 2/a`, with a domination lemma for rpow bounds (`isCompactOperator_of_le_rpow`).
* Not trace class (Step 4, lines 300-312), in the form of decision 7: the orthonormal cell
  indicators `N^{1/2} 1_{(j/N,(j+1)/N)}` have `K` quadratic forms summing to
  `2N^a/((1-a)(2-a))` (each cell gives `N · 2N^{a-2}/((1-a)(2-a))`), and the same sum is
  `∑ ‖K^{1/2} ι ι⁻¹ e_j‖²`.  Proved for every temporal mean data (`notTrace`).
* `cameron_temporal_map : TemporalMapTarget p r` with no hypothesis, and the fallback named input
  `TemporalCompact p` as a theorem (`temporalCompact`).
-/
public import Mathlib
public import StratonovichHAMSecondMoment.CameronInterface
public import StratonovichHAMSecondMoment.CameronTemporalMap
public import StratonovichHAMSecondMoment.CompactOperatorFoundation

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal RealInnerProductSpace

namespace StratonovichHAMSecondMoment.CameronTemporal

open SpaceTimePositivity (timeMeasure)
open TimeSchur (kern kern_nonneg measurable_kern)
open OccupationCompletion (TParams Ht J kform kform_congr kform_integrable)
open CameronInterface (L2I IsTimeKernelOp IsPosSqrt TemporalMeanCore KaNorm cell
  TemporalNotTraceTarget TemporalMapTarget TemporalCompact)

/-! ### Compactness tools -/

/-- **B1's `L²`-kernel lemma on `L²(I)`** (`CompactOperatorFoundation.isCompactOperator_of_L2_kernel`,
item L16-B1), the hypothesis `L2KernelCompact` of `CameronTemporalKernel` discharged. -/
theorem l2KernelCompact : L2KernelCompact := fun T k hk hT =>
  CompactOperatorFoundation.isCompactOperator_of_L2_kernel T k hk hT

/-- **Domination lemma, power form**: if `K` is compact and `‖T x‖ ≤ C ‖K x‖^τ ‖x‖^{1-τ}` with
`0 < τ ≤ 1`, then `T` is compact (image of the unit ball totally bounded). -/
theorem isCompactOperator_of_le_rpow {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] (T : E →L[ℝ] F) (K : E →L[ℝ] G) (hK : IsCompactOperator K) {C τ : ℝ}
    (hC : 0 ≤ C) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    (hT : ∀ x, ‖T x‖ ≤ C * ‖K x‖ ^ τ * ‖x‖ ^ (1 - τ)) : IsCompactOperator T := by
  classical
  refine (isCompactOperator_iff_isCompact_closure_image_closedBall
    (T : E →ₛₗ[RingHom.id ℝ] F) zero_lt_one).mpr ?_
  have hKtb : TotallyBounded (K '' closedBall 0 1) :=
    ((hK.isCompact_closure_image_closedBall 1).totallyBounded).subset subset_closure
  suffices htb : TotallyBounded (T '' closedBall 0 1) from
    htb.closure.isCompact_of_isClosed isClosed_closure
  rw [Metric.totallyBounded_iff]
  intro ε hε
  set δ : ℝ := (ε / (2 * (C + 1))) ^ (1 / τ) with hδ
  have hδ0 : 0 < δ := Real.rpow_pos_of_pos (by positivity) _
  have hδτ : δ ^ τ = ε / (2 * (C + 1)) := by
    rw [hδ, ← Real.rpow_mul (by positivity), one_div_mul_cancel hτ0.ne', Real.rpow_one]
  obtain ⟨t, htK, htf, hcov⟩ := Metric.finite_approx_of_totallyBounded hKtb _ hδ0
  let pre : G → E := fun y => if h : y ∈ K '' closedBall (0 : E) 1 then h.choose else 0
  have hpre : ∀ y ∈ t, pre y ∈ closedBall (0 : E) 1 ∧ K (pre y) = y := by
    intro y hy
    have h : y ∈ K '' closedBall (0 : E) 1 := htK hy
    simp only [pre, h, dite_true]
    exact h.choose_spec
  refine ⟨(fun y => T (pre y)) '' t, htf.image _, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hyt, hy⟩ := mem_iUnion₂.mp (hcov (mem_image_of_mem K hx))
  obtain ⟨hpb, hKp⟩ := hpre y hyt
  refine mem_iUnion₂.mpr ⟨T (pre y), mem_image_of_mem _ hyt, ?_⟩
  rw [mem_ball, dist_eq_norm, ← map_sub]
  have hx1 : ‖x‖ ≤ 1 := by simpa using hx
  have hp1 : ‖pre y‖ ≤ 1 := by simpa using hpb
  have hKd : ‖K (x - pre y)‖ ≤ δ := by
    rw [map_sub, hKp, ← dist_eq_norm]
    exact (mem_ball.1 hy).le
  have hd : ‖x - pre y‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
  have hd' : ‖x - pre y‖ ^ (1 - τ) ≤ 2 := by
    calc ‖x - pre y‖ ^ (1 - τ) ≤ 2 ^ (1 - τ) :=
          Real.rpow_le_rpow (norm_nonneg _) hd (by linarith)
      _ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  calc ‖T (x - pre y)‖ ≤ C * ‖K (x - pre y)‖ ^ τ * ‖x - pre y‖ ^ (1 - τ) := hT _
    _ ≤ C * δ ^ τ * 2 := by
        gcongr
    _ = C * (ε / (2 * (C + 1))) * 2 := by rw [hδτ]
    _ < ε := by
        rw [show C * (ε / (2 * (C + 1))) * 2 = ε * (C / (C + 1)) by field_simp]
        have : C / (C + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
        nlinarith

/-- **Interpolation of `L^p` norms** (TeX line 296): for `2 < ρ < ρ₂` and
`θ = (ρ₂-ρ)/(ρ₂-2)`, `‖u‖_ρ ≤ ‖u‖₂^{2θ/ρ} ‖u‖_{ρ₂}^{ρ₂(1-θ)/ρ}` (Hölder with exponents `θ`, `1-θ`). -/
theorem eLpNorm_interpolate {μ : Measure ℝ} {u : ℝ → ℝ} (hu : AEStronglyMeasurable u μ)
    {ρ ρ₂ : ℝ} (h2 : 2 < ρ) (hρ : ρ < ρ₂) :
    eLpNorm u (ENNReal.ofReal ρ) μ ≤
      eLpNorm u 2 μ ^ (2 * ((ρ₂ - ρ) / (ρ₂ - 2)) / ρ) *
        eLpNorm u (ENNReal.ofReal ρ₂) μ ^ (ρ₂ * (1 - (ρ₂ - ρ) / (ρ₂ - 2)) / ρ) := by
  set θ := (ρ₂ - ρ) / (ρ₂ - 2) with hθ
  have hρ0 : 0 < ρ := by linarith
  have hρ₂0 : 0 < ρ₂ := by linarith
  have hd : 0 < ρ₂ - 2 := by linarith
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hd.le
  have hθ1 : 0 ≤ 1 - θ := by
    rw [hθ, sub_nonneg, div_le_one hd]; linarith
  have hsum : 2 * θ + ρ₂ * (1 - θ) = ρ := by rw [hθ]; field_simp; ring
  have hpt : ∀ x, ‖u x‖ₑ ^ ρ = (‖u x‖ₑ ^ (2 : ℝ)) ^ θ * (‖u x‖ₑ ^ ρ₂) ^ (1 - θ) := by
    intro x
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
      ← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (mul_nonneg hρ₂0.le hθ1), hsum]
  have hH := ENNReal.lintegral_mul_norm_pow_le (μ := μ) (hu.enorm.pow_const (2 : ℝ))
    (hu.enorm.pow_const ρ₂) hθ0 hθ1 (by ring)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hρ0) ENNReal.ofReal_ne_top hu,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hu,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hρ₂0) ENNReal.ofReal_ne_top hu,
    ENNReal.toReal_ofReal hρ0.le, ENNReal.toReal_ofReal hρ₂0.le, ENNReal.toReal_ofNat]
  simp_rw [hpt]
  calc (∫⁻ x, (‖u x‖ₑ ^ (2 : ℝ)) ^ θ * (‖u x‖ₑ ^ ρ₂) ^ (1 - θ) ∂μ) ^ (1 / ρ)
      ≤ ((∫⁻ x, ‖u x‖ₑ ^ (2 : ℝ) ∂μ) ^ θ * (∫⁻ x, ‖u x‖ₑ ^ ρ₂ ∂μ) ^ (1 - θ)) ^ (1 / ρ) :=
        ENNReal.rpow_le_rpow hH (by positivity)
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        congr 2
        · field_simp
        · field_simp

variable {p : TParams} {S : L2I →L[ℝ] L2I}

/-- **`K^{1/2}` is compact** (TeX line 265): `S† S = S S = K` and B1's
`isCompactOperator_of_adjoint_comp_self`. -/
theorem isCompactOperator_sqrt (hS : IsPosSqrt (kOpK p) S) : IsCompactOperator S := by
  refine CompactOperatorFoundation.isCompactOperator_of_adjoint_comp_self S ?_
  have hsa : IsSelfAdjoint S := hS.1.isSelfAdjoint
  have : ContinuousLinearMap.adjoint S ∘L S = kOpK p := by
    rw [← ContinuousLinearMap.star_eq_adjoint, hsa.star_eq]
    exact hS.2
  rw [this]
  exact isCompactOperator_kOpK l2KernelCompact p

/-- **`K^{1/2} : L²(I) → L^r(I)` is compact** (TeX lines 293-296): interpolation between the
compact `L²` map and the bounded `L^{r₂}` map, `r < r₂ < 2/a`. -/
theorem isCompactOperator_sqrtLr (hS : IsPosSqrt (kOpK p) S) {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (h2 : 2 < r) (hr : r < ENNReal.ofReal (2 / p.a)) : IsCompactOperator (sqrtLr hS h2 hr) := by
  obtain ⟨htop, h2', hr', hrr⟩ := exponent_bounds h2 hr
  set ρ := r.toReal
  set ρ₂ := (ρ + 2 / p.a) / 2 with hρ₂
  have hρρ₂ : ρ < ρ₂ := by rw [hρ₂]; linarith
  have hρ₂a : ρ₂ < 2 / p.a := by rw [hρ₂]; linarith
  have h2₂ : 2 < ρ₂ := by linarith
  set θ := (ρ₂ - ρ) / (ρ₂ - 2) with hθ
  set τ := 2 * θ / ρ with hτ
  have hd : 0 < ρ₂ - 2 := by linarith
  have hρ0 : 0 < ρ := by linarith
  have hθ0 : 0 < θ := div_pos (by linarith) hd
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one hd]; linarith
  have hτ0 : 0 < τ := by positivity
  have hτ1 : τ ≤ 1 := by
    rw [hτ, div_le_one hρ0]; nlinarith
  have hτ' : ρ₂ * (1 - θ) / ρ = 1 - τ := by
    rw [hτ, hθ]; field_simp; ring
  set C₂ := √(KaNorm p.a ρ₂)
  refine isCompactOperator_of_le_rpow (sqrtLr hS h2 hr) S (isCompactOperator_sqrt hS)
    (C := C₂ ^ (1 - τ)) (Real.rpow_nonneg (Real.sqrt_nonneg _) _) hτ0 hτ1 fun g => ?_
  have hint := eLpNorm_interpolate (Lp.aestronglyMeasurable (S g)) h2' hρρ₂
  rw [← hθ, ← hτ, hτ', ← hrr] at hint
  have hfin2 : eLpNorm (S g : ℝ → ℝ) 2 timeMeasure ≠ ⊤ := Lp.eLpNorm_ne_top _
  have hb₂ := eLpNorm_sqrt_le hS h2₂ hρ₂a g
  have hfin₂ : eLpNorm (S g : ℝ → ℝ) (ENNReal.ofReal ρ₂) timeMeasure ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb₂
  have hnorm : ‖sqrtLr hS h2 hr g‖ = (eLpNorm (S g : ℝ → ℝ) r timeMeasure).toReal := by
    rw [Lp.norm_def]
    exact congrArg ENNReal.toReal (eLpNorm_congr_ae (coeFn_sqrtLr hS h2 hr g))
  rw [hnorm]
  calc (eLpNorm (S g : ℝ → ℝ) r timeMeasure).toReal
      ≤ (eLpNorm (S g : ℝ → ℝ) 2 timeMeasure ^ τ *
          eLpNorm (S g : ℝ → ℝ) (ENNReal.ofReal ρ₂) timeMeasure ^ (1 - τ)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hτ0.le hfin2)
          (ENNReal.rpow_ne_top_of_nonneg (by linarith) hfin₂)) hint
    _ = ‖S g‖ ^ τ * (eLpNorm (S g : ℝ → ℝ) (ENNReal.ofReal ρ₂) timeMeasure).toReal ^ (1 - τ) := by
        rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow, Lp.norm_def]
    _ ≤ ‖S g‖ ^ τ * (C₂ * ‖g‖) ^ (1 - τ) := by
        gcongr
        exact ENNReal.toReal_le_of_le_ofReal (by positivity) hb₂
    _ = C₂ ^ (1 - τ) * ‖S g‖ ^ τ * ‖g‖ ^ (1 - τ) := by
        rw [Real.mul_rpow (Real.sqrt_nonneg _) (norm_nonneg _)]
        ring

/-! ### Not trace class: the cell indicators (TeX lines 300-312) -/

/-- Auxiliary: the cell indicator is measurable. -/
theorem measurable_cell (N j : ℕ) : Measurable (cell N j) :=
  measurable_const.indicator measurableSet_Ioo

/-- Auxiliary: the cell indicator lies in `L²(I)`. -/
theorem memLp_cell (N j : ℕ) : MemLp (cell N j) 2 timeMeasure :=
  MemLp.of_bound (measurable_cell N j).aestronglyMeasurable √(N : ℝ) (ae_of_all _ fun t => by
    unfold cell
    by_cases ht : t ∈ Ioo ((j : ℝ) / N) (((j : ℝ) + 1) / N)
    · rw [indicator_of_mem ht, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    · rw [indicator_of_notMem ht, norm_zero]; exact Real.sqrt_nonneg _)

/-- The cell indicator as an element of `L²(I)`. -/
def cellL (N j : ℕ) : L2I := (memLp_cell N j).toLp _

/-- Auxiliary: `cellL N j = cell N j` a.e. -/
theorem coeFn_cellL (N j : ℕ) : (cellL N j : ℝ → ℝ) =ᵐ[timeMeasure] cell N j :=
  (memLp_cell N j).coeFn_toLp

/-- Auxiliary: the cells of index `< N` lie in `I`. -/
theorem cell_subset {N j : ℕ} (hj : j < N) :
    Ioo ((j : ℝ) / N) (((j : ℝ) + 1) / N) ⊆ Ioo (0 : ℝ) 1 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hj)
  intro t ht
  refine ⟨lt_of_le_of_lt (by positivity) ht.1, lt_of_lt_of_le ht.2 ?_⟩
  rw [div_le_one hN]
  exact_mod_cast hj

/-- Auxiliary: distinct cells are disjoint. -/
theorem cell_mul_cell {N i j : ℕ} (hij : i ≠ j) (t : ℝ) : cell N i t * cell N j t = 0 := by
  unfold cell
  by_cases hi : t ∈ Ioo ((i : ℝ) / N) (((i : ℝ) + 1) / N)
  · by_cases hj : t ∈ Ioo ((j : ℝ) / N) (((j : ℝ) + 1) / N)
    · exfalso
      have hN : (0 : ℝ) < N := by
        rcases Nat.eq_zero_or_pos N with h | h
        · subst h; simp at hi
        · exact_mod_cast h
      have h1 : (i : ℝ) < j + 1 := (div_lt_div_iff_of_pos_right hN).1 (hi.1.trans hj.2)
      have h2 : (j : ℝ) < i + 1 := (div_lt_div_iff_of_pos_right hN).1 (hj.1.trans hi.2)
      have h1' : i < j + 1 := by exact_mod_cast h1
      have h2' : j < i + 1 := by exact_mod_cast h2
      omega
    · rw [indicator_of_notMem hj, mul_zero]
  · rw [indicator_of_notMem hi, zero_mul]

/-- Auxiliary: `cell² = N 1_{cell}`. -/
theorem cell_mul_self (N j : ℕ) (t : ℝ) :
    cell N j t * cell N j t =
      (Ioo ((j : ℝ) / N) (((j : ℝ) + 1) / N)).indicator (fun _ => (N : ℝ)) t := by
  unfold cell
  by_cases ht : t ∈ Ioo ((j : ℝ) / N) (((j : ℝ) + 1) / N)
  · rw [indicator_of_mem ht, indicator_of_mem ht, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  · rw [indicator_of_notMem ht, indicator_of_notMem ht, zero_mul]

/-- Auxiliary: the cell indicators are orthonormal in `L²(I)` (TeX line 303). -/
theorem orthonormal_cellL {N : ℕ} (hN : 0 < N) : Orthonormal ℝ fun j : Fin N => cellL N j := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [inner_L2I]
  have hint : ∫ s, (cellL N i : ℝ → ℝ) s * (cellL N j : ℝ → ℝ) s ∂timeMeasure =
      ∫ s, cell N i s * cell N j s ∂timeMeasure :=
    integral_congr_ae (by
      filter_upwards [coeFn_cellL N i, coeFn_cellL N j] with s h1 h2
      rw [h1, h2])
  rw [hint]
  split_ifs with h
  · subst h
    simp only [cell_mul_self]
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    rw [integral_indicator_const _ measurableSet_Ioo, Measure.real,
      Measure.restrict_apply measurableSet_Ioo, inter_eq_left.2 (cell_subset i.2),
      Real.volume_Ioo, ENNReal.toReal_ofReal (by
        rw [sub_nonneg]; exact div_le_div_of_nonneg_right (by linarith) hNr.le), smul_eq_mul]
    field_simp
    ring
  · have hne : (i : ℕ) ≠ j := fun h' => h (Fin.ext h')
    simp only [cell_mul_cell hne]
    simp

/-- Auxiliary: `∫_α^β |s-t|^{-a} dt = ((s-α)^{1-a} + (β-s)^{1-a})/(1-a)` for `s ∈ [α, β]`. -/
theorem integral_row_Ioo {a α β s : ℝ} (ha1 : a < 1) (hs : s ∈ Icc α β) :
    ∫ t in Ioo α β, kern a (s - t) = ((s - α) ^ (1 - a) + (β - s) ^ (1 - a)) / (1 - a) := by
  have hr : -1 < -a := by linarith
  have hαβ : α ≤ β := hs.1.trans hs.2
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hαβ]
  have e1 : ∫ t in α..β, kern a (s - t) = ∫ y in (s - β)..(s - α), |y| ^ (-a) := by
    simp only [kern]
    exact intervalIntegral.integral_comp_sub_left (fun y : ℝ => |y| ^ (-a)) s
  rw [e1, ← intervalIntegral.integral_add_adjacent_intervals
    (TimeSchur.intervalIntegrable_abs_rpow hr _ _) (TimeSchur.intervalIntegrable_abs_rpow hr _ _)]
  have e2 : s - β = -(β - s) := by ring
  rw [e2, TimeSchur.integral_abs_rpow_neg hr (by linarith [hs.2]),
    TimeSchur.integral_abs_rpow_zero hr (by linarith [hs.1])]
  have : -a + 1 = 1 - a := by ring
  rw [this]
  ring

/-- Auxiliary: `∫_α^β ((s-α)^{1-a} + (β-s)^{1-a}) ds/(1-a) = 2(β-α)^{2-a}/((1-a)(2-a))`. -/
theorem integral_rows_Ioo {a α β : ℝ} (ha1 : a < 1) (hαβ : α ≤ β) :
    ∫ s in Ioo α β, ((s - α) ^ (1 - a) + (β - s) ^ (1 - a)) / (1 - a) =
      2 * (β - α) ^ (2 - a) / ((1 - a) * (2 - a)) := by
  have h1a : 0 < 1 - a := by linarith
  have hc1 : Continuous fun s : ℝ => (s - α) ^ (1 - a) :=
    (continuous_id.sub continuous_const).rpow_const fun _ => Or.inr h1a.le
  have hc2 : Continuous fun s : ℝ => (β - s) ^ (1 - a) :=
    (continuous_const.sub continuous_id).rpow_const fun _ => Or.inr h1a.le
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hαβ,
    intervalIntegral.integral_div, intervalIntegral.integral_add (hc1.intervalIntegrable _ _)
      (hc2.intervalIntegrable _ _),
    intervalIntegral.integral_comp_sub_right (fun x : ℝ => x ^ (1 - a)),
    intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (1 - a)),
    sub_self, sub_self, integral_rpow (Or.inl (by linarith))]
  have h2a : (1 - a + 1) = 2 - a := by ring
  rw [h2a, Real.zero_rpow (by linarith), sub_zero]
  have : (2 - a) ≠ 0 := by linarith
  field_simp
  ring

/-- **The `K` quadratic form of one cell** (TeX lines 305-308): for `j < N`,
`∫∫_{I²} |s-t|^{-a} e_j(s) e_j(t) = N · 2N^{a-2}/((1-a)(2-a)) = 2N^a/(N(1-a)(2-a))`. -/
theorem kform_cell {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {N j : ℕ} (hj : j < N) :
    kform a (cell N j) (cell N j) = 2 * (N : ℝ) ^ a / N / ((1 - a) * (2 - a)) := by
  set α : ℝ := (j : ℝ) / N
  set β : ℝ := ((j : ℝ) + 1) / N
  set C := Ioo α β with hC
  have hN : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hj)
  have hαβ : α ≤ β := div_le_div_of_nonneg_right (by linarith) hN.le
  have hβα : β - α = 1 / N := by simp only [α, β]; field_simp; ring
  have hsub := cell_subset hj
  have hrestr : timeMeasure.restrict C = volume.restrict C := by
    rw [Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.2 hsub]
  rw [OccupationCompletion.kform, integral_prod _
    (kform_integrable (G := ℝ) ha0 ha1 (memLp_cell N j) (memLp_cell N j))]
  -- the inner integral
  have hinner : ∀ s, ∫ t, kern a ((s, t).1 - (s, t).2) * ⟪cell N j (s, t).1, cell N j (s, t).2⟫
      ∂timeMeasure = C.indicator (fun s => (N : ℝ) * (((s - α) ^ (1 - a) + (β - s) ^ (1 - a)) /
        (1 - a))) s := by
    intro s
    have hpt : ∀ t, kern a ((s, t).1 - (s, t).2) * ⟪cell N j (s, t).1, cell N j (s, t).2⟫ =
        cell N j s * √(N : ℝ) * C.indicator (fun t => kern a (s - t)) t := by
      intro t
      simp only [RCLike.inner_apply, conj_trivial]
      unfold cell
      by_cases ht : t ∈ C
      · rw [indicator_of_mem ht, indicator_of_mem ht]; ring
      · rw [indicator_of_notMem ht, indicator_of_notMem ht]; ring
    simp_rw [hpt]
    rw [integral_const_mul, integral_indicator measurableSet_Ioo, hrestr]
    unfold cell
    by_cases hs : s ∈ C
    · rw [indicator_of_mem hs, indicator_of_mem hs,
        integral_row_Ioo ha1 (Ioo_subset_Icc_self hs),
        Real.mul_self_sqrt (Nat.cast_nonneg _)]
    · rw [indicator_of_notMem hs, indicator_of_notMem hs, zero_mul, zero_mul]
  simp_rw [hinner]
  rw [integral_indicator measurableSet_Ioo, hrestr, integral_const_mul,
    integral_rows_Ioo ha1 hαβ, hβα]
  have hN2 : ((1 : ℝ) / N) ^ (2 - a) = (N : ℝ) ^ a / N / N := by
    rw [one_div, Real.inv_rpow hN.le, ← Real.rpow_neg hN.le, neg_sub,
      Real.rpow_sub hN, Real.rpow_two]
    field_simp
  rw [hN2]
  field_simp

/-- Auxiliary: for a positive square root `S` of an operator `K`, `‖S g‖² = ⟪K g, g⟫`. -/
theorem norm_sq_eq_inner_of_isPosSqrt {K S : L2I →L[ℝ] L2I} (hS : IsPosSqrt K S) (g : L2I) :
    ‖S g‖ ^ 2 = ⟪K g, g⟫ := by
  have hsym : ⟪S g, S g⟫ = ⟪g, S (S g)⟫ := hS.1.isSymmetric g (S g)
  rw [← real_inner_self_eq_norm_sq, hsym, real_inner_comm, ← ContinuousLinearMap.comp_apply, hS.2]

/-- **C target, "not trace class / not Hilbert-Schmidt"** (`integrated_cameron_mean.tex` lines
235-236, proof Step 4 lines 300-312, at revision edf7085f (book 1.1.3)), for every
temporal mean data `T`: the cell indicators are orthonormal and both sums equal
`2N^a/((1-a)(2-a))`. -/
theorem notTrace {r : ℝ≥0∞} [Fact (1 ≤ r)] (T : TemporalMeanCore p r) :
    TemporalNotTraceTarget T := by
  intro N hN
  have hcell : ∀ j : Fin N, ⟪T.K (cellL N j), cellL N j⟫ =
      2 * (N : ℝ) ^ p.a / N / ((1 - p.a) * (2 - p.a)) := by
    intro j
    rw [inner_K_eq_kform T.K_kernel, kform_congr p.a (coeFn_cellL N j) (coeFn_cellL N j)]
    exact kform_cell p.ha0.le p.ha1 j.2
  have hsum : ∑ j : Fin N, ⟪T.K (cellL N j), cellL N j⟫ =
      2 * (N : ℝ) ^ p.a / ((1 - p.a) * (2 - p.a)) := by
    simp_rw [hcell]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
  refine ⟨fun j => cellL N j, orthonormal_cellL hN, fun j => coeFn_cellL N j,
    hsum, ?_⟩
  simp_rw [LinearIsometryEquiv.apply_symm_apply, norm_sq_eq_inner_of_isPosSqrt T.S_sqrt]
  exact hsum

/-! ### `P:cameron-temporal-map` -/

/-- **C target 4: `P:cameron-temporal-map`** (`integrated_cameron_mean.tex` lines 225-237, proof
239-314, at revision edf7085f (book 1.1.3)), whole: for `2 < r < 2/a` the temporal
mean data exist with `K`, `K^{1/2}` and `C_t : H_t → L^r(I)` compact, and not trace class in the
form of `TemporalNotTraceTarget`. -/
theorem cameron_temporal_map (p : TParams) {r : ℝ≥0∞} [Fact (1 ≤ r)] (h2 : 2 < r)
    (hr : r < ENNReal.ofReal (2 / p.a)) : TemporalMapTarget p r := by
  obtain ⟨S, hSpos, hSS⟩ := exists_isPositive_sqrt (kOpK p)
    (isCompactOperator_kOpK l2KernelCompact p)
    (isPositive_of_isTimeKernelOp (isTimeKernelOp_kOpK p))
  have hS : IsPosSqrt (kOpK p) S := ⟨hSpos, hSS⟩
  refine ⟨coreOf hS h2 hr, isCompactOperator_kOpK l2KernelCompact p, isCompactOperator_sqrt hS,
    ?_, notTrace _⟩
  exact (isCompactOperator_sqrtLr hS h2 hr).comp_clm _

/-- **The fallback named input `TemporalCompact` holds** (`integrated_cameron_mean.tex` lines 227
and 233 at revision edf7085f (book 1.1.3)): every operator with kernel `|s-t|^{-a}` is
compact, and `C_t` of every temporal mean data is compact into `L^r(I)`. -/
theorem temporalCompact (p : TParams) : TemporalCompact p where
  K_compact _ hK := isCompactOperator_of_isTimeKernelOp l2KernelCompact hK
  Ct_compact r _ T := by
    have hK : T.K = kOpK p := eq_of_isTimeKernelOp T.K_kernel (isTimeKernelOp_kOpK p)
    have hS : IsPosSqrt (kOpK p) T.S := hK ▸ T.S_sqrt
    have hCt : T.Ct = sqrtLr hS T.two_lt_r T.r_lt ∘L
        T.ι.toContinuousLinearEquiv.toContinuousLinearMap := by
      ext1 h
      exact Lp.ext ((T.Ct_L2 h).trans (coeFn_sqrtLr hS T.two_lt_r T.r_lt (T.ι h)).symm)
    rw [hCt]
    exact (isCompactOperator_sqrtLr hS T.two_lt_r T.r_lt).comp_clm _

end StratonovichHAMSecondMoment.CameronTemporal
