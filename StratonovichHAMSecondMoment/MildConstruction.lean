module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L20, item L20-F (approved by Le on 2026-11-22 with the default answers to all thirteen
decisions): Steps 5 and 6 of the proof of `P:mild-construction`, TeX lines 2290-2339 at revision
edf7085f (book 1.1.3), and the proposition itself, `E:mild-construction` (TeX lines 2151-2165 at
revision edf7085f (book 1.1.3), display 2156-2161).

* `external_vertex : ExternalVertexTarget` (Step 5, `E:external-vertex-limit`, TeX 2290-2303)
  from item D's `PartialVertexTarget` (its partial-vertex limit `E:partial-vertex-limit`) and
  L19's joint fixed-order convergence (`SourceFinal.fixed_order_l2_l19`, first clause,
  `L:joint-fixed-order`).  Route as the TeX (2298-2302): fix `ζ > 0`; the joint limit gives
  neighbourhoods of the inner widths and of the external pair on which
  `‖Y_n^{(b,a)} - X_n‖ < ζ/2`; at a fixed external pair in its neighbourhood the inner widths
  tend to zero in D's limit, so `‖I_{n,a} - X_n‖ ≤ ζ/2`.  The only bookkeeping is that the
  vertexwise widths of `Fin.snoc b a` are the `Fin.snoc` of the width vectors (`posW_snoc`) and
  that `Fin.snoc` maps the inner width filter times the external one into the width filter of
  order `n` (`tendsto_snoc`).
* `mild_construction : MildConstructionTarget` (Step 6, TeX 2307-2339): at fixed `a` and
  `0 ≤ s ≤ T`, item A's closedness clause (TeX 2318-2320) identifies `W_a u` with the `L²` sum
  of the `W_a X_n`, whose norms are bounded by D's `E:fixed-external-domination`,
  `2 √(n+1) √V_a q_n(T)`, summable by `E:vertex-summability` (`summable_sqrt_qn`, TeX 2311-2317);
  the partial sums converge in `L²` by `expansion_l2_l19` for `s > 0`, and at `s = 0` the
  positive orders vanish (TeX 2210; the chain measure of positive order at time `0` is zero), so
  `u(0,y) = X_0(0,y)`.  Dominated Green integration (`tendsto_integral_of_dominated_convergence`,
  the mild measure is finite and lives on `0 ≤ s ≤ t`) gives `I_a = Σ_{n ≥ 1} I_{n,a}`
  (TeX 2320-2325, with integrability of `W_a u` and its strong measurability as the pointwise
  limit of D's integrable partial sums), and the final `ε/N` tail argument (TeX 2329-2336) is
  Tannery's theorem (`tendsto_tsum_of_dominated_convergence`) with the uniform bound
  `‖I_{n,a}‖ ≤ q_n(t)` of D's `E:mixed-vertex-bound` and the limits of Step 5; `u - 1` is the
  tail `Σ_{n ≥ 1} X_n` (`X_0 = 1`, `Ya_zero`).
* `mild_construction_of`: the same with only the hypotheses the proof uses (A, D, Step 5);
  `mild_construction` (frozen signature) also takes B and C, which this route does not need
  (B's membership and C's measurability are already inside D's clauses), and forwards.

Route difference (disclosed): Step 6's sentence "the sum of the product integrands is spatially
`L²`-continuous by uniform summability, so its Green-width limit is justified in exactly the same
way" (TeX 2327-2328) is the `u` clause of item E's `GreenWidthMildTarget`, not part of
`MildConstructionTarget`; it is not proved here.

No `sorry`, no axiom, no instance declared.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.MildInterface

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal Real Nat

namespace StratonovichHAMSecondMoment.MildConstruction

universe u

open HomogHypothesis (Rd HomogCovariance)
open FiniteWick (CenteredGaussianField)
open TerminalWick (Pt prodL2)
open TerminalWickInputs (chainMeasure fieldL2)
open WickInterface (widthFilter posOrthant)
open SourceInterface
open MildInterface

/-! ### `mulL2` with zero and sums -/

section Mul

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem memLp_zero_mul (G : Lp ℝ 2 P) : MemLp (fun ω => (0 : Lp ℝ 2 P) ω * G ω) 2 P := by
  refine MemLp.zero.ae_eq ?_
  filter_upwards [Lp.coeFn_zero ℝ 2 P] with ω h
  show (0 : Ω → ℝ) ω = _
  rw [h]
  simp

theorem memLp_mul_zero (H : Lp ℝ 2 P) : MemLp (fun ω => H ω * (0 : Lp ℝ 2 P) ω) 2 P := by
  refine MemLp.zero.ae_eq ?_
  filter_upwards [Lp.coeFn_zero ℝ 2 P] with ω h
  show (0 : Ω → ℝ) ω = _
  rw [h]
  simp

theorem mulL2_zero_left (G : Lp ℝ 2 P) : mulL2 (0 : Lp ℝ 2 P) G = 0 := by
  refine Lp.ext ?_
  filter_upwards [coeFn_mulL2 (memLp_zero_mul G), Lp.coeFn_zero ℝ 2 P] with ω h1 h2
  rw [h1, h2]
  simp

theorem mulL2_zero_right (H : Lp ℝ 2 P) : mulL2 H (0 : Lp ℝ 2 P) = 0 := by
  refine Lp.ext ?_
  filter_upwards [coeFn_mulL2 (memLp_mul_zero H), Lp.coeFn_zero ℝ 2 P] with ω h1 h2
  rw [h1, h2]
  simp

/-- Additivity of `mulL2` in the second slot when both products are in `L²`. -/
theorem mulL2_add {H F₁ F₂ : Lp ℝ 2 P} (h₁ : MemLp (fun ω => H ω * F₁ ω) 2 P)
    (h₂ : MemLp (fun ω => H ω * F₂ ω) 2 P) :
    MemLp (fun ω => H ω * (F₁ + F₂) ω) 2 P ∧ mulL2 H (F₁ + F₂) = mulL2 H F₁ + mulL2 H F₂ := by
  have h₁₂ : MemLp (fun ω => H ω * (F₁ + F₂) ω) 2 P := by
    refine (h₁.add h₂).ae_eq ?_
    filter_upwards [Lp.coeFn_add F₁ F₂] with ω h
    simp only [Pi.add_apply, h, mul_add]
  refine ⟨h₁₂, Lp.ext ?_⟩
  filter_upwards [coeFn_mulL2 h₁₂, coeFn_mulL2 h₁, coeFn_mulL2 h₂,
    Lp.coeFn_add (mulL2 H F₁) (mulL2 H F₂), Lp.coeFn_add F₁ F₂] with ω e₁₂ e₁ e₂ ea eb
  rw [e₁₂, ea, Pi.add_apply, e₁, e₂, eb, Pi.add_apply, mul_add]

/-- Finite sums: `H · Σ_{n<N} X_n ∈ L²` and `mulL2 H (Σ_{n<N} X_n) = Σ_{n<N} mulL2 H X_n`. -/
theorem mulL2_sum_range {H : Lp ℝ 2 P} {X : ℕ → Lp ℝ 2 P}
    (hX : ∀ n, MemLp (fun ω => H ω * X n ω) 2 P) (N : ℕ) :
    MemLp (fun ω => H ω * (∑ n ∈ Finset.range N, X n) ω) 2 P ∧
      mulL2 H (∑ n ∈ Finset.range N, X n) = ∑ n ∈ Finset.range N, mulL2 H (X n) := by
  induction N with
  | zero => simpa using ⟨memLp_mul_zero H, mulL2_zero_right H⟩
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    obtain ⟨hm, he⟩ := mulL2_add ih.1 (hX N)
    exact ⟨hm, by rw [he, ih.2]⟩

end Mul

/-- **The series form of A's closedness clause** (TeX 2318-2320 at revision edf7085f (book
1.1.3): "partial sums of `u` converge in `L²`, and their products converge by this estimate, so
an almost surely convergent subsequence identifies the product limit"): if `Σ X_n = U` in `L²`,
every `H X_n ∈ L²` and `Σ mulL2 H X_n` converges, then `H U ∈ L²` and
`Σ mulL2 H X_n = mulL2 H U`. -/
theorem hasSum_mulL2 (hA : OccupiedMultTarget.{u, 0}) {X₀ : Type} {Ω : Type u}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {W : X₀ → Ω → ℝ}
    {K : X₀ → X₀ → ℝ} (hW : CenteredGaussianField W K P) {H U : Lp ℝ 2 P} {X : ℕ → Lp ℝ 2 P}
    (hXU : HasSum X U) (hX : ∀ n, MemLp (fun ω => H ω * X n ω) 2 P)
    (hS : Summable fun n => mulL2 H (X n)) :
    MemLp (fun ω => H ω * U ω) 2 P ∧ HasSum (fun n => mulL2 H (X n)) (mulL2 H U) := by
  have hpart := mulL2_sum_range hX
  have hlim : Tendsto (fun N => mulL2 H (∑ n ∈ Finset.range N, X n)) atTop
      (𝓝 (∑' n, mulL2 H (X n))) := by
    simp_rw [fun N => (hpart N).2]
    exact hS.hasSum.tendsto_sum_nat
  obtain ⟨hm, he⟩ := (hA P W K hW).2 H (fun N => ∑ n ∈ Finset.range N, X n) U _
    (fun N => (hpart N).1) hXU.tendsto_sum_nat hlim
  exact ⟨hm, he ▸ hS.hasSum⟩

/-! ### Width bookkeeping for Step 5 -/

/-- The vertexwise width pairs of `Fin.snoc` width vectors are the `Fin.snoc` of the width
pairs (on the positive quadrant for the external pair). -/
theorem posW_snoc {m : ℕ} (ε δ : Fin m → ℝ) (e : ℝ × ℝ) (he : 0 < e.1 ∧ 0 < e.2) :
    posW (Fin.snoc ε e.1 : Fin (m + 1) → ℝ) (Fin.snoc δ e.2) =
      (Fin.snoc (posW ε δ) (toPosW e) : Fin (m + 1) → PosW) := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [posW, toPosW, he]
  · simp [posW]

theorem continuous_snoc {m : ℕ} :
    Continuous fun q : (Fin m → ℝ) × ℝ => (Fin.snoc q.1 q.2 : Fin (m + 1) → ℝ) := by
  refine continuous_pi fun j => ?_
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simpa using continuous_snd
  · simp only [Fin.snoc_castSucc]
    exact (continuous_apply i).comp continuous_fst

/-- `Fin.snoc` maps the width filter of order `m` times `𝓝[>] 0` into the width filter of order
`m + 1` ("every vertex width below `r`", TeX 2299-2300). -/
theorem tendsto_snoc (m : ℕ) :
    Tendsto (fun q : (Fin m → ℝ) × ℝ => (Fin.snoc q.1 q.2 : Fin (m + 1) → ℝ))
      (widthFilter m ×ˢ 𝓝[>] (0 : ℝ)) (widthFilter (m + 1)) := by
  unfold widthFilter
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have h0 : (Fin.snoc (0 : Fin m → ℝ) (0 : ℝ) : Fin (m + 1) → ℝ) = 0 := by
      funext j
      refine Fin.lastCases ?_ (fun i => ?_) j <;> simp
    have h := (continuous_snoc (m := m)).tendsto ((0 : Fin m → ℝ), (0 : ℝ))
    simp only [h0] at h
    refine h.mono_left ?_
    rw [nhds_prod_eq]
    exact Filter.prod_mono nhdsWithin_le_nhds nhdsWithin_le_nhds
  · filter_upwards [prod_mem_prod (self_mem_nhdsWithin (s := posOrthant m) (a := 0))
      (self_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0))] with q hq
    simp only [posOrthant, Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies] at hq ⊢
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa using hq.2
    · simpa using hq.1 i

/-! ### The time-zero orders and the expansion at `s ≥ 0` -/

section Fields

variable {d : ℕ} {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)} {Ω : Type u} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {W : SrcPt d → Ω → ℝ}

/-- At `t = 0` the terminal chain measure of positive order is zero (mass `0^{2n}/(2n)! = 0`). -/
theorem chainMeasure_zero_time (x : Rd d) (n : ℕ) :
    chainMeasure d (n + 1) 0 le_rfl x = 0 := by
  refine Measure.measure_univ_eq_zero.mp ?_
  rw [TerminalWickInputs.chainMeasure_univ_eq, TerminalWickInputs.chainMeasureRaw_univ_eq,
    TerminalWick.chainMassReal_eq (n + 1) 0 le_rfl]
  simp

omit [IsProbabilityMeasure P] in
/-- At `s = 0`, `X_{n+1} = 0` (TeX 2210: the positive orders vanish). -/
theorem XL2_zero_time (hW : SourceField α₀ Γ P W) (x : Rd d) (n : ℕ) :
    XL2 hW 0 le_rfl x (n + 1) = 0 := by
  have hY : Ycom hW 0 le_rfl x (n + 1) = fun _ => 0 := by
    funext p
    simp only [Ycom, Yw, Ya, chainMeasure_zero_time x n, integral_zero_measure]
  rw [XL2_succ]
  unfold stratInt
  rw [hY]
  exact tendsto_const_nhds.limUnder_eq

/-- `u(s,y) = Σ_n X_n(s,y)` in `L²` for every `s ≥ 0` (`expansion_l2_l19` for `s > 0`; at
`s = 0` only `X_0` is nonzero). -/
theorem hasSum_XL2 (hH : HomogCovariance d alpha α₀ Γ μ) (hW : SourceField α₀ Γ P W) (s : ℝ)
    (hs : 0 ≤ s) (y : Rd d) : HasSum (XL2 hW s hs y) (uL2 hW s hs y) := by
  rcases hs.lt_or_eq with hpos | h0
  · exact (SourceFinal.expansion_l2_l19 d hH P W hW s hpos y).2
  · subst h0
    have hfin : ∀ n, n ≠ 0 → XL2 hW 0 hs y n = 0 := by
      intro n hn
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      exact XL2_zero_time hW y m
    have h := hasSum_single 0 hfin
    have hu : uL2 hW 0 hs y = XL2 hW 0 hs y 0 := h.tsum_eq
    rw [hu]
    exact h

/-- `X_0 = 1` as an `L²` class (`Ya_zero`). -/
theorem XL2_zero_eq_const (hH : HomogCovariance d alpha α₀ Γ μ) (hW : SourceField α₀ Γ P W)
    (t : ℝ) (ht : 0 ≤ t) (x : Rd d) : XL2 hW t ht x 0 = Lp.const 2 P (1 : ℝ) := by
  refine Lp.ext ?_
  filter_upwards [Ya_zero hH.dim hW t ht x (Fin.elim0 : Fin 0 → PosW),
    Lp.coeFn_const 2 P (1 : ℝ)] with ω h1 h2
  rw [XL2_zero, h1, h2]
  rfl

/-- The mild point map is measurable. -/
theorem measurable_mildPt {t : ℝ} : Measurable (mildPt (d := d) (t := t)) :=
  (measurable_subtype_coe.comp (measurable_fst.comp (measurable_pi_apply 0))).prodMk
    (measurable_snd.comp (measurable_pi_apply 0))

/-- The mild measure lives on times `s ≤ t`. -/
theorem ae_mildMeasure_le (t : ℝ) (ht : 0 ≤ t) (x : Rd d) :
    ∀ᵐ p ∂mildMeasure d t ht x, p.1 ≤ t := by
  unfold mildMeasure
  rw [ae_map_iff measurable_mildPt.aemeasurable (measurableSet_le measurable_fst measurable_const)]
  exact ae_of_all _ fun z => (z 0).1.2.2

theorem qn_nonneg (C θ₀ : ℝ) (n : ℕ) {T : ℝ} (hT : 0 ≤ T) : 0 ≤ qn C θ₀ n T := by
  unfold qn
  positivity

/-- **The product series at a fixed field point** (Step 6, TeX 2310-2320 at revision edf7085f
(book 1.1.3)): with D's `E:fixed-external-domination` (second clause of
`PartialVertexTarget`) and A's closedness clause, `W_a(p) u(p) ∈ L²` and
`Σ_n mulL2 (W_a(p)) (X_n(p)) = mulL2 (W_a(p)) (u(p))` at every `p` (for `s < 0` all are `0`). -/
theorem prod_hasSum (hA : OccupiedMultTarget.{u, 0}) (hH : HomogCovariance d alpha α₀ Γ μ)
    (hW : SourceField α₀ Γ P W) {C θ₀ : ℝ} (hC : 0 < C)
    (hD2 : ∀ (a : PosW) (n : ℕ), 1 ≤ n → ∀ (T s : ℝ), 0 ≤ s → s ≤ T → ∀ y : Rd d,
      MemLp (fun ω => Wa hW a (s, y) ω * Xf hW (n - 1) (s, y) ω) 2 P ∧
        ‖mulL2 (Wa hW a (s, y)) (Xf hW (n - 1) (s, y))‖ ≤
          2 * Real.sqrt n * Real.sqrt (Va α₀ Γ a) * qn C θ₀ (n - 1) T)
    (a : PosW) (p : ℝ × Rd d) :
    MemLp (fun ω => Wa hW a p ω * uf hW p ω) 2 P ∧
      HasSum (fun n => mulL2 (Wa hW a p) (Xf hW n p)) (mulL2 (Wa hW a p) (uf hW p)) := by
  obtain ⟨s, y⟩ := p
  by_cases hs : 0 ≤ s
  · have hXf : (fun n => Xf hW n (s, y)) = XL2 hW s hs y := funext fun n => Xf_of_nonneg hW n hs y
    have hX : HasSum (fun n => Xf hW n (s, y)) (uf hW (s, y)) := by
      rw [hXf, uf_of_nonneg hW hs y]
      exact hasSum_XL2 hH hW s hs y
    have hD' : ∀ n : ℕ, MemLp (fun ω => Wa hW a (s, y) ω * Xf hW n (s, y) ω) 2 P ∧
        ‖mulL2 (Wa hW a (s, y)) (Xf hW n (s, y))‖ ≤
          2 * Real.sqrt ((n : ℝ) + 1) * Real.sqrt (Va α₀ Γ a) * qn C θ₀ n s := by
      intro n
      have h := hD2 a (n + 1) (by omega) s s hs le_rfl y
      simpa only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] using h
    have hS : Summable fun n => mulL2 (Wa hW a (s, y)) (Xf hW n (s, y)) := by
      refine Summable.of_norm_bounded ?_ fun n => (hD' n).2
      exact ((SourceVertexCrude.summable_sqrt_qn hC.le θ₀ s).mul_left
        (2 * Real.sqrt (Va α₀ Γ a))).congr
        fun n => by ring
    exact hasSum_mulL2 hA hW hX (fun n => (hD' n).1) hS
  · have hWa : Wa hW a (s, y) = 0 := by simp [Wa, hs]
    rw [hWa]
    refine ⟨memLp_zero_mul _, ?_⟩
    simp only [mulL2_zero_left]
    exact hasSum_zero

end Fields

/-! ### Step 5: `E:external-vertex-limit` -/

/-- **Step 5, `E:external-vertex-limit`** (TeX lines 2290-2303 at revision edf7085f (book
1.1.3), display 2295-2297): under `H:homog`, for every source field, `t > 0`, `x` and `n ≥ 1`,
`I_{n,a}(t,x) → X_n(t,x)` in `L²` as the external pair `a = (ε, δ) ↓ 0` with arbitrary relative
rates.  From item D's partial-vertex limit (fourth clause of `PartialVertexTarget`,
`E:partial-vertex-limit`) and L19's joint fixed-order convergence (`fixed_order_l2_l19`, the
`ζ`-argument of 2298-2302). -/
theorem external_vertex (d : ℕ) (hD : PartialVertexTarget.{u} d) : ExternalVertexTarget.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW t ht x n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨C, θ₀, -, -, hDf⟩ := hD hH
  have hD4 := (hDf P W hW).2.2.2.1
  have hfix := (SourceFinal.fixed_order_l2_l19 d hH P W hW t ht x (m + 1) (by omega)).1
  have hg : Tendsto (fun q : ((Fin m → ℝ) × (Fin m → ℝ)) × (ℝ × ℝ) =>
      ((Fin.snoc q.1.1 q.2.1 : Fin (m + 1) → ℝ), (Fin.snoc q.1.2 q.2.2 : Fin (m + 1) → ℝ)))
      ((widthFilter m ×ˢ widthFilter m) ×ˢ (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)))
      (widthFilter (m + 1) ×ˢ widthFilter (m + 1)) := by
    refine Tendsto.prodMk ?_ ?_
    · exact (tendsto_snoc m).comp
        ((tendsto_fst.comp tendsto_fst).prodMk (tendsto_fst.comp tendsto_snd))
    · exact (tendsto_snoc m).comp
        ((tendsto_snd.comp tendsto_fst).prodMk (tendsto_snd.comp tendsto_snd))
  have hcomp := hfix.comp hg
  rw [XL2_succ, Metric.tendsto_nhds]
  intro ζ hζ
  have hev := (Metric.tendsto_nhds.mp hcomp) (ζ / 2) (by linarith)
  obtain ⟨pa, hpa, pb, hpb, hall⟩ := Filter.eventually_prod_iff.mp hev
  have hpos : ∀ᶠ e : ℝ × ℝ in 𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ), 0 < e.1 ∧ 0 < e.2 :=
    prod_mem_prod (self_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0))
      (self_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0))
  filter_upwards [hpb, hpos] with e he hep
  have hlim := hD4 t ht x (toPosW e) m
  have hev2 : ∀ᶠ b in widthFilter m ×ˢ widthFilter m,
      dist (Ya hW t ht.le x (Fin.snoc (posW b.1 b.2) (toPosW e) : Fin (m + 1) → PosW))
        (stratInt hW t ht.le x (m + 1)) ≤ ζ / 2 := by
    filter_upwards [hpa] with b hb
    have h := hall hb he
    simp only [Function.comp_apply, Yw] at h
    rw [posW_snoc b.1 b.2 e hep] at h
    exact h.le
  have hle := le_of_tendsto (hlim.dist tendsto_const_nhds) hev2
  linarith

/-! ### Step 6 and `E:mild-construction` -/

/-- **`P:mild-construction`, `E:mild-construction`, with the hypotheses the proof uses** (TeX
lines 2151-2165 and Step 6, 2307-2339 at revision edf7085f (book 1.1.3)): from item A's
`OccupiedMultTarget` (closedness clause), item D's `PartialVertexTarget` and Step 5's
`ExternalVertexTarget`. -/
theorem mild_construction_of (d : ℕ) (hA : OccupiedMultTarget.{u, 0})
    (hD : PartialVertexTarget.{u} d) (hX : ExternalVertexTarget.{u} d) :
    MildConstructionTarget.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW t ht x
  obtain ⟨C, θ₀, hC0, -, hDf⟩ := hD hH
  obtain ⟨-, hD2, hD3, -, hD5⟩ := hDf P W hW
  have hprod := fun a p => prod_hasSum hA hH hW hC0 hD2 a p
  set M := mildMeasure d t ht.le x with hM
  have : IsFiniteMeasure M := by rw [hM]; unfold mildMeasure; infer_instance
  -- the termwise bound on `0 ≤ s ≤ t` (and trivially for `s < 0`)
  set gb : PosW → ℕ → ℝ := fun a n =>
    2 * Real.sqrt ((n : ℝ) + 1) * Real.sqrt (Va α₀ Γ a) * qn C θ₀ n t with hgb
  have hgb_nonneg : ∀ a n, 0 ≤ gb a n := fun a n => by
    have := qn_nonneg C θ₀ n ht.le
    simp only [hgb]
    positivity
  have hgb_sum : ∀ a, Summable (gb a) := fun a =>
    ((SourceVertexCrude.summable_sqrt_qn hC0.le θ₀ t).mul_left
      (2 * Real.sqrt (Va α₀ Γ a))).congr
      fun n => by simp only [hgb]; ring
  have hG : ∀ a n (p : ℝ × Rd d), p.1 ≤ t →
      ‖mulL2 (Wa hW a p) (Xf hW n p)‖ ≤ gb a n := by
    intro a n p hpt
    obtain ⟨s, y⟩ := p
    by_cases hs : 0 ≤ s
    · have h := (hD2 a (n + 1) (by omega) t s hs hpt y).2
      simpa only [hgb, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] using h
    · have hWa : Wa hW a (s, y) = 0 := by simp [Wa, hs]
      rw [hWa, mulL2_zero_left, norm_zero]
      exact hgb_nonneg a n
  -- the partial sums and their limit
  have hInt : ∀ a n, Integrable (fun p => mulL2 (Wa hW a p) (Xf hW n p)) M := by
    intro a n
    have h := hD3 t ht x a (n + 1) (by omega)
    simpa only [Nat.add_sub_cancel] using h
  have hSmeas : ∀ a N, AEStronglyMeasurable
      (fun p => ∑ n ∈ Finset.range N, mulL2 (Wa hW a p) (Xf hW n p)) M := fun a N =>
    (integrable_finsetSum _ fun n _ => hInt a n).aestronglyMeasurable
  have hlim : ∀ a p, Tendsto (fun N => ∑ n ∈ Finset.range N, mulL2 (Wa hW a p) (Xf hW n p))
      atTop (𝓝 (mulL2 (Wa hW a p) (uf hW p))) := fun a p => (hprod a p).2.tendsto_sum_nat
  have hmeas : ∀ a, AEStronglyMeasurable (fun p => mulL2 (Wa hW a p) (uf hW p)) M := fun a =>
    aestronglyMeasurable_of_tendsto_ae atTop (hSmeas a) (ae_of_all _ (hlim a))
  have hsupp := ae_mildMeasure_le (d := d) t ht.le x
  have hbound : ∀ a, ∀ᵐ p ∂M, ‖mulL2 (Wa hW a p) (uf hW p)‖ ≤ ∑' n, gb a n := fun a => by
    filter_upwards [hsupp] with p hp
    exact (hprod a p).2.norm_le_of_bounded (hgb_sum a).hasSum fun n => hG a n p hp
  have hSbound : ∀ a N, ∀ᵐ p ∂M,
      ‖∑ n ∈ Finset.range N, mulL2 (Wa hW a p) (Xf hW n p)‖ ≤ ∑' n, gb a n := fun a N => by
    filter_upwards [hsupp] with p hp
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun n _ => hG a n p hp).trans ?_
    exact Summable.sum_le_tsum _ (fun n _ => hgb_nonneg a n) (hgb_sum a)
  have hint : ∀ a, Integrable (fun p => mulL2 (Wa hW a p) (uf hW p)) M := fun a =>
    Integrable.of_bound (hmeas a) _ (hbound a)
  -- `I_a = Σ_{n ≥ 1} I_{n,a}` (dominated Green integration)
  have hqsum : Summable fun n : ℕ => qn C θ₀ n t :=
    Summable.of_nonneg_of_le (fun n => qn_nonneg C θ₀ n ht.le)
      (fun n => le_mul_of_one_le_left (qn_nonneg C θ₀ n ht.le)
        (Real.one_le_sqrt.mpr (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])))
      (SourceVertexCrude.summable_sqrt_qn hC0.le θ₀ t)
  have hqsum1 : Summable fun n : ℕ => qn C θ₀ (n + 1) t :=
    (summable_nat_add_iff 1).mpr hqsum
  have hInab : ∀ a n, ‖Ina hW a (n + 1) t ht.le x‖ ≤ qn C θ₀ (n + 1) t := fun a n =>
    hD5 t ht x a (n + 1) (by omega)
  have hIa : ∀ a, HasSum (fun n => Ina hW a (n + 1) t ht.le x) (Ia hW a t ht.le x) := by
    intro a
    have hdct := tendsto_integral_of_dominated_convergence (fun _ => ∑' n, gb a n) (hSmeas a)
      (integrable_const _) (hSbound a) (ae_of_all _ (hlim a))
    refine (hasSum_iff_tendsto_nat_of_summable_norm
      (Summable.of_nonneg_of_le (fun n => norm_nonneg _) (hInab a) hqsum1)).mpr ?_
    have heq : ∀ N, ∫ p, ∑ n ∈ Finset.range N, mulL2 (Wa hW a p) (Xf hW n p) ∂M =
        ∑ n ∈ Finset.range N, Ina hW a (n + 1) t ht.le x := fun N =>
      integral_finsetSum _ fun n _ => hInt a n
    simp_rw [heq] at hdct
    exact hdct
  -- `u - 1 = Σ_{n ≥ 1} X_n`
  have hXsum := hasSum_XL2 hH hW t ht.le x
  have htail : HasSum (fun n => XL2 hW t ht.le x (n + 1))
      (uL2 hW t ht.le x - Lp.const 2 P (1 : ℝ)) := by
    have h := (hasSum_nat_add_iff' 1).mpr hXsum
    simpa only [Finset.sum_range_one, XL2_zero_eq_const hH hW t ht.le x] using h
  refine ⟨fun a p => (hprod a p).1, hint, ?_⟩
  -- the final uniform tail (Tannery)
  have hT := tendsto_tsum_of_dominated_convergence
    (f := fun e : ℝ × ℝ => fun n : ℕ => Ina hW (toPosW e) (n + 1) t ht.le x)
    (g := fun n => XL2 hW t ht.le x (n + 1)) (𝓕 := 𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ))
    hqsum1 (fun n => hX hH P W hW t ht x (n + 1) (by omega))
    (Eventually.of_forall fun e n => hInab (toPosW e) n)
  rw [htail.tsum_eq] at hT
  refine hT.congr fun e => ?_
  exact (hIa (toPosW e)).tsum_eq

/-- **`P:mild-construction`, `E:mild-construction`** (TeX lines 2151-2165 at revision edf7085f
(book 1.1.3), display 2156-2161; proof Steps 5-6, 2290-2339), frozen signature: under
`H:homog`, for every source field, `t > 0` and `x`: `W_a u ∈ L²` at every point, the mild
integrand is integrable against the mild (Green) measure, and
`∫_0^t ∫ G(t-s, x-dy) u(s,y) W_{ε,δ}(s,y) ds → u(t,x) - 1` in `L²` as `ε, δ ↓ 0` with arbitrary
relative rates.  Items B and C are not used by this route (their content enters through D);
see `mild_construction_of`. -/
theorem mild_construction (d : ℕ) (hA : OccupiedMultTarget.{u, 0}) (_hB : PolyMemTarget.{u} d)
    (_hC : FieldMeasTarget.{u} d) (hD : PartialVertexTarget.{u} d)
    (hX : ExternalVertexTarget.{u} d) : MildConstructionTarget.{u} d :=
  mild_construction_of d hA hD hX

end StratonovichHAMSecondMoment.MildConstruction
