module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L20, item D (second module): `PartialVertexTarget`, `P:mild-construction` Step 3 (TeX lines
2233-2265 at revision edf7085f (book 1.1.3)): the partially regularized terminal integral
`I_{n,a}(t,x)` (2236-2243), `E:fixed-external-domination` (2245-2248), `E:partial-vertex-limit`
(2253-2256, with the terminal-kernel Fubini 2257-2260) and `E:mixed-vertex-bound` (2263-2265).

Hypotheses (the frozen signature, interface section 2 D): A's `OccupiedMultTarget` (used at the
source field, `X = SrcPt d`), B's `PolyMemTarget`, C's `FieldMeasTarget` (only its joint
measurability half `JointMeasTarget` is used) and `TerminalFubiniTarget` (proved without
hypotheses in `MildTerminalFubini.terminal_fubini`); all are discharged at integration.  Besides
`Mathlib` and `MildInterface` this module imports item D's own first module
`MildTerminalFubini` (for the description of the mild measure: finiteness, times in `(0,t)`).

Route:
* `E:occupied-multiplication` makes `(H, F) ↦ H F` jointly continuous on `LinG × P_(≤n)`
  (`tendsto_mulL2`: the product is bilinear there and bounded by `2√(n+1)‖H‖‖F‖`); composed
  with the orthogonal projections onto these closed subspaces it is continuous on `L² × L²`, so
  `p ↦ W_a(p) Y(p)` is strongly measurable when `W_a` and `Y` are (C) and take values in the
  subspaces (`Wa_mem_LinG`; B for `Y`, `X`) (`stronglyMeasurable_mulL2`);
* `E:fixed-external-domination`: A's bound, `‖W_a(s,y)‖₂ = √V_a` (`Va_eq_srcCov`) and
  `‖X_{n-1}(s,y)‖₂ ≤ q_{n-1}(s) ≤ q_{n-1}(T)` (`E:vertex-crude`, `vertex_crude_l19`, the same
  `C, θ₀`; `q_k` is monotone in `t ≥ 0`); at `s = 0` (interface TeX observation 4) the positive
  orders vanish (TeX 2210; `g_k^{0,y} = 0` for `k ≥ 1`) and `X_0 = 1`;
* `E:partial-vertex-limit`: the terminal-kernel Fubini rewrites `Y_{m+1}^{(b,a)}(t,x)` as the
  mild integral of `W_a Y_m^b`; dominated Bochner convergence along the inner width filter
  (`tendsto_integral_filter_of_dominated_convergence`; the mild measure sees only `0 < s < t`)
  with `fixed_order_l2_l19` at each `(s, y)` and the continuity of the product; for `m = 0`
  (`n = 1`) the identity is exact (`widthFilter 0` is a point);
* `E:mixed-vertex-bound`: `‖Y_{m+1}^c(t,x)‖₂ ≤ q_{m+1}(t)` for all widths (`E:vertex-crude`)
  passes to the limit.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.MildInterface
public import StratonovichHAMSecondMoment.MildTerminalFubini

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal Real Nat

namespace StratonovichHAMSecondMoment.MildPartialVertex

universe u

open HomogHypothesis (Rd HomogCovariance)
open WaveGreen (waveGreen)
open FiniteWick (CenteredGaussianField)
open TerminalWick (Pt prodL2)
open TerminalWickInputs (chainMeasure fieldL2)
open WickInterface (widthFilter)
open SourceInterface
open MildInterface

/-! ### `mulL2` on `LinG × P_(≤n)` (`E:occupied-multiplication`) -/

section Mul

variable {X : Type*} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : X → Ω → ℝ}
  {K : X → X → ℝ}

/-- `LinG` is complete (closed in `L²`); named. -/
instance instCompleteSpaceLinG (hW : CenteredGaussianField W K P) :
    CompleteSpace (LinG hW) :=
  Submodule.topologicalClosure.completeSpace _

/-- `P_(≤n)` is complete (closed in `L²`); named. -/
instance instCompleteSpacePolyLE (hW : CenteredGaussianField W K P)
    (n : ℕ) : CompleteSpace (PolyLE hW n) :=
  Submodule.topologicalClosure.completeSpace _

/-- `mulL2` is additive in the first factor on `L²` products. -/
theorem mulL2_sub_left {H H' F : Lp ℝ 2 P} (h1 : MemLp (fun ω => H ω * F ω) 2 P)
    (h2 : MemLp (fun ω => H' ω * F ω) 2 P) :
    mulL2 (H - H') F = mulL2 H F - mulL2 H' F := by
  have h3 : MemLp (fun ω => (H - H') ω * F ω) 2 P := by
    refine (h1.sub h2).ae_eq ?_
    filter_upwards [Lp.coeFn_sub H H'] with ω hω
    rw [hω]; simp [sub_mul]
  refine Lp.ext ?_
  filter_upwards [coeFn_mulL2 h3, Lp.coeFn_sub (mulL2 H F) (mulL2 H' F), coeFn_mulL2 h1,
    coeFn_mulL2 h2, Lp.coeFn_sub H H'] with ω e3 es e1 e2 eH
  rw [e3, es, Pi.sub_apply, e1, e2, eH, Pi.sub_apply, sub_mul]

/-- `mulL2` is additive in the second factor on `L²` products. -/
theorem mulL2_sub_right {H F F' : Lp ℝ 2 P} (h1 : MemLp (fun ω => H ω * F ω) 2 P)
    (h2 : MemLp (fun ω => H ω * F' ω) 2 P) :
    mulL2 H (F - F') = mulL2 H F - mulL2 H F' := by
  have h3 : MemLp (fun ω => H ω * (F - F') ω) 2 P := by
    refine (h1.sub h2).ae_eq ?_
    filter_upwards [Lp.coeFn_sub F F'] with ω hω
    rw [hω]; simp [mul_sub]
  refine Lp.ext ?_
  filter_upwards [coeFn_mulL2 h3, Lp.coeFn_sub (mulL2 H F) (mulL2 H F'), coeFn_mulL2 h1,
    coeFn_mulL2 h2, Lp.coeFn_sub F F'] with ω e3 es e1 e2 eF
  rw [e3, es, Pi.sub_apply, e1, e2, eF, Pi.sub_apply, mul_sub]

variable {hW : CenteredGaussianField W K P} {n : ℕ}
  (hM : ∀ H ∈ LinG hW, ∀ F ∈ PolyLE hW n,
    MemLp (fun ω => H ω * F ω) 2 P ∧ ‖mulL2 H F‖ ≤ 2 * Real.sqrt ((n : ℝ) + 1) * ‖H‖ * ‖F‖)
include hM

/-- **Joint continuity of the product on `LinG × P_(≤n)`** (from `E:occupied-multiplication`,
TeX 2189-2191: the product is bilinear there with the bound `2√(n+1)‖H‖‖F‖`). -/
theorem tendsto_mulL2 {ι : Type*} {l : Filter ι} {H F : ι → Lp ℝ 2 P} {H₀ F₀ : Lp ℝ 2 P}
    (hH : ∀ i, H i ∈ LinG hW) (hF : ∀ i, F i ∈ PolyLE hW n) (hH₀ : H₀ ∈ LinG hW)
    (hF₀ : F₀ ∈ PolyLE hW n) (h1 : Tendsto H l (𝓝 H₀)) (h2 : Tendsto F l (𝓝 F₀)) :
    Tendsto (fun i => mulL2 (H i) (F i)) l (𝓝 (mulL2 H₀ F₀)) := by
  set c : ℝ := 2 * Real.sqrt ((n : ℝ) + 1) with hc
  have hid : ∀ i, mulL2 (H i) (F i) - mulL2 H₀ F₀ =
      mulL2 (H i - H₀) (F i) + mulL2 H₀ (F i - F₀) := by
    intro i
    rw [mulL2_sub_left (hM _ (hH i) _ (hF i)).1 (hM _ hH₀ _ (hF i)).1,
      mulL2_sub_right (hM _ hH₀ _ (hF i)).1 (hM _ hH₀ _ hF₀).1]
    abel
  have hb : ∀ i, ‖mulL2 (H i) (F i) - mulL2 H₀ F₀‖ ≤
      c * ‖H i - H₀‖ * ‖F i‖ + c * ‖H₀‖ * ‖F i - F₀‖ := by
    intro i
    rw [hid]
    exact (norm_add_le _ _).trans (add_le_add (hM _ (sub_mem (hH i) hH₀) _ (hF i)).2
      (hM _ hH₀ _ (sub_mem (hF i) hF₀)).2)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun i => norm_nonneg _) hb ?_
  have e1 : Tendsto (fun i => ‖H i - H₀‖) l (𝓝 0) := (tendsto_iff_norm_sub_tendsto_zero).1 h1
  have e2 : Tendsto (fun i => ‖F i - F₀‖) l (𝓝 0) := (tendsto_iff_norm_sub_tendsto_zero).1 h2
  have e3 : Tendsto (fun i => ‖F i‖) l (𝓝 ‖F₀‖) := h2.norm
  have h := (((tendsto_const_nhds (x := c)).mul e1).mul e3).add
    ((tendsto_const_nhds (x := c * ‖H₀‖)).mul e2)
  simpa using h

/-- The product after the orthogonal projections onto `LinG` and `P_(≤n)` is continuous on
`L² × L²`. -/
theorem continuous_mulL2_proj :
    Continuous fun q : Lp ℝ 2 P × Lp ℝ 2 P =>
      mulL2 ((LinG hW).starProjection q.1) ((PolyLE hW n).starProjection q.2) := by
  rw [continuous_iff_continuousAt]
  intro q
  exact tendsto_mulL2 hM (fun q => Submodule.starProjection_apply_mem _ _)
    (fun q => Submodule.starProjection_apply_mem _ _) (Submodule.starProjection_apply_mem _ _)
    (Submodule.starProjection_apply_mem _ _)
    ((ContinuousLinearMap.continuous _).comp continuous_fst).continuousAt
    ((ContinuousLinearMap.continuous _).comp continuous_snd).continuousAt

/-- **Strong measurability of the products**: strongly measurable maps into `LinG` and
`P_(≤n)` have a strongly measurable product. -/
theorem stronglyMeasurable_mulL2 {α : Type*} [MeasurableSpace α] {f g : α → Lp ℝ 2 P}
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) (hf' : ∀ a, f a ∈ LinG hW)
    (hg' : ∀ a, g a ∈ PolyLE hW n) : StronglyMeasurable fun a => mulL2 (f a) (g a) := by
  have h := (continuous_mulL2_proj hM).comp_stronglyMeasurable (hf.prodMk hg)
  have heq : (fun a => mulL2 (f a) (g a)) = fun a =>
      mulL2 ((LinG hW).starProjection (f a)) ((PolyLE hW n).starProjection (g a)) := by
    funext a
    rw [Submodule.starProjection_eq_self_iff.2 (hf' a),
      Submodule.starProjection_eq_self_iff.2 (hg' a)]
  rw [heq]
  exact h

end Mul

/-! ### The total fields in the closed subspaces -/

section Fields

variable {d : ℕ} {α₀ : ℝ} {Γ : Measure (Rd d)} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : SrcPt d → Ω → ℝ}

theorem Wa_mem_LinG (hW : SourceField α₀ Γ P W) (a : PosW) (p : ℝ × Rd d) :
    Wa hW a p ∈ LinG hW := by
  unfold Wa
  split_ifs
  · exact fieldL2_mem_LinG hW _
  · exact zero_mem _

theorem norm_fieldL2 (hW : SourceField α₀ Γ P W) (z : ↥(Set.Ici (0 : ℝ)) × Rd d) (a : PosW) :
    ‖fieldL2 hW (z, a)‖ = Real.sqrt (Va α₀ Γ a) := by
  rw [Va_eq_srcCov α₀ Γ a z, ← TerminalWickInputs.inner_fieldL2 hW (z, a) (z, a),
    real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

/-- `q_k` is monotone in `t ≥ 0`. -/
theorem qn_mono {C θ₀ : ℝ} (hθ : 0 ≤ θ₀) (k : ℕ) {s T : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) :
    qn C θ₀ k s ≤ qn C θ₀ k T := by
  unfold qn
  gcongr

/-- `g_k^{0,y} = 0` for `k ≥ 1` (the open simplex below `0` is empty). -/
theorem chainMeasure_time_zero (k : ℕ) (y : Rd d) :
    chainMeasure d (k + 1) 0 le_rfl y = 0 := by
  rw [← Measure.measure_univ_eq_zero, TerminalWickInputs.chainMeasure_univ_eq,
    TerminalWickInputs.chainMeasureRaw_univ_eq, TerminalWick.chainMassReal_eq (k + 1) 0 le_rfl]
  simp

/-- `X_k(0, y) = 0` for `k ≥ 1` (TeX 2210: the positive orders vanish at time `0`). -/
theorem XL2_time_zero (hW : SourceField α₀ Γ P W) (k : ℕ) (y : Rd d) :
    XL2 hW 0 le_rfl y (k + 1) = 0 := by
  rw [XL2_succ, stratInt]
  have h0 : Ycom hW 0 le_rfl y (k + 1) = fun _ => 0 := by
    funext e
    rw [Ycom, Yw, Ya, chainMeasure_time_zero, integral_zero_measure]
  rw [h0]
  exact tendsto_const_nhds.limUnder_eq

end Fields

/-! ### `PartialVertexTarget` (TeX 2236-2265) -/

/-- **`PartialVertexTarget`** (`P:mild-construction` Step 3, TeX lines 2236-2265 at revision
edf7085f (book 1.1.3): `E:fixed-external-domination` 2245-2248, `E:partial-vertex-limit`
2253-2256 with the terminal-kernel Fubini 2257-2260, `E:mixed-vertex-bound` 2263-2265): under
`H:homog` there are the constants `C, θ₀` of `E:vertex-crude` such that for every source field
(i) `‖X_n(t,x)‖₂ ≤ q_n(t)`; (ii) `W_a X_{n-1}` is in `L²` with
`‖W_a(s,y) X_{n-1}(s,y)‖₂ ≤ 2√n √V_a q_{n-1}(T)` for `0 ≤ s ≤ T`; (iii) `I_{n,a}(t,x)` exists
(Bochner integrability); (iv) `Y_{m+1}^{(b,a)}(t,x) → I_{m+1,a}(t,x)` in `L²` as the inner widths
`b ↓ 0` at arbitrary rates; (v) `‖I_{n,a}(t,x)‖₂ ≤ q_n(t)`.  Route: module docstring.  Of C's
target only the joint measurability half is used, of A's only the bound (first) clause. -/
theorem partial_vertex (d : ℕ) (hA : OccupiedMultTarget.{u, 0}) (hB : PolyMemTarget.{u} d)
    (hC : FieldMeasTarget.{u} d) (hF : TerminalFubiniTarget.{u} d) : PartialVertexTarget.{u} d := by
  intro alpha α₀ Γ μ hH
  obtain ⟨C, θ₀, hC0, hθ, hY, hX, -⟩ := SourceFinal.vertex_crude_l19.{u} d hH
  refine ⟨C, θ₀, hC0, hθ, ?_⟩
  intro Ω _ P _ W hW
  have hM : ∀ k : ℕ, ∀ H ∈ LinG hW, ∀ F ∈ PolyLE hW k,
      MemLp (fun ω => H ω * F ω) 2 P ∧ ‖mulL2 H F‖ ≤ 2 * Real.sqrt ((k : ℝ) + 1) * ‖H‖ * ‖F‖ :=
    (hA P W (srcCov α₀ Γ) hW).1
  have hJ := hC.1 hH P W hW
  have hYmem : ∀ (k : ℕ) (b : Fin k → PosW) (p : ℝ × Rd d), Yf hW b p ∈ PolyLE hW k := by
    intro k b p
    unfold Yf
    split_ifs with h
    · exact (hB hH P W hW p.1 h p.2 k).1 b
    · exact zero_mem _
  have hXmem : ∀ (k : ℕ) (p : ℝ × Rd d), Xf hW k p ∈ PolyLE hW k := by
    intro k p
    unfold Xf
    split_ifs with h
    · exact (hB hH P W hW p.1 h p.2 k).2
    · exact zero_mem _
  -- `‖X_k(s,y)‖ ≤ q_k(T)` for `0 ≤ s ≤ T` (interface TeX observation 4 at `s = 0`; TeX 2210)
  have hXle : ∀ (k : ℕ) (T s : ℝ) (hs : 0 ≤ s), s ≤ T → ∀ y : Rd d,
      ‖XL2 hW s hs y k‖ ≤ qn C θ₀ k T := by
    intro k T s hs hsT y
    rcases hs.lt_or_eq with hs' | hs'
    · exact (hX P W hW s hs' y k).trans (qn_mono hθ.le k hs hsT)
    · subst hs'
      rcases k with _ | k
      · have h1 : ‖XL2 hW 0 hs y 0‖ = 1 := by
          have hsq : ‖XL2 hW 0 hs y 0‖ ^ 2 = 1 := by
            rw [← real_inner_self_eq_norm_sq, ← UniformSeriesTail.integral_mul_eq_inner,
              XL2_zero]
            have hae := Ya_zero hH.dim hW 0 hs y (Fin.elim0 : Fin 0 → PosW)
            have he : (fun ω => (Ya hW 0 hs y (Fin.elim0 : Fin 0 → PosW) : Ω → ℝ) ω *
                (Ya hW 0 hs y (Fin.elim0 : Fin 0 → PosW) : Ω → ℝ) ω) =ᵐ[P] fun _ => (1 : ℝ) := by
              filter_upwards [hae] with ω hω
              rw [hω, one_mul]
            rw [integral_congr_ae he]
            simp
          nlinarith [norm_nonneg (XL2 hW 0 hs y 0)]
        rw [h1, qn_zero]
        exact Real.one_le_exp (mul_nonneg hθ.le hsT)
      · rw [XL2_time_zero, norm_zero]
        exact qn_nonneg hsT (k + 1)
  -- clause (ii): `E:fixed-external-domination`
  have h2 : ∀ (a : PosW) (n : ℕ), 1 ≤ n → ∀ (T s : ℝ), 0 ≤ s → s ≤ T → ∀ y : Rd d,
      MemLp (fun ω => Wa hW a (s, y) ω * Xf hW (n - 1) (s, y) ω) 2 P ∧
        ‖mulL2 (Wa hW a (s, y)) (Xf hW (n - 1) (s, y))‖ ≤
          2 * Real.sqrt n * Real.sqrt (Va α₀ Γ a) * qn C θ₀ (n - 1) T := by
    intro a n hn T s hs hsT y
    obtain ⟨hmem, hle⟩ := hM (n - 1) _ (Wa_mem_LinG hW a (s, y)) _ (hXmem (n - 1) (s, y))
    refine ⟨hmem, hle.trans ?_⟩
    have hcast : ((n - 1 : ℕ) : ℝ) + 1 = n := by
      rw [Nat.cast_sub hn]; ring
    rw [hcast, Wa_of_nonneg hW a hs y, norm_fieldL2, Xf_of_nonneg hW (n - 1) hs y]
    exact mul_le_mul_of_nonneg_left (hXle (n - 1) T s hs hsT y) (by positivity)
  -- the mild measure
  have hfin : ∀ (t : ℝ) (ht : 0 < t) (x : Rd d), IsFiniteMeasure (mildMeasure d t ht.le x) :=
    fun t ht x => MildTerminalFubini.isFiniteMeasure_mildMeasure t ht.le x
  -- clause (iii): integrability
  have h3 : ∀ (t : ℝ) (ht : 0 < t) (x : Rd d) (a : PosW) (n : ℕ), 1 ≤ n →
      Integrable (fun p => mulL2 (Wa hW a p) (Xf hW (n - 1) p)) (mildMeasure d t ht.le x) := by
    intro t ht x a n hn
    have := hfin t ht x
    have hsm : StronglyMeasurable fun p => mulL2 (Wa hW a p) (Xf hW (n - 1) p) :=
      stronglyMeasurable_mulL2 (hM (n - 1)) (hJ.1 a) (hJ.2.2.1 (n - 1)) (Wa_mem_LinG hW a)
        (hXmem (n - 1))
    refine Integrable.of_bound hsm.aestronglyMeasurable
      (2 * Real.sqrt n * Real.sqrt (Va α₀ Γ a) * qn C θ₀ (n - 1) t) ?_
    filter_upwards [MildTerminalFubini.ae_mildMeasure t ht.le x] with p hp
    obtain ⟨s, y⟩ := p
    exact (h2 a n hn t s hp.1.le hp.2.le y).2
  -- clause (iv): `E:partial-vertex-limit`
  have h4 : ∀ (t : ℝ) (ht : 0 < t) (x : Rd d) (a : PosW) (m : ℕ),
      Tendsto (fun e : (Fin m → ℝ) × (Fin m → ℝ) =>
          Ya hW t ht.le x (Fin.snoc (posW e.1 e.2) a : Fin (m + 1) → PosW))
        (widthFilter m ×ˢ widthFilter m) (𝓝 (Ina hW a (m + 1) t ht.le x)) := by
    intro t ht x a m
    have hTF : ∀ b : Fin m → PosW, Ya hW t ht.le x (Fin.snoc b a : Fin (m + 1) → PosW) =
        mildInt (fun p => mulL2 (Wa hW a p) (Yf hW b p)) t ht.le x :=
      fun b => (hF hH P W hW t ht x m b a).2.2
    simp_rw [hTF]
    rcases m with _ | k
    · -- `n = 1`: no inner widths, the identity is exact
      have hYX : ∀ b : Fin 0 → PosW, Yf hW b = Xf hW 0 := by
        intro b
        funext p
        unfold Yf Xf
        split_ifs
        · rw [Subsingleton.elim b Fin.elim0]; rfl
        · rfl
      simp_rw [hYX]
      exact tendsto_const_nhds
    · have := hfin t ht x
      have : (widthFilter (k + 1)).IsCountablyGenerated := by
        unfold widthFilter; infer_instance
      refine tendsto_integral_filter_of_dominated_convergence
        (fun _ => 2 * Real.sqrt ((k + 1 : ℕ) + 1 : ℝ) * Real.sqrt (Va α₀ Γ a) *
          qn C θ₀ (k + 1) t) ?_ ?_ (integrable_const _) ?_
      · refine Filter.Eventually.of_forall fun e => ?_
        exact (stronglyMeasurable_mulL2 (hM (k + 1)) (hJ.1 a) (hJ.2.1 (k + 1) _)
          (Wa_mem_LinG hW a) (hYmem (k + 1) _)).aestronglyMeasurable
      · refine Filter.Eventually.of_forall fun e => ?_
        filter_upwards [MildTerminalFubini.ae_mildMeasure t ht.le x] with p hp
        obtain ⟨s, y⟩ := p
        have hs : 0 ≤ s := hp.1.le
        refine (hM (k + 1) _ (Wa_mem_LinG hW a (s, y)) _ (hYmem (k + 1) _ (s, y))).2.trans ?_
        rw [Wa_of_nonneg hW a hs y, norm_fieldL2, Yf_of_nonneg hW _ hs y]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact (hY P W hW s hp.1 y (k + 1) (Nat.succ_pos k) _).trans
          (qn_mono hθ.le (k + 1) hs hp.2.le)
      · filter_upwards [MildTerminalFubini.ae_mildMeasure t ht.le x] with p hp
        obtain ⟨s, y⟩ := p
        have hs : 0 ≤ s := hp.1.le
        have hfo := (SourceFinal.fixed_order_l2_l19.{u} d hH P W hW s hp.1 y (k + 1)
          (Nat.succ_pos k)).1
        refine tendsto_mulL2 (hM (k + 1)) (fun _ => Wa_mem_LinG hW a (s, y))
          (fun e => hYmem (k + 1) _ (s, y)) (Wa_mem_LinG hW a (s, y)) (hXmem (k + 1) (s, y))
          tendsto_const_nhds ?_
        have he : (fun e : (Fin (k + 1) → ℝ) × (Fin (k + 1) → ℝ) => Yf hW (posW e.1 e.2) (s, y)) =
            fun e => Yw hW s hs y e.1 e.2 := by
          funext e
          rw [Yf_of_nonneg hW _ hs y]
          rfl
        rw [he]
        change Tendsto _ _ (𝓝 (Xf hW (k + 1) (s, y)))
        rw [Xf_of_nonneg hW (k + 1) hs y, XL2_succ]
        exact hfo
  refine ⟨fun t ht x n => hX P W hW t ht x n, h2, h3, h4, ?_⟩
  -- clause (v): `E:mixed-vertex-bound`
  intro t ht x a n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.sub_add_cancel hn).symm⟩
  have hlim := (h4 t ht x a m).norm
  refine le_of_tendsto' hlim fun e => ?_
  exact hY P W hW t ht x (m + 1) (Nat.succ_pos m) _

end StratonovichHAMSecondMoment.MildPartialVertex
