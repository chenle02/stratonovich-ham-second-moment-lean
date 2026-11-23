module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L20, item E: the Green-width limit at fixed external widths (Step 4 of the proof of
`P:mild-construction`, TeX lines 2268-2287, with the d = 3 sentence 2162-2164, the d = 3 reading
2167-2169 and the summed product of Step 6, 2327-2328, at revision edf7085f (book 1.1.3)).

Statement proved (`green_width_mild`, the frozen `GreenWidthMildTarget` of `MildInterface`):
under `H:homog`, for every source field, `t > 0`, `x` and a fixed external width `a`,
* for `n ≥ 1` the products `W_a(s,y) X_{n-1}(s,y)` are `L²`-continuous in `y` at each `s ≥ 0`,
  integrable against the Green-smoothed order-one chain measures (`mildMeasureReg`, `p_η * G`)
  and their smoothed mild integrals converge in `L²(Ω)` to `I_{n,a}(t,x)` as `η ↓ 0`;
* the same for the summed product `W_a(s,y) u(s,y)` and `I_a(t,x)` (TeX 2327-2328).

Hypotheses (other L20 items, with exactly their frozen signatures, discharged at integration):
A's `OccupiedMultTarget.{u, 0}`, B's `PolyMemTarget`, C's `FieldMeasTarget`, D's
`PartialVertexTarget`.

Route (decision 3; disclosed route difference): instead of the TeX's compact-set partition of
unity, scalar weak convergence and tightness (2279-2283), both the smoothed and the unsmoothed
order-one chain measures are pushed to L11's noise space
(`chainMeasureReg = noiseMeasure.map (regPt η)`, `chainMeasure_eq_map_noise`); the smoothing
moves only the spatial coordinate, continuously in `η`, and leaves the time coordinate fixed in
`[0, t]`.  Dominated convergence on the noise space then needs, at each fixed time, only the
spatial `L²` continuity of the integrand (TeX 2272-2277: A applied to the two increments, with C's
continuity of `X_{n-1}(s,·)` and of the field value `W_a(s,·)`), its strong measurability, and
the uniform bound `E:fixed-external-domination` (2245-2248, D's second clause; TeX 2277 "uniform
in `y`").  Two Lean-level steps not spelled out in the TeX:
* strong measurability of `(s,y) ↦ W_a(s,y) X_{n-1}(s,y)`: the product is the composition of the
  measurable fields with the map `(H, F) ↦ H·F` precomposed with the orthogonal projections onto
  `LinG` and `PolyLE (n-1)`, which is continuous on `L² × L²` by A's bound (`continuous_mulP`);
* the summed product: by A's closedness clause (TeX 2318-2320) `W_a u = Σ_n W_a X_{n-1}` at every
  `s ≥ 0` (at `s = 0` the positive orders vanish, `XL2_time_zero`), the series converging
  uniformly in `y` by D's bound and `E:vertex-summability` (`summable_sqrt_qn`), whence its
  continuity, measurability and bound (TeX 2327-2328, "by uniform summability").
The statement is stated and proved for every `d` (the TeX's sentence is about d = 3; the d = 1, 2
cases are extra, interface section 4 item 5, as L19's `GreenFirstTarget`).
-/
public import Mathlib
public import StratonovichHAMSecondMoment.MildInterface

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal Real Nat

namespace StratonovichHAMSecondMoment.MildGreenWidth

universe u v

open HomogHypothesis (Rd HomogCovariance)
open FiniteWick (CenteredGaussianField)
open TerminalWick (Pt prodL2)
open TerminalWickInputs (chainMeasure fieldL2)
open TerminalWickRegularization (chainMeasureReg noiseMeasure regPt Noise)
open SourceInterface
open MildInterface

/-! ### Additivity of `mulL2` on products in `L²` -/

section Mul

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Multiplication by the zero class gives the zero class (the product is in `L²`). -/
theorem mulL2_zero_left (F : Lp ℝ 2 P) :
    MemLp (fun ω => (0 : Lp ℝ 2 P) ω * F ω) 2 P ∧ mulL2 (0 : Lp ℝ 2 P) F = 0 := by
  have h0 : (fun ω => (0 : Lp ℝ 2 P) ω * F ω) =ᵐ[P] ⇑(0 : Lp ℝ 2 P) := by
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := P)] with ω h
    rw [h, Pi.zero_apply, zero_mul]
  have h : MemLp (fun ω => (0 : Lp ℝ 2 P) ω * F ω) 2 P := (Lp.memLp _).ae_eq h0.symm
  exact ⟨h, Lp.ext ((coeFn_mulL2 h).trans h0)⟩

/-- Multiplication by the zero class on the right. -/
theorem mulL2_zero_right (H : Lp ℝ 2 P) :
    MemLp (fun ω => H ω * (0 : Lp ℝ 2 P) ω) 2 P ∧ mulL2 H (0 : Lp ℝ 2 P) = 0 := by
  have h0 : (fun ω => H ω * (0 : Lp ℝ 2 P) ω) =ᵐ[P] ⇑(0 : Lp ℝ 2 P) := by
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := P)] with ω h
    rw [h, Pi.zero_apply, mul_zero]
  have h : MemLp (fun ω => H ω * (0 : Lp ℝ 2 P) ω) 2 P := (Lp.memLp _).ae_eq h0.symm
  exact ⟨h, Lp.ext ((coeFn_mulL2 h).trans h0)⟩

/-- `mulL2` is additive in the left factor when the products are in `L²`. -/
theorem mulL2_sub_left {H₁ H₂ F : Lp ℝ 2 P} (h₁ : MemLp (fun ω => H₁ ω * F ω) 2 P)
    (h₂ : MemLp (fun ω => H₂ ω * F ω) 2 P) :
    mulL2 (H₁ - H₂) F = mulL2 H₁ F - mulL2 H₂ F := by
  have he : (fun ω => H₁ ω * F ω - H₂ ω * F ω) =ᵐ[P] fun ω => (H₁ - H₂) ω * F ω := by
    filter_upwards [Lp.coeFn_sub H₁ H₂] with ω h
    rw [h, Pi.sub_apply, sub_mul]
  have h : MemLp (fun ω => (H₁ - H₂) ω * F ω) 2 P := (h₁.sub h₂).ae_eq he
  refine Lp.ext ?_
  filter_upwards [coeFn_mulL2 h, coeFn_mulL2 h₁, coeFn_mulL2 h₂,
    Lp.coeFn_sub (mulL2 H₁ F) (mulL2 H₂ F), Lp.coeFn_sub H₁ H₂] with ω e e₁ e₂ e₃ e₄
  rw [e, e₃, Pi.sub_apply, e₁, e₂, e₄, Pi.sub_apply, sub_mul]

/-- `mulL2` is additive in the right factor when the products are in `L²`. -/
theorem mulL2_sub_right {H F₁ F₂ : Lp ℝ 2 P} (h₁ : MemLp (fun ω => H ω * F₁ ω) 2 P)
    (h₂ : MemLp (fun ω => H ω * F₂ ω) 2 P) :
    mulL2 H (F₁ - F₂) = mulL2 H F₁ - mulL2 H F₂ := by
  have he : (fun ω => H ω * F₁ ω - H ω * F₂ ω) =ᵐ[P] fun ω => H ω * (F₁ - F₂) ω := by
    filter_upwards [Lp.coeFn_sub F₁ F₂] with ω h
    rw [h, Pi.sub_apply, mul_sub]
  have h : MemLp (fun ω => H ω * (F₁ - F₂) ω) 2 P := (h₁.sub h₂).ae_eq he
  refine Lp.ext ?_
  filter_upwards [coeFn_mulL2 h, coeFn_mulL2 h₁, coeFn_mulL2 h₂,
    Lp.coeFn_sub (mulL2 H F₁) (mulL2 H F₂), Lp.coeFn_sub F₁ F₂] with ω e e₁ e₂ e₃ e₄
  rw [e, e₃, Pi.sub_apply, e₁, e₂, e₄, Pi.sub_apply, mul_sub]

/-- `mulL2` is additive in the right factor, with the `L²` membership of the sum. -/
theorem mulL2_add_right {H F₁ F₂ : Lp ℝ 2 P} (h₁ : MemLp (fun ω => H ω * F₁ ω) 2 P)
    (h₂ : MemLp (fun ω => H ω * F₂ ω) 2 P) :
    MemLp (fun ω => H ω * (F₁ + F₂) ω) 2 P ∧ mulL2 H (F₁ + F₂) = mulL2 H F₁ + mulL2 H F₂ := by
  have he : (fun ω => H ω * F₁ ω + H ω * F₂ ω) =ᵐ[P] fun ω => H ω * (F₁ + F₂) ω := by
    filter_upwards [Lp.coeFn_add F₁ F₂] with ω h
    rw [h, Pi.add_apply, mul_add]
  have h : MemLp (fun ω => H ω * (F₁ + F₂) ω) 2 P := (h₁.add h₂).ae_eq he
  refine ⟨h, Lp.ext ?_⟩
  filter_upwards [coeFn_mulL2 h, coeFn_mulL2 h₁, coeFn_mulL2 h₂,
    Lp.coeFn_add (mulL2 H F₁) (mulL2 H F₂), Lp.coeFn_add F₁ F₂] with ω e e₁ e₂ e₃ e₄
  rw [e, e₃, Pi.add_apply, e₁, e₂, e₄, Pi.add_apply, mul_add]

/-- `mulL2 H` commutes with finite partial sums when every product is in `L²`. -/
theorem mulL2_sum_range {H : Lp ℝ 2 P} {F : ℕ → Lp ℝ 2 P}
    (h : ∀ k, MemLp (fun ω => H ω * F k ω) 2 P) (N : ℕ) :
    MemLp (fun ω => H ω * (∑ k ∈ Finset.range N, F k) ω) 2 P ∧
      mulL2 H (∑ k ∈ Finset.range N, F k) = ∑ k ∈ Finset.range N, mulL2 H (F k) := by
  induction N with
  | zero => simpa using mulL2_zero_right H
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    obtain ⟨hm, he⟩ := mulL2_add_right ih.1 (h N)
    exact ⟨hm, by rw [he, ih.2]⟩

end Mul

/-! ### Multiplication as a continuous map on `L² × L²` (via the orthogonal projections) -/

section Proj

variable {X : Type v} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : X → Ω → ℝ}
  {K : X → X → ℝ}

/-- Auxiliary: `LinG` admits the orthogonal projection (a closed subspace of `L²`). -/
theorem hasOrthProj_LinG (hW : CenteredGaussianField W K P) :
    (LinG hW).HasOrthogonalProjection := by
  have : CompleteSpace (LinG hW) :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  infer_instance

/-- Auxiliary: `PolyLE n` admits the orthogonal projection (a closed subspace of `L²`). -/
theorem hasOrthProj_PolyLE (hW : CenteredGaussianField W K P) (n : ℕ) :
    (PolyLE hW n).HasOrthogonalProjection := by
  have : CompleteSpace (PolyLE hW n) :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  infer_instance

/-- Auxiliary: the product `π_L H · π_n F` of the orthogonal projections onto `LinG` and
`PolyLE n` (equal to `mulL2 H F` on `LinG × PolyLE n`, `mulP_eq`). -/
def mulP (hW : CenteredGaussianField W K P) (n : ℕ) (H F : Lp ℝ 2 P) : Lp ℝ 2 P :=
  haveI := hasOrthProj_LinG hW
  haveI := hasOrthProj_PolyLE hW n
  mulL2 ((LinG hW).starProjection H) ((PolyLE hW n).starProjection F)

theorem mulP_eq (hW : CenteredGaussianField W K P) {n : ℕ} {H F : Lp ℝ 2 P}
    (hH : H ∈ LinG hW) (hF : F ∈ PolyLE hW n) : mulP hW n H F = mulL2 H F := by
  have := hasOrthProj_LinG hW
  have := hasOrthProj_PolyLE hW n
  unfold mulP
  rw [Submodule.starProjection_eq_self_iff.mpr hH, Submodule.starProjection_eq_self_iff.mpr hF]

/-- **Multiplication is continuous on `LinG × PolyLE n`** (from A's bound
`E:occupied-multiplication`, TeX 2189-2191, applied to the two increments as at TeX 2273-2276):
`(H, F) ↦ π_L H · π_n F` is continuous on `L² × L²`. -/
theorem continuous_mulP (hA : OccupiedMultTarget.{u, v}) [IsProbabilityMeasure P]
    (hW : CenteredGaussianField W K P) (n : ℕ) :
    Continuous fun q : Lp ℝ 2 P × Lp ℝ 2 P => mulP hW n q.1 q.2 := by
  have := hasOrthProj_LinG hW
  have := hasOrthProj_PolyLE hW n
  set c : ℝ := 2 * Real.sqrt ((n : ℝ) + 1) with hc
  have hc0 : 0 ≤ c := by positivity
  have hb : ∀ H ∈ LinG hW, ∀ F ∈ PolyLE hW n,
      MemLp (fun ω => H ω * F ω) 2 P ∧ ‖mulL2 H F‖ ≤ c * ‖H‖ * ‖F‖ :=
    fun H hH F hF => (hA P W K hW).1 n H hH F hF
  rw [continuous_iff_continuousAt]
  rintro ⟨H₀, F₀⟩
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have key : ∀ q : Lp ℝ 2 P × Lp ℝ 2 P,
      ‖mulP hW n q.1 q.2 - mulP hW n H₀ F₀‖ ≤
        c * ‖q.1 - H₀‖ * ‖q.2‖ + c * ‖H₀‖ * ‖q.2 - F₀‖ := by
    intro q
    set h := (LinG hW).starProjection q.1 with hh
    set h₀ := (LinG hW).starProjection H₀ with hh₀
    set f := (PolyLE hW n).starProjection q.2 with hf
    set f₀ := (PolyLE hW n).starProjection F₀ with hf₀
    have mh : h ∈ LinG hW := Submodule.starProjection_apply_mem _ _
    have mh₀ : h₀ ∈ LinG hW := Submodule.starProjection_apply_mem _ _
    have mf : f ∈ PolyLE hW n := Submodule.starProjection_apply_mem _ _
    have mf₀ : f₀ ∈ PolyLE hW n := Submodule.starProjection_apply_mem _ _
    have e : mulP hW n q.1 q.2 - mulP hW n H₀ F₀ = mulL2 (h - h₀) f + mulL2 h₀ (f - f₀) := by
      rw [mulL2_sub_left (hb h mh f mf).1 (hb h₀ mh₀ f mf).1,
        mulL2_sub_right (hb h₀ mh₀ f mf).1 (hb h₀ mh₀ f₀ mf₀).1]
      unfold mulP
      abel
    have n1 : ‖h - h₀‖ ≤ ‖q.1 - H₀‖ := by
      rw [hh, hh₀, ← map_sub]; exact (LinG hW).norm_starProjection_apply_le _
    have n2 : ‖f‖ ≤ ‖q.2‖ := (PolyLE hW n).norm_starProjection_apply_le _
    have n3 : ‖h₀‖ ≤ ‖H₀‖ := (LinG hW).norm_starProjection_apply_le _
    have n4 : ‖f - f₀‖ ≤ ‖q.2 - F₀‖ := by
      rw [hf, hf₀, ← map_sub]; exact (PolyLE hW n).norm_starProjection_apply_le _
    rw [e]
    calc ‖mulL2 (h - h₀) f + mulL2 h₀ (f - f₀)‖
        ≤ ‖mulL2 (h - h₀) f‖ + ‖mulL2 h₀ (f - f₀)‖ := norm_add_le _ _
      _ ≤ c * ‖h - h₀‖ * ‖f‖ + c * ‖h₀‖ * ‖f - f₀‖ :=
        add_le_add (hb _ (sub_mem mh mh₀) f mf).2 (hb h₀ mh₀ _ (sub_mem mf mf₀)).2
      _ ≤ c * ‖q.1 - H₀‖ * ‖q.2‖ + c * ‖H₀‖ * ‖q.2 - F₀‖ :=
        add_le_add
          (mul_le_mul (mul_le_mul_of_nonneg_left n1 hc0) n2 (norm_nonneg _) (by positivity))
          (mul_le_mul (mul_le_mul_of_nonneg_left n3 hc0) n4 (norm_nonneg _) (by positivity))
  have hg : Continuous fun q : Lp ℝ 2 P × Lp ℝ 2 P =>
      c * ‖q.1 - H₀‖ * ‖q.2‖ + c * ‖H₀‖ * ‖q.2 - F₀‖ := by fun_prop
  have hlim : Tendsto (fun q : Lp ℝ 2 P × Lp ℝ 2 P =>
      c * ‖q.1 - H₀‖ * ‖q.2‖ + c * ‖H₀‖ * ‖q.2 - F₀‖) (𝓝 (H₀, F₀)) (𝓝 0) := by
    simpa using hg.tendsto (H₀, F₀)
  exact squeeze_zero (fun q => norm_nonneg _) key hlim

end Proj

/-! ### The common-noise representation of the order-one mild measures -/

section Noise

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem continuous_mildPt {t : ℝ} : Continuous (mildPt (d := d) (t := t)) :=
  (continuous_subtype_val.comp (continuous_fst.comp (continuous_apply 0))).prodMk
    (continuous_snd.comp (continuous_apply 0))

/-- **The Green-width limit of a mild integral** (TeX 2277-2284, common-noise route; module
docstring): if `g : ℝ × ℝ^d → L²(Ω)` is strongly measurable, `L²`-continuous in `y` at every
fixed time `s ≥ 0` and bounded by `M` on `[0, t] × ℝ^d`, then `g` is integrable against every
smoothed mild measure and the smoothed mild integrals converge to the mild integral as `η ↓ 0`. -/
theorem mild_reg_limit (g : ℝ × Rd d → Lp ℝ 2 P) (hg : StronglyMeasurable g)
    (hc : ∀ s : ℝ, 0 ≤ s → Continuous fun y : Rd d => g (s, y)) (M : ℝ) {t : ℝ}
    (hM : ∀ (s : ℝ) (y : Rd d), 0 ≤ s → s ≤ t → ‖g (s, y)‖ ≤ M) (ht : 0 < t) (x : Rd d) :
    (∀ η : ℝ, Integrable g (mildMeasureReg d t ht.le x η)) ∧
      Tendsto (fun η => mildIntReg g t ht.le x η) (𝓝[>] (0 : ℝ)) (𝓝 (mildInt g t ht.le x)) := by
  have := TerminalWickRegularization.isFiniteMeasure_noiseMeasure d 1 ht.le
  set rp : ℝ → Noise d 1 → ℝ × Rd d := fun η q => mildPt (regPt ht.le x η q) with hrpdef
  have hrpc : Continuous fun p : ℝ × Noise d 1 => rp p.1 p.2 :=
    continuous_mildPt.comp (TerminalWickRegularization.continuous_regPt ht.le x)
  have hrp : ∀ η, Measurable (rp η) := fun η =>
    (hrpc.comp (continuous_const.prodMk continuous_id)).measurable
  have hmap : ∀ η, mildMeasureReg d t ht.le x η = (noiseMeasure d 1 t).map (rp η) := by
    intro η
    rw [mildMeasureReg, chainMeasureReg, Measure.map_map continuous_mildPt.measurable
      (TerminalWickRegularization.measurable_regPt ht.le x η)]
    rfl
  have hmap0 : mildMeasure d t ht.le x = (noiseMeasure d 1 t).map (rp 0) := by
    rw [mildMeasure, TerminalWickRegularization.chainMeasure_eq_map_noise,
      Measure.map_map continuous_mildPt.measurable
        (TerminalWickRegularization.measurable_regPt ht.le x 0)]
    rfl
  have htime : ∀ η q, 0 ≤ (rp η q).1 ∧ (rp η q).1 ≤ t := fun η q =>
    (regPt ht.le x η q 0).1.2
  have htime0 : ∀ η q, (rp η q).1 = (rp 0 q).1 := fun η q => rfl
  have hbd : ∀ η q, ‖g (rp η q)‖ ≤ M := fun η q => hM _ _ (htime η q).1 (htime η q).2
  have hint : ∀ η, Integrable g (mildMeasureReg d t ht.le x η) := by
    intro η
    rw [hmap η, integrable_map_measure hg.aestronglyMeasurable (hrp η).aemeasurable]
    exact (integrable_const M).mono' (hg.comp_measurable (hrp η)).aestronglyMeasurable
      (ae_of_all _ (hbd η))
  refine ⟨hint, ?_⟩
  have e : (fun η => mildIntReg g t ht.le x η) =
      fun η => ∫ q, g (rp η q) ∂(noiseMeasure d 1 t) := by
    funext η
    rw [mildIntReg, hmap η, integral_map (hrp η).aemeasurable hg.aestronglyMeasurable]
  have e0 : mildInt g t ht.le x = ∫ q, g (rp 0 q) ∂(noiseMeasure d 1 t) := by
    rw [mildInt, hmap0, integral_map (hrp 0).aemeasurable hg.aestronglyMeasurable]
  rw [e, e0]
  refine (tendsto_integral_filter_of_dominated_convergence (fun _ => M)
    (Eventually.of_forall fun η => (hg.comp_measurable (hrp η)).aestronglyMeasurable)
    (Eventually.of_forall fun η => ae_of_all _ (hbd η)) (integrable_const _)
    (ae_of_all _ fun q => ?_)).mono_left nhdsWithin_le_nhds
  have hy : Continuous fun η : ℝ => (rp η q).2 := by
    have hq : Continuous fun η : ℝ => ((η, q) : ℝ × Noise d 1) :=
      continuous_id.prodMk continuous_const
    have e : (fun η : ℝ => (rp η q).2) =
        Prod.snd ∘ (fun p : ℝ × Noise d 1 => rp p.1 p.2) ∘ fun η : ℝ => (η, q) := rfl
    rw [e]
    exact continuous_snd.comp (hrpc.comp hq)
  have hlim := ((hc _ (htime 0 q).1).tendsto ((rp 0 q).2)).comp (hy.tendsto 0)
  rw [Prod.mk.eta] at hlim
  refine hlim.congr fun η => ?_
  show g ((rp 0 q).1, (rp η q).2) = g (rp η q)
  rw [← htime0 η q, Prod.mk.eta]

end Noise

/-! ### The source fields: membership, continuity, vanishing at time `0` -/

section Source

variable {d : ℕ} {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)} {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} {W : SrcPt d → Ω → ℝ}

theorem Wa_mem_LinG (hW : SourceField α₀ Γ P W) (a : PosW) (p : ℝ × Rd d) :
    Wa hW a p ∈ LinG hW := by
  unfold Wa
  split_ifs with h
  · exact fieldL2_mem_LinG hW _
  · exact zero_mem _

theorem Wa_of_neg (hW : SourceField α₀ Γ P W) (a : PosW) {s : ℝ} (hs : ¬ 0 ≤ s) (y : Rd d) :
    Wa hW a (s, y) = 0 := by
  unfold Wa; simp [hs]

theorem Xf_of_neg (hW : SourceField α₀ Γ P W) (n : ℕ) {s : ℝ} (hs : ¬ 0 ≤ s) (y : Rd d) :
    Xf hW n (s, y) = 0 := by
  unfold Xf; simp [hs]

theorem uf_of_neg (hW : SourceField α₀ Γ P W) {s : ℝ} (hs : ¬ 0 ≤ s) (y : Rd d) :
    uf hW (s, y) = 0 := by
  unfold uf; simp [hs]

/-- The field value `W_a(s,·)` is `L²`-continuous at each fixed time (L19's
`SourceWick.continuous_fieldL2_w` with `SourceFeatures.source_cov_continuous`). -/
theorem continuous_Wa (hH : HomogCovariance d alpha α₀ Γ μ) (hW : SourceField α₀ Γ P W)
    (a : PosW) {s : ℝ} (hs : 0 ≤ s) : Continuous fun y : Rd d => Wa hW a (s, y) := by
  have e : (fun y : Rd d => Wa hW a (s, y)) = fun y => fieldL2 hW ((⟨s, hs⟩, y), a) :=
    funext fun y => Wa_of_nonneg hW a hs y
  rw [e]
  exact (SourceWick.continuous_fieldL2_w hW a
    (SourceFeatures.source_cov_continuous d hH a a)).comp
    (f := fun y : Rd d => ((⟨s, hs⟩ : ↥(Ici (0 : ℝ))), y)) (continuous_const.prodMk continuous_id)

/-- At time `0` the chain integrals of positive order vanish (the chain measure of order
`n ≥ 1` on `[0,0]` has mass `0^{2n}/(2n)! = 0`; TeX 2210, "At `t = 0` all positive-order terms
vanish"). -/
theorem Ya_time_zero (hW : SourceField α₀ Γ P W) (h0 : (0 : ℝ) ≤ 0) (y : Rd d) {n : ℕ}
    (hn : 1 ≤ n) (b : Fin n → PosW) : Ya hW 0 h0 y b = 0 := by
  have hz : chainMeasure d n 0 h0 y = 0 := by
    rw [← Measure.measure_univ_eq_zero, TerminalWickInputs.chainMeasure_univ_eq,
      TerminalWickInputs.chainMeasureRaw_univ_eq, TerminalWick.chainMassReal_eq n 0 le_rfl,
      zero_pow (by omega : 2 * n ≠ 0)]
    simp
  unfold Ya
  rw [hz, integral_zero_measure]

/-- `X_n(0, y) = 0` for `n ≥ 1` (TeX 2210). -/
theorem XL2_time_zero (hW : SourceField α₀ Γ P W) (h0 : (0 : ℝ) ≤ 0) (y : Rd d) (k : ℕ) :
    XL2 hW 0 h0 y (k + 1) = 0 := by
  rw [XL2_succ]
  have hY : Ycom hW 0 h0 y (k + 1) = fun _ => 0 := by
    funext p
    exact Ya_time_zero hW h0 y (by omega) _
  unfold stratInt
  rw [hY]
  exact tendsto_const_nhds.limUnder_eq

/-- `u = Σ_n X_n` at every time `s ≥ 0` (L19's `expansion_l2_l19` for `s > 0`; at `s = 0` only
`X_0` is nonzero, `XL2_time_zero`). -/
theorem hasSum_XL2 (hH : HomogCovariance d alpha α₀ Γ μ) {Ω' : Type u} [MeasurableSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {W' : SrcPt d → Ω' → ℝ}
    (hW : SourceField α₀ Γ P' W') {s : ℝ} (hs : 0 ≤ s) (y : Rd d) :
    HasSum (fun k => XL2 hW s hs y k) (uL2 hW s hs y) := by
  rcases hs.lt_or_eq with hpos | hzero
  · exact (SourceFinal.expansion_l2_l19.{u} d hH P' W' hW s hpos y).2
  · subst hzero
    have h1 := hasSum_single (f := fun k => XL2 hW 0 hs y k) 0 fun k hk => by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      exact XL2_time_zero hW hs y j
    show HasSum _ (∑' k, XL2 hW 0 hs y k)
    rw [h1.tsum_eq]
    exact h1

end Source

/-! ### Step 4 -/

/-- **The Green-width limit at fixed external widths** (`GreenWidthMildTarget`; Step 4 of
`P:mild-construction`, TeX lines 2268-2287, with 2162-2164, 2167-2169 and the summed product
2327-2328 at revision edf7085f (book 1.1.3)), with A's `OccupiedMultTarget`, B's
`PolyMemTarget`, C's `FieldMeasTarget` and D's `PartialVertexTarget` as hypotheses.  Route
(disclosed difference, module docstring): the common-noise representation of the smoothed
order-one chain measures and dominated convergence (`mild_reg_limit`) in place of the TeX's
partition of unity and tightness; spatial continuity of the products from A (`continuous_mulP`)
and C; domination from D's second clause (`E:fixed-external-domination`); the summed product by
A's closedness clause and uniform summability (`E:vertex-summability`).  Stated and proved for
every `d` (the TeX's convention is d = 3; the d = 1, 2 cases are extra). -/
theorem green_width_mild (d : ℕ) (hA : OccupiedMultTarget.{u, 0}) (hB : PolyMemTarget.{u} d)
    (hC : FieldMeasTarget.{u} d) (hD : PartialVertexTarget.{u} d) :
    GreenWidthMildTarget.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW t ht x a
  obtain ⟨C, θ₀, hC0, -, hDf⟩ := hD hH
  obtain ⟨-, hDii, -⟩ := hDf P W hW
  have hJ := hC.1 hH P W hW
  have hK := hC.2 hH P W hW
  set V : ℝ := Real.sqrt (Va α₀ Γ a) with hV
  -- the products `W_a X_m`
  obtain ⟨f, hfdef⟩ : ∃ f : ℕ → ℝ × Rd d → Lp ℝ 2 P,
      f = fun m p => mulL2 (Wa hW a p) (Xf hW m p) := ⟨_, rfl⟩
  have hXmem : ∀ m p, Xf hW m p ∈ PolyLE hW m := by
    intro m p
    unfold Xf
    split_ifs with h
    · exact (hB hH P W hW p.1 h p.2 m).2
    · exact zero_mem _
  have hfP : ∀ m, f m = (fun q : Lp ℝ 2 P × Lp ℝ 2 P => mulP hW m q.1 q.2) ∘
      fun p => (Wa hW a p, Xf hW m p) := by
    intro m
    subst hfdef
    exact funext fun p => (mulP_eq hW (Wa_mem_LinG hW a p) (hXmem m p)).symm
  have hfm : ∀ m, StronglyMeasurable (f m) := by
    intro m
    have h := Continuous.comp_stronglyMeasurable (continuous_mulP hA hW m)
      (StronglyMeasurable.prodMk (hJ.1 a) (hJ.2.2.1 m))
    rw [hfP m]
    exact h
  have hfc : ∀ m (s : ℝ), 0 ≤ s → Continuous fun y : Rd d => f m (s, y) := by
    intro m s hs
    have hX : Continuous fun y : Rd d => Xf hW m (s, y) := by
      have e : (fun y : Rd d => Xf hW m (s, y)) = fun y => XL2 hW s hs y m :=
        funext fun y => Xf_of_nonneg hW m hs y
      rw [e]
      exact (hK s hs).2.2.1 m
    have e : (fun y : Rd d => f m (s, y)) =
        (fun q : Lp ℝ 2 P × Lp ℝ 2 P => mulP hW m q.1 q.2) ∘
          fun y => (Wa hW a (s, y), Xf hW m (s, y)) := by
      rw [hfP m]; rfl
    rw [e]
    exact (continuous_mulP hA hW m).comp ((continuous_Wa hH hW a hs).prodMk hX)
  have hfb : ∀ m (T s : ℝ) (y : Rd d), 0 ≤ s → s ≤ T →
      ‖f m (s, y)‖ ≤ 2 * V * (Real.sqrt ((m : ℝ) + 1) * qn C θ₀ m T) := by
    intro m T s y hs hsT
    have h := (hDii a (m + 1) (by omega) T s hs hsT y).2
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at h
    subst hfdef
    calc ‖mulL2 (Wa hW a (s, y)) (Xf hW m (s, y))‖ ≤ 2 * Real.sqrt ((m : ℝ) + 1) * V * qn C θ₀ m T := h
      _ = 2 * V * (Real.sqrt ((m : ℝ) + 1) * qn C θ₀ m T) := by ring
  have hfmem : ∀ m (s : ℝ) (y : Rd d), 0 ≤ s →
      MemLp (fun ω => Wa hW a (s, y) ω * Xf hW m (s, y) ω) 2 P := by
    intro m s y hs
    have h := (hDii a (m + 1) (by omega) s s hs le_rfl y).1
    simpa only [Nat.add_sub_cancel] using h
  have hsB : ∀ T : ℝ, Summable fun m : ℕ => 2 * V * (Real.sqrt ((m : ℝ) + 1) * qn C θ₀ m T) :=
    fun T => (SourceVertexCrude.summable_sqrt_qn hC0.le θ₀ T).mul_left (2 * V)
  refine ⟨?_, ?_⟩
  · -- the fixed-order clauses
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have L := mild_reg_limit (f m) (hfm m) (hfc m) _ (fun s y hs hst => hfb m t s y hs hst) ht x
    have hc := hfc m
    subst hfdef
    exact ⟨fun s hs => hc s hs, Eventually.of_forall L.1, L.2⟩
  · -- the summed product `W_a u` (TeX 2327-2328)
    have hsum : ∀ p : ℝ × Rd d, Summable fun k => f k p := by
      rintro ⟨s, y⟩
      by_cases hs : 0 ≤ s
      · exact Summable.of_norm_bounded (hsB s) fun k => hfb k s s y hs le_rfl
      · have e : (fun k => f k (s, y)) = fun _ => 0 := by
          funext k
          rw [hfdef]
          simp only [Wa_of_neg hW a hs y, Xf_of_neg hW k hs y]
          exact (mulL2_zero_left _).2
        rw [e]
        exact summable_zero
    have hfu : ∀ p : ℝ × Rd d, mulL2 (Wa hW a p) (uf hW p) = ∑' k, f k p := by
      rintro ⟨s, y⟩
      by_cases hs : 0 ≤ s
      · have hk : ∀ k, MemLp (fun ω => Wa hW a (s, y) ω * Xf hW k (s, y) ω) 2 P :=
          fun k => hfmem k s y hs
        have hX : HasSum (fun k => Xf hW k (s, y)) (uf hW (s, y)) := by
          have e : (fun k => Xf hW k (s, y)) = fun k => XL2 hW s hs y k :=
            funext fun k => Xf_of_nonneg hW k hs y
          rw [e, uf_of_nonneg hW hs y]
          exact hasSum_XL2 hH hW hs y
        have hG : Tendsto (fun N => mulL2 (Wa hW a (s, y))
            (∑ k ∈ Finset.range N, Xf hW k (s, y))) atTop (𝓝 (∑' k, f k (s, y))) := by
          refine (hsum (s, y)).hasSum.tendsto_sum_nat.congr fun N => ?_
          rw [(mulL2_sum_range hk N).2, hfdef]
        exact ((hA P W (srcCov α₀ Γ) hW).2 (Wa hW a (s, y))
          (fun N => ∑ k ∈ Finset.range N, Xf hW k (s, y)) (uf hW (s, y)) _
          (fun N => (mulL2_sum_range hk N).1) hX.tendsto_sum_nat hG).2
      · have e : (fun k => f k (s, y)) = fun _ => 0 := by
          funext k
          rw [hfdef]
          simp only [Wa_of_neg hW a hs y, Xf_of_neg hW k hs y]
          exact (mulL2_zero_left _).2
        rw [Wa_of_neg hW a hs y, (mulL2_zero_left _).2, e, tsum_zero]
    have hgu : (fun p => mulL2 (Wa hW a p) (uf hW p)) = fun p => ∑' k, f k p := funext hfu
    have hgum : StronglyMeasurable fun p => ∑' k, f k p :=
      stronglyMeasurable_of_tendsto atTop
        (f := fun N p => ∑ k ∈ Finset.range N, f k p)
        (fun N => Finset.stronglyMeasurable_fun_sum _ fun k _ => hfm k)
        (tendsto_pi_nhds.mpr fun p => (hsum p).hasSum.tendsto_sum_nat)
    have hguc : ∀ s : ℝ, 0 ≤ s → Continuous fun y : Rd d => ∑' k, f k (s, y) :=
      fun s hs => continuous_tsum (fun k => hfc k s hs) (hsB s)
        fun k y => hfb k s s y hs le_rfl
    have hgub : ∀ (s : ℝ) (y : Rd d), 0 ≤ s → s ≤ t →
        ‖∑' k, f k (s, y)‖ ≤ ∑' m : ℕ, 2 * V * (Real.sqrt ((m : ℝ) + 1) * qn C θ₀ m t) :=
      fun s y hs hst => tsum_of_norm_bounded (hsB t).hasSum fun k => hfb k t s y hs hst
    have L := mild_reg_limit _ hgum hguc _ hgub ht x
    refine ⟨fun s hs => ?_, ?_, ?_⟩
    · have e : (fun y : Rd d => mulL2 (Wa hW a (s, y)) (uf hW (s, y))) =
          fun y => ∑' k, f k (s, y) := funext fun y => hfu (s, y)
      rw [e]
      exact hguc s hs
    · rw [hgu]
      exact Eventually.of_forall L.1
    · unfold Ia
      rw [hgu]
      exact L.2

end StratonovichHAMSecondMoment.MildGreenWidth
