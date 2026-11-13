module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Density of smooth compactly supported functions in the weak-gradient `H^1`
(half (a) of the D8-lite foundation; wave L7, item L7-c).

Foundation item with no manuscript label of its own.  The fact is stated in
one sentence in the proof of Proposition `P:spatial-four-linear` of
`notes/integrated_spatial_occupation.tex` at revision a284420, lines 262-266
("Smooth compact functions are dense in `H^1`. Cutoffs equal to one on the
radius-`R` ball, vanishing beyond `2R` and with gradient at most `C/R`,
converge ... Mollification then converges in `H^1` by `L^2` translation
continuity of the function and its weak gradients."), and it is used where
smooth-profile statements are extended to `H^1`: the same proof, lines
270-271, and the proof of Proposition `P:spatial-energy-map`, lines 328-330.

The space is the package's hand-rolled `H^1` of `WeakSobolev`
(`IsTestFunction`, `HasWeakGradient`, `MemH1`); the classical gradient of a
smooth function is `VariationalFloor.grad`.

Formalized here, unconditionally (no supplied inputs):
* `H1TestDense d` (the predicate, with the exact body fixed for the
  consumers L7-d and L7-e) and `h1TestDense : H1TestDense d` for every `d`
  (including `d = 0`): for `f, g ∈ L²` with `g` a weak gradient of `f` there
  are test functions `φ_n` with `φ_n → f` and `∇φ_n → g` in `L²`.
* `exists_test_approx` (the `ε` form) and `h1TestDense_of_memH1`
  (the `MemH1` form).
* `hasWeakGradient_of_tendsto`: the converse (an `L²` graph limit of test
  functions has the limit gradient as weak gradient); the manuscript
  sentence does not state it, and it is used by the refutations of this
  item.

Lean proof route (differs from the TeX in order and in the mollification
step; the lemmas marked "Auxiliary to the Lean proof route" serve only this
route and are not TeX steps):
1. Mollify first: `mollify φ u = ρ_φ ⋆ u` with the normalized bump
   `ρ_φ = φ.normed volume`.  An `L²` contraction `‖ρ ⋆ u‖₂ ≤ ‖u‖₂`
   (`eLpNorm_mollify_le`, Cauchy-Schwarz in `lintegral` plus Tonelli) and the
   density of continuous compactly supported functions in `L²` give
   `ρ_n ⋆ u → u` in `L²` when the bump radii tend to `0`
   (`tendsto_mollify`); the TeX invokes `L²` translation continuity instead.
   The weak-gradient identity tested against `y ↦ ρ(x - y)` gives
   `∇(ρ ⋆ f) = ρ ⋆ g` (`grad_mollify`).
2. Then cut off the smooth function `h = ρ ⋆ f` with `χ(x/(n+1))`,
   `χ = 1` on the unit ball and `0` beyond radius `2`; the classical product
   rule gives `∇(χ_n h) = χ_n ∇h + h ∇χ_n` (`grad_cutoff_mul`), the first two
   terms converge by dominated convergence (`tendsto_cutoff_smul`) and
   `‖h ∇χ_n‖₂ ≤ C ‖h‖₂ / (n+1)` (`norm_grad_cutoff_le`).  This is the TeX's
   cutoff estimate, applied after mollification, so no weak product rule is
   needed.
3. An `ε/2` argument and a choice of `ε = 1/(k+1)` give the sequence.

The mollifier sequence reuses `VariationalFloor.bumpN` (so
`mollify (VariationalFloor.bumpN d n) f` is `VariationalFloor.moll f n` for
real `f`, by definition).  Not formalized: the separability remark of the
same proof (lines 266-268).
-/
public import Mathlib
public import StratonovichHAMSecondMoment.HomogHypothesis
public import StratonovichHAMSecondMoment.WeakSobolev
public import StratonovichHAMSecondMoment.VariationalFloor

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped ENNReal Pointwise ContDiff

namespace StratonovichHAMSecondMoment.H1Density

open HomogHypothesis (Rd)
open WeakSobolev
open VariationalFloor (grad bumpN)

variable {d : ℕ}

/-! ### The density predicate -/

open MeasureTheory Filter Topology in
/-- Smooth compactly supported functions are dense in the weak-gradient `H^1`. -/
def H1TestDense (d : ℕ) : Prop :=
  ∀ (f : Rd d → ℝ) (g : Rd d → Rd d), MemLp f 2 volume → MemLp g 2 volume →
    WeakSobolev.HasWeakGradient f g →
    ∃ φ : ℕ → Rd d → ℝ, (∀ n, WeakSobolev.IsTestFunction (φ n)) ∧
      Tendsto (fun n => eLpNorm (fun x => φ n x - f x) 2 volume) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (fun x => VariationalFloor.grad (φ n) x - g x) 2 volume) atTop (𝓝 0)

/-! ### Two general auxiliary facts -/

/-- Auxiliary to the Lean proof route: Cauchy-Schwarz for a probability
weight in `lintegral` form, `(∫⁻ a b)² ≤ ∫⁻ a b²` when `∫⁻ a = 1`
(`a, b` a.e.-measurable). -/
theorem lintegral_mul_sq_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {a b : α → ℝ≥0∞} (ha : AEMeasurable a μ) (hb : AEMeasurable b μ)
    (h1 : ∫⁻ x, a x ∂μ = 1) :
    (∫⁻ x, a x * b x ∂μ) ^ (2 : ℝ) ≤ ∫⁻ x, a x * b x ^ (2 : ℝ) ∂μ := by
  have hsplit : ∀ x, a x * b x = a x ^ (1 / 2 : ℝ) * (a x ^ (1 / 2 : ℝ) * b x) := by
    intro x
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    (f := fun x => a x ^ (1 / 2 : ℝ)) (g := fun x => a x ^ (1 / 2 : ℝ) * b x)
    (ha.pow_const _) ((ha.pow_const _).mul hb)
  have e1 : ∀ x, (a x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = a x := by
    intro x; rw [← ENNReal.rpow_mul]; norm_num
  have e2 : ∀ x, (a x ^ (1 / 2 : ℝ) * b x) ^ (2 : ℝ) = a x * b x ^ (2 : ℝ) := by
    intro x; rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), e1]
  simp only [Pi.mul_apply, e1, e2, h1, ENNReal.one_rpow, one_mul] at hH
  simp_rw [hsplit]
  calc (∫⁻ x, a x ^ (1 / 2 : ℝ) * (a x ^ (1 / 2 : ℝ) * b x) ∂μ) ^ (2 : ℝ)
      ≤ ((∫⁻ x, a x * b x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow hH (by norm_num)
    _ = ∫⁻ x, a x * b x ^ (2 : ℝ) ∂μ := by rw [← ENNReal.rpow_mul]; norm_num

/-- Auxiliary to the Lean proof route: if `M < ∞` and for every `η > 0`
eventually `a n ≤ η M`, then `a n → 0`. -/
theorem tendsto_zero_of_eventually_le {a : ℕ → ℝ≥0∞} {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (h : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, a n ≤ ENNReal.ofReal η * M) :
    Tendsto a atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have T : Tendsto (fun k : ℕ => ENNReal.ofReal (1 / ((k : ℝ) + 1)) * M) atTop (𝓝 0) := by
    have h0 : Tendsto (fun k : ℕ => ENNReal.ofReal (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using ENNReal.Tendsto.mul_const h0 (Or.inr hM)
  obtain ⟨k, hk⟩ := (T.eventually (gt_mem_nhds hε)).exists
  filter_upwards [h _ (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1))] with n hn
  exact hn.trans hk.le

/-- Auxiliary to the Lean proof route: dominated convergence in `L²`.  If
`F n → 0` pointwise, each `F n` is a.e.-strongly measurable and
`‖F n x‖ ≤ ‖B x‖` with `B ∈ L²`, then `‖F n‖₂ → 0`. -/
theorem tendsto_eLpNorm_two_of_dominated {G H : Type*} [NormedAddCommGroup G]
    [NormedAddCommGroup H] {F : ℕ → Rd d → G} {B : Rd d → H} (hB : MemLp B 2 volume)
    (hF : ∀ n, AEStronglyMeasurable (F n) volume) (hle : ∀ n x, ‖F n x‖ ≤ ‖B x‖)
    (hlim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F n) 2 volume) atTop (𝓝 0) := by
  have e : ∀ n, eLpNorm (F n) 2 volume = (∫⁻ x, ‖F n x‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
    intro n
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) (hF n),
      ENNReal.toReal_ofNat]
  simp_rw [e]
  have hfin : ∫⁻ x, ‖B x‖ₑ ^ (2 : ℝ) ≠ ⊤ := by
    have := hB.eLpNorm_lt_top
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hB.aestronglyMeasurable,
      ENNReal.toReal_ofNat] at this
    exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).mp this |>.ne
  have hL : Tendsto (fun n => ∫⁻ x, ‖F n x‖ₑ ^ (2 : ℝ)) atTop (𝓝 (∫⁻ _ : Rd d, 0)) := by
    refine tendsto_lintegral_of_dominated_convergence' (fun x => ‖B x‖ₑ ^ (2 : ℝ))
      (fun n => (hF n).enorm.pow_const _) (fun n => Eventually.of_forall fun x => ?_) hfin
      (Eventually.of_forall fun x => ?_)
    · exact ENNReal.rpow_le_rpow (enorm_le_iff_norm_le.mpr (hle n x)) (by norm_num)
    · have h0 := (continuous_enorm.tendsto (0 : G)).comp (hlim x)
      rw [enorm_zero] at h0
      have h2 := ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto 0).comp h0
      rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h2
      exact h2
  rw [lintegral_zero] at hL
  have h2 := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp hL
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h2
  exact h2

/-! ### Mollification -/

section Mollify

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Auxiliary to the Lean proof route: the mollification
`ρ_φ ⋆ u (x) = ∫ ρ_φ(t) u(x - t) dt` with the normalized bump
`ρ_φ = φ.normed volume` (nonnegative, integral `1`, support the ball of
radius `φ.rOut`), for real- or vector-valued `u`. -/
def mollify (φ : ContDiffBump (0 : Rd d)) (u : Rd d → F) : Rd d → F :=
  convolution (φ.normed volume) u (ContinuousLinearMap.lsmul ℝ ℝ) volume

/-- Auxiliary to the Lean proof route: the mollification of a locally
integrable function is continuous. -/
theorem continuous_mollify (φ : ContDiffBump (0 : Rd d)) {u : Rd d → F}
    (hu : LocallyIntegrable u volume) : Continuous (mollify φ u) :=
  φ.hasCompactSupport_normed.continuous_convolution_left _
    (φ.continuous_normed (μ := volume)) hu

/-- Auxiliary to the Lean proof route: the mollification of a locally
integrable function is smooth. -/
theorem contDiff_mollify (φ : ContDiffBump (0 : Rd d)) {u : Rd d → F}
    (hu : LocallyIntegrable u volume) : ContDiff ℝ ∞ (mollify φ u) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed hu

/-- Auxiliary to the Lean proof route: the `L²` contraction
`‖ρ_φ ⋆ u‖₂ ≤ ‖u‖₂` (Cauchy-Schwarz against the probability weight `ρ_φ`,
then Tonelli and translation invariance). -/
theorem eLpNorm_mollify_le (φ : ContDiffBump (0 : Rd d)) {u : Rd d → F}
    (hu : MemLp u 2 volume) :
    eLpNorm (mollify φ u) 2 volume ≤ eLpNorm u 2 volume := by
  set ρ : Rd d → ℝ := φ.normed volume with hρ
  set a : Rd d → ℝ≥0∞ := fun t => ENNReal.ofReal (ρ t) with ha
  have ham : Measurable a := (φ.continuous_normed (μ := volume)).measurable.ennreal_ofReal
  have ha1 : ∫⁻ t, a t = 1 := by
    rw [ha, ← ofReal_integral_eq_lintegral_ofReal φ.integrable_normed
      (Filter.Eventually.of_forall fun t => φ.nonneg_normed t), φ.integral_normed,
      ENNReal.ofReal_one]
  have hloc : LocallyIntegrable u volume := hu.locallyIntegrable (by norm_num)
  have hpt : ∀ x, ‖mollify φ u x‖ₑ ^ (2 : ℝ) ≤ ∫⁻ t, a t * ‖u (x - t)‖ₑ ^ (2 : ℝ) := by
    intro x
    have h1 : ‖mollify φ u x‖ₑ ≤ ∫⁻ t, a t * ‖u (x - t)‖ₑ := by
      rw [mollify, convolution_def]
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      congr 1; funext t
      rw [ContinuousLinearMap.lsmul_apply, enorm_smul, Real.enorm_eq_ofReal (φ.nonneg_normed t)]
    have hbm : AEMeasurable (fun t => ‖u (x - t)‖ₑ) volume :=
      hu.aestronglyMeasurable.enorm.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_left_of_right_invariant volume x)
    exact (ENNReal.rpow_le_rpow h1 (by norm_num)).trans
      (lintegral_mul_sq_le volume ham.aemeasurable hbm ha1)
  have hprod : AEMeasurable (Function.uncurry fun x t => a t * ‖u (x - t)‖ₑ ^ (2 : ℝ))
      ((volume : Measure (Rd d)).prod volume) := by
    have hb : AEMeasurable (fun p : Rd d × Rd d => ‖u (p.1 - p.2)‖ₑ)
        ((volume : Measure (Rd d)).prod volume) :=
      hu.aestronglyMeasurable.enorm.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_of_right_invariant volume volume)
    exact (ham.comp measurable_snd).aemeasurable.mul (hb.pow_const _)
  have hint : ∫⁻ x, ‖mollify φ u x‖ₑ ^ (2 : ℝ) ≤ ∫⁻ x, ‖u x‖ₑ ^ (2 : ℝ) := by
    calc _ ≤ ∫⁻ x, ∫⁻ t, a t * ‖u (x - t)‖ₑ ^ (2 : ℝ) := lintegral_mono hpt
      _ = ∫⁻ t, ∫⁻ x, a t * ‖u (x - t)‖ₑ ^ (2 : ℝ) := lintegral_lintegral_swap hprod
      _ = ∫⁻ t, a t * ∫⁻ x, ‖u x‖ₑ ^ (2 : ℝ) := by
        congr 1; funext t
        have hm : AEMeasurable (fun x => ‖u (x - t)‖ₑ ^ (2 : ℝ)) volume :=
          (hu.aestronglyMeasurable.enorm.comp_quasiMeasurePreserving
            ((measurePreserving_sub_right volume t).quasiMeasurePreserving)).pow_const _
        rw [lintegral_const_mul'' _ hm]
        rw [lintegral_sub_right_eq_self (fun x => ‖u x‖ₑ ^ (2 : ℝ)) t]
      _ = ∫⁻ x, ‖u x‖ₑ ^ (2 : ℝ) := by
        rw [lintegral_mul_const _ ham, ha1, one_mul]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      (continuous_mollify φ hloc).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hu.aestronglyMeasurable]
  rw [ENNReal.toReal_ofNat]
  exact ENNReal.rpow_le_rpow hint (by norm_num)

/-- Auxiliary to the Lean proof route: the mollification of an `L²`
function is in `L²`. -/
theorem memLp_mollify (φ : ContDiffBump (0 : Rd d)) {u : Rd d → F}
    (hu : MemLp u 2 volume) : MemLp (mollify φ u) 2 volume :=
  memLp_iff.mpr (lt_of_le_of_lt (eLpNorm_mollify_le φ hu) hu.eLpNorm_lt_top)

/-- Auxiliary to the Lean proof route: mollification is additive on
differences of locally integrable functions. -/
theorem mollify_sub (φ : ContDiffBump (0 : Rd d)) {u w : Rd d → F}
    (hu : LocallyIntegrable u volume) (hw : LocallyIntegrable w volume) (x : Rd d) :
    mollify φ u x - mollify φ w x = mollify φ (fun y => u y - w y) x := by
  have eu := (φ.hasCompactSupport_normed.convolutionExists_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (φ.continuous_normed (μ := volume)) hu x).integrable
  have ew := (φ.hasCompactSupport_normed.convolutionExists_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (φ.continuous_normed (μ := volume)) hw x).integrable
  simp only [mollify, convolution_def]
  rw [← integral_sub eu ew]
  congr 1; funext t
  simp [smul_sub]

variable [CompleteSpace F]

/-- Auxiliary to the Lean proof route: for a continuous compactly
supported `c` with values in a complete space, `ρ_n ⋆ c → c` in `L²` when
the bump radii tend to `0` (uniform convergence on a fixed compact set). -/
theorem tendsto_mollify_of_continuous {c : Rd d → F} (hc : Continuous c)
    (hcs : HasCompactSupport c) {φ : ℕ → ContDiffBump (0 : Rd d)}
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => mollify (φ n) c x - c x) 2 volume) atTop (𝓝 0) := by
  set K : Set (Rd d) := Metric.closedBall (0 : Rd d) 1 + tsupport c with hK
  have hKc : IsCompact K := (isCompact_closedBall (0 : Rd d) 1).add hcs
  have hM : (volume K) ^ (1 / (2 : ℝ≥0∞).toReal) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hKc.measure_lt_top.ne
  refine tendsto_zero_of_eventually_le hM fun η hη => ?_
  obtain ⟨δ, hδ, hδc⟩ := Metric.uniformContinuous_iff.mp
    (hcs.uniformContinuous_of_continuous hc) η hη
  filter_upwards [hφ.eventually (gt_mem_nhds (lt_min hδ one_pos))] with n hn
  have hn' := lt_min_iff.mp hn
  have hloc : LocallyIntegrable c volume := hc.locallyIntegrable
  refine eLpNorm_sub_le_of_dist_bdd volume (by norm_num)
    hKc.isClosed.measurableSet.nullMeasurableSet hη.le
    ((continuous_mollify (φ n) hloc).sub hc).aestronglyMeasurable ?_ ?_ ?_
  · intro x
    refine (φ n).dist_normed_convolution_le hc.aestronglyMeasurable fun y hy => ?_
    exact (hδc (lt_trans (Metric.mem_ball.mp hy) hn'.1)).le
  · refine (support_convolution_subset _).trans ?_
    rw [(φ n).support_normed_eq]
    exact Set.add_subset_add (Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall hn'.2.le)) (subset_tsupport c)
  · exact (subset_tsupport c).trans fun x hx => ⟨0, Metric.mem_closedBall_self zero_le_one, x,
      hx, zero_add x⟩

/-- Auxiliary to the Lean proof route (in place of the TeX's `L²`
translation continuity): for `u ∈ L²` with values in a complete space,
`ρ_n ⋆ u → u` in `L²` when the bump radii `(φ n).rOut` tend to `0`. -/
theorem tendsto_mollify {u : Rd d → F} (hu : MemLp u 2 volume)
    {φ : ℕ → ContDiffBump (0 : Rd d)} (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => mollify (φ n) u x - u x) 2 volume) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨c, hcs, hcε, hc, hcL⟩ := hu.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num)
    (ENNReal.div_pos hε.ne' (by norm_num : (3 : ℝ≥0∞) ≠ ⊤)).ne'
  have hloc : LocallyIntegrable u volume := hu.locallyIntegrable (by norm_num)
  have hlocc : LocallyIntegrable c volume := hc.locallyIntegrable
  filter_upwards [(ENNReal.tendsto_nhds_zero.mp (tendsto_mollify_of_continuous hc hcs hφ))
    (ε / 3) (ENNReal.div_pos hε.ne' (by norm_num : (3 : ℝ≥0∞) ≠ ⊤))] with n hn
  have hA : eLpNorm (fun x => mollify (φ n) u x - mollify (φ n) c x) 2 volume ≤ ε / 3 := by
    simp_rw [mollify_sub (φ n) hloc hlocc]
    exact (eLpNorm_mollify_le (φ n) (hu.sub hcL)).trans hcε
  have hsplit : (fun x => mollify (φ n) u x - u x) =
      ((fun x => mollify (φ n) u x - mollify (φ n) c x) + fun x => mollify (φ n) c x - c x) +
        fun x => c x - u x := by
    funext x; simp only [Pi.add_apply]; abel
  have hcu : eLpNorm (fun x => c x - u x) 2 volume ≤ ε / 3 := by
    rw [show (fun x => c x - u x) = c - u from rfl, eLpNorm_sub_comm]; exact hcε
  rw [hsplit]
  calc _ ≤ eLpNorm ((fun x => mollify (φ n) u x - mollify (φ n) c x) +
          fun x => mollify (φ n) c x - c x) 2 volume + eLpNorm (fun x => c x - u x) 2 volume :=
        eLpNorm_add_le (by norm_num)
    _ ≤ (eLpNorm (fun x => mollify (φ n) u x - mollify (φ n) c x) 2 volume +
          eLpNorm (fun x => mollify (φ n) c x - c x) 2 volume) +
          eLpNorm (fun x => c x - u x) 2 volume := by
        gcongr; exact eLpNorm_add_le (by norm_num)
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by gcongr
    _ = ε := ENNReal.add_thirds ε

end Mollify

/-- Auxiliary to the Lean proof route: if `g` is a weak gradient of the
locally integrable `f` (with `g` locally integrable), the derivative of
`ρ_φ ⋆ f` in the direction `v` is `⟪ρ_φ ⋆ g, v⟫`: the weak-gradient identity
tested against the test function `y ↦ ρ_φ(x - y)`. -/
theorem fderiv_mollify_apply (φ : ContDiffBump (0 : Rd d)) {f : Rd d → ℝ} {g : Rd d → Rd d}
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume)
    (h : HasWeakGradient f g) (x v : Rd d) :
    fderiv ℝ (mollify φ f) x v = inner ℝ (mollify φ g x) v := by
  set ρ : Rd d → ℝ := φ.normed volume with hρ
  have hρs : HasCompactSupport ρ := φ.hasCompactSupport_normed
  have hρc : ContDiff ℝ ∞ ρ := φ.contDiff_normed
  have hρ1 : ContDiff ℝ 1 ρ := hρc.of_le (by exact_mod_cast le_top)
  have hD : HasFDerivAt (mollify φ f)
      (convolution (fderiv ℝ ρ) f (ContinuousLinearMap.precompL (Rd d)
        (ContinuousLinearMap.lsmul ℝ ℝ)) volume x) x :=
    hρs.hasFDerivAt_convolution_left _ hρ1 hf x
  have hex := (hρs.fderiv ℝ).convolutionExists_left
    (ContinuousLinearMap.precompL (Rd d) (ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)))
    (hρc.continuous_fderiv (by simp)) hf x
  rw [hD.fderiv, convolution_def, ContinuousLinearMap.integral_apply hex v]
  simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [← integral_sub_left_eq_self _ volume x]
  simp only [sub_sub_cancel]
  set ψ : Rd d → ℝ := fun s => ρ (x - s) with hψ
  have hψt : IsTestFunction ψ := by
    refine ⟨hρc.comp (contDiff_const.sub contDiff_id), ?_⟩
    exact hρs.comp_homeomorph (Homeomorph.subLeft x)
  have hψd : ∀ s, fderiv ℝ ψ s v = -(fderiv ℝ ρ (x - s) v) := by
    intro s
    have h1 : HasFDerivAt (fun s => x - s) (-ContinuousLinearMap.id ℝ (Rd d)) s :=
      (hasFDerivAt_id s).const_sub x
    have h2 := ((hρc.differentiable (by simp)) (x - s)).hasFDerivAt.comp s h1
    rw [show ψ = ρ ∘ fun s => x - s from rfl, h2.fderiv]
    simp
  have hw := h ψ hψt v
  simp only [hψd, mul_neg, integral_neg, neg_inj] at hw
  have hexg := (φ.hasCompactSupport_normed.convolutionExists_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (φ.continuous_normed (μ := volume)) hg x).integrable
  have hR : inner ℝ (mollify φ g x) v = ∫ s, inner ℝ (g s) v * ψ s := by
    rw [mollify, convolution_def, real_inner_comm, ← integral_inner hexg v]
    simp only [ContinuousLinearMap.lsmul_apply, real_inner_smul_right]
    rw [← integral_sub_left_eq_self _ volume x]
    simp only [sub_sub_cancel]
    congr 1; funext s; rw [hψ, real_inner_comm, mul_comm]
  have e1 : (∫ s, fderiv ℝ ρ (x - s) v * f s) = ∫ s, f s * fderiv ℝ ρ (x - s) v := by
    congr 1; funext s; ring
  rw [hR, e1, hw]

/-- Auxiliary to the Lean proof route: the classical gradient of a
mollified function is the mollified weak gradient, `∇(ρ_φ ⋆ f) = ρ_φ ⋆ g`,
for locally integrable `f, g` with `HasWeakGradient f g`. -/
theorem grad_mollify (φ : ContDiffBump (0 : Rd d)) {f : Rd d → ℝ} {g : Rd d → Rd d}
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume)
    (h : HasWeakGradient f g) : grad (mollify φ f) = mollify φ g := by
  funext x
  rw [grad, LinearIsometryEquiv.symm_apply_eq]
  ext v
  rw [fderiv_mollify_apply φ hf hg h x v, InnerProductSpace.toDual_apply_apply]

/-- Auxiliary to the Lean proof route: the radii `2/(n+2)` of
`VariationalFloor.bumpN` tend to `0`. -/
theorem tendsto_bumpN_rOut : Tendsto (fun n => (bumpN d n).rOut) atTop (𝓝 0) := by
  show Tendsto (fun n : ℕ => (2 : ℝ) / (n + 2)) atTop (𝓝 0)
  have h := tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)
  refine (h.comp (tendsto_add_atTop_nat 2)).congr' ?_
  filter_upwards with n; simp [Nat.cast_add]

/-! ### Cutoff -/

/-- Auxiliary to the Lean proof route: the cutoff profile `χ`, equal to `1`
on the closed unit ball and `0` outside the open ball of radius `2`. -/
def cutBump (d : ℕ) : ContDiffBump (0 : Rd d) := ⟨1, 2, by norm_num, by norm_num⟩

/-- Auxiliary to the Lean proof route: the cutoff `χ_n(x) = χ(x/(n+1))`
(TeX line 262-263 with `R = n + 1`). -/
def cutoff (n : ℕ) (x : Rd d) : ℝ := cutBump d (((n : ℝ) + 1)⁻¹ • x)

/-- Auxiliary to the Lean proof route: `χ_n` is smooth. -/
theorem cutoff_contDiff (n : ℕ) : ContDiff ℝ ∞ (cutoff (d := d) n) :=
  (cutBump d).contDiff.comp (contDiff_const_smul _)

/-- Auxiliary to the Lean proof route: `χ_n` has compact support. -/
theorem cutoff_hasCompactSupport (n : ℕ) : HasCompactSupport (cutoff (d := d) n) :=
  (cutBump d).hasCompactSupport.comp_smul (inv_ne_zero (by positivity))

/-- Auxiliary to the Lean proof route: `0 ≤ χ_n`. -/
theorem cutoff_nonneg (n : ℕ) (x : Rd d) : 0 ≤ cutoff n x := (cutBump d).nonneg

/-- Auxiliary to the Lean proof route: `χ_n ≤ 1`. -/
theorem cutoff_le_one (n : ℕ) (x : Rd d) : cutoff n x ≤ 1 := (cutBump d).le_one

/-- Auxiliary to the Lean proof route: `χ_n = 1` on the ball of radius
`n + 1`. -/
theorem cutoff_eq_one {n : ℕ} {x : Rd d} (hx : ‖x‖ ≤ (n : ℝ) + 1) : cutoff n x = 1 := by
  refine (cutBump d).one_of_mem_closedBall ?_
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  show ((n : ℝ) + 1)⁻¹ * ‖x‖ ≤ 1
  rw [inv_mul_le_iff₀ (by positivity)]; simpa using hx

/-- Auxiliary to the Lean proof route: `χ_n h` is a test function for
every smooth `h`. -/
theorem cutoff_isTest (n : ℕ) {h : Rd d → ℝ} (hh : ContDiff ℝ ∞ h) :
    IsTestFunction (fun x => cutoff n x * h x) :=
  ⟨(cutoff_contDiff n).mul hh, (cutoff_hasCompactSupport n).mul_right⟩

/-- Auxiliary to the Lean proof route: the classical product rule
`∇(χ_n h) = χ_n ∇h + h ∇χ_n` for smooth `h`. -/
theorem grad_cutoff_mul (n : ℕ) {h : Rd d → ℝ} (hh : ContDiff ℝ ∞ h) (x : Rd d) :
    grad (fun x => cutoff n x * h x) x = cutoff n x • grad h x + h x • grad (cutoff n) x := by
  have h1 : DifferentiableAt ℝ (cutoff (d := d) n) x :=
    ((cutoff_contDiff n).differentiable (by simp)) x
  have h2 : DifferentiableAt ℝ h x := (hh.differentiable (by simp)) x
  simp only [grad]
  rw [fderiv_fun_mul h1 h2, map_add, map_smul, map_smul]

/-- Auxiliary to the Lean proof route: `‖Dχ‖` is bounded. -/
theorem exists_bound_fderiv_cutBump :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Rd d, ‖fderiv ℝ (cutBump d) y‖ ≤ C := by
  obtain ⟨C, hC⟩ := ((cutBump d).hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (((cutBump d).contDiff (n := 1)).continuous_fderiv one_ne_zero)
  exact ⟨max C 0, le_max_right _ _, fun y => (hC y).trans (le_max_left _ _)⟩

/-- Auxiliary to the Lean proof route: `‖∇χ_n‖ ≤ C/(n+1)` when `‖Dχ‖ ≤ C`
(the TeX's gradient bound `C/R`, line 263). -/
theorem norm_grad_cutoff_le {C : ℝ} (hC : ∀ y : Rd d, ‖fderiv ℝ (cutBump d) y‖ ≤ C)
    (n : ℕ) (x : Rd d) : ‖grad (cutoff n) x‖ ≤ C / ((n : ℝ) + 1) := by
  simp only [grad, LinearIsometryEquiv.norm_map]
  rw [show cutoff (d := d) n = fun x => (cutBump d) (((n : ℝ) + 1)⁻¹ • x) from rfl,
    fderiv_comp_smul, norm_smul, norm_inv, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1), div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (hC _) (by positivity)

/-- Auxiliary to the Lean proof route: `χ_n w → w` in `L²` for every
`w ∈ L²` (dominated convergence; the TeX's "function and gradient tails"). -/
theorem tendsto_cutoff_smul {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {w : Rd d → G} (hw : MemLp w 2 volume) :
    Tendsto (fun n => eLpNorm (fun x => cutoff n x • w x - w x) 2 volume) atTop (𝓝 0) := by
  refine tendsto_eLpNorm_two_of_dominated hw (fun n => ?_) (fun n x => ?_) (fun x => ?_)
  · exact (((cutoff_contDiff n).continuous.aestronglyMeasurable).smul
      hw.aestronglyMeasurable).sub hw.aestronglyMeasurable
  · rw [show cutoff n x • w x - w x = (cutoff n x - 1) • w x by rw [sub_smul, one_smul],
      norm_smul, Real.norm_eq_abs,
      abs_of_nonpos (by linarith [cutoff_le_one (d := d) n x])]
    have := cutoff_nonneg n x
    exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)
  · refine tendsto_const_nhds.congr' ?_
    obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [cutoff_eq_one (by linarith [(Nat.cast_le (α := ℝ)).mpr hn]), one_smul, sub_self]

/-- Auxiliary to the Lean proof route: for smooth `h` with `h, ∇h ∈ L²`,
the test functions `χ_n h` converge to `h` and their gradients to `∇h` in
`L²` (the TeX's cutoff step, lines 262-265, applied to a smooth function). -/
theorem tendsto_cutoff_test {h : Rd d → ℝ} (hh : ContDiff ℝ ∞ h) (hL : MemLp h 2 volume)
    (hG : MemLp (grad h) 2 volume) :
    Tendsto (fun n => eLpNorm (fun x => cutoff n x * h x - h x) 2 volume) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (fun x => grad (fun y => cutoff n y * h y) x - grad h x) 2
        volume) atTop (𝓝 0) := by
  refine ⟨by simpa [smul_eq_mul] using tendsto_cutoff_smul hL, ?_⟩
  obtain ⟨C, hC0, hC⟩ := exists_bound_fderiv_cutBump (d := d)
  have hgc : Continuous (grad h) :=
    (InnerProductSpace.toDual ℝ (Rd d)).symm.continuous.comp (hh.continuous_fderiv (by simp))
  have hA := tendsto_cutoff_smul hG
  have hB : Tendsto (fun n : ℕ => ENNReal.ofReal (C / ((n : ℝ) + 1)) * eLpNorm h 2 volume)
      atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => C / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul C
      simp only [mul_zero] at this
      refine this.congr fun n => ?_
      rw [mul_one_div]
    have h1 := ENNReal.tendsto_ofReal h0
    rw [ENNReal.ofReal_zero] at h1
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hL.eLpNorm_lt_top.ne)
  have hsum := hA.add hB
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) (fun n => ?_)
  have hsplit : (fun x => grad (fun y => cutoff n y * h y) x - grad h x) =
      (fun x => cutoff n x • grad h x - grad h x) + fun x => h x • grad (cutoff n) x := by
    funext x; rw [grad_cutoff_mul n hh x, Pi.add_apply]; abel
  rw [hsplit]
  refine (eLpNorm_add_le (by norm_num)).trans (add_le_add le_rfl ?_)
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul ?_ (Eventually.of_forall fun x => ?_) 2
  · exact (hh.continuous.smul (VariationalFloor.continuous_grad
      ⟨cutoff_contDiff n, cutoff_hasCompactSupport n⟩)).aestronglyMeasurable
  · rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right (norm_grad_cutoff_le hC n x) (norm_nonneg _)

/-! ### Density -/

/-- Density in `ε` form: for `f, g ∈ L²` with `g` a weak gradient of `f`
and every `ε > 0` there is a test function `ψ` with `‖ψ - f‖₂ ≤ ε` and
`‖∇ψ - g‖₂ ≤ ε`.  (Lean proof route: mollify, then cut off; see the module
doc comment.) -/
theorem exists_test_approx {f : Rd d → ℝ} {g : Rd d → Rd d} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) (hw : HasWeakGradient f g) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ ψ : Rd d → ℝ, IsTestFunction ψ ∧
      eLpNorm (fun x => ψ x - f x) 2 volume ≤ ε ∧
      eLpNorm (fun x => grad ψ x - g x) 2 volume ≤ ε := by
  have hε2 : 0 < ε / 2 := ENNReal.div_pos hε.ne' (by norm_num)
  have hfl : LocallyIntegrable f volume := hf.locallyIntegrable (by norm_num)
  have hgl : LocallyIntegrable g volume := hg.locallyIntegrable (by norm_num)
  have T1 := ENNReal.tendsto_nhds_zero.mp (tendsto_mollify hf (tendsto_bumpN_rOut (d := d)))
    (ε / 2) hε2
  have T2 := ENNReal.tendsto_nhds_zero.mp (tendsto_mollify hg (tendsto_bumpN_rOut (d := d)))
    (ε / 2) hε2
  obtain ⟨N, hN1, hN2⟩ := (T1.and T2).exists
  set h : Rd d → ℝ := mollify (bumpN d N) f with hhdef
  have hh : ContDiff ℝ ∞ h := contDiff_mollify _ hfl
  have hgrad : grad h = mollify (bumpN d N) g := grad_mollify _ hfl hgl hw
  have hL : MemLp h 2 volume := memLp_mollify _ hf
  have hG : MemLp (grad h) 2 volume := hgrad ▸ memLp_mollify _ hg
  obtain ⟨C1, C2⟩ := tendsto_cutoff_test hh hL hG
  obtain ⟨n, hn1, hn2⟩ :=
    ((ENNReal.tendsto_nhds_zero.mp C1 (ε / 2) hε2).and
      (ENNReal.tendsto_nhds_zero.mp C2 (ε / 2) hε2)).exists
  refine ⟨fun x => cutoff n x * h x, cutoff_isTest n hh, ?_, ?_⟩
  · have hs : (fun x => cutoff n x * h x - f x) =
        (fun x => cutoff n x * h x - h x) + fun x => h x - f x := by
      funext x; simp only [Pi.add_apply]; ring
    rw [hs]
    calc _ ≤ _ := eLpNorm_add_le (by norm_num)
      _ ≤ ε / 2 + ε / 2 := add_le_add hn1 hN1
      _ = ε := ENNReal.add_halves ε
  · have hs : (fun x => grad (fun y => cutoff n y * h y) x - g x) =
        (fun x => grad (fun y => cutoff n y * h y) x - grad h x) + fun x => grad h x - g x := by
      funext x; simp only [Pi.add_apply]; abel
    rw [hs]
    calc _ ≤ _ := eLpNorm_add_le (by norm_num)
      _ ≤ ε / 2 + ε / 2 := by
        refine add_le_add hn2 ?_
        rw [hgrad]; exact hN2
      _ = ε := ENNReal.add_halves ε

/-- **Density of `C_c^∞` in the weak-gradient `H^1`** (half (a) of the
D8-lite foundation; `notes/integrated_spatial_occupation.tex`, proof of
`P:spatial-four-linear`, lines 262-266 at a284420), for every dimension `d`.
Lean proof route: mollification first (with an `L²` contraction and density
of `C_c` in `L²` in place of the TeX's translation continuity), then the
TeX's cutoff estimate; see the module doc comment. -/
theorem h1TestDense (d : ℕ) : H1TestDense d := by
  intro f g hf hg hw
  have hpos : ∀ k : ℕ, 0 < ENNReal.ofReal (1 / ((k : ℝ) + 1)) := fun k =>
    ENNReal.ofReal_pos.mpr (by positivity)
  choose φ hφt hφ1 hφ2 using fun k : ℕ => exists_test_approx hf hg hw (hpos k)
  have hT : Tendsto (fun k : ℕ => ENNReal.ofReal (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
  exact ⟨φ, hφt,
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT (fun _ => zero_le) hφ1,
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT (fun _ => zero_le) hφ2⟩

/-- The `MemH1` form of the density: every `f ∈ H^1(ℝ^d; ℝ)` has an `L²`
weak gradient `g` and test functions `φ_n` with `φ_n → f` and `∇φ_n → g` in
`L²`. -/
theorem h1TestDense_of_memH1 {f : Rd d → ℝ} (hf : MemH1 f) :
    ∃ g : Rd d → Rd d, MemLp g 2 volume ∧ HasWeakGradient f g ∧
      ∃ φ : ℕ → Rd d → ℝ, (∀ n, IsTestFunction (φ n)) ∧
        Tendsto (fun n => eLpNorm (fun x => φ n x - f x) 2 volume) atTop (𝓝 0) ∧
        Tendsto (fun n => eLpNorm (fun x => grad (φ n) x - g x) 2 volume) atTop (𝓝 0) := by
  obtain ⟨hfL, g, hg, hw⟩ := hf
  exact ⟨g, hg, hw, h1TestDense d f g hfL hg hw⟩

/-! ### The converse: limits of test functions -/

/-- Auxiliary to the Lean proof route of `hasWeakGradient_of_tendsto`: if
`u n → u₀` in `L²` (all in `L²`) and `w ∈ L²`, then `∫ u n w → ∫ u₀ w`
(Hölder with exponents `2, 2, 1`). -/
theorem tendsto_integral_mul_of_L2 {u : ℕ → Rd d → ℝ} {u0 w : Rd d → ℝ}
    (hu : ∀ n, MemLp (u n) 2 volume) (hu0 : MemLp u0 2 volume) (hw : MemLp w 2 volume)
    (hT : Tendsto (fun n => eLpNorm (fun x => u n x - u0 x) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, u n x * w x) atTop (𝓝 (∫ x, u0 x * w x)) := by
  refine tendsto_integral_of_L1 (fun x => u0 x * w x)
    (hu0.aestronglyMeasurable.mul hw.aestronglyMeasurable)
    (Eventually.of_forall fun n => (hu n).integrable_mul hw) ?_
  have hB : Tendsto (fun n => eLpNorm (fun x => u n x - u0 x) 2 volume * eLpNorm w 2 volume)
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const hT (Or.inr hw.eLpNorm_lt_top.ne)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hB
    (fun _ => zero_le) (fun n => ?_)
  have hm : AEStronglyMeasurable (fun x => u n x - u0 x) volume :=
    (hu n).aestronglyMeasurable.sub hu0.aestronglyMeasurable
  have e : (fun x => ‖u n x * w x - u0 x * w x‖ₑ) =
      fun x => ‖((fun x => u n x - u0 x) • w) x‖ₑ := by
    funext x
    show ‖u n x * w x - u0 x * w x‖ₑ = ‖(u n x - u0 x) * w x‖ₑ
    rw [sub_mul]
  calc ∫⁻ x, ‖u n x * w x - u0 x * w x‖ₑ
      = eLpNorm ((fun x => u n x - u0 x) • w) 1 volume := by
        rw [e, eLpNorm_one_eq_lintegral_enorm (hm.smul hw.aestronglyMeasurable)]
    _ ≤ _ := eLpNorm_smul_le_mul_eLpNorm hm hw.aestronglyMeasurable

/-- The converse of the density (closedness of the weak gradient under
`L²` limits of test functions): if test functions `φ n` satisfy `φ n → f` and
`∇φ n → g` in `L²`, with `f, g ∈ L²`, then `g` is a weak gradient of `f`.
Together with `h1TestDense` this identifies the weak-gradient `H^1` with the
closure of `C_c^∞` under the norm `‖f‖₂ + ‖∇f‖₂`. -/
theorem hasWeakGradient_of_tendsto {f : Rd d → ℝ} {g : Rd d → Rd d}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) {φ : ℕ → Rd d → ℝ}
    (hφ : ∀ n, IsTestFunction (φ n))
    (h1 : Tendsto (fun n => eLpNorm (fun x => φ n x - f x) 2 volume) atTop (𝓝 0))
    (h2 : Tendsto (fun n => eLpNorm (fun x => grad (φ n) x - g x) 2 volume) atTop (𝓝 0)) :
    HasWeakGradient f g := by
  intro ψ hψ v
  have hinner : ∀ G : Rd d → Rd d, MemLp G 2 volume →
      MemLp (fun x => inner ℝ (G x) v) 2 volume := by
    intro G hG
    refine ((innerSL ℝ v).comp_memLp' hG).congr_norm hG.aestronglyMeasurable.inner_const
      (Eventually.of_forall fun x => ?_)
    simp [real_inner_comm]
  have hwv : MemLp (fun x => fderiv ℝ ψ x v) 2 volume := by
    refine ((hψ.1.continuous_fderiv (by simp)).clm_apply
      continuous_const).memLp_of_hasCompactSupport ?_
    exact (hψ.2.fderiv ℝ).comp_left (g := fun L : Rd d →L[ℝ] ℝ => L v) (by simp)
  have A := tendsto_integral_mul_of_L2 (fun n => VariationalFloor.memLp_test (hφ n)) hf hwv h1
  have hB : Tendsto (fun n => eLpNorm (fun x => inner ℝ (grad (φ n) x) v - inner ℝ (g x) v) 2
      volume) atTop (𝓝 0) := by
    have hM : Tendsto (fun n => ENNReal.ofReal ‖v‖ *
        eLpNorm (fun x => grad (φ n) x - g x) 2 volume) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul h2 (Or.inr (ENNReal.ofReal_ne_top (r := ‖v‖)))
      rwa [mul_zero] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hM
      (fun _ => zero_le) (fun n => ?_)
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul ?_ (Eventually.of_forall fun x => ?_) 2
    · exact ((hinner _ (VariationalFloor.memLp_grad (hφ n))).sub
        (hinner _ hg)).aestronglyMeasurable
    · rw [← inner_sub_left, mul_comm]
      exact (Real.norm_eq_abs _).trans_le (abs_real_inner_le_norm _ _)
  have B := tendsto_integral_mul_of_L2
    (fun n => hinner _ (VariationalFloor.memLp_grad (hφ n)))
    (hinner _ hg) (VariationalFloor.memLp_test hψ) hB
  have A' : Tendsto (fun n => ∫ x, φ n x * fderiv ℝ ψ x v) atTop
      (𝓝 (-∫ x, inner ℝ (g x) v * ψ x)) := by
    refine B.neg.congr fun n => ?_
    exact (VariationalFloor.hasWeakGradient_of_test (hφ n) ψ hψ v).symm
  exact tendsto_nhds_unique A A'

end StratonovichHAMSecondMoment.H1Density
