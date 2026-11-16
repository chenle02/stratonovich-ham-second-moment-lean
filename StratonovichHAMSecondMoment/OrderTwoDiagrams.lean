module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Order-two closed forms of the two-chain diagram integrals in `d = 1` (wave
L13 item D4).  Main TeX file `notes/notes_stratonovich_ham_second_moment.tex` at
revision 39f2597a:
* `L:white-test` (statement lines 940-949, proof 951-964): for `d = α = 1`,
  `γ = δ₀`, `c_0 = ((1-α₀)(2-α₀)(3-α₀))^{-1}`, `E X_1² = c_0 t^{3-α₀}`,
  `E X_2 = c_0 t^{3-α₀}/2`, and the total-order-two contribution to
  `E:full-second` is `2 c_0 t^{3-α₀}`;
* `P:riesz-small` (statement lines 5125-5172, proof 5174-5220): for `d = 1`,
  `γ(y) = c|y|^{-α}`, the two displays of `E:riesz-two` (lines 5129-5141), "their
  total is `E X_1² + 2 E X_2`" (line 5142), and the order-four representation
  `E:riesz-four` with its finiteness (lines 5144-5171, proof 5199-5219).

The objects are those of `DiagramModel` (not edited here): `diagram G γ α₀ m n D t`
is `J_{m,n,D}(t)` of `E:mixed-diagram` for a covariance density, `diagramLim` the
TeX's `J` for a covariance measure (the limit of the diagrams with `p_ε * Γ` as
`ε ↓ 0`), `coeffA`, `coeffALim` the total-order coefficients `A_k(t)`.

Formalized (all proved; the only supplied inputs are named below):
* the diagram values, whole on the model.  White noise (`Γ = δ₀`,
  `diagramLim`, `α₀ < 1`, `t ≥ 0`): `white_cross` (`J_{1,1,D} = c_0 t^{3-α₀}`),
  `white_self_two_zero`, `white_self_zero_two` (`J_{2,0,D} = J_{0,2,D} =
  c_0 t^{3-α₀}/2`), `white_coeffALim_one` (`A_1 = 2 c_0 t^{3-α₀}`).  Riesz
  density (`diagram` with `γ = riesz c α`, `c ≥ 0`, `α < 1`, `α₀ < 1`, `t ≥ 0`):
  `riesz_self_two_zero`, `riesz_self_zero_two` (the first display of
  `E:riesz-two`), `riesz_cross` (the second display, with the bracket `rbr`),
  `riesz_coeffA_one` (`A_1 = J_{1,1} + 2 J_{2,0}`);
* the steps of the TeX proofs: the spatial parts `spatial_riesz_self`
  (`c r v^{1-α}/(1-α)`), `spatial_riesz_cross` (the kernel `rK`), the collapsed
  white spatial parts `whiteSpatial_self` (`G_r` has mass `r`, `G_{s-r}(0) = 1/2`)
  and `whiteSpatial_cross` (`∫ G_s G_r = min(s,r)/2`), and the time integrals
  (`time_white_self`, `time_white_cross`, `time_riesz_self`, `time_riesz_cross`:
  "integrate on `s > r` and double, set `v = s - r`, and integrate `r` over
  `(0, t - v)`");
* the lemmas as stated about the chaos terms: `white_test_paper` and
  `riesz_small_paper` (wrappers with the TeX's hypotheses), through the supplied
  input `MixedMoment`.

Supplied inputs (named):
* `DiagramModel.MixedMoment` (`P:mixed`), in both wrappers: the identification
  `E[X_m X_n] = Σ_D J_{m,n,D}(t)`.  TRUE (`P:mixed`); not proved (blocker D5).
* `RieszDiagramLimit` (this module), in `riesz_small_paper` only: at total
  order two, the model's `diagramLim` for `Γ(dy) = c|y|^{-α} dy` equals the
  literal diagram with the density.  TRUE (see its doc comment); not proved in
  this module, but proved in `RieszFourDiagrams.rieszDiagramLimit` (for `c ≥ 0`,
  `0 ≤ α < 1`, `0 ≤ α₀ < 1`, `t ≥ 0`), whose `riesz_small_paper'` is the successor
  of `riesz_small_paper` without this input.
  The white-noise limits `ε ↓ 0` have no corresponding input: they are
  `WhiteCollapse.tendsto_diagram_white` (wave L13 item D6, every `m, n, D`), which
  `tendsto_white_self` and `tendsto_white_cross` specialize to two labels (L13
  integration: this module's own order-two smoothing argument was removed in
  favour of D6's general one; the headline statements are unchanged).

Hypotheses: the diagram values need only `α₀ < 1`, `α < 1`, `c ≥ 0`, `t ≥ 0`
(broader than the TeX's `0 < α₀`, `0 < α`, `c > 0`; `α₀ = 0` is the static case
the TeX also uses at line 5121).  The wrappers carry the TeX's hypotheses;
`white_test_paper` uses `H:homog` only for `α₀ < 1`; `riesz_small_paper` carries
`H:homog`, `0 < α`, `0 < α₀` unused and uses `c > 0` only as `c ≥ 0`.  `X_0 = 1`
is the TeX's convention (line 796), stated as a hypothesis.

Not formalized, category per label:
* `L:white-test`: narrower.  Every conclusion is proved for the diagrams
  (whole on the model); the identification with `E X_1²`, `E X_2` is the supplied
  input `MixedMoment` about unconstructed `X` (split modelled-object rule).
* `P:riesz-small`: narrower.  Missing here: the order-four representation
  `E:riesz-four` and its finiteness; the order-two identification with the chaos
  terms rests on `MixedMoment` and `RieszDiagramLimit`.  The follow-up module
  `RieszFourDiagrams` proves `RieszDiagramLimit`, `E:riesz-four` and its finiteness
  (on the density diagrams) and gives the updated class.
The `a ↑ 1` limit `2^{2-α}(1-α)` (`P:nogo-04`, which exists only after the
re-anchor) is not formalized here.

Readings: pairs are oriented as in `DiagramModel` (`γ(y_j - y_h)` at the opener
`j < h`; `γ` is even here); the time domain is the model's open simplices; the
Riesz density at `0` is Lean's `0^{-α} = 0` (a null point).

Lemmas marked "Auxiliary" serve only the Lean route.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.DiagramModel
public import StratonovichHAMSecondMoment.DiagramBridge
public import StratonovichHAMSecondMoment.WhiteCollapse
public import StratonovichHAMSecondMoment.HigherRieszTwo

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace StratonovichHAMSecondMoment.OrderTwoDiagrams

open HomogHypothesis (Rd)
open WaveGreen (waveGreen)
open VariationalMean (heatK heatK_pos)
open HigherRieszTwo (riesz lintegral_heatK integral_heatK tendsto_heat_conv)
open DiagramModel
open DiagramBridge (e1 measurePreserving_e1 e1_sub)

/-! ### One-dimensional integrals -/

/-- Auxiliary: a nonnegative interval-integrable function has lower integral
over `(a, b)` equal to `ofReal` of its interval integral. -/
theorem lintegral_Ioo_ofReal {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) (h0 : ∀ x ∈ Ioo a b, 0 ≤ f x) :
    ∫⁻ x in Ioo a b, ENNReal.ofReal (f x) = ENNReal.ofReal (∫ x in a..b, f x) := by
  rw [intervalIntegral.integral_of_le hab, setIntegral_congr_set Ioo_ae_eq_Ioc.symm]
  rw [ofReal_integral_eq_lintegral_ofReal]
  · exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hf).mono_set Ioo_subset_Ioc_self
  · exact (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall h0)

/-- Auxiliary: `∫_0^s (s - x)^q x dx = s^{q+2}/((q+1)(q+2))` for `q > -1`, `s ≥ 0`
(the Beta integral `B(q+1, 2) s^{q+2}`). -/
theorem integral_sub_rpow_mul {q s : ℝ} (hq : -1 < q) (hs : 0 ≤ s) :
    ∫ x in (0 : ℝ)..s, (s - x) ^ q * x = s ^ (q + 2) / ((q + 1) * (q + 2)) := by
  have h1 : q + 1 ≠ 0 := by linarith
  have h2 : q + 2 ≠ 0 := by linarith
  have e : ∫ x in (0 : ℝ)..s, (s - x) ^ q * x = ∫ u in (0 : ℝ)..s, u ^ q * (s - u) := by
    have := intervalIntegral.integral_comp_sub_left (fun u : ℝ => u ^ q * (s - u)) s
      (a := 0) (b := s)
    simp only [sub_sub_cancel, sub_self, sub_zero] at this
    exact this
  rw [e]
  have e2 : ∀ u ∈ uIcc (0 : ℝ) s, u ^ q * (s - u) = s * u ^ q - u ^ (q + 1) := by
    intro u hu
    rw [uIcc_of_le hs] at hu
    rw [Real.rpow_add' hu.1 h1, Real.rpow_one]
    ring
  rw [intervalIntegral.integral_congr e2, intervalIntegral.integral_sub
    ((intervalIntegral.intervalIntegrable_rpow' hq).const_mul s)
    (intervalIntegral.intervalIntegrable_rpow' (by linarith)),
    intervalIntegral.integral_const_mul, integral_rpow (Or.inl hq),
    integral_rpow (Or.inl (by linarith))]
  rw [Real.zero_rpow h1, Real.zero_rpow (by linarith : q + 1 + 1 ≠ 0)]
  have e3 : s * s ^ (q + 1) = s ^ (q + 2) := by
    rw [show q + 2 = (q + 1) + 1 by ring, Real.rpow_add' (y := q + 1) (z := 1) hs (by linarith),
      Real.rpow_one, mul_comm]
  rw [show q + 1 + 1 = q + 2 by ring]
  field_simp
  rw [← e3]
  ring

/-- Auxiliary: `∫_0^a x^p dx = a^{p+1}/(p+1)` for `p > -1`, as a lower integral. -/
theorem lintegral_rpow_Ioo {p a : ℝ} (hp : -1 < p) (ha : 0 ≤ a) :
    ∫⁻ x in Ioo 0 a, ENNReal.ofReal (x ^ p) = ENNReal.ofReal (a ^ (p + 1) / (p + 1)) := by
  rw [lintegral_Ioo_ofReal ha (intervalIntegral.intervalIntegrable_rpow' hp)
    (fun x hx => Real.rpow_nonneg hx.1.le _), integral_rpow (Or.inl hp),
    Real.zero_rpow (by linarith), sub_zero]

/-! ### The odd primitive `Φ` and the even primitive `Ψ` of `|x|^{-α}` -/

/-- Auxiliary: `Φ(x) = x|x|^{-α}/(1-α)`, the odd primitive of `|x|^{-α}`
(`= sign(x)|x|^{1-α}/(1-α)`). -/
def rPhi (α x : ℝ) : ℝ := x * |x| ^ (-α) / (1 - α)

/-- Auxiliary: `Ψ(x) = |x|^{2-α}/((1-α)(2-α))`, the even primitive of `Φ`. -/
def rPsi (α x : ℝ) : ℝ := |x| ^ (2 - α) / ((1 - α) * (2 - α))

/-- Auxiliary: `|Φ(x)| = |x|^{1-α}/(1-α)`. -/
theorem abs_rPhi {α : ℝ} (hα : α < 1) (x : ℝ) : |rPhi α x| = |x| ^ (1 - α) / (1 - α) := by
  unfold rPhi
  rw [abs_div, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 - α),
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) _)]
  rcases eq_or_ne x 0 with rfl | hx
  · simp [Real.zero_rpow (by linarith : (1 : ℝ) - α ≠ 0)]
  · congr 1
    rw [show (1 : ℝ) - α = 1 + -α by ring, Real.rpow_add (abs_pos.2 hx), Real.rpow_one]

/-- Auxiliary: `Φ` is continuous. -/
theorem continuous_rPhi {α : ℝ} (hα : α < 1) : Continuous (rPhi α) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · have h0 : rPhi α 0 = 0 := by simp [rPhi]
    rw [ContinuousAt, h0, tendsto_zero_iff_norm_tendsto_zero]
    simp only [Real.norm_eq_abs, abs_rPhi hα]
    have hc : Continuous fun y : ℝ => |y| ^ (1 - α) / (1 - α) :=
      ((Real.continuous_rpow_const (by linarith)).comp continuous_abs).div_const _
    have := hc.tendsto 0
    simpa [Real.zero_rpow (by linarith : (1 : ℝ) - α ≠ 0)] using this
  · unfold rPhi
    exact ((continuousAt_id.mul ((continuous_abs.continuousAt).rpow_const
      (Or.inl (abs_ne_zero.2 hx)))).div_const _)

/-- Auxiliary: `Ψ' = Φ` everywhere (`2 - α > 1`). -/
theorem hasDerivAt_rPsi {α : ℝ} (hα : α < 1) (x : ℝ) : HasDerivAt (rPsi α) (rPhi α x) x := by
  have h := (hasDerivAt_abs_rpow x (p := 2 - α) (by linarith)).div_const ((1 - α) * (2 - α))
  have e : rPsi α = fun x => |x| ^ (2 - α) / ((1 - α) * (2 - α)) := rfl
  rw [e]
  refine h.congr_deriv ?_
  unfold rPhi
  rw [show (2 - α - 2) = -α by ring]
  have h1 : (1 - α) ≠ 0 := by linarith
  have h2 : (2 - α) ≠ 0 := by linarith
  field_simp

/-- Auxiliary: `Φ' = |x|^{-α}` away from `0`. -/
theorem hasDerivAt_rPhi {α : ℝ} (hα : α < 1) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (rPhi α) (|x| ^ (-α)) x := by
  have h1 : (1 - α) ≠ 0 := by linarith
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have hd := ((Real.hasDerivAt_rpow_const (p := 1 - α) (Or.inl (by linarith : -x ≠ 0))).comp x
      (hasDerivAt_neg x)).neg.div_const (1 - α)
    have heq : (fun y : ℝ => -((fun z => z ^ (1 - α)) ∘ (fun y => -y)) y / (1 - α)) =ᶠ[𝓝 x]
        rPhi α := by
      filter_upwards [Iio_mem_nhds hneg] with y hy
      simp only [Function.comp_apply, rPhi]
      rw [abs_of_neg hy, show (1 : ℝ) - α = 1 + -α by ring,
        Real.rpow_add (neg_pos.2 (Set.mem_Iio.1 hy)),
        Real.rpow_one]
      ring
    refine (hd.congr_of_eventuallyEq heq.symm).congr_deriv ?_
    rw [abs_of_neg hneg, show (1 : ℝ) - α - 1 = -α by ring]
    field_simp
  · have hd := (Real.hasDerivAt_rpow_const (p := 1 - α) (Or.inl hx)).div_const (1 - α)
    have heq : (fun y : ℝ => y ^ (1 - α) / (1 - α)) =ᶠ[𝓝 x] rPhi α := by
      filter_upwards [Ioi_mem_nhds hpos] with y hy
      simp only [rPhi]
      rw [abs_of_pos hy, show (1 : ℝ) - α = 1 + -α by ring, Real.rpow_add hy, Real.rpow_one]
    refine (hd.congr_of_eventuallyEq heq.symm).congr_deriv ?_
    rw [abs_of_pos hpos, show (1 : ℝ) - α - 1 = -α by ring]
    field_simp

/-- Auxiliary: `|x|^{-α}` is interval integrable on every interval (`α < 1`). -/
theorem intervalIntegrable_abs_rpow {α : ℝ} (hα : α < 1) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => |x| ^ (-α)) volume a b := by
  have hpos : ∀ c : ℝ, 0 ≤ c → IntervalIntegrable (fun x : ℝ => |x| ^ (-α)) volume 0 c := by
    intro c hc
    have h := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := c) (r := -α) (by linarith)
    rw [intervalIntegrable_iff, uIoc_of_le hc] at h ⊢
    refine h.congr_fun (fun x hx => ?_) measurableSet_Ioc
    simp only [abs_of_pos hx.1]
  have hall : ∀ c : ℝ, IntervalIntegrable (fun x : ℝ => |x| ^ (-α)) volume 0 c := by
    intro c
    rcases le_total 0 c with hc | hc
    · exact hpos c hc
    · rw [IntervalIntegrable.iff_comp_neg, neg_zero]
      simpa only [abs_neg] using hpos (-c) (by linarith)
  exact (hall a).symm.trans (hall b)

/-- Auxiliary: `∫_a^b |x|^{-α} dx = Φ(b) - Φ(a)` for all `a, b` (`α < 1`). -/
theorem integral_abs_rpow {α : ℝ} (hα : α < 1) (a b : ℝ) :
    ∫ x in a..b, |x| ^ (-α) = rPhi α b - rPhi α a :=
  integral_eq_of_hasDerivAt_off_countable (rPhi α) (fun x => |x| ^ (-α))
    (Set.countable_singleton 0) (continuous_rPhi hα).continuousOn
    (fun _ hx => hasDerivAt_rPhi hα hx.2) (intervalIntegrable_abs_rpow hα a b)

/-- Auxiliary: `∫_a^b Φ = Ψ(b) - Ψ(a)`. -/
theorem integral_rPhi {α : ℝ} (hα : α < 1) (a b : ℝ) :
    ∫ x in a..b, rPhi α x = rPsi α b - rPsi α a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_rPsi hα x)
    ((continuous_rPhi hα).intervalIntegrable a b)

/-- Auxiliary: `Ψ` is even. -/
theorem rPsi_neg (α x : ℝ) : rPsi α (-x) = rPsi α x := by simp [rPsi]

/-! ### Lebesgue integrals over intervals and triangles -/

/-- Auxiliary: splitting `(0, t)` at an interior point (the point itself is null). -/
theorem setLIntegral_Ioo_split {x t : ℝ} (hx : x ∈ Ioo 0 t) (f : ℝ → ℝ≥0∞) :
    ∫⁻ y in Ioo 0 t, f y = (∫⁻ y in Ioo 0 x, f y) + ∫⁻ y in Ioo x t, f y := by
  rw [← Set.Ioo_union_Ico_eq_Ioo hx.1 hx.2.le, lintegral_union measurableSet_Ico
    (Set.disjoint_left.2 fun y h1 h2 => lt_irrefl _ (h1.2.trans_le h2.1)),
    setLIntegral_congr Ioo_ae_eq_Ico.symm]

/-- Auxiliary: reflection `y ↦ x - y` of `(0, x)`. -/
theorem setLIntegral_Ioo_reflect (x : ℝ) (φ : ℝ → ℝ≥0∞) :
    ∫⁻ y in Ioo 0 x, φ (x - y) = ∫⁻ v in Ioo 0 x, φ v := by
  rw [← lintegral_indicator measurableSet_Ioo, ← lintegral_indicator measurableSet_Ioo,
    ← lintegral_sub_left_eq_self ((Ioo 0 x).indicator φ) x]
  refine lintegral_congr fun y => ?_
  by_cases h : y ∈ Ioo 0 x
  · have h' : x - y ∈ Ioo 0 x := ⟨by linarith [h.2], by linarith [h.1]⟩
    rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
  · have h' : x - y ∉ Ioo 0 x := fun h' => h ⟨by linarith [h'.2], by linarith [h'.1]⟩
    rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']

/-- Auxiliary: translation `x = r + v` of `(v, t)` to `(0, t - v)`. -/
theorem setLIntegral_Ioo_translate (v t : ℝ) (φ : ℝ → ℝ≥0∞) :
    ∫⁻ x in Ioo v t, φ x = ∫⁻ r in Ioo 0 (t - v), φ (r + v) := by
  rw [← lintegral_indicator measurableSet_Ioo, ← lintegral_indicator measurableSet_Ioo,
    ← lintegral_add_right_eq_self ((Ioo v t).indicator φ) v]
  refine lintegral_congr fun r => ?_
  by_cases h : r ∈ Ioo 0 (t - v)
  · have h' : r + v ∈ Ioo v t := ⟨by linarith [h.1], by linarith [h.2]⟩
    rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
  · have h' : r + v ∉ Ioo v t := fun h' => h ⟨by linarith [h'.1], by linarith [h'.2]⟩
    rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']

/-- Auxiliary: a nested set integral as an iterated integral of an indicator. -/
theorem lintegral_nested {A : Set ℝ} (hA : MeasurableSet A) {B : ℝ → Set ℝ}
    (hB : ∀ x, MeasurableSet (B x)) (f : ℝ → ℝ → ℝ≥0∞) :
    ∫⁻ x in A, ∫⁻ y in B x, f x y =
      ∫⁻ x, ∫⁻ y, {p : ℝ × ℝ | p.1 ∈ A ∧ p.2 ∈ B p.1}.indicator (fun p => f p.1 p.2) (x, y) := by
  rw [← lintegral_indicator hA]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ A
  · rw [Set.indicator_of_mem hx, ← lintegral_indicator (hB x)]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ B x
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (show (x, y) ∈
        {p : ℝ × ℝ | p.1 ∈ A ∧ p.2 ∈ B p.1} from ⟨hx, hy⟩)]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (show (x, y) ∉
        {p : ℝ × ℝ | p.1 ∈ A ∧ p.2 ∈ B p.1} from fun h => hy h.2)]
  · rw [Set.indicator_of_notMem hx]
    symm
    refine lintegral_eq_zero_of_ae_eq_zero (Eventually.of_forall fun y => ?_)
    exact Set.indicator_of_notMem (show (x, y) ∉
      {p : ℝ × ℝ | p.1 ∈ A ∧ p.2 ∈ B p.1} from fun h => hx h.1) _

/-- Auxiliary: the triangle `{0 < x < y < t}`. -/
def tri (t : ℝ) : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < t}

/-- Auxiliary: the triangle is measurable. -/
theorem measurableSet_tri (t : ℝ) : MeasurableSet (tri t) :=
  (measurableSet_lt measurable_const measurable_fst).inter
    ((measurableSet_lt measurable_fst measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_const))

/-- Auxiliary: the triangle with the larger variable outside. -/
theorem lintegral_tri_outer {t : ℝ} {f : ℝ → ℝ → ℝ≥0∞}
    (hf : Measurable fun p : ℝ × ℝ => f p.1 p.2) :
    ∫⁻ y in Ioo 0 t, ∫⁻ x in Ioo 0 y, f x y =
      ∫⁻ x, ∫⁻ y, (tri t).indicator (fun p => f p.1 p.2) (x, y) := by
  rw [lintegral_nested measurableSet_Ioo (fun _ => measurableSet_Ioo)]
  have hm : Measurable fun p : ℝ × ℝ => (tri t).indicator (fun p => f p.1 p.2) (p.2, p.1) :=
    (hf.indicator (measurableSet_tri t)).comp measurable_swap
  rw [lintegral_lintegral_swap (f := fun y x =>
    {p : ℝ × ℝ | p.1 ∈ Ioo 0 t ∧ p.2 ∈ Ioo 0 p.1}.indicator
    (fun p => f p.2 p.1) (y, x))]
  · refine lintegral_congr fun x => lintegral_congr fun y => ?_
    by_cases h : (x, y) ∈ tri t
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show (y, x) ∈
        {p : ℝ × ℝ | p.1 ∈ Ioo 0 t ∧ p.2 ∈ Ioo 0 p.1} from
          ⟨⟨by linarith [h.1, h.2.1], h.2.2⟩, h.1, h.2.1⟩)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show (y, x) ∉
        {p : ℝ × ℝ | p.1 ∈ Ioo 0 t ∧ p.2 ∈ Ioo 0 p.1} from
          fun h' => h ⟨h'.2.1, h'.2.2, h'.1.2⟩)]
  · refine Measurable.aemeasurable ?_
    exact (hf.comp measurable_swap).indicator
      ((measurableSet_lt measurable_const measurable_fst).inter
        (measurableSet_lt measurable_fst measurable_const) |>.inter
        ((measurableSet_lt measurable_const measurable_snd).inter
          (measurableSet_lt measurable_snd measurable_fst)))

/-- Auxiliary: exchanging the order of integration over the triangle. -/
theorem lintegral_tri_swap {t : ℝ} {f : ℝ → ℝ → ℝ≥0∞}
    (hf : Measurable fun p : ℝ × ℝ => f p.1 p.2) :
    ∫⁻ x in Ioo 0 t, ∫⁻ y in Ioo x t, f x y = ∫⁻ y in Ioo 0 t, ∫⁻ x in Ioo 0 y, f x y := by
  rw [lintegral_tri_outer hf, lintegral_nested measurableSet_Ioo (fun _ => measurableSet_Ioo)]
  refine lintegral_congr fun x => lintegral_congr fun y => ?_
  have : {p : ℝ × ℝ | p.1 ∈ Ioo 0 t ∧ p.2 ∈ Ioo p.1 t} = tri t := by
    ext p
    simp only [Set.mem_ofPred_eq, mem_Ioo, tri]
    constructor
    · rintro ⟨⟨h1, _⟩, h3, h4⟩; exact ⟨h1, h3, h4⟩
    · rintro ⟨h1, h3, h4⟩; exact ⟨⟨h1, h3.trans h4⟩, h3, h4⟩
  rw [this]

/-- Auxiliary: on the square `(0, t)^2` a symmetric integrand integrates to twice
its integral over the half `y < x` (the diagonal is null). -/
theorem lintegral_square_symm {t : ℝ} {f : ℝ → ℝ → ℝ≥0∞}
    (hf : Measurable fun p : ℝ × ℝ => f p.1 p.2) (hsym : ∀ x y, f x y = f y x) :
    ∫⁻ x in Ioo 0 t, ∫⁻ y in Ioo 0 t, f x y = 2 * ∫⁻ x in Ioo 0 t, ∫⁻ y in Ioo 0 x, f x y := by
  rw [setLIntegral_congr_fun measurableSet_Ioo (fun x hx => setLIntegral_Ioo_split hx (f x))]
  have hm : Measurable fun x => ∫⁻ y in Ioo 0 x, f x y := by
    have : (fun x => ∫⁻ y in Ioo 0 x, f x y) = fun x => ∫⁻ y,
        {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1}.indicator (fun p => f p.1 p.2) (x, y) := by
      funext x
      rw [← lintegral_indicator measurableSet_Ioo]
      refine lintegral_congr fun y => ?_
      by_cases h : y ∈ Ioo 0 x
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show (x, y) ∈
          {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1} from h)]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show (x, y) ∉
          {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1} from h)]
    rw [this]
    exact (hf.indicator ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_fst))).lintegral_prod_right'
  rw [show (∫⁻ x in Ioo 0 t, ((∫⁻ y in Ioo 0 x, f x y) + ∫⁻ y in Ioo x t, f x y)) =
      (∫⁻ x in Ioo 0 t, ∫⁻ y in Ioo 0 x, f x y) + ∫⁻ x in Ioo 0 t, ∫⁻ y in Ioo x t, f x y from
    lintegral_add_left hm _, lintegral_tri_swap hf, two_mul]
  congr 1
  refine setLIntegral_congr_fun measurableSet_Ioo fun y _ => ?_
  exact setLIntegral_congr_fun measurableSet_Ioo fun x _ => hsym x y

/-- Auxiliary: integrals over a set of times `s : Fin 2 → ℝ` given by the pair
`(s 0, s 1)` as iterated integrals in the plane. -/
theorem setLIntegral_fin_two {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) {g : ℝ × ℝ → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ s in {s : Fin 2 → ℝ | (s 0, s 1) ∈ S}, g (s 0, s 1) =
      ∫⁻ x, ∫⁻ y, S.indicator g (x, y) := by
  have hT : MeasurableSet {s : Fin 2 → ℝ | (s 0, s 1) ∈ S} :=
    hS.preimage ((measurable_pi_apply 0).prodMk (measurable_pi_apply 1))
  rw [← lintegral_indicator hT]
  have e : ∀ s : Fin 2 → ℝ, {s : Fin 2 → ℝ | (s 0, s 1) ∈ S}.indicator
      (fun s => g (s 0, s 1)) s = S.indicator g (s 0, s 1) := fun s => by
    by_cases h : (s 0, s 1) ∈ S
    · rw [Set.indicator_of_mem (show s ∈ {s : Fin 2 → ℝ | (s 0, s 1) ∈ S} from h),
        Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem (show s ∉ {s : Fin 2 → ℝ | (s 0, s 1) ∈ S} from h),
        Set.indicator_of_notMem h]
  simp_rw [e]
  rw [← lintegral_prod _ (hg.indicator hS).aemeasurable, ← Measure.volume_eq_prod]
  exact (volume_preserving_finTwoArrow ℝ).lintegral_comp_emb
    MeasurableEquiv.finTwoArrow.measurableEmbedding (S.indicator g)

/-- Auxiliary: integrals over the square `(0, t)^2` of times. -/
theorem setLIntegral_square {t : ℝ} {f : ℝ → ℝ → ℝ≥0∞}
    (hf : Measurable fun p : ℝ × ℝ => f p.1 p.2) :
    ∫⁻ s in {s : Fin 2 → ℝ | (s 0, s 1) ∈ Ioo 0 t ×ˢ Ioo 0 t}, f (s 0) (s 1) =
      ∫⁻ x in Ioo 0 t, ∫⁻ y in Ioo 0 t, f x y := by
  rw [setLIntegral_fin_two (g := fun p => f p.1 p.2) (measurableSet_Ioo.prod measurableSet_Ioo)
    hf, lintegral_nested measurableSet_Ioo (fun _ => measurableSet_Ioo)]
  rfl

/-- Auxiliary: integrals over the ordered times `0 < s_0 < s_1 < t`. -/
theorem setLIntegral_triangle {t : ℝ} {f : ℝ → ℝ → ℝ≥0∞}
    (hf : Measurable fun p : ℝ × ℝ => f p.1 p.2) :
    ∫⁻ s in {s : Fin 2 → ℝ | (s 0, s 1) ∈ tri t}, f (s 0) (s 1) =
      ∫⁻ y in Ioo 0 t, ∫⁻ x in Ioo 0 y, f x y := by
  rw [setLIntegral_fin_two (g := fun p => f p.1 p.2) (measurableSet_tri t) hf,
    lintegral_tri_outer hf]

/-! ### `ℝ^1` and the `d = 1` Green measures -/

/-- Auxiliary: the norm on `ℝ^1` is the absolute value of the coordinate. -/
theorem norm_rd1 (x : Rd 1) : ‖x‖ = |e1 x| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs, Real.sqrt_sq_eq_abs]
  rfl

/-- Auxiliary: `e1 (-a) = -e1 a`. -/
theorem e1_neg (a : Rd 1) : e1 (-a) = -e1 a := by
  have h := e1_sub 0 a
  rwa [zero_sub, DiagramBridge.e1_zero, zero_sub] at h

/-- Auxiliary: the ball of `ℝ^1` is the preimage of the interval. -/
theorem e1_preimage_Ioo (r : ℝ) : e1 ⁻¹' Ioo (-r) r = Metric.ball (0 : Rd 1) r := by
  ext x
  simp only [mem_preimage, mem_Ioo, Metric.mem_ball, dist_zero_right, norm_rd1, abs_lt]

/-- Auxiliary: `|B(0, r)| = 2r` in `ℝ^1`. -/
theorem volume_ball_rd1 (r : ℝ) :
    volume (Metric.ball (0 : Rd 1) r) = ENNReal.ofReal (2 * r) := by
  rw [← e1_preimage_Ioo, measurePreserving_e1.measure_preimage
    measurableSet_Ioo.nullMeasurableSet, Real.volume_Ioo]
  congr 1
  ring

/-- Auxiliary: integrals against `G_h = ½ 1_{|y|<h} dy` in the coordinate. -/
theorem lintegral_waveGreen_one (h : ℝ) (F : ℝ → ℝ≥0∞) :
    ∫⁻ w, F (e1 w) ∂waveGreen 1 h = ENNReal.ofReal (1 / 2) * ∫⁻ x in Ioo (-h) h, F x := by
  rw [show waveGreen 1 h = ENNReal.ofReal (1 / 2) • volume.restrict (Metric.ball (0 : Rd 1) h)
    from rfl, lintegral_smul_measure, ← e1_preimage_Ioo,
    measurePreserving_e1.setLIntegral_comp_preimage_emb e1.measurableEmbedding, smul_eq_mul]

/-- Auxiliary: the product of two Green measures in `Fin 2` form. -/
theorem pi_waveGreen_two (h : Fin 2 → ℝ) :
    Measure.pi (fun i => waveGreen 1 (h i)) =
      Measure.pi ![waveGreen 1 (h 0), waveGreen 1 (h 1)] := by
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Auxiliary: Tonelli for a product of two measures indexed by `Fin 2`. -/
theorem lintegral_pi_two {α : Type*} [MeasurableSpace α] (μ ν : Measure α) [SigmaFinite μ]
    [SigmaFinite ν] {g : α × α → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ w, g (w 0, w 1) ∂Measure.pi ![μ, ν] = ∫⁻ x, ∫⁻ y, g (x, y) ∂ν ∂μ := by
  rw [← lintegral_prod _ hg.aemeasurable]
  exact (measurePreserving_finTwoArrow_vec μ ν).lintegral_comp_emb
    MeasurableEquiv.finTwoArrow.measurableEmbedding g

/-! ### Two labels: pairings, positions, increments, time simplices -/

/-- Auxiliary: the only pairing of two labels swaps them. -/
theorem pair_two {D : Fin 2 → Fin 2} (hD : ∀ i, D i ≠ i ∧ D (D i) = i) : D 0 = 1 ∧ D 1 = 0 := by
  have h0 : (D 0 : ℕ) ≠ 0 := fun h => (hD 0).1 (Fin.ext h)
  have h1 : (D 1 : ℕ) ≠ 1 := fun h => (hD 1).1 (Fin.ext h)
  have l0 := (D 0).isLt
  have l1 := (D 1).isLt
  exact ⟨Fin.ext (by rw [Fin.val_one]; omega), Fin.ext (by rw [Fin.val_zero]; omega)⟩

/-- Auxiliary: the pairing of two labels has the single opener `0`. -/
theorem openers_two {D : Fin 2 → Fin 2} (h0 : D 0 = 1) (h1 : D 1 = 0) : openers D = {0} := by
  ext i
  fin_cases i <;> simp [openers, h0, h1]

/-- Auxiliary: the temporal weight of the pairing of two labels. -/
theorem timeWeight_two {D : Fin 2 → Fin 2} (hD : ∀ i, D i ≠ i ∧ D (D i) = i) (α₀ : ℝ)
    (s : Fin 2 → ℝ) : timeWeight α₀ D s = timeCov α₀ (s 0) (s 1) := by
  obtain ⟨h0, h1⟩ := pair_two hD
  rw [timeWeight, openers_two h0 h1, Finset.prod_singleton, h0]

/-- Auxiliary: the spatial weight of the pairing of two labels. -/
theorem covWeight_two {d : ℕ} {D : Fin 2 → Fin 2} (hD : ∀ i, D i ≠ i ∧ D (D i) = i)
    (γ : Rd d → ℝ≥0∞) (y : Fin 2 → Rd d) : covWeight γ D y = γ (y 0 - y 1) := by
  obtain ⟨h0, h1⟩ := pair_two hD
  rw [covWeight, openers_two h0 h1, Finset.prod_singleton, h0]

/-- Auxiliary: two chains of length one: each position is its own increment. -/
theorem pos_cross {d : ℕ} (w : Fin 2 → Rd d) : pos 1 w 0 = w 0 ∧ pos 1 w 1 = w 1 := by
  constructor <;> simp [pos, SameChain, Finset.sum_filter, Fin.sum_univ_two]

/-- Auxiliary: one chain of length two (`m = 2` or `m = 0`): `y_1 = w_0`,
`y_2 = w_0 + w_1`. -/
theorem pos_self {m : ℕ} (hm : m = 0 ∨ m = 2) {d : ℕ} (w : Fin 2 → Rd d) :
    pos m w 0 = w 0 ∧ pos m w 1 = w 0 + w 1 := by
  rcases hm with rfl | rfl <;>
    constructor <;> simp [pos, SameChain, Finset.sum_filter, Fin.sum_univ_two]

/-- Auxiliary: with two chains of length one every predecessor value is the root. -/
theorem predVal_cross {α : Type*} [Zero α] (f : Fin 2 → α) (i : Fin 2) : predVal 1 f i = 0 := by
  fin_cases i <;> simp [predVal, pred]

/-- Auxiliary: in one chain of length two the predecessor of label `1` is label `0`. -/
theorem predVal_self {m : ℕ} (hm : m = 0 ∨ m = 2) {α : Type*} [Zero α] (f : Fin 2 → α) :
    predVal m f 0 = 0 ∧ predVal m f 1 = f 0 := by
  rcases hm with rfl | rfl <;> constructor <;> simp [predVal, pred]

/-- Auxiliary: the times of two chains of length one fill the square `(0,t)^2`. -/
theorem simplex_cross (t : ℝ) :
    {s : Fin 2 → ℝ | ∀ i, predVal 1 s i < s i ∧ s i < t} =
      {s | (s 0, s 1) ∈ Ioo 0 t ×ˢ Ioo 0 t} := by
  ext s
  simp only [Set.mem_ofPred_eq, predVal_cross, Fin.forall_fin_two, mem_prod, mem_Ioo]

/-- Auxiliary: the times of one chain of length two fill the triangle. -/
theorem simplex_self {m : ℕ} (hm : m = 0 ∨ m = 2) (t : ℝ) :
    {s : Fin 2 → ℝ | ∀ i, predVal m s i < s i ∧ s i < t} = {s | (s 0, s 1) ∈ tri t} := by
  ext s
  simp only [Set.mem_ofPred_eq, Fin.forall_fin_two, (predVal_self hm s).1, (predVal_self hm s).2,
    tri]
  constructor
  · rintro ⟨⟨h1, _⟩, h3, h4⟩; exact ⟨h1, h3, h4⟩
  · rintro ⟨h1, h3, h4⟩; exact ⟨⟨h1, h3.trans h4⟩, h3, h4⟩

/-- Auxiliary: the increments of two chains of length one are the times. -/
theorem incr_cross (s : Fin 2 → ℝ) : incr 1 s = s := by
  funext i; simp [incr, predVal_cross]

/-- Auxiliary: the increments of one chain of length two. -/
theorem incr_self {m : ℕ} (hm : m = 0 ∨ m = 2) (s : Fin 2 → ℝ) :
    incr m s 0 = s 0 ∧ incr m s 1 = s 1 - s 0 := by
  simp [incr, (predVal_self hm s).1, (predVal_self hm s).2]

/-- Auxiliary: the measurability of the `d = 1` spatial part in the time increments. -/
theorem measurable_spatial_one {γ : Rd 1 → ℝ≥0∞} (hγ : Measurable γ) (m : ℕ) {N : ℕ}
    (D : Fin N → Fin N) : Measurable (spatial (waveGreen 1) γ m D) := by
  have e : spatial (waveGreen 1) γ m D = spatialPos green1 γ m D := by
    funext h; exact DiagramBridge.spatial_waveGreen_one_eq_spatialPos γ m D h
  rw [e]
  have hp : ∀ i : Fin N, Measurable fun y : Fin N → Rd 1 => predVal m y i := by
    intro i
    rcases hpi : pred m i with _ | j
    · simp_rw [predVal_of_none m _ i hpi]; exact measurable_const
    · simp_rw [predVal_of_some m _ i j hpi]; exact measurable_pi_apply j
  have hG : ∀ i : Fin N, Measurable fun q : (Fin N → ℝ) × (Fin N → Rd 1) =>
      green1 (q.1 i) (q.2 i - predVal m q.2 i) := by
    intro i
    have h1 : Measurable fun q : (Fin N → ℝ) × (Fin N → Rd 1) => q.1 i :=
      (measurable_pi_apply i).comp measurable_fst
    have h2 : Measurable fun q : (Fin N → ℝ) × (Fin N → Rd 1) => q.2 i - predVal m q.2 i :=
      ((measurable_pi_apply i).comp measurable_snd).sub ((hp i).comp measurable_snd)
    have e : (fun q : (Fin N → ℝ) × (Fin N → Rd 1) => green1 (q.1 i) (q.2 i - predVal m q.2 i)) =
        {q : (Fin N → ℝ) × (Fin N → Rd 1) | ‖q.2 i - predVal m q.2 i‖ < q.1 i}.indicator
          fun _ => ENNReal.ofReal (1 / 2) := by
      funext q
      simp only [green1, Set.indicator, Metric.mem_ball, dist_zero_right, Set.mem_ofPred_eq]
    rw [e]
    exact measurable_const.indicator (measurableSet_lt h2.norm h1)
  have hF : Measurable fun q : (Fin N → ℝ) × (Fin N → Rd 1) =>
      (∏ i, green1 (q.1 i) (q.2 i - predVal m q.2 i)) * covWeight γ D q.2 := by
    refine (Finset.measurable_prod _ fun i _ => hG i).mul ?_
    exact (Finset.measurable_prod _ fun i _ => hγ.comp
      ((measurable_pi_apply i).sub (measurable_pi_apply (D i)))).comp measurable_snd
  exact hF.lintegral_prod_right' (ν := volume)

/-! ### The spatial parts for the Riesz covariance `c|y|^{-α}` -/

/-- Auxiliary: `riesz c α` in the coordinate of `ℝ^1`. -/
theorem riesz_rd1 (c α : ℝ) (x : Rd 1) : riesz c α x = ENNReal.ofReal (c * |e1 x| ^ (-α)) := by
  rw [riesz, norm_rd1]

/-- Auxiliary: the Riesz density is measurable. -/
theorem measurable_riesz (c α : ℝ) : Measurable (riesz c α : Rd 1 → ℝ≥0∞) :=
  ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_norm.pow_const _))

/-- Auxiliary: `∫ G_h(dy) c|y|^{-α} = c h^{1-α}/(1-α)`. -/
theorem lintegral_riesz_waveGreen {c α : ℝ} (hc : 0 ≤ c) (hα : α < 1) {h : ℝ} (hh : 0 ≤ h) :
    ∫⁻ y, riesz c α (-y) ∂waveGreen 1 h = ENNReal.ofReal (c * h ^ (1 - α) / (1 - α)) := by
  have e : ∀ y : Rd 1, riesz c α (-y) = ENNReal.ofReal (c * |e1 y| ^ (-α)) := fun y => by
    rw [riesz_rd1, e1_neg, abs_neg]
  simp_rw [e]
  rw [lintegral_waveGreen_one h (fun x => ENNReal.ofReal (c * |x| ^ (-α))),
    lintegral_Ioo_ofReal (by linarith) ((intervalIntegrable_abs_rpow hα _ _).const_mul c)
      (fun x _ => mul_nonneg hc (Real.rpow_nonneg (abs_nonneg x) _)),
    intervalIntegral.integral_const_mul, integral_abs_rpow hα, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  have hpow : h ^ (1 - α) = h * h ^ (-α) := by
    rw [show (1 : ℝ) - α = 1 + -α by ring, Real.rpow_add' hh (by linarith), Real.rpow_one]
  unfold rPhi
  rw [abs_neg, abs_of_nonneg hh, hpow]
  have : (1 : ℝ) - α ≠ 0 := by linarith
  field_simp
  ring

/-- The `d = 1` Riesz spatial part of one chain of length two (`m = 2` or
`m = 0`): with increments `h_0, h_1 ≥ 0`, `S(h) = h_0 · c h_1^{1-α}/(1-α)` (main
TeX lines 5189-5191: "the spatial integral is `c_α r v^{1-α}/(1-α)`"). -/
theorem spatial_riesz_self {m : ℕ} (hm : m = 0 ∨ m = 2) {c α : ℝ} (hc : 0 ≤ c) (hα : α < 1)
    {D : Fin 2 → Fin 2} (hD : ∀ i, D i ≠ i ∧ D (D i) = i) {h : Fin 2 → ℝ} (h0 : 0 ≤ h 0)
    (h1 : 0 ≤ h 1) :
    spatial (waveGreen 1) (riesz c α) m D h =
      ENNReal.ofReal (h 0 * (c * h 1 ^ (1 - α) / (1 - α))) := by
  unfold spatial
  have e : ∀ w : Fin 2 → Rd 1, covWeight (riesz c α) D (pos m w) = riesz c α (-(w 1)) :=
    fun w => by rw [covWeight_two hD, (pos_self hm w).1, (pos_self hm w).2, sub_add_cancel_left]
  simp_rw [e]
  have hg : Measurable fun p : Rd 1 × Rd 1 => riesz c α (-p.2) :=
    (measurable_riesz c α).comp measurable_snd.neg
  rw [pi_waveGreen_two h, lintegral_pi_two (g := fun p : Rd 1 × Rd 1 => riesz c α (-p.2)) _ _ hg]
  simp only
  rw [lintegral_const, lintegral_riesz_waveGreen hc hα h1,
    WaveGreen.waveGreen_mass 1 (Or.inl rfl) _ h0, mul_comm, ← ENNReal.ofReal_mul h0]

/-- The kernel `K(a, b) = c((a+b)^{2-α} - |a-b|^{2-α})/(2(1-α)(2-α))` (main TeX
lines 5182-5187). -/
def rK (c α a b : ℝ) : ℝ := c * ((a + b) ^ (2 - α) - |a - b| ^ (2 - α)) / (2 * (1 - α) * (2 - α))

/-- Auxiliary: the inner integral of the Riesz cross term. -/
theorem inner_riesz {c α : ℝ} (hc : 0 ≤ c) (hα : α < 1) {h : ℝ} (hh : 0 ≤ h) (x : Rd 1) :
    ∫⁻ y, riesz c α (x - y) ∂waveGreen 1 h =
      ENNReal.ofReal (1 / 2 * (c * (rPhi α (e1 x + h) - rPhi α (e1 x - h)))) := by
  have e : ∀ y : Rd 1, riesz c α (x - y) = ENNReal.ofReal (c * |e1 x - e1 y| ^ (-α)) := fun y => by
    rw [riesz_rd1, e1_sub]
  simp_rw [e]
  have hint : IntervalIntegrable (fun v => |e1 x - v| ^ (-α)) volume (-h) h := by
    have := (intervalIntegrable_abs_rpow hα (e1 x + h) (e1 x - h)).comp_sub_left (e1 x)
    simpa using this
  rw [lintegral_waveGreen_one h (fun v => ENNReal.ofReal (c * |e1 x - v| ^ (-α))),
    lintegral_Ioo_ofReal (by linarith) (hint.const_mul c)
      (fun v _ => mul_nonneg hc (Real.rpow_nonneg (abs_nonneg _) _)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_left (fun w => |w| ^ (-α)) (e1 x), integral_abs_rpow hα,
    ← ENNReal.ofReal_mul (by norm_num), sub_neg_eq_add]

/-- The `d = 1` Riesz spatial part of two chains of length one: with time
increments `h_0, h_1 ≥ 0`,
`∫∫ G(h_0, y) G(h_1, z) c|y - z|^{-α} dy dz = K(h_0, h_1)` (main TeX lines
5182-5187). -/
theorem spatial_riesz_cross {c α : ℝ} (hc : 0 ≤ c) (hα : α < 1) {D : Fin 2 → Fin 2}
    (hD : ∀ i, D i ≠ i ∧ D (D i) = i) {h : Fin 2 → ℝ} (h0 : 0 ≤ h 0) (h1 : 0 ≤ h 1) :
    spatial (waveGreen 1) (riesz c α) 1 D h = ENNReal.ofReal (rK c α (h 0) (h 1)) := by
  unfold spatial
  have e : ∀ w : Fin 2 → Rd 1, covWeight (riesz c α) D (pos 1 w) = riesz c α (w 0 - w 1) :=
    fun w => by rw [covWeight_two hD, (pos_cross w).1, (pos_cross w).2]
  simp_rw [e]
  have hg : Measurable fun p : Rd 1 × Rd 1 => riesz c α (p.1 - p.2) :=
    (measurable_riesz c α).comp (measurable_fst.sub measurable_snd)
  rw [pi_waveGreen_two h, lintegral_pi_two (g := fun p : Rd 1 × Rd 1 => riesz c α (p.1 - p.2))
    _ _ hg]
  simp only
  simp_rw [inner_riesz hc hα h1]
  set q : ℝ → ℝ := fun u => 1 / 2 * (c * (rPhi α (u + h 1) - rPhi α (u - h 1))) with hq
  have hqc : Continuous q :=
    continuous_const.mul (continuous_const.mul
      (((continuous_rPhi hα).comp (continuous_id.add continuous_const)).sub
        ((continuous_rPhi hα).comp (continuous_id.sub continuous_const))))
  have hq0 : ∀ u, 0 ≤ q u := by
    intro u
    have : 0 ≤ rPhi α (u + h 1) - rPhi α (u - h 1) := by
      rw [← integral_abs_rpow hα]
      exact intervalIntegral.integral_nonneg (by linarith)
        (fun w _ => Real.rpow_nonneg (abs_nonneg w) _)
    exact mul_nonneg (by norm_num) (mul_nonneg hc this)
  rw [lintegral_waveGreen_one (h 0) (fun u => ENNReal.ofReal (q u)),
    lintegral_Ioo_ofReal (by linarith) (hqc.intervalIntegrable _ _) (fun u _ => hq0 u),
    ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  have hc1 : Continuous fun u => rPhi α (u + h 1) :=
    (continuous_rPhi hα).comp (continuous_id.add continuous_const)
  have hc2 : Continuous fun u => rPhi α (u - h 1) :=
    (continuous_rPhi hα).comp (continuous_id.sub continuous_const)
  simp only [hq]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _),
    intervalIntegral.integral_comp_add_right (fun u => rPhi α u),
    intervalIntegral.integral_comp_sub_right (fun u => rPhi α u),
    integral_rPhi hα, integral_rPhi hα,
    show -h 0 + h 1 = -(h 0 - h 1) by ring, show -h 0 - h 1 = -(h 0 + h 1) by ring,
    rPsi_neg, rPsi_neg]
  unfold rPsi rK
  rw [abs_of_nonneg (by linarith : 0 ≤ h 0 + h 1)]
  have : (1 : ℝ) - α ≠ 0 := by linarith
  have : (2 : ℝ) - α ≠ 0 := by linarith
  field_simp
  ring

/-! ### The white spatial parts `Γ = δ₀`, collapsed (from `WhiteCollapse`)

The white-noise limit `ε ↓ 0` is not re-proved here: `WhiteCollapse.diagramLim_white`
identifies `J_{m,n,D}(t)` with `WhiteCollapse.whiteDiagram` for every diagram, whose
spatial factor `whiteSpatial` has the two positions of every pair identified.  For
two labels that factor is computed below. -/

/-- Auxiliary: Tonelli on `ℝ^2` in `Fin 2` form. -/
theorem lintegral_fin_two_real {g : ℝ × ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ v : Fin 2 → ℝ, g (v 0, v 1) = ∫⁻ x, ∫⁻ y, g (x, y) := by
  rw [← lintegral_prod _ hg.aemeasurable, ← Measure.volume_eq_prod]
  exact (volume_preserving_finTwoArrow ℝ).lintegral_comp_emb
    MeasurableEquiv.finTwoArrow.measurableEmbedding g

/-- Auxiliary: the `d = 1` Green kernel `g(h, x) = ½ 1_{|x| < h}` as an indicator. -/
theorem g1_eq_indicator (h x : ℝ) :
    WhiteCollapse.g1 h x = (Ioo (-h) h).indicator (fun _ => ENNReal.ofReal (1 / 2)) x := by
  unfold WhiteCollapse.g1
  by_cases hx : |x| < h
  · simp only [hx, ↓reduceIte]
    rw [Set.indicator_of_mem (by rw [mem_Ioo, ← abs_lt]; exact hx)]
  · simp only [hx, ↓reduceIte]
    rw [Set.indicator_of_notMem (by rw [mem_Ioo, ← abs_lt]; exact hx)]

/-- Auxiliary: `∫ g(h, x) dx = h` (the spatial mass of `G_h`; `0` for `h ≤ 0`). -/
theorem lintegral_g1 (h : ℝ) : ∫⁻ x, WhiteCollapse.g1 h x = ENNReal.ofReal h := by
  simp_rw [g1_eq_indicator]
  rw [lintegral_indicator_const measurableSet_Ioo, Real.volume_Ioo,
    ← ENNReal.ofReal_mul (by norm_num)]
  congr 1; ring

/-- Auxiliary: `∫ g(a, x) g(b, x) dx = min(a, b)/2` (`0` if `min(a, b) ≤ 0`). -/
theorem lintegral_g1_mul (a b : ℝ) :
    ∫⁻ x, WhiteCollapse.g1 a x * WhiteCollapse.g1 b x = ENNReal.ofReal (min a b / 2) := by
  have e : ∀ x, WhiteCollapse.g1 a x * WhiteCollapse.g1 b x =
      (Ioo (-min a b) (min a b)).indicator
        (fun _ => ENNReal.ofReal (1 / 2) * ENNReal.ofReal (1 / 2)) x := by
    intro x
    unfold WhiteCollapse.g1
    by_cases hx : |x| < min a b
    · rw [lt_min_iff] at hx
      simp only [hx.1, hx.2, ↓reduceIte]
      rw [Set.indicator_of_mem
        (by rw [mem_Ioo, ← abs_lt, lt_min_iff]; exact hx)]
    · rw [Set.indicator_of_notMem (by rw [mem_Ioo, ← abs_lt]; exact hx)]
      rw [lt_min_iff, not_and_or] at hx
      rcases hx with hx | hx
      · simp only [hx, ↓reduceIte, zero_mul]
      · simp only [hx, ↓reduceIte, mul_zero]
  simp_rw [e]
  rw [lintegral_indicator_const measurableSet_Ioo, Real.volume_Ioo,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]
  congr 1; ring

/-- Auxiliary: integrating out the closer coordinate of the pairing of two
labels (its standard Gaussian weight has mass one). -/
theorem whiteSpatial_two {m : ℕ} {D : Fin 2 → Fin 2} (hD : ∀ i, D i ≠ i ∧ D (D i) = i)
    (h : Fin 2 → ℝ) (Φ : ℝ → ℝ≥0∞) (hΦ : Measurable Φ)
    (hG : ∀ x : ℝ, WhiteCollapse.greenProd m h (fun _ => x) = Φ x) :
    WhiteCollapse.whiteSpatial m D h = ∫⁻ x, Φ x := by
  obtain ⟨h0, h1⟩ := pair_two hD
  have hop : ∀ v : Fin 2 → ℝ, (fun i => v (WhiteCollapse.opener D i)) = fun _ => v 0 := by
    intro v; funext i
    fin_cases i <;> simp [WhiteCollapse.opener, h0, h1]
  have hgw : ∀ v : Fin 2 → ℝ, WhiteCollapse.gaussW D v =
      ENNReal.ofReal (WhiteCollapse.phi 1 (v 1)) := by
    intro v
    rw [WhiteCollapse.gaussW, openers_two h0 h1, Finset.prod_singleton, h0]
  have hφ : Measurable fun r => ENNReal.ofReal (WhiteCollapse.phi 1 r) :=
    ENNReal.measurable_ofReal.comp (WhiteCollapse.continuous_phi 1).measurable
  unfold WhiteCollapse.whiteSpatial
  simp_rw [hop, hgw, hG]
  rw [lintegral_fin_two_real (g := fun p : ℝ × ℝ => Φ p.1 *
    ENNReal.ofReal (WhiteCollapse.phi 1 p.2)) ((hΦ.comp measurable_fst).mul
      (hφ.comp measurable_snd))]
  refine lintegral_congr fun x => ?_
  simp only
  rw [lintegral_const_mul _ hφ, WhiteCollapse.lintegral_phi_one, mul_one]

/-- The collapsed white spatial part of one chain of length two is
`ofReal(h_0) · ofReal(1/2)`, that is `h_0/2` for `h_0 ≥ 0`, when `h_1 > 0` (main TeX lines
959-962: "the first factor `G_r` has spatial mass `r`,
while `G_{s-r}(0) = 1/2`"). -/
theorem whiteSpatial_self {m : ℕ} (hm : m = 0 ∨ m = 2) {D : Fin 2 → Fin 2}
    (hD : ∀ i, D i ≠ i ∧ D (D i) = i) {h : Fin 2 → ℝ} (h1 : 0 < h 1) :
    WhiteCollapse.whiteSpatial m D h = ENNReal.ofReal (h 0) * ENNReal.ofReal (1 / 2) := by
  have hg1 : Measurable fun x => WhiteCollapse.g1 (h 0) x :=
    WhiteCollapse.measurable_g1_uncurry.comp (measurable_const.prodMk measurable_id)
  rw [whiteSpatial_two hD h (fun x => WhiteCollapse.g1 (h 0) x * ENNReal.ofReal (1 / 2))
    (hg1.mul_const _) (fun x => ?_), lintegral_mul_const _ hg1, lintegral_g1]
  rw [WhiteCollapse.greenProd, Fin.prod_univ_two, (predVal_self hm _).1,
    (predVal_self hm _).2, sub_zero, sub_self]
  congr 1
  unfold WhiteCollapse.g1
  simp only [abs_zero, h1, ↓reduceIte]

/-- The collapsed white spatial part of two chains of length one is
`∫ G(h_0, y) G(h_1, y) dy = min(h_0, h_1)/2` (main TeX lines 952-953), for every
`h` (for `min(h_0, h_1) ≤ 0` both sides vanish). -/
theorem whiteSpatial_cross {D : Fin 2 → Fin 2} (hD : ∀ i, D i ≠ i ∧ D (D i) = i)
    (h : Fin 2 → ℝ) :
    WhiteCollapse.whiteSpatial 1 D h = ENNReal.ofReal (min (h 0) (h 1) / 2) := by
  have hg : ∀ a : ℝ, Measurable fun x => WhiteCollapse.g1 a x := fun a =>
    WhiteCollapse.measurable_g1_uncurry.comp (measurable_const.prodMk measurable_id)
  rw [whiteSpatial_two hD h (fun x => WhiteCollapse.g1 (h 0) x * WhiteCollapse.g1 (h 1) x)
    ((hg _).mul (hg _)) (fun x => ?_), lintegral_g1_mul]
  simp only [WhiteCollapse.greenProd, Fin.prod_univ_two, predVal_cross, sub_zero]

/-! ### The time integrals -/

/-- The constant `c_0 = ((1-α₀)(2-α₀)(3-α₀))^{-1}` of `L:white-test` (main TeX
lines 941-942). -/
def c0 (α₀ : ℝ) : ℝ := ((1 - α₀) * (2 - α₀) * (3 - α₀))⁻¹

/-- Auxiliary: `|x - y|^{-α₀}` for `x < y`. -/
theorem timeCov_of_lt (α₀ : ℝ) {x y : ℝ} (h : x < y) :
    timeCov α₀ x y = ENNReal.ofReal ((y - x) ^ (-α₀)) := by
  rw [timeCov, abs_sub_comm, abs_of_pos (sub_pos.2 h),
    ENNReal.ofReal_rpow_of_pos (sub_pos.2 h)]

/-- Auxiliary: the temporal covariance is symmetric. -/
theorem timeCov_comm (α₀ x y : ℝ) : timeCov α₀ x y = timeCov α₀ y x := by
  rw [timeCov, timeCov, abs_sub_comm]

/-- Auxiliary: the Beta-integral identity on the triangle,
`∫_0^t dy ∫_0^y K (y - x)^q x dx = K t^{q+3}/((q+1)(q+2)(q+3))`. -/
theorem lintegral_tri_value {q : ℝ} (hq : -1 < q) {t : ℝ} (ht : 0 ≤ t) {K : ℝ} (hK : 0 ≤ K) :
    ∫⁻ y in Ioo 0 t, ∫⁻ x in Ioo 0 y, ENNReal.ofReal (K * ((y - x) ^ q * x)) =
      ENNReal.ofReal (K * t ^ (q + 3) / ((q + 1) * (q + 2) * (q + 3))) := by
  have hq1 : 0 < q + 1 := by linarith
  have hq2 : 0 < q + 2 := by linarith
  have hq3 : 0 < q + 3 := by linarith
  have hin : ∀ y ∈ Ioo (0 : ℝ) t, ∫⁻ x in Ioo 0 y, ENNReal.ofReal (K * ((y - x) ^ q * x)) =
      ENNReal.ofReal (K / ((q + 1) * (q + 2)) * y ^ (q + 2)) := by
    intro y hy
    have hint : IntervalIntegrable (fun x => (y - x) ^ q * x) volume 0 y := by
      have h1 := (intervalIntegral.intervalIntegrable_rpow' (a := y) (b := 0) hq).comp_sub_left y
      simp only [sub_self, sub_zero] at h1
      exact h1.mul_continuousOn continuous_id.continuousOn
    rw [lintegral_Ioo_ofReal hy.1.le (hint.const_mul K) (fun x hx => mul_nonneg hK
        (mul_nonneg (Real.rpow_nonneg (by linarith [hx.2]) _) hx.1.le)),
      intervalIntegral.integral_const_mul, integral_sub_rpow_mul hq hy.1.le]
    congr 1
    field_simp
  rw [setLIntegral_congr_fun measurableSet_Ioo hin,
    lintegral_Ioo_ofReal ht ((intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul _)
      (fun y hy => mul_nonneg (div_nonneg hK (mul_pos hq1 hq2).le) (Real.rpow_nonneg hy.1.le _)),
    intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)),
    Real.zero_rpow (by linarith), sub_zero, show q + 2 + 1 = q + 3 by ring]
  congr 1
  field_simp

/-- Auxiliary: the time integral of the white self-pairing diagram,
`∫_{0<x<y<t} (y-x)^{-α₀} x/2 = c_0 t^{3-α₀}/2` (main TeX lines 959-962). -/
theorem time_white_self {m : ℕ} (hm : m = 0 ∨ m = 2) {D : Fin 2 → Fin 2}
    (hD : ∀ i, D i ≠ i ∧ D (D i) = i) {α₀ : ℝ} (hα0 : α₀ < 1) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ s in {s : Fin 2 → ℝ | ∀ i, predVal m s i < s i ∧ s i < t},
        timeWeight α₀ D s * (ENNReal.ofReal (incr m s 0) * ENNReal.ofReal (1 / 2)) =
      ENNReal.ofReal (c0 α₀ / 2 * t ^ (3 - α₀)) := by
  rw [simplex_self hm]
  simp_rw [timeWeight_two hD, (incr_self hm _).1]
  have hg : Measurable fun p : ℝ × ℝ =>
      timeCov α₀ p.1 p.2 * (ENNReal.ofReal p.1 * ENNReal.ofReal (1 / 2)) :=
    (measurable_timeCov α₀).mul ((ENNReal.measurable_ofReal.comp measurable_fst).mul_const _)
  rw [setLIntegral_triangle (f := fun x y => timeCov α₀ x y *
    (ENNReal.ofReal x * ENNReal.ofReal (1 / 2))) hg]
  have hin : ∀ y ∈ Ioo (0 : ℝ) t, ∫⁻ x in Ioo 0 y, timeCov α₀ x y *
      (ENNReal.ofReal x * ENNReal.ofReal (1 / 2)) =
        ∫⁻ x in Ioo 0 y, ENNReal.ofReal (1 / 2 * ((y - x) ^ (-α₀) * x)) := by
    intro y _
    refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    rw [timeCov_of_lt α₀ hx.2, ← ENNReal.ofReal_mul hx.1.le,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith [hx.2]) _)]
    congr 1; ring
  rw [setLIntegral_congr_fun measurableSet_Ioo hin,
    lintegral_tri_value (by linarith) ht (by norm_num)]
  congr 1
  unfold c0
  rw [show -α₀ + 3 = 3 - α₀ by ring, show -α₀ + 1 = 1 - α₀ by ring,
    show -α₀ + 2 = 2 - α₀ by ring]
  field_simp

/-- Auxiliary: the time integral of the white cross-pairing diagram,
`∫_{(0,t)^2} |x-y|^{-α₀} min(x,y)/2 = c_0 t^{3-α₀}` (main TeX lines 952-958). -/
theorem time_white_cross {D : Fin 2 → Fin 2} (hD : ∀ i, D i ≠ i ∧ D (D i) = i) {α₀ : ℝ}
    (hα0 : α₀ < 1) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ s in {s : Fin 2 → ℝ | ∀ i, predVal 1 s i < s i ∧ s i < t},
        timeWeight α₀ D s * ENNReal.ofReal (min (incr 1 s 0) (incr 1 s 1) / 2) =
      ENNReal.ofReal (c0 α₀ * t ^ (3 - α₀)) := by
  rw [simplex_cross]
  simp_rw [timeWeight_two hD, incr_cross]
  have hg : Measurable fun p : ℝ × ℝ => timeCov α₀ p.1 p.2 * ENNReal.ofReal (min p.1 p.2 / 2) :=
    (measurable_timeCov α₀).mul (ENNReal.measurable_ofReal.comp
      ((measurable_fst.min measurable_snd).div_const _))
  rw [setLIntegral_square (f := fun x y => timeCov α₀ x y * ENNReal.ofReal (min x y / 2)) hg,
    lintegral_square_symm hg (fun x y => by rw [timeCov_comm, min_comm])]
  have hin : ∀ x ∈ Ioo (0 : ℝ) t, ∫⁻ y in Ioo 0 x, timeCov α₀ x y *
      ENNReal.ofReal (min x y / 2) =
        ∫⁻ y in Ioo 0 x, ENNReal.ofReal (1 / 2 * ((x - y) ^ (-α₀) * y)) := by
    intro x _
    refine setLIntegral_congr_fun measurableSet_Ioo fun y hy => ?_
    rw [timeCov_comm, timeCov_of_lt α₀ hy.2, min_eq_right hy.2.le,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith [hy.2]) _)]
    congr 1; ring
  rw [setLIntegral_congr_fun measurableSet_Ioo hin,
    lintegral_tri_value (by linarith) ht (by norm_num),
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  unfold c0
  rw [show -α₀ + 3 = 3 - α₀ by ring, show -α₀ + 1 = 1 - α₀ by ring,
    show -α₀ + 2 = 2 - α₀ by ring]
  field_simp

/-- Auxiliary: `c_0 > 0` for `α₀ < 1`. -/
theorem c0_pos {α₀ : ℝ} (hα0 : α₀ < 1) : 0 < c0 α₀ := by
  unfold c0
  have : 0 < (1 - α₀) * (2 - α₀) * (3 - α₀) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  positivity

/-- Auxiliary: sets of times given by the pair `(s 0, s 1)` are measurable. -/
theorem measurableSet_pairSet {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) :
    MeasurableSet {s : Fin 2 → ℝ | (s 0, s 1) ∈ S} :=
  hS.preimage ((measurable_pi_apply 0).prodMk (measurable_pi_apply 1))

/-- Auxiliary: the time integral of the Riesz self-pairing diagram (main TeX
lines 5189-5193): `∫_{0<x<y<t} (y-x)^{-α₀} x c (y-x)^{1-α}/(1-α)
= c t^β/((1-α)(2-α-α₀)(3-α-α₀)(4-α-α₀))`. -/
theorem time_riesz_self {c α α₀ : ℝ} (hc : 0 ≤ c) (hα : α < 1) (hα0 : α₀ < 1) {t : ℝ}
    (ht : 0 ≤ t) :
    ∫⁻ s in {s : Fin 2 → ℝ | (s 0, s 1) ∈ tri t},
        timeCov α₀ (s 0) (s 1) * ENNReal.ofReal (s 0 * (c * (s 1 - s 0) ^ (1 - α) / (1 - α))) =
      ENNReal.ofReal (c * t ^ (4 - α - α₀) /
        ((1 - α) * (2 - α - α₀) * (3 - α - α₀) * (4 - α - α₀))) := by
  have hg : Measurable fun p : ℝ × ℝ => timeCov α₀ p.1 p.2 *
      ENNReal.ofReal (p.1 * (c * (p.2 - p.1) ^ (1 - α) / (1 - α))) :=
    (measurable_timeCov α₀).mul (ENNReal.measurable_ofReal.comp (measurable_fst.mul
      ((measurable_const.mul ((measurable_snd.sub measurable_fst).pow_const _)).div_const _)))
  rw [setLIntegral_triangle (f := fun x y => timeCov α₀ x y *
    ENNReal.ofReal (x * (c * (y - x) ^ (1 - α) / (1 - α)))) hg]
  have hin : ∀ y ∈ Ioo (0 : ℝ) t, ∫⁻ x in Ioo 0 y, timeCov α₀ x y *
      ENNReal.ofReal (x * (c * (y - x) ^ (1 - α) / (1 - α))) =
        ∫⁻ x in Ioo 0 y, ENNReal.ofReal (c / (1 - α) * ((y - x) ^ (1 - α - α₀) * x)) := by
    intro y _
    refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    rw [timeCov_of_lt α₀ hx.2, ← ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith [hx.2]) _)]
    congr 1
    rw [show 1 - α - α₀ = -α₀ + (1 - α) by ring, Real.rpow_add (by linarith [hx.2])]
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioo hin,
    lintegral_tri_value (by linarith) ht (div_nonneg hc (by linarith))]
  congr 1
  rw [show 1 - α - α₀ + 3 = 4 - α - α₀ by ring, show 1 - α - α₀ + 1 = 2 - α - α₀ by ring,
    show 1 - α - α₀ + 2 = 3 - α - α₀ by ring]
  have : (1 : ℝ) - α ≠ 0 := by linarith
  field_simp

/-- The bracket of `E:riesz-two` (main TeX lines 5138-5139):
`((2t - v)^{3-α} - v^{3-α})/(2(3-α)) - (t - v) v^{2-α}`. -/
def rbr (t α v : ℝ) : ℝ :=
  ((2 * t - v) ^ (3 - α) - v ^ (3 - α)) / (2 * (3 - α)) - (t - v) * v ^ (2 - α)

/-- Auxiliary: `∫_0^{t-v} ((2r+v)^{2-α} - v^{2-α}) dr` is the bracket. -/
theorem integral_rbr {α : ℝ} (hα : α < 1) {t v : ℝ} :
    ∫ r in (0 : ℝ)..(t - v), ((2 * r + v) ^ (2 - α) - v ^ (2 - α)) = rbr t α v := by
  have h2 : (0 : ℝ) ≤ 2 - α := by linarith
  have hc : Continuous fun r : ℝ => (2 * r + v) ^ (2 - α) :=
    (Real.continuous_rpow_const h2).comp ((continuous_const.mul continuous_id).add continuous_const)
  rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_comp_mul_add (fun x : ℝ => x ^ (2 - α)) two_ne_zero v,
    integral_rpow (Or.inl (by linarith)), intervalIntegral.integral_const, smul_eq_mul,
    smul_eq_mul]
  unfold rbr
  rw [show 2 * (t - v) + v = 2 * t - v by ring, show 2 * 0 + v = v by ring,
    show 2 - α + 1 = 3 - α by ring]
  have : (3 : ℝ) - α ≠ 0 := by linarith
  field_simp
  ring

/-- Auxiliary: the bracket is continuous in `v`. -/
theorem continuous_rbr {α : ℝ} (hα : α < 1) (t : ℝ) : Continuous (rbr t α) := by
  have h2 : (0 : ℝ) ≤ 2 - α := by linarith
  have h3 : (0 : ℝ) ≤ 3 - α := by linarith
  unfold rbr
  exact ((((Real.continuous_rpow_const h3).comp (continuous_const.sub continuous_id)).sub
    (Real.continuous_rpow_const h3)).div_const _).sub
      ((continuous_const.sub continuous_id).mul (Real.continuous_rpow_const h2))

/-- Auxiliary: the bracket is nonnegative for `0 ≤ v ≤ t`. -/
theorem rbr_nonneg {α : ℝ} (hα : α < 1) {t v : ℝ} (hv : 0 ≤ v) (hvt : v ≤ t) :
    0 ≤ rbr t α v := by
  rw [← integral_rbr hα]
  exact intervalIntegral.integral_nonneg (by linarith) fun r hr =>
    sub_nonneg.2 (Real.rpow_le_rpow hv (by linarith [hr.1]) (by linarith))

/-- Auxiliary: `K` is continuous. -/
theorem continuous_rK (c : ℝ) {α : ℝ} (hα : α < 1) :
    Continuous fun p : ℝ × ℝ => rK c α p.1 p.2 := by
  have h2 : (0 : ℝ) ≤ 2 - α := by linarith
  unfold rK
  exact (continuous_const.mul (((Real.continuous_rpow_const h2).comp
    (continuous_fst.add continuous_snd)).sub ((Real.continuous_rpow_const h2).comp
      (continuous_fst.sub continuous_snd).abs))).div_const _

/-- Auxiliary: the time integral of the Riesz cross-pairing diagram (main TeX
lines 5188-5189): integrate on `s > r`, double, set `v = s - r`, integrate `r`
over `(0, t - v)`. -/
theorem time_riesz_cross {c α α₀ : ℝ} (hc : 0 ≤ c) (hα : α < 1) (hα0 : α₀ < 1) {t : ℝ}
    (ht : 0 ≤ t) :
    ∫⁻ s in {s : Fin 2 → ℝ | (s 0, s 1) ∈ Ioo 0 t ×ˢ Ioo 0 t},
        timeCov α₀ (s 0) (s 1) * ENNReal.ofReal (rK c α (s 0) (s 1)) =
      ENNReal.ofReal (c / ((1 - α) * (2 - α)) * ∫ v in (0 : ℝ)..t, v ^ (-α₀) * rbr t α v) := by
  have hK := continuous_rK c hα
  have hg : Measurable fun p : ℝ × ℝ => timeCov α₀ p.1 p.2 * ENNReal.ofReal (rK c α p.1 p.2) :=
    (measurable_timeCov α₀).mul (ENNReal.measurable_ofReal.comp hK.measurable)
  rw [setLIntegral_square (f := fun x y => timeCov α₀ x y * ENNReal.ofReal (rK c α x y)) hg,
    lintegral_square_symm hg (fun x y => by
      rw [timeCov_comm]; unfold rK; rw [add_comm x y, abs_sub_comm])]
  set F : ℝ → ℝ → ℝ≥0∞ := fun x v => ENNReal.ofReal (v ^ (-α₀) * rK c α x (x - v)) with hF
  have hFm : Measurable fun p : ℝ × ℝ => F p.2 p.1 :=
    ENNReal.measurable_ofReal.comp ((measurable_fst.pow_const _).mul
      (hK.measurable.comp (measurable_snd.prodMk (measurable_snd.sub measurable_fst))))
  -- reflection `v = x - y`
  have step1 : ∀ x ∈ Ioo (0 : ℝ) t, ∫⁻ y in Ioo 0 x, timeCov α₀ x y *
      ENNReal.ofReal (rK c α x y) = ∫⁻ v in Ioo 0 x, F x v := by
    intro x _
    rw [← setLIntegral_Ioo_reflect x (F x)]
    refine setLIntegral_congr_fun measurableSet_Ioo fun y hy => ?_
    simp only [hF, sub_sub_cancel]
    rw [timeCov_comm, timeCov_of_lt α₀ hy.2,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith [hy.2]) _)]
  rw [setLIntegral_congr_fun measurableSet_Ioo step1]
  -- exchange the order of integration
  have hswap := lintegral_tri_swap (t := t) (f := fun a b => F b a) hFm
  rw [← hswap]
  -- translation `x = r + v` and the inner integral
  have step3 : ∀ v ∈ Ioo (0 : ℝ) t, ∫⁻ x in Ioo v t, F x v =
      ENNReal.ofReal (v ^ (-α₀) * (c / (2 * (1 - α) * (2 - α))) * rbr t α v) := by
    intro v hv
    rw [setLIntegral_Ioo_translate v t (fun x => F x v)]
    have h2 : (0 : ℝ) ≤ 2 - α := by linarith
    have hc2 : Continuous fun r : ℝ => (2 * r + v) ^ (2 - α) - v ^ (2 - α) :=
      ((Real.continuous_rpow_const h2).comp
        ((continuous_const.mul continuous_id).add continuous_const)).sub continuous_const
    have hA : 0 ≤ v ^ (-α₀) * (c / (2 * (1 - α) * (2 - α))) :=
      mul_nonneg (Real.rpow_nonneg hv.1.le _) (div_nonneg hc (by
        have : 0 < 2 * (1 - α) * (2 - α) := mul_pos (mul_pos two_pos (by linarith)) (by linarith)
        exact this.le))
    have e : ∀ r ∈ Ioo (0 : ℝ) (t - v), F (r + v) v = ENNReal.ofReal
        (v ^ (-α₀) * (c / (2 * (1 - α) * (2 - α))) * ((2 * r + v) ^ (2 - α) - v ^ (2 - α))) := by
      intro r _
      simp only [hF, add_sub_cancel_right]
      congr 1
      unfold rK
      rw [show r + v + r = 2 * r + v by ring, show r + v - r = v by ring,
        abs_of_pos hv.1]
      ring
    rw [setLIntegral_congr_fun measurableSet_Ioo e,
      lintegral_Ioo_ofReal (by linarith [hv.2]) ((hc2.intervalIntegrable _ _).const_mul _)
        (fun r hr => mul_nonneg hA (sub_nonneg.2 (Real.rpow_le_rpow hv.1.le
          (by linarith [hr.1]) h2))),
      intervalIntegral.integral_const_mul, integral_rbr hα]
  rw [setLIntegral_congr_fun measurableSet_Ioo step3,
    ← lintegral_const_mul' _ _ (by simp : (2 : ℝ≥0∞) ≠ ⊤)]
  have step4 : ∀ v ∈ Ioo (0 : ℝ) t,
      2 * ENNReal.ofReal (v ^ (-α₀) * (c / (2 * (1 - α) * (2 - α))) * rbr t α v) =
        ENNReal.ofReal (c / ((1 - α) * (2 - α)) * (v ^ (-α₀) * rbr t α v)) := by
    intro v _
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    have : (1 : ℝ) - α ≠ 0 := by linarith
    have : (2 : ℝ) - α ≠ 0 := by linarith
    field_simp
  rw [setLIntegral_congr_fun measurableSet_Ioo step4,
    lintegral_Ioo_ofReal ht
      (((intervalIntegral.intervalIntegrable_rpow' (by linarith)).mul_continuousOn
      (continuous_rbr hα t).continuousOn).const_mul _)
      (fun v hv => mul_nonneg (div_nonneg hc (mul_pos (by linarith) (by linarith)).le)
        (mul_nonneg (Real.rpow_nonneg hv.1.le _) (rbr_nonneg hα hv.1.le hv.2.le))),
    intervalIntegral.integral_const_mul]

/-! ### The order-two diagrams `J_{m,n,D}(t)`, `m + n = 2` -/

/-- Auxiliary: `J_{m,n,D}(t)` of `DiagramModel.diagram` (`d = 1`) for `m + n = 2`,
with the two labels written as `Fin 2` (definitionally the diagram for
`(m, n) = (1, 1), (2, 0), (0, 2)`: `diagram_one_one`, `diagram_two_zero`,
`diagram_zero_two`). -/
def diag2 (γ : Rd 1 → ℝ≥0∞) (α₀ : ℝ) (m : ℕ) (D : Fin 2 → Fin 2) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in {s : Fin 2 → ℝ | ∀ i, predVal m s i < s i ∧ s i < t},
    timeWeight α₀ D s * spatial (waveGreen 1) γ m D (incr m s)

/-- Auxiliary: the `(1,1)` diagram is `diag2 … 1`. -/
theorem diagram_one_one (γ : Rd 1 → ℝ≥0∞) (α₀ : ℝ) (D : Fin (1 + 1) → Fin (1 + 1)) (t : ℝ) :
    diagram (waveGreen 1) γ α₀ 1 1 D t = diag2 γ α₀ 1 D t := rfl

/-- Auxiliary: the `(2,0)` diagram is `diag2 … 2`. -/
theorem diagram_two_zero (γ : Rd 1 → ℝ≥0∞) (α₀ : ℝ) (D : Fin (2 + 0) → Fin (2 + 0)) (t : ℝ) :
    diagram (waveGreen 1) γ α₀ 2 0 D t = diag2 γ α₀ 2 D t := rfl

/-- Auxiliary: the `(0,2)` diagram is `diag2 … 0`. -/
theorem diagram_zero_two (γ : Rd 1 → ℝ≥0∞) (α₀ : ℝ) (D : Fin (0 + 2) → Fin (0 + 2)) (t : ℝ) :
    diagram (waveGreen 1) γ α₀ 0 2 D t = diag2 γ α₀ 0 D t := rfl

/-- Auxiliary: the white self-pairing diagram of two labels, collapsed, is
`c_0 t^{3-α₀}/2` (main TeX lines 959-962). -/
theorem whiteDiagram_self {m : ℕ} (hm : m = 0 ∨ m = 2) {D : Fin 2 → Fin 2}
    (hD : ∀ i, D i ≠ i ∧ D (D i) = i) {α₀ : ℝ} (hα0 : α₀ < 1) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ s in {s : Fin 2 → ℝ | ∀ i, predVal m s i < s i ∧ s i < t},
        timeWeight α₀ D s * WhiteCollapse.whiteSpatial m D (incr m s) =
      ENNReal.ofReal (c0 α₀ / 2 * t ^ (3 - α₀)) := by
  rw [← time_white_self hm hD hα0 ht]
  refine setLIntegral_congr_fun ?_ fun s hs => ?_
  · rcases hm with rfl | rfl
    · exact measurableSet_twoSimplex 0 2 t
    · exact measurableSet_twoSimplex 2 0 t
  · have e1 := (incr_self hm s).2
    have hlt := (hs 1).1
    rw [(predVal_self hm s).2] at hlt
    rw [whiteSpatial_self hm hD (by rw [e1]; linarith)]

/-- Auxiliary: the white cross-pairing diagram of two labels, collapsed, is
`c_0 t^{3-α₀}` (main TeX lines 952-958). -/
theorem whiteDiagram_cross {D : Fin 2 → Fin 2} (hD : ∀ i, D i ≠ i ∧ D (D i) = i) {α₀ : ℝ}
    (hα0 : α₀ < 1) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ s in {s : Fin 2 → ℝ | ∀ i, predVal 1 s i < s i ∧ s i < t},
        timeWeight α₀ D s * WhiteCollapse.whiteSpatial 1 D (incr 1 s) =
      ENNReal.ofReal (c0 α₀ * t ^ (3 - α₀)) := by
  simp_rw [whiteSpatial_cross hD]
  exact time_white_cross hD hα0 ht

/-- Auxiliary: the smoothed white self-pairing diagrams converge to
`c_0 t^{3-α₀}/2` (`WhiteCollapse.tendsto_diagram_white` and `whiteDiagram_self`). -/
theorem tendsto_white_self {m : ℕ} (hm : m = 0 ∨ m = 2) {D : Fin 2 → Fin 2}
    (hD : ∀ i, D i ≠ i ∧ D (D i) = i) {α₀ : ℝ} (hα0 : α₀ < 1) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun ε => diag2 (covEps (Measure.dirac (0 : Rd 1)) ε) α₀ m D t) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (c0 α₀ / 2 * t ^ (3 - α₀)))) := by
  rw [← whiteDiagram_self hm hD hα0 ht]
  rcases hm with rfl | rfl
  · exact WhiteCollapse.tendsto_diagram_white hα0 0 2 (D := D) hD t
  · exact WhiteCollapse.tendsto_diagram_white hα0 2 0 (D := D) hD t

/-- Auxiliary: the smoothed white cross-pairing diagrams converge to
`c_0 t^{3-α₀}` (`WhiteCollapse.tendsto_diagram_white` and `whiteDiagram_cross`). -/
theorem tendsto_white_cross {D : Fin 2 → Fin 2} (hD : ∀ i, D i ≠ i ∧ D (D i) = i) {α₀ : ℝ}
    (hα0 : α₀ < 1) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun ε => diag2 (covEps (Measure.dirac (0 : Rd 1)) ε) α₀ 1 D t) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (c0 α₀ * t ^ (3 - α₀)))) := by
  rw [← whiteDiagram_cross hD hα0 ht]
  exact WhiteCollapse.tendsto_diagram_white hα0 1 1 (D := D) hD t

/-- `L:white-test`, the `(1,1)` diagram (main TeX lines 940-949, proof 952-958): for spatial white
noise in `d = 1` (`Γ = δ₀`, the TeX's `J` being the limit of the smoothed
diagrams, `diagramLim`) and `α₀ < 1`, every pairing `D ∈ Π` of two chains of
length one has `J_{1,1,D}(t) = c_0 t^{3-α₀}`. -/
theorem white_cross {D : Fin (1 + 1) → Fin (1 + 1)} (hD : D ∈ Pi2 1 1) {α₀ : ℝ}
    (hα0 : α₀ < 1) {t : ℝ} (ht : 0 ≤ t) :
    diagramLim 1 (Measure.dirac 0) α₀ 1 1 D t = ENNReal.ofReal (c0 α₀ * t ^ (3 - α₀)) :=
  (tendsto_white_cross (mem_Pi2.1 hD) hα0 ht).limUnder_eq

/-- `L:white-test`, the `(2,0)` diagram (main TeX lines 940-949, proof 959-962):
`J_{2,0,D}(t) = c_0 t^{3-α₀}/2` for the self-pairing of the first chain. -/
theorem white_self_two_zero {D : Fin (2 + 0) → Fin (2 + 0)} (hD : D ∈ Pi2 2 0) {α₀ : ℝ}
    (hα0 : α₀ < 1) {t : ℝ} (ht : 0 ≤ t) :
    diagramLim 1 (Measure.dirac 0) α₀ 2 0 D t = ENNReal.ofReal (c0 α₀ / 2 * t ^ (3 - α₀)) :=
  (tendsto_white_self (Or.inr rfl) (mem_Pi2.1 hD) hα0 ht).limUnder_eq

/-- `L:white-test`, the `(0,2)` diagram (main TeX line 962: "the `(2,0)` term is
identical"): `J_{0,2,D}(t) = c_0 t^{3-α₀}/2`. -/
theorem white_self_zero_two {D : Fin (0 + 2) → Fin (0 + 2)} (hD : D ∈ Pi2 0 2) {α₀ : ℝ}
    (hα0 : α₀ < 1) {t : ℝ} (ht : 0 ≤ t) :
    diagramLim 1 (Measure.dirac 0) α₀ 0 2 D t = ENNReal.ofReal (c0 α₀ / 2 * t ^ (3 - α₀)) :=
  (tendsto_white_self (Or.inl rfl) (mem_Pi2.1 hD) hα0 ht).limUnder_eq

/-- Auxiliary: a sum over `Π` of two labels is its single term. -/
theorem sum_Pi2_two {m n : ℕ} (hmn : m + n = 2) {β : Type*} [AddCommMonoid β]
    {f : (Fin (m + n) → Fin (m + n)) → β} {a : β} (h : ∀ D ∈ Pi2 m n, f D = a) :
    ∑ D ∈ Pi2 m n, f D = a := by
  rw [Finset.sum_congr rfl h, Finset.sum_const, card_Pi2 (k := 1) hmn,
    show Nat.doubleFactorial (2 * 1 - 1) = 1 from rfl, one_nsmul]

/-- `L:white-test`, last sentence (main TeX lines 947-948): the total-order-two
coefficient `A_1(t) = Σ_{m=0}^{2} Σ_{D ∈ Π} J_{m,2-m,D}(t)` of `E:full-second` for
white noise is `2 c_0 t^{3-α₀}`. -/
theorem white_coeffALim_one {α₀ : ℝ} (hα0 : α₀ < 1) {t : ℝ} (ht : 0 ≤ t) :
    coeffALim 1 (Measure.dirac 0) α₀ 1 t = ENNReal.ofReal (2 * c0 α₀ * t ^ (3 - α₀)) := by
  have hnn : 0 ≤ c0 α₀ * t ^ (3 - α₀) := mul_nonneg (c0_pos hα0).le (Real.rpow_nonneg ht _)
  unfold coeffALim
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    sum_Pi2_two (m := 0) (n := 2 * 1 - 0) (by norm_num)
      (fun D hD => white_self_zero_two hD hα0 ht),
    sum_Pi2_two (m := 1) (n := 2 * 1 - 1) (by norm_num) (fun D hD => white_cross hD hα0 ht),
    sum_Pi2_two (m := 2) (n := 2 * 1 - 2) (by norm_num)
      (fun D hD => white_self_two_zero hD hα0 ht),
    ← ENNReal.ofReal_add (by linarith) hnn, ← ENNReal.ofReal_add (by linarith) (by linarith)]
  congr 1
  ring

/-! ### The Riesz order-two diagrams -/

/-- `P:riesz-small`, first formula of `E:riesz-two` on the model (main TeX lines
5125-5134, proof 5189-5193): for `γ(y) = c|y|^{-α}` in `d = 1` with `c ≥ 0`,
`α < 1`, `α₀ < 1`, the single-chain diagram `J_{2,0,D}(t)` equals
`c t^β/((1-α)(2-α-α₀)(3-α-α₀)(4-α-α₀))`, `β = 4 - α - α₀`. -/
theorem riesz_self_two_zero {D : Fin (2 + 0) → Fin (2 + 0)} (hD : D ∈ Pi2 2 0) {c α α₀ : ℝ}
    (hc : 0 ≤ c) (hα : α < 1) (hα0 : α₀ < 1) {t : ℝ} (ht : 0 ≤ t) :
    diagram (waveGreen 1) (riesz c α) α₀ 2 0 D t =
      ENNReal.ofReal (c * t ^ (4 - α - α₀) /
        ((1 - α) * (2 - α - α₀) * (3 - α - α₀) * (4 - α - α₀))) := by
  have hm : (2 : ℕ) = 0 ∨ (2 : ℕ) = 2 := Or.inr rfl
  have hD' : ∀ i : Fin 2, D i ≠ i ∧ D (D i) = i := mem_Pi2.1 hD
  rw [diagram_two_zero]
  unfold diag2
  rw [simplex_self hm, ← time_riesz_self hc hα hα0 ht]
  refine setLIntegral_congr_fun (measurableSet_pairSet (measurableSet_tri t)) fun s hs => ?_
  have e0 := (incr_self hm s).1
  have e1 := (incr_self hm s).2
  rw [timeWeight_two hD', spatial_riesz_self hm hc hα hD' (by rw [e0]; exact hs.1.le)
    (by rw [e1]; linarith [hs.2.1]), e0, e1]

/-- `P:riesz-small`, the `(0,2)` term: the same value as the `(2,0)` term. -/
theorem riesz_self_zero_two {D : Fin (0 + 2) → Fin (0 + 2)} (hD : D ∈ Pi2 0 2) {c α α₀ : ℝ}
    (hc : 0 ≤ c) (hα : α < 1) (hα0 : α₀ < 1) {t : ℝ} (ht : 0 ≤ t) :
    diagram (waveGreen 1) (riesz c α) α₀ 0 2 D t =
      ENNReal.ofReal (c * t ^ (4 - α - α₀) /
        ((1 - α) * (2 - α - α₀) * (3 - α - α₀) * (4 - α - α₀))) := by
  have hm : (0 : ℕ) = 0 ∨ (0 : ℕ) = 2 := Or.inl rfl
  have hD' : ∀ i : Fin 2, D i ≠ i ∧ D (D i) = i := mem_Pi2.1 hD
  rw [diagram_zero_two]
  unfold diag2
  rw [simplex_self hm, ← time_riesz_self hc hα hα0 ht]
  refine setLIntegral_congr_fun (measurableSet_pairSet (measurableSet_tri t)) fun s hs => ?_
  have e0 := (incr_self hm s).1
  have e1 := (incr_self hm s).2
  rw [timeWeight_two hD', spatial_riesz_self hm hc hα hD' (by rw [e0]; exact hs.1.le)
    (by rw [e1]; linarith [hs.2.1]), e0, e1]

/-- `P:riesz-small`, second formula of `E:riesz-two` on the model (main TeX lines
5135-5139, proof 5182-5189): the cross diagram `J_{1,1,D}(t)` equals
`c/((1-α)(2-α)) ∫_0^t v^{-α₀} [((2t-v)^{3-α} - v^{3-α})/(2(3-α)) - (t-v) v^{2-α}] dv`. -/
theorem riesz_cross {D : Fin (1 + 1) → Fin (1 + 1)} (hD : D ∈ Pi2 1 1) {c α α₀ : ℝ}
    (hc : 0 ≤ c) (hα : α < 1) (hα0 : α₀ < 1) {t : ℝ} (ht : 0 ≤ t) :
    diagram (waveGreen 1) (riesz c α) α₀ 1 1 D t =
      ENNReal.ofReal (c / ((1 - α) * (2 - α)) * ∫ v in (0 : ℝ)..t, v ^ (-α₀) * rbr t α v) := by
  have hD' : ∀ i : Fin 2, D i ≠ i ∧ D (D i) = i := mem_Pi2.1 hD
  rw [diagram_one_one]
  unfold diag2
  rw [simplex_cross, ← time_riesz_cross hc hα hα0 ht]
  refine setLIntegral_congr_fun
    (measurableSet_pairSet (measurableSet_Ioo.prod measurableSet_Ioo)) fun s hs => ?_
  rw [incr_cross, timeWeight_two hD', spatial_riesz_cross hc hα hD' hs.1.1.le hs.2.1.le]

/-- Auxiliary: the cross value of `E:riesz-two` is nonnegative. -/
theorem rieszCross_nonneg {c α α₀ : ℝ} (hc : 0 ≤ c) (hα : α < 1) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ c / ((1 - α) * (2 - α)) * ∫ v in (0 : ℝ)..t, v ^ (-α₀) * rbr t α v :=
  mul_nonneg (div_nonneg hc (mul_pos (by linarith) (by linarith)).le)
    (intervalIntegral.integral_nonneg ht fun v hv =>
      mul_nonneg (Real.rpow_nonneg hv.1 _) (rbr_nonneg hα hv.1 hv.2))

/-- Auxiliary: the self value of `E:riesz-two` is nonnegative. -/
theorem rieszSelf_nonneg {c α α₀ : ℝ} (hc : 0 ≤ c) (hα : α < 1) (hα0 : α₀ < 1) {t : ℝ}
    (ht : 0 ≤ t) :
    0 ≤ c * t ^ (4 - α - α₀) / ((1 - α) * (2 - α - α₀) * (3 - α - α₀) * (4 - α - α₀)) := by
  have : 0 < (1 - α) * (2 - α - α₀) * (3 - α - α₀) * (4 - α - α₀) := by
    have h1 : 0 < 1 - α := by linarith
    have h2 : 0 < 2 - α - α₀ := by linarith
    have h3 : 0 < 3 - α - α₀ := by linarith
    have h4 : 0 < 4 - α - α₀ := by linarith
    positivity
  exact div_nonneg (mul_nonneg hc (Real.rpow_nonneg ht _)) this.le

/-- `P:riesz-small`, "their total is `E X_1² + 2 E X_2`" (main TeX line 5142), on
the model: `A_1(t) = J_{1,1} + 2 J_{2,0}` for the Riesz density. -/
theorem riesz_coeffA_one {c α α₀ : ℝ} (hc : 0 ≤ c) (hα : α < 1) (hα0 : α₀ < 1) {t : ℝ}
    (ht : 0 ≤ t) :
    coeffA (waveGreen 1) (riesz c α) α₀ 1 t =
      ENNReal.ofReal ((c / ((1 - α) * (2 - α)) * ∫ v in (0 : ℝ)..t, v ^ (-α₀) * rbr t α v) +
        2 * (c * t ^ (4 - α - α₀) /
          ((1 - α) * (2 - α - α₀) * (3 - α - α₀) * (4 - α - α₀)))) := by
  have h1 := rieszCross_nonneg (α₀ := α₀) hc hα ht
  have h2 := rieszSelf_nonneg hc hα hα0 ht
  unfold coeffA
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    sum_Pi2_two (m := 0) (n := 2 * 1 - 0) (by norm_num)
      (fun D hD => riesz_self_zero_two hD hc hα hα0 ht),
    sum_Pi2_two (m := 1) (n := 2 * 1 - 1) (by norm_num) (fun D hD => riesz_cross hD hc hα hα0 ht),
    sum_Pi2_two (m := 2) (n := 2 * 1 - 2) (by norm_num)
      (fun D hD => riesz_self_two_zero hD hc hα hα0 ht),
    ← ENNReal.ofReal_add h2 h1, ← ENNReal.ofReal_add (add_nonneg h2 h1) h2]
  congr 1
  ring

/-! ### The lemmas as stated, through the supplied input `MixedMoment` -/

/-- `L:white-test` (main TeX lines 940-964) about the chaos terms, through the
supplied input `MixedMoment` (`P:mixed`): for `d = α = 1`, `γ = δ₀` (`H:homog`
for `Γ = δ₀`, from which only `α₀ < 1` is used), `X_0 = 1` (the TeX's
convention, line 796) and `t ≥ 0`:
`E X_1² = c_0 t^{3-α₀}`, `E X_2 = c_0 t^{3-α₀}/2`, and the total-order-two
contribution `Σ_{m=0}^{2} E[X_m X_{2-m}]` to `E:full-second` is `2 c_0 t^{3-α₀}`.
Narrower than the TeX by the split modelled-object rule: `X`, `u` are arbitrary
random variables tied to the diagrams only by `MixedMoment`. -/
theorem white_test_paper {α₀ : ℝ} {μ : Measure (Rd 1)}
    (hH : HomogHypothesis.HomogCovariance 1 1 α₀ (Measure.dirac 0) μ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ} {u : Ω → ℝ} {t : ℝ}
    (ht : 0 ≤ t) (hM : MixedMoment 1 α₀ (Measure.dirac 0) P X u t) (hX0 : ∀ ω, X 0 ω = 1) :
    ∫ ω, X 1 ω ^ 2 ∂P = c0 α₀ * t ^ (3 - α₀) ∧
      ∫ ω, X 2 ω ∂P = c0 α₀ / 2 * t ^ (3 - α₀) ∧
      ∑ m ∈ Finset.range 3, ∫ ω, X m ω * X (2 - m) ω ∂P = 2 * c0 α₀ * t ^ (3 - α₀) := by
  have hα0 := hH.alpha0_lt_one
  have hnn : 0 ≤ c0 α₀ * t ^ (3 - α₀) := mul_nonneg (c0_pos hα0).le (Real.rpow_nonneg ht _)
  refine ⟨?_, ?_, ?_⟩
  · simp_rw [sq]
    rw [(hM.2.1 1 1).2, sum_Pi2_two (by norm_num)
      (fun D hD => congrArg ENNReal.toReal (white_cross hD hα0 ht)), ENNReal.toReal_ofReal hnn]
  · have e : ∫ ω, X 2 ω ∂P = ∫ ω, X 2 ω * X 0 ω ∂P := by simp [hX0]
    rw [e, (hM.2.1 2 0).2, sum_Pi2_two (by norm_num)
      (fun D hD => congrArg ENNReal.toReal (white_self_two_zero hD hα0 ht)),
      ENNReal.toReal_ofReal (by linarith)]
  · have h := hM.coeffA_eq 1
    rw [white_coeffALim_one hα0 ht, ENNReal.toReal_ofReal (by linarith)] at h
    exact h.symm

/-- **Supplied input `RieszDiagramLimit`** (the identification, at total order
two, of the model's `J_{m,n,D}(t)` for the covariance measure
`Γ(dy) = c|y|^{-α} dy` with the literal diagram integral `E:mixed-diagram` with the
density `γ(y) = c|y|^{-α}`; main TeX lines 825-832 and `L:joint-fixed-order`,
lines 1853-1966).  `DiagramModel.MixedMoment` speaks of `diagramLim`, the limit as
the noise width `ε ↓ 0` of the diagrams with `p_ε * γ`; this input says that, for
`m + n = 2`, that limit is the unsmoothed integral.  TRUE for `c ≥ 0`,
`0 < α < 1` (`p_ε * γ → γ` off `0` with Gaussian-tail domination against the
bounded, compactly supported Green densities, and a time domination by
`sup_x ∫ γ(x + y) G_h(dy) ≤ c h^{1-α}/(1-α)`); not proved here.  Used only by
`riesz_small_paper`.  Proved in `RieszFourDiagrams.rieszDiagramLimit` for `c ≥ 0`,
`0 ≤ α < 1`, `0 ≤ α₀ < 1`, `t ≥ 0`. -/
def RieszDiagramLimit (c α α₀ t : ℝ) : Prop :=
  ∀ (m n : ℕ) (D : Fin (m + n) → Fin (m + n)), m + n = 2 → D ∈ Pi2 m n →
    diagramLim 1 (volume.withDensity (riesz c α)) α₀ m n D t =
      diagram (waveGreen 1) (riesz c α) α₀ m n D t

/-- `P:riesz-small`, the order-two part `E:riesz-two` (main TeX lines 5125-5142)
about the chaos terms, through the supplied inputs `MixedMoment` (`P:mixed`) and
`RieszDiagramLimit`: for `d = 1`, `0 < α < 1`, `0 < α₀ < 1`,
`γ(y) = c|y|^{-α}`, `c > 0`, `X_0 = 1`, `t ≥ 0`: `E X_2(t,x)` and `E X_1(t,x)²` are
the two displays of `E:riesz-two`, and the total `Σ_{m=0}^{2} E[X_m X_{2-m}]` is
`E X_1² + 2 E X_2`.  Narrower: the order-four representation `E:riesz-four` and
its finiteness are not formalized, and `X` is tied to the diagrams only by the
supplied inputs.  Carried but unused: `H:homog` (`hH`), `0 < α`, `0 < α₀`, and
`c > 0` beyond `c ≥ 0`. -/
theorem riesz_small_paper {c α α₀ : ℝ} {μ : Measure (Rd 1)}
    (_hH : HomogHypothesis.HomogCovariance 1 α α₀ (volume.withDensity (riesz c α)) μ)
    (hc : 0 < c) (_hα : 0 < α) (hα1 : α < 1) (_hα0 : 0 < α₀) (hα01 : α₀ < 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ} {u : Ω → ℝ} {t : ℝ}
    (ht : 0 ≤ t) (hM : MixedMoment 1 α₀ (volume.withDensity (riesz c α)) P X u t)
    (hL : RieszDiagramLimit c α α₀ t) (hX0 : ∀ ω, X 0 ω = 1) :
    ∫ ω, X 2 ω ∂P = c * t ^ (4 - α - α₀) /
        ((1 - α) * (2 - α - α₀) * (3 - α - α₀) * (4 - α - α₀)) ∧
      ∫ ω, X 1 ω ^ 2 ∂P =
        c / ((1 - α) * (2 - α)) * ∫ v in (0 : ℝ)..t, v ^ (-α₀) * rbr t α v ∧
      ∑ m ∈ Finset.range 3, ∫ ω, X m ω * X (2 - m) ω ∂P =
        ∫ ω, X 1 ω ^ 2 ∂P + 2 * ∫ ω, X 2 ω ∂P := by
  refine ⟨?_, ?_, ?_⟩
  · have e : ∫ ω, X 2 ω ∂P = ∫ ω, X 2 ω * X 0 ω ∂P := by simp [hX0]
    rw [e, (hM.2.1 2 0).2, sum_Pi2_two (by norm_num) (fun D hD => congrArg ENNReal.toReal
      ((hL 2 0 D rfl hD).trans (riesz_self_two_zero hD hc.le hα1 hα01 ht))),
      ENNReal.toReal_ofReal (rieszSelf_nonneg hc.le hα1 hα01 ht)]
  · simp_rw [sq]
    rw [(hM.2.1 1 1).2, sum_Pi2_two (by norm_num) (fun D hD => congrArg ENNReal.toReal
      ((hL 1 1 D rfl hD).trans (riesz_cross hD hc.le hα1 hα01 ht))),
      ENNReal.toReal_ofReal (rieszCross_nonneg hc.le hα1 ht)]
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [hX0, Nat.sub_zero, Nat.sub_self, one_mul, mul_one, sq,
      show 2 - 1 = 1 from rfl]
    ring

end StratonovichHAMSecondMoment.OrderTwoDiagrams
