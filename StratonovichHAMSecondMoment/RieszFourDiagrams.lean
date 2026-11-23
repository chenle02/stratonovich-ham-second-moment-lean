module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

The Riesz diagrams in `d = 1`: the order-two diagram limit and the order-four
unit-domain representation (wave L13 item D4, follow-up).  Main TeX file
`notes/notes_stratonovich_ham_second_moment.tex` at revision edf7085f:
* `P:riesz-small` (statement lines 5125-5172, proof 5174-5220): the order-two part
  `E:riesz-two` (lines 5129-5142; formalized in `OrderTwoDiagrams`), and the
  order-four part: the domain `H_m` (lines 5144-5150), the chain sums `S_l` and
  positions `Y_l` with `U_l` independent uniform on `[-1,1]` (lines 5150-5156),
  the representation `E:riesz-four` (lines 5157-5168), "a finite nonnegative
  integral" (line 5169), all five splits and all three pairings (lines
  5169-5171); proof of the representation lines 5199-5208, of finiteness lines
  5213-5219;
* the generalized-kernel and regularization conventions (lines 825-832) by which
  the TeX's `J` for the covariance measure `Γ(dy) = c|y|^{-α} dy` is the diagram
  with the density, and `L:joint-fixed-order` (lines 1853-1966);
* `A_k(t) = Σ_{m=0}^{2k} E[X_m X_{2k-m}]` (lines 5446-5451).

The objects are those of `DiagramModel` (not edited here): `diagram`,
`diagramLim`, `coeffA`; and of `OrderTwoDiagrams` (`riesz_small_paper`,
`RieszDiagramLimit`, `rbr`).

Formalized (all proved):
* `rieszDiagramLimit`: the former supplied input `RieszDiagramLimit c α α₀ t` of
  `OrderTwoDiagrams.riesz_small_paper` holds for `c ≥ 0`, `0 ≤ α < 1`,
  `0 ≤ α₀ < 1`, `t ≥ 0` (`tendsto_riesz_two`: the diagrams with
  `γ_ε = p_ε * Γ` converge to the density diagram at total order two).  Lean
  route (not the TeX's pointwise route `p_ε * γ → γ` off `0`): `γ_ε(x) =
  ∫ p_ε(z) γ(x - z) dz`, so the smoothed spatial part is a Gaussian average over
  shifts `z` of the spatial part with `γ(· - z)`; that function of `z` is
  continuous and bounded by the sup-convolution bound
  `sup_u ∫ c|u - y|^{-α} G_h(dy) ≤ c(2h)^{1-α}/(1-α)` (`rq_le`), so the average
  converges (`tendsto_heat_avg`, a rescaling and dominated convergence); the time
  integrals converge by dominated convergence with the integrable time weight
  (`tendsto_diagram_of_spatial`, `lintegral_twoSimplex_timeWeight_ne_top`);
* `riesz_small_paper'`: the successor of `OrderTwoDiagrams.riesz_small_paper` with
  `RieszDiagramLimit` discharged (only `MixedMoment` supplied);
* `diagram_riesz_eq`: `E:riesz-four` for every order (`m + n = 2k`):
  `J_{m,n,D}(t) = c^k t^{kβ} rieszUnit α α₀ m n D` for `c ≥ 0`, `t > 0`, with the
  unit-domain integral `rieszUnit` written as in the TeX (`hm` is `H_m`, `timePos`
  is `S`, `yPos` is `Y`, `unifLaw` is the uniform law); the proof follows the TeX
  (time increments with determinant one, `measurePreserving_incr`; spatial
  increments `h_l U_l`, `pi_waveGreen_eq_smul_map`; scaling by `t`,
  `lintegral_comp_smul_pos`);
* `diagram_riesz_ne_top`, `rieszUnit_ne_top`: finiteness for every order, for
  `0 ≤ α < 1`, `0 ≤ α₀ < 1`, as in the TeX (cube and box enlargement, Green
  indicators bounded, disjoint pair factors integrated one at a time,
  `lintegral_pi_matching_le`);
* `riesz_four` (`m + n = 4`: three pairings, the representation with `c^2 t^{2β}`,
  finiteness), `riesz_coeffA_two` (`A_2(t) = c^2 t^{2β} Σ_m Σ_D I_{m,D} < ∞`), and
  the wrapper `riesz_four_paper` with the TeX's hypotheses;
* `diagram_riesz_pos` (auxiliary, for non-vacuous refutations): `J_{m,n,D}(t) > 0`
  for `c > 0`, `α₀ ≥ 0`, `t > 0`.

Supplied inputs: only `DiagramModel.MixedMoment` (`P:mixed`; blocker D5 when this module was
written, discharged in wave L19 for the source-field chaos terms by
`SourceFinal.mixed_terms_l19`), in `riesz_small_paper'` (through `riesz_small_paper`).  Nothing
else.

Hypotheses: the diagram results need `c ≥ 0`, `0 ≤ α < 1`, `0 ≤ α₀ < 1` (broader
than the TeX's strict inequalities).  The wrappers carry the TeX's hypotheses:
`H:homog` is carried and unused in both; `0 < α`, `0 < α₀`, `c > 0` are used only
as `≥ 0`.

Readings and differences from the TeX:
* `U_l` uniform on `[-1,1]` is `unifLaw = G_1 = ½ 1_{|y|<1} dy` on `ℝ^1`
  (`map_e1_unifLaw`: in the coordinate it is `½ 1_{(-1,1)}(u) du`); `|Y_j - Y_q|` is
  the norm on `ℝ^1`; the time factor is the model's `timeWeight` (`|0|^{-α₀} = ∞`)
  and `|0|^{-α} = 0` in the spatial factor (null sets);
* `E:riesz-four` is stated on the model's density diagram `diagram (waveGreen 1)
  (riesz c α)` (the TeX's `J` for a density); at order four the identification of
  the measure-form limit `diagramLim` with it is NOT proved (only at order two,
  `rieszDiagramLimit`);
* the TeX's multiplicity form `E:total-four` (`2 Σ_D J_{0,4,D} + 2 Σ_D J_{1,3,D} +
  Σ_D J_{2,2,D}`, lines 4965-4969) needs the chain-swap symmetry
  `J_{m,n,D} = J_{n,m,D'}`, not formalized; `riesz_coeffA_two` is the plain sum over
  the five splits.

Not formalized, category per label:
* `P:riesz-small`: narrower.  Order two: the diagram values are whole on the model
  (`OrderTwoDiagrams`) and the identification with `E X_1²`, `E X_2` rests on the
  supplied input `MixedMoment` (split modelled-object rule; `RieszDiagramLimit` is
  now proved).  Order four: `E:riesz-four`, its finiteness, the five splits and three
  pairings are whole on the model's density diagrams; the multiplicity form and the
  order-four identification with the measure-form `diagramLim` are missing.
* `L:white-test`: unchanged (narrower, through `MixedMoment` only).

Lemmas marked "Auxiliary" serve only the Lean route.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.OrderTwoDiagrams

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace StratonovichHAMSecondMoment.RieszFourDiagrams

open HomogHypothesis (Rd)
open WaveGreen (waveGreen)
open VariationalMean (heatK heatK_pos)
open HigherRieszTwo (riesz lintegral_heatK)
open DiagramModel
open DiagramBridge (e1 e1_sub pred_eq_some_val)
open OrderTwoDiagrams

/-! ### A one-dimensional bound for the primitive `Φ` -/

/-- Auxiliary: `Φ(x) = x^{1-α}/(1-α)` for `x ≥ 0`. -/
theorem rPhi_of_nonneg {α : ℝ} (hα : α < 1) {x : ℝ} (hx : 0 ≤ x) :
    rPhi α x = x ^ (1 - α) / (1 - α) := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [rPhi, Real.zero_rpow (by linarith : (1 : ℝ) - α ≠ 0)]
  · unfold rPhi
    rw [abs_of_pos hx, show (1 : ℝ) - α = 1 + -α by ring, Real.rpow_add hx, Real.rpow_one]

/-- Auxiliary: `Φ(x) = -(-x)^{1-α}/(1-α)` for `x ≤ 0`. -/
theorem rPhi_of_nonpos {α : ℝ} (hα : α < 1) {x : ℝ} (hx : x ≤ 0) :
    rPhi α x = -((-x) ^ (1 - α)) / (1 - α) := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [rPhi, Real.zero_rpow (by linarith : (1 : ℝ) - α ≠ 0)]
  · unfold rPhi
    rw [abs_of_neg hx, show (1 : ℝ) - α = 1 + -α by ring, Real.rpow_add (by linarith),
      Real.rpow_one]
    ring

/-- Auxiliary: subadditivity of `x ↦ x^p` on `[0, ∞)` for `0 ≤ p ≤ 1`. -/
theorem rpow_add_le_add {p a b : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ p ≤ a ^ p + b ^ p := by
  have h' := NNReal.coe_le_coe.2 (NNReal.rpow_add_le_add_rpow a.toNNReal b.toNNReal hp hp1)
  simp only [NNReal.coe_rpow, NNReal.coe_add, Real.coe_toNNReal a ha,
    Real.coe_toNNReal b hb] at h'
  exact h'

/-- Auxiliary: `∫_x^y |u|^{-α} du = Φ(y) - Φ(x) ≤ 2 (y - x)^{1-α}/(1-α)` for
`x ≤ y` and `0 ≤ α < 1` (the integral of `|u|^{-α}` over an interval of length
`L` is at most twice its integral over `(0, L)`). -/
theorem rPhi_sub_le {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 1) {x y : ℝ} (hxy : x ≤ y) :
    rPhi α y - rPhi α x ≤ 2 * (y - x) ^ (1 - α) / (1 - α) := by
  have hp : 0 ≤ 1 - α := by linarith
  have hp1 : 1 - α ≤ 1 := by linarith
  have h1 : 0 < 1 - α := by linarith
  have h0 : 0 ≤ (y - x) ^ (1 - α) := Real.rpow_nonneg (sub_nonneg.2 hxy) _
  rcases le_total 0 x with hx | hx
  · rw [rPhi_of_nonneg hα (hx.trans hxy), rPhi_of_nonneg hα hx, ← sub_div]
    refine (div_le_div_iff_of_pos_right h1).2 ?_
    have := rpow_add_le_add hp hp1 hx (sub_nonneg.2 hxy)
    rw [add_sub_cancel] at this
    linarith
  · rcases le_total y 0 with hy | hy
    · rw [rPhi_of_nonpos hα hy, rPhi_of_nonpos hα hx, ← sub_div]
      refine (div_le_div_iff_of_pos_right h1).2 ?_
      have := rpow_add_le_add hp hp1 (neg_nonneg.2 hy) (sub_nonneg.2 hxy)
      rw [show -y + (y - x) = -x by ring] at this
      have h0' : 0 ≤ (-y) ^ (1 - α) := Real.rpow_nonneg (neg_nonneg.2 hy) _
      linarith
    · rw [rPhi_of_nonneg hα hy, rPhi_of_nonpos hα hx, ← sub_div]
      refine (div_le_div_iff_of_pos_right h1).2 ?_
      have a1 : y ^ (1 - α) ≤ (y - x) ^ (1 - α) := Real.rpow_le_rpow hy (by linarith) hp
      have a2 : (-x) ^ (1 - α) ≤ (y - x) ^ (1 - α) :=
        Real.rpow_le_rpow (by linarith) (by linarith) hp
      linarith

/-! ### The convolution `q_h(u) = ∫ G_h(dy) c|u - y|^{-α}` in `d = 1` -/

/-- Auxiliary: `e1 : ℝ^1 → ℝ` is continuous (an isometry). -/
theorem continuous_e1 : Continuous (e1 : Rd 1 → ℝ) := by
  refine (Isometry.of_dist_eq fun x y => ?_).continuous
  rw [Real.dist_eq, dist_eq_norm, norm_rd1, e1_sub]

/-- Auxiliary: `q_h(u) = ½ c (Φ(u + h) - Φ(u - h))`, the value of
`∫ G_h(dy) c|x - y|^{-α}` at `u = x` (`OrderTwoDiagrams.inner_riesz`). -/
def rq (c α h u : ℝ) : ℝ := 1 / 2 * (c * (rPhi α (u + h) - rPhi α (u - h)))

/-- Auxiliary: `q_h` is continuous. -/
theorem continuous_rq (c : ℝ) {α : ℝ} (hα : α < 1) (h : ℝ) : Continuous (rq c α h) :=
  continuous_const.mul (continuous_const.mul
    (((continuous_rPhi hα).comp (continuous_id.add continuous_const)).sub
      ((continuous_rPhi hα).comp (continuous_id.sub continuous_const))))

/-- Auxiliary: the sup-convolution bound `q_h(u) ≤ c (2h)^{1-α}/(1-α)` for every
shift `u` (the TeX's time domination `sup_x ∫ γ(x + y) G_h(dy)`). -/
theorem rq_le {c α : ℝ} (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα : α < 1) {h : ℝ} (hh : 0 ≤ h)
    (u : ℝ) : rq c α h u ≤ c * (2 * h) ^ (1 - α) / (1 - α) := by
  unfold rq
  have := rPhi_sub_le hα0 hα (show u - h ≤ u + h by linarith)
  rw [show u + h - (u - h) = 2 * h by ring] at this
  calc 1 / 2 * (c * (rPhi α (u + h) - rPhi α (u - h)))
      ≤ 1 / 2 * (c * (2 * (2 * h) ^ (1 - α) / (1 - α))) := by gcongr
    _ = c * (2 * h) ^ (1 - α) / (1 - α) := by ring

/-- Auxiliary: the ball integral `∫_{|y|<R} c|x - y|^{-α} dy ≤ 2 c (2R)^{1-α}/(1-α)`
for every `x`. -/
theorem lintegral_ball_riesz_le {c α : ℝ} (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα : α < 1) {R : ℝ}
    (hR : 0 ≤ R) (x : Rd 1) :
    ∫⁻ y in Metric.ball (0 : Rd 1) R, riesz c α (x - y) ≤
      ENNReal.ofReal (2 * (c * (2 * R) ^ (1 - α) / (1 - α))) := by
  have h := inner_riesz hc hα hR x
  rw [show waveGreen 1 R = ENNReal.ofReal (1 / 2) • volume.restrict (Metric.ball (0 : Rd 1) R)
    from rfl, lintegral_smul_measure, smul_eq_mul] at h
  have e : ∫⁻ y in Metric.ball (0 : Rd 1) R, riesz c α (x - y) =
      ENNReal.ofReal 2 * ENNReal.ofReal (rq c α R (e1 x)) := by
    rw [show rq c α R (e1 x) = 1 / 2 * (c * (rPhi α (e1 x + R) - rPhi α (e1 x - R))) from rfl,
      ← h, ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  rw [e, ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (rq_le hc hα0 hα hR _) (by norm_num))

/-- Auxiliary: the time integral `∫_0^t |a - b|^{-α₀} db ≤ 2 t^{1-α₀}/(1-α₀)` for
every `a` (`|0|^{-α₀}` is `∞` at the single point `b = a`). -/
theorem lintegral_timeCov_le {α₀ : ℝ} (h0 : 0 ≤ α₀) (h1 : α₀ < 1) {t : ℝ} (ht : 0 ≤ t) (a : ℝ) :
    ∫⁻ b in Ioo 0 t, timeCov α₀ a b ≤ ENNReal.ofReal (2 * t ^ (1 - α₀) / (1 - α₀)) := by
  have hne : ∀ᵐ b ∂(volume.restrict (Ioo (0 : ℝ) t)), b ≠ a :=
    ae_restrict_of_ae (ae_iff.2 (by simp))
  have hae : ∀ᵐ b ∂(volume.restrict (Ioo (0 : ℝ) t)),
      timeCov α₀ a b = ENNReal.ofReal (|a - b| ^ (-α₀)) := by
    filter_upwards [hne] with b hb
    rw [timeCov, ENNReal.ofReal_rpow_of_pos (abs_pos.2 (sub_ne_zero.2 hb.symm))]
  have hint : IntervalIntegrable (fun b => |a - b| ^ (-α₀)) volume 0 t := by
    simpa using (intervalIntegrable_abs_rpow h1 a (a - t)).comp_sub_left a
  rw [lintegral_congr_ae hae, lintegral_Ioo_ofReal ht hint
    (fun b _ => Real.rpow_nonneg (abs_nonneg _) _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e : ∫ b in (0 : ℝ)..t, |a - b| ^ (-α₀) = ∫ u in a - t..a, |u| ^ (-α₀) := by
    simpa using intervalIntegral.integral_comp_sub_left (fun u : ℝ => |u| ^ (-α₀)) a
      (a := 0) (b := t)
  rw [e, integral_abs_rpow h1]
  have := rPhi_sub_le h0 h1 (show a - t ≤ a by linarith)
  rwa [sub_sub_cancel] at this

/-! ### Products over a pairing: integrating out the closers -/

/-- Auxiliary: the closers `D(j)`, `j` an opener, are not openers. -/
theorem not_opener_of_opener {N : ℕ} {D : Fin N → Fin N} (hD : ∀ i, D i ≠ i ∧ D (D i) = i)
    {i : Fin N} (hi : i ∈ openers D) : D i ∉ openers D := by
  simp only [openers, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  rw [(hD i).2]
  exact not_lt.2 hi.le

/-- Auxiliary: every label is an opener or the partner of one. -/
theorem univ_eq_openers_union {N : ℕ} {D : Fin N → Fin N} (hD : ∀ i, D i ≠ i ∧ D (D i) = i) :
    (Finset.univ : Finset (Fin N)) = openers D ∪ (openers D).image D := by
  ext i
  simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_image, openers, Finset.mem_filter,
    true_and, true_iff]
  rcases lt_or_gt_of_ne (hD i).1.symm with h | h
  · exact Or.inl h
  · refine Or.inr ⟨D i, ?_, (hD i).2⟩
    rw [(hD i).2]
    exact h

/-- Auxiliary: the openers and the closers are disjoint. -/
theorem disjoint_openers_image {N : ℕ} {D : Fin N → Fin N} (hD : ∀ i, D i ≠ i ∧ D (D i) = i) :
    Disjoint (openers D) ((openers D).image D) := by
  rw [Finset.disjoint_left]
  intro i hi hi'
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hi'
  exact not_opener_of_opener hD hj hi

/-- Auxiliary: integrating the product `∏_{(j, D j)} f(x_j, x_{D j})` over a pairing
`D` against a product measure: if `∫ f(x, y) ν(dy) ≤ A` for every `x`, then
`∫ ∏_{(j, D j)} f(x_j, x_{D j}) ν^{⊗N}(dx) ≤ A^k ν(X)^k`, `k` the number of pairs.
(Integrate each closer `D j` first; it occurs only in its own factor.) -/
theorem lintegral_pi_matching_le {X : Type*} [MeasurableSpace X] (ν : Measure X) [SigmaFinite ν]
    {N : ℕ} {D : Fin N → Fin N} (hD : ∀ i, D i ≠ i ∧ D (D i) = i)
    {f : X → X → ℝ≥0∞} (hf : Measurable (Function.uncurry f)) {A : ℝ≥0∞}
    (hA : ∀ x, ∫⁻ y, f x y ∂ν ≤ A) :
    ∫⁻ x, ∏ i ∈ openers D, f (x i) (x (D i)) ∂Measure.pi (fun _ => ν) ≤
      A ^ (openers D).card * ν Set.univ ^ (openers D).card := by
  classical
  set O := openers D with hO
  set F : (Fin N → X) → ℝ≥0∞ := fun x => ∏ i ∈ O, f (x i) (x (D i)) with hF
  have hfi : ∀ i j : Fin N, Measurable fun x : Fin N → X => f (x i) (x j) := fun i j =>
    Measurable.comp (f := fun x : Fin N → X => (x i, x j)) hf
      ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
  have hFm : Measurable F := Finset.measurable_prod _ fun i _ => hfi i (D i)
  have hinj : ∀ a b : Fin N, D a = D b → a = b := fun a b h => by
    rw [← (hD a).2, ← (hD b).2, h]
  have claim : ∀ P : Finset (Fin N), P ⊆ O → ∀ x : Fin N → X,
      (∫⋯∫⁻_(P.image D), F ∂(fun _ => ν)) x ≤ A ^ P.card * ∏ i ∈ O \ P, f (x i) (x (D i)) := by
    intro P
    induction P using Finset.induction_on with
    | empty => intro _ x; simp [hF]
    | insert a P ha ih =>
      intro hsub x
      have haO : a ∈ O := hsub (Finset.mem_insert_self a P)
      have hPO : P ⊆ O := fun i hi => hsub (Finset.mem_insert_of_mem hi)
      have hDa : D a ∉ P.image D := by
        intro h
        obtain ⟨b, hb, hba⟩ := Finset.mem_image.1 h
        exact ha (hinj b a hba ▸ hb)
      rw [Finset.image_insert, lmarginal_insert F hFm hDa x]
      have hsplit : O \ P = insert a (O \ insert a P) := by
        ext i
        simp only [Finset.mem_sdiff, Finset.mem_insert]
        constructor
        · rintro ⟨hi, hiP⟩
          by_cases h : i = a
          · exact Or.inl h
          · exact Or.inr ⟨hi, fun h' => h'.elim h hiP⟩
        · rintro (rfl | ⟨hi, hiP⟩)
          · exact ⟨haO, ha⟩
          · exact ⟨hi, fun h' => hiP (Or.inr h')⟩
      have hanot : a ∉ O \ insert a P := by simp
      set R := ∏ i ∈ O \ insert a P, f (x i) (x (D i)) with hR
      have hpt : ∀ y : X, (∫⋯∫⁻_(P.image D), F ∂(fun _ => ν)) (Function.update x (D a) y) ≤
          A ^ P.card * R * f (x a) y := by
        intro y
        refine (ih hPO _).trans (le_of_eq ?_)
        rw [hsplit, Finset.prod_insert hanot]
        have hxa : Function.update x (D a) y a = x a :=
          Function.update_of_ne (hD a).1.symm _ _
        have hxDa : Function.update x (D a) y (D a) = y := Function.update_self _ _ _
        rw [hxa, hxDa]
        have hrest : ∏ i ∈ O \ insert a P,
            f (Function.update x (D a) y i) (Function.update x (D a) y (D i)) = R := by
          refine Finset.prod_congr rfl fun i hi => ?_
          have hiO : i ∈ O := (Finset.mem_sdiff.1 hi).1
          have hia : i ≠ a := fun h => (Finset.mem_sdiff.1 hi).2 (h ▸ Finset.mem_insert_self _ _)
          have h1 : i ≠ D a := fun h => not_opener_of_opener hD haO (h ▸ hiO)
          have h2 : D i ≠ D a := fun h => hia (hinj _ _ h)
          rw [Function.update_of_ne h1, Function.update_of_ne h2]
        rw [hrest]
        ring
      calc ∫⁻ y, (∫⋯∫⁻_(P.image D), F ∂(fun _ => ν)) (Function.update x (D a) y) ∂ν
          ≤ ∫⁻ y, A ^ P.card * R * f (x a) y ∂ν := lintegral_mono hpt
        _ = A ^ P.card * R * ∫⁻ y, f (x a) y ∂ν :=
            lintegral_const_mul _ (hf.comp (measurable_const.prodMk measurable_id))
        _ ≤ A ^ P.card * R * A := by gcongr; exact hA _
        _ = A ^ (insert a P).card * R := by rw [Finset.card_insert_of_notMem ha, pow_succ]; ring
  rcases isEmpty_or_nonempty (Fin N → X) with hE | ⟨⟨x0⟩⟩
  · simp [lintegral_of_isEmpty]
  rw [lintegral_eq_lmarginal_univ x0, univ_eq_openers_union hD,
    lmarginal_union _ F hFm (disjoint_openers_image hD)]
  calc (∫⋯∫⁻_O, ∫⋯∫⁻_(O.image D), F ∂(fun _ => ν) ∂(fun _ => ν)) x0
      ≤ (∫⋯∫⁻_O, (fun _ => A ^ O.card) ∂(fun _ => ν)) x0 := by
        refine lmarginal_mono (fun x => ?_) x0
        refine (claim O subset_rfl x).trans (le_of_eq ?_)
        simp
    _ = A ^ O.card * ν Set.univ ^ O.card := by
        simp only [lmarginal, lintegral_const, Measure.pi_univ, Finset.prod_const,
          Finset.card_univ, Fintype.card_coe]

/-! ### The smoothed Riesz covariance -/

/-- Auxiliary: the smoothed covariance of the measure `volume.withDensity (riesz c α)`
(density `ofReal(c|y|^{-α})`) is `x ↦ ∫ ofReal(p_ε(z)) riesz c α (x - z) dz`, that is
`γ_ε(x) = ∫ p_ε(z) c|x - z|^{-α} dz` for `c > 0`. -/
theorem covEps_riesz (c α ε : ℝ) (x : Rd 1) :
    covEps ((volume : Measure (Rd 1)).withDensity (riesz c α)) ε x =
      ∫⁻ z, ENNReal.ofReal (heatK ε z) * riesz c α (x - z) := by
  rw [← HigherRieszTwo.smoothCov_eq]
  unfold covEps HigherRieszTwo.smoothCov
  have hg : Measurable fun z : Rd 1 => ENNReal.ofReal (LowAlphaConvolution.heatDens ε (x - z)) :=
    ((HigherRieszTwo.measurable_heatK ε).comp (measurable_const.sub measurable_id)).ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_riesz c α) hg]
  refine lintegral_congr fun y => ?_
  simp only [Pi.mul_apply]
  rw [mul_comm]
  rfl

/-- Auxiliary: the smoothed Riesz covariance is measurable. -/
theorem measurable_covEps_riesz (c α ε : ℝ) :
    Measurable (covEps ((volume : Measure (Rd 1)).withDensity (riesz c α)) ε) := by
  have : covEps ((volume : Measure (Rd 1)).withDensity (riesz c α)) ε =
      HigherRieszTwo.smoothCov (riesz c α) ε := by
    funext x; rw [covEps_riesz, HigherRieszTwo.smoothCov_eq]
  rw [this]
  exact HigherRieszTwo.measurable_smoothCov (measurable_riesz c α) ε

/-- Auxiliary: for a pairing of two labels, the spatial part with `γ_ε = p_ε * γ`
is the `p_ε`-average over shifts `z` of the spatial parts with `γ(· - z)`. -/
theorem spatial_covEps_riesz {m : ℕ} {D : Fin 2 → Fin 2} (hD : ∀ i, D i ≠ i ∧ D (D i) = i)
    (c α ε : ℝ) (h : Fin 2 → ℝ) :
    spatial (waveGreen 1) (covEps ((volume : Measure (Rd 1)).withDensity (riesz c α)) ε) m D h =
      ∫⁻ z, ENNReal.ofReal (heatK ε z) *
        spatial (waveGreen 1) (fun x => riesz c α (x - z)) m D h := by
  unfold spatial
  simp_rw [covWeight_two hD, covEps_riesz]
  rw [lintegral_lintegral_swap]
  · refine lintegral_congr fun z => ?_
    rw [lintegral_const_mul]
    exact (measurable_riesz c α).comp
      (((measurable_pos m 0).sub (measurable_pos m 1)).sub_const z)
  · exact (((HigherRieszTwo.measurable_heatK ε).comp measurable_snd).ennreal_ofReal.mul
      ((measurable_riesz c α).comp ((((measurable_pos m 0).comp measurable_fst).sub
        ((measurable_pos m 1).comp measurable_fst)).sub measurable_snd))).aemeasurable

/-- Auxiliary: the shifted spatial part of one chain of length two. -/
theorem spatial_shift_self {m : ℕ} (hm : m = 0 ∨ m = 2) {c α : ℝ} (hc : 0 ≤ c) (hα : α < 1)
    {D : Fin 2 → Fin 2} (hD : ∀ i, D i ≠ i ∧ D (D i) = i) {h : Fin 2 → ℝ} (h0 : 0 ≤ h 0)
    (h1 : 0 ≤ h 1) (z : Rd 1) :
    spatial (waveGreen 1) (fun x => riesz c α (x - z)) m D h =
      ENNReal.ofReal (h 0) * ENNReal.ofReal (rq c α (h 1) (-e1 z)) := by
  unfold spatial
  have e : ∀ w : Fin 2 → Rd 1, covWeight (fun x => riesz c α (x - z)) D (pos m w) =
      riesz c α (-z - w 1) := fun w => by
    rw [covWeight_two hD, (pos_self hm w).1, (pos_self hm w).2]
    congr 1
    abel
  simp_rw [e]
  have hg : Measurable fun p : Rd 1 × Rd 1 => riesz c α (-z - p.2) :=
    (measurable_riesz c α).comp (measurable_const.sub measurable_snd)
  rw [pi_waveGreen_two h, lintegral_pi_two (g := fun p : Rd 1 × Rd 1 => riesz c α (-z - p.2))
    _ _ hg]
  simp only
  rw [lintegral_const, inner_riesz hc hα h1, WaveGreen.waveGreen_mass 1 (Or.inl rfl) _ h0,
    mul_comm, e1_neg]
  rfl

/-- Auxiliary: the shifted spatial part of two chains of length one. -/
theorem spatial_shift_cross {c α : ℝ} (hc : 0 ≤ c) (hα : α < 1) {D : Fin 2 → Fin 2}
    (hD : ∀ i, D i ≠ i ∧ D (D i) = i) {h : Fin 2 → ℝ} (h1 : 0 ≤ h 1) (z : Rd 1) :
    spatial (waveGreen 1) (fun x => riesz c α (x - z)) 1 D h =
      ∫⁻ x, ENNReal.ofReal (rq c α (h 1) (e1 x - e1 z)) ∂waveGreen 1 (h 0) := by
  unfold spatial
  have e : ∀ w : Fin 2 → Rd 1, covWeight (fun x => riesz c α (x - z)) D (pos 1 w) =
      riesz c α ((w 0 - z) - w 1) := fun w => by
    rw [covWeight_two hD, (pos_cross w).1, (pos_cross w).2]
    congr 1
    abel
  simp_rw [e]
  have hg : Measurable fun p : Rd 1 × Rd 1 => riesz c α ((p.1 - z) - p.2) :=
    (measurable_riesz c α).comp ((measurable_fst.sub_const z).sub measurable_snd)
  rw [pi_waveGreen_two h, lintegral_pi_two
    (g := fun p : Rd 1 × Rd 1 => riesz c α ((p.1 - z) - p.2)) _ _ hg]
  simp only
  refine lintegral_congr fun x => ?_
  rw [inner_riesz hc hα h1, e1_sub]
  rfl

/-! ### The Gaussian average of a bounded function continuous at `0` -/

/-- Auxiliary: `∫ p_ε(z) F(z) dz → F(0)` as `ε ↓ 0` for a measurable `F ≤ B < ∞`
continuous at `0` (rescale `z = √ε w` and use dominated convergence against
`B p_1`). -/
theorem tendsto_heat_avg {F : Rd 1 → ℝ≥0∞} (hFm : Measurable F) {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (hFB : ∀ z, F z ≤ B) (hF0 : Tendsto F (𝓝 0) (𝓝 (F 0))) :
    Tendsto (fun ε => ∫⁻ z, ENNReal.ofReal (heatK ε z) * F z) (𝓝[>] 0) (𝓝 (F 0)) := by
  have hK1 : Measurable fun w : Rd 1 => ENNReal.ofReal (heatK 1 w) :=
    (HigherRieszTwo.measurable_heatK 1).ennreal_ofReal
  have key : ∀ ε : ℝ, 0 < ε → ∫⁻ z, ENNReal.ofReal (heatK ε z) * F z =
      ∫⁻ w, ENNReal.ofReal (heatK 1 w) * F (Real.sqrt ε • w) := by
    intro ε hε
    have ha0 : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
    have hmeas : Measurable fun z : Rd 1 =>
        ENNReal.ofReal (heatK 1 ((Real.sqrt ε)⁻¹ • z)) * F z :=
      ((HigherRieszTwo.measurable_heatK 1).comp (measurable_const_smul _)).ennreal_ofReal.mul hFm
    have hmap := lintegral_map hmeas (measurable_const_smul (Real.sqrt ε))
      (μ := (volume : Measure (Rd 1)))
    rw [Measure.map_addHaar_smul _ ha0.ne', lintegral_smul_measure] at hmap
    simp only [smul_smul, inv_mul_cancel₀ ha0.ne', one_smul, finrank_euclideanSpace,
      Fintype.card_fin, pow_one, smul_eq_mul] at hmap
    rw [← hmap, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun z => ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos (inv_pos.2 ha0),
      HigherRieszTwo.heatK_scale hε z, pow_one]
  have hlim : Tendsto (fun ε => ∫⁻ w : Rd 1, ENNReal.ofReal (heatK 1 w) * F (Real.sqrt ε • w))
      (𝓝[>] 0) (𝓝 (∫⁻ w : Rd 1, ENNReal.ofReal (heatK 1 w) * F 0)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence
      (fun w : Rd 1 => ENNReal.ofReal (heatK 1 w) * B)
      (Eventually.of_forall fun ε => hK1.mul (hFm.comp (measurable_const_smul _)))
      (Eventually.of_forall fun ε => Eventually.of_forall fun w => by gcongr; exact hFB _)
      ?_ (Eventually.of_forall fun w => ?_)
    · rw [lintegral_mul_const _ hK1, lintegral_heatK one_pos, one_mul]
      exact hB
    · refine ENNReal.Tendsto.const_mul (hF0.comp ?_) (Or.inr ENNReal.ofReal_ne_top)
      have hc : Continuous fun ε : ℝ => Real.sqrt ε • w := by fun_prop
      have h := hc.tendsto 0
      simp only [Real.sqrt_zero, zero_smul] at h
      exact h.mono_left nhdsWithin_le_nhds
  rw [lintegral_mul_const _ hK1, lintegral_heatK one_pos, one_mul] at hlim
  exact hlim.congr' (eventually_nhdsWithin_of_forall fun ε hε => (key ε hε).symm)

/-- Auxiliary: a Gaussian average of a function bounded by `B` is bounded by `B`. -/
theorem heat_avg_le {F : Rd 1 → ℝ≥0∞} {B : ℝ≥0∞} (hFB : ∀ z, F z ≤ B) {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ z, ENNReal.ofReal (heatK ε z) * F z ≤ B := by
  calc ∫⁻ z, ENNReal.ofReal (heatK ε z) * F z ≤ ∫⁻ z, ENNReal.ofReal (heatK ε z) * B :=
        lintegral_mono fun z => by gcongr; exact hFB z
    _ = B := by
        rw [lintegral_mul_const _ (HigherRieszTwo.measurable_heatK ε).ennreal_ofReal,
          lintegral_heatK hε, one_mul]

/-! ### The time integrals of the pairing weight -/

/-- Auxiliary: in the time simplices every time increment is below `t`. -/
theorem incr_lt_of_mem {m n : ℕ} {t : ℝ} {s : Fin (m + n) → ℝ} (hs : s ∈ twoSimplex m n t)
    (i : Fin (m + n)) : incr m s i < t := by
  have h0 : 0 ≤ predVal m s i := by
    rcases hp : pred m i with _ | j
    · rw [predVal_of_none m s i hp]
    · rw [predVal_of_some m s i j hp]; exact (pos_of_mem_twoSimplex hs j).le
  unfold incr
  linarith [(hs i).2]

/-- Auxiliary: the time simplices lie in the cube `(0, t)^N`. -/
theorem twoSimplex_subset_cube (m n : ℕ) (t : ℝ) :
    twoSimplex m n t ⊆ Set.univ.pi fun _ => Ioo (0 : ℝ) t :=
  fun _ hs i _ => ⟨pos_of_mem_twoSimplex hs i, (hs i).2⟩

/-- The pairing time weight is integrable over the cube `(0, t)^N`:
`∫_{(0,t)^N} ∏_{(j,h) ∈ D} |s_j - s_h|^{-α₀} ds ≤ (2 t^{2-α₀}/(1-α₀))^k` (main TeX
line 5215: "the two time covariance factors involve disjoint pairs and are
integrable since `α₀ < 1`", here for every number of pairs). -/
theorem lintegral_cube_timeWeight_le {α₀ : ℝ} (h0 : 0 ≤ α₀) (h1 : α₀ < 1) {t : ℝ} (ht : 0 ≤ t)
    {N : ℕ} {D : Fin N → Fin N} (hD : ∀ i, D i ≠ i ∧ D (D i) = i) :
    ∫⁻ s in Set.univ.pi (fun _ : Fin N => Ioo (0 : ℝ) t), timeWeight α₀ D s ≤
      ENNReal.ofReal (2 * t ^ (1 - α₀) / (1 - α₀)) ^ (openers D).card *
        ENNReal.ofReal t ^ (openers D).card := by
  rw [MeasureTheory.volume_pi, Measure.restrict_pi_pi]
  refine (lintegral_pi_matching_le _ hD (measurable_timeCov α₀)
    (lintegral_timeCov_le h0 h1 ht)).trans (le_of_eq ?_)
  rw [Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero]

/-- Auxiliary: the time integral of the pairing weight over the time simplices is
finite. -/
theorem lintegral_twoSimplex_timeWeight_ne_top {α₀ : ℝ} (h0 : 0 ≤ α₀) (h1 : α₀ < 1) {t : ℝ}
    (ht : 0 ≤ t) {m n : ℕ} {D : Fin (m + n) → Fin (m + n)} (hD : ∀ i, D i ≠ i ∧ D (D i) = i) :
    ∫⁻ s in twoSimplex m n t, timeWeight α₀ D s ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ ((lintegral_mono_set (twoSimplex_subset_cube m n t)).trans
    (lintegral_cube_timeWeight_le h0 h1 ht hD))
  exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

/-- Auxiliary: dominated convergence of the diagrams in the time variables: if the
spatial parts are bounded by `K` on the time simplices and converge there, the
diagrams converge. -/
theorem tendsto_diagram_of_spatial {m n : ℕ} {D : Fin (m + n) → Fin (m + n)} {α₀ t : ℝ}
    {γε : ℝ → Rd 1 → ℝ≥0∞} {γ : Rd 1 → ℝ≥0∞} (hγε : ∀ ε, 0 < ε → Measurable (γε ε))
    {K : ℝ≥0∞} (hK : K ≠ ⊤) (hfin : ∫⁻ s in twoSimplex m n t, timeWeight α₀ D s ≠ ⊤)
    (hle : ∀ ε, 0 < ε → ∀ s ∈ twoSimplex m n t,
      spatial (waveGreen 1) (γε ε) m D (incr m s) ≤ K)
    (hlim : ∀ s ∈ twoSimplex m n t, Tendsto (fun ε => spatial (waveGreen 1) (γε ε) m D (incr m s))
      (𝓝[>] 0) (𝓝 (spatial (waveGreen 1) γ m D (incr m s)))) :
    Tendsto (fun ε => diagram (waveGreen 1) (γε ε) α₀ m n D t) (𝓝[>] 0)
      (𝓝 (diagram (waveGreen 1) γ α₀ m n D t)) := by
  have hT := measurableSet_twoSimplex m n t
  have hW := measurable_timeWeight α₀ D
  have hae : ∀ᵐ s ∂(volume.restrict (twoSimplex m n t)), timeWeight α₀ D s < ⊤ :=
    ae_lt_top hW hfin
  refine tendsto_lintegral_filter_of_dominated_convergence (fun s => timeWeight α₀ D s * K)
    (eventually_nhdsWithin_of_forall fun ε hε =>
      hW.mul ((measurable_spatial_one (hγε ε hε) m D).comp (measurable_incr m)))
    (eventually_nhdsWithin_of_forall fun ε hε => (ae_restrict_iff' hT).2
      (Eventually.of_forall fun s hs => by gcongr; exact hle ε hε s hs)) ?_ ?_
  · rw [lintegral_mul_const _ hW]
    exact ENNReal.mul_ne_top hfin hK
  · filter_upwards [hae, ae_restrict_mem hT] with s hs hsT
    exact ENNReal.Tendsto.const_mul (hlim s hsT) (Or.inr hs.ne)

/-! ### `RieszDiagramLimit` at total order two -/

/-- Auxiliary: the uniform bound of the order-two Riesz spatial parts. -/
def rieszBound (c α t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal t * ENNReal.ofReal (c * (2 * t) ^ (1 - α) / (1 - α))

/-- Auxiliary: monotonicity of the order-two bound in the increments. -/
theorem rieszBound_mono {c α : ℝ} (hc : 0 ≤ c) (hα : α < 1) {a b t : ℝ} (hat : a ≤ t)
    (hb : 0 ≤ b) (hbt : b ≤ t) :
    ENNReal.ofReal a * ENNReal.ofReal (c * (2 * b) ^ (1 - α) / (1 - α)) ≤ rieszBound c α t := by
  have h1 : 0 < 1 - α := by linarith
  have hp : (2 * b) ^ (1 - α) ≤ (2 * t) ^ (1 - α) :=
    Real.rpow_le_rpow (by linarith) (by linarith) h1.le
  unfold rieszBound
  gcongr

/-- Auxiliary: the smoothed Riesz spatial parts of one chain of length two converge
and are bounded. -/
theorem spatial_riesz_self_lim {m : ℕ} (hm : m = 0 ∨ m = 2) {c α : ℝ} (hc : 0 ≤ c)
    (hα0 : 0 ≤ α) (hα : α < 1) {D : Fin 2 → Fin 2} (hD : ∀ i, D i ≠ i ∧ D (D i) = i)
    {h : Fin 2 → ℝ} (h0 : 0 ≤ h 0) (h1 : 0 ≤ h 1) :
    Tendsto (fun ε => spatial (waveGreen 1)
        (covEps ((volume : Measure (Rd 1)).withDensity (riesz c α)) ε) m D h) (𝓝[>] 0)
        (𝓝 (spatial (waveGreen 1) (riesz c α) m D h)) ∧
      ∀ ε, 0 < ε → spatial (waveGreen 1)
        (covEps ((volume : Measure (Rd 1)).withDensity (riesz c α)) ε) m D h ≤
          ENNReal.ofReal (h 0) * ENNReal.ofReal (c * (2 * h 1) ^ (1 - α) / (1 - α)) := by
  have hF := spatial_shift_self hm hc hα hD h0 h1
  have h00 : spatial (waveGreen 1) (riesz c α) m D h =
      ENNReal.ofReal (h 0) * ENNReal.ofReal (rq c α (h 1) (-e1 0)) := by
    rw [← hF 0]
    simp_rw [sub_zero]
  have hB : ∀ z : Rd 1, ENNReal.ofReal (h 0) * ENNReal.ofReal (rq c α (h 1) (-e1 z)) ≤
      ENNReal.ofReal (h 0) * ENNReal.ofReal (c * (2 * h 1) ^ (1 - α) / (1 - α)) := fun z => by
    gcongr
    exact rq_le hc hα0 hα h1 _
  have hcont : Continuous fun z : Rd 1 =>
      ENNReal.ofReal (h 0) * ENNReal.ofReal (rq c α (h 1) (-e1 z)) :=
    ENNReal.continuous_const_mul ENNReal.ofReal_ne_top |>.comp
      (ENNReal.continuous_ofReal.comp ((continuous_rq c hα _).comp continuous_e1.neg))
  simp_rw [spatial_covEps_riesz hD, hF]
  refine ⟨?_, fun ε hε => heat_avg_le hB hε⟩
  rw [h00]
  exact tendsto_heat_avg hcont.measurable
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hB (hcont.tendsto 0)

/-- Auxiliary: the smoothed Riesz spatial parts of two chains of length one converge
and are bounded. -/
theorem spatial_riesz_cross_lim {c α : ℝ} (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα : α < 1)
    {D : Fin 2 → Fin 2} (hD : ∀ i, D i ≠ i ∧ D (D i) = i) {h : Fin 2 → ℝ} (h0 : 0 ≤ h 0)
    (h1 : 0 ≤ h 1) :
    Tendsto (fun ε => spatial (waveGreen 1)
        (covEps ((volume : Measure (Rd 1)).withDensity (riesz c α)) ε) 1 D h) (𝓝[>] 0)
        (𝓝 (spatial (waveGreen 1) (riesz c α) 1 D h)) ∧
      ∀ ε, 0 < ε → spatial (waveGreen 1)
        (covEps ((volume : Measure (Rd 1)).withDensity (riesz c α)) ε) 1 D h ≤
          ENNReal.ofReal (h 0) * ENNReal.ofReal (c * (2 * h 1) ^ (1 - α) / (1 - α)) := by
  have hF := spatial_shift_cross hc hα hD h1
  set G : Rd 1 → ℝ≥0∞ := fun z =>
    ∫⁻ x, ENNReal.ofReal (rq c α (h 1) (e1 x - e1 z)) ∂waveGreen 1 (h 0) with hG
  have h00 : spatial (waveGreen 1) (riesz c α) 1 D h = G 0 := by
    simp only [hG]
    rw [← hF 0]
    simp_rw [sub_zero]
  set Bq := c * (2 * h 1) ^ (1 - α) / (1 - α) with hBq
  have hqc : Continuous fun p : Rd 1 × Rd 1 => rq c α (h 1) (e1 p.2 - e1 p.1) :=
    (continuous_rq c hα _).comp ((continuous_e1.comp continuous_snd).sub
      (continuous_e1.comp continuous_fst))
  have hGm : Measurable G :=
    (ENNReal.measurable_ofReal.comp hqc.measurable).lintegral_prod_right'
  have hB : ∀ z, G z ≤ ENNReal.ofReal (h 0) * ENNReal.ofReal Bq := fun z => by
    calc G z ≤ ∫⁻ _, ENNReal.ofReal Bq ∂waveGreen 1 (h 0) :=
          lintegral_mono fun x => ENNReal.ofReal_le_ofReal (rq_le hc hα0 hα h1 _)
      _ = ENNReal.ofReal (h 0) * ENNReal.ofReal Bq := by
          rw [lintegral_const, WaveGreen.waveGreen_mass 1 (Or.inl rfl) _ h0, mul_comm]
  have hG0 : Tendsto G (𝓝 0) (𝓝 (G 0)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence (fun _ => ENNReal.ofReal Bq)
      (Eventually.of_forall fun z => ENNReal.measurable_ofReal.comp
        ((continuous_rq c hα _).comp (continuous_e1.sub continuous_const)).measurable)
      (Eventually.of_forall fun z => Eventually.of_forall fun x =>
        ENNReal.ofReal_le_ofReal (rq_le hc hα0 hα h1 _)) ?_
      (Eventually.of_forall fun x => ?_)
    · rw [lintegral_const]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
    · have hc' : Continuous fun z : Rd 1 => ENNReal.ofReal (rq c α (h 1) (e1 x - e1 z)) :=
        ENNReal.continuous_ofReal.comp ((continuous_rq c hα _).comp
          (continuous_const.sub continuous_e1))
      exact hc'.tendsto 0
  simp_rw [spatial_covEps_riesz hD, hF]
  refine ⟨?_, fun ε hε => heat_avg_le hB hε⟩
  rw [h00]
  exact tendsto_heat_avg hGm (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    hB hG0

/-- `RieszDiagramLimit` holds (the supplied input of `OrderTwoDiagrams.riesz_small_paper`,
now proved): at total order two, the model's `J_{m,n,D}(t)` for the covariance
measure `Γ(dy) = c|y|^{-α} dy` (`diagramLim`, the `ε ↓ 0` limit with
`γ_ε = p_ε * Γ`) equals the diagram with the density `γ(y) = c|y|^{-α}`, for
`c ≥ 0`, `0 ≤ α < 1`, `0 ≤ α₀ < 1`, `t ≥ 0` (main TeX lines 825-832: the
regularization convention; the TeX's `J` for a density is the density diagram).
Lean route: `γ_ε(x) = ∫ p_ε(z) γ(x - z) dz`, so the smoothed spatial part is the
`p_ε`-average over shifts `z` of the spatial part with `γ(· - z)`; that function of
`z` is continuous and bounded by `sup_x ∫ γ(x + y) G_h(dy) ≤ c(2h)^{1-α}/(1-α)`, so
the Gaussian average converges to its value at `z = 0`; the time integrals converge
by dominated convergence with the integrable time weight. -/
theorem tendsto_riesz_two {c α α₀ t : ℝ} (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα : α < 1)
    (h0 : 0 ≤ α₀) (h1 : α₀ < 1) (ht : 0 ≤ t) {m n : ℕ} (hmn : m + n = 2)
    {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n) :
    Tendsto (fun ε => diagram (waveGreen 1)
        (covEps ((volume : Measure (Rd 1)).withDensity (riesz c α)) ε) α₀ m n D t) (𝓝[>] 0)
      (𝓝 (diagram (waveGreen 1) (riesz c α) α₀ m n D t)) := by
  have hD' := mem_Pi2.1 hD
  have hK : rieszBound c α t ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hfin := lintegral_twoSimplex_timeWeight_ne_top h0 h1 ht hD'
  have hmeas : ∀ ε, 0 < ε →
      Measurable (covEps ((volume : Measure (Rd 1)).withDensity (riesz c α)) ε) :=
    fun ε _ => measurable_covEps_riesz c α ε
  have hle0 : m ≤ 2 := by omega
  interval_cases m
  · obtain rfl : n = 2 := by omega
    refine tendsto_diagram_of_spatial hmeas hK hfin (fun ε hε s hs => ?_) (fun s hs => ?_)
    · exact ((spatial_riesz_self_lim (Or.inl rfl) hc hα0 hα hD' (incr_pos hs 0).le
        (incr_pos hs 1).le).2 ε hε).trans (rieszBound_mono hc hα
          (incr_lt_of_mem hs 0).le (incr_pos hs 1).le (incr_lt_of_mem hs 1).le)
    · exact (spatial_riesz_self_lim (Or.inl rfl) hc hα0 hα hD' (incr_pos hs 0).le
        (incr_pos hs 1).le).1
  · obtain rfl : n = 1 := by omega
    refine tendsto_diagram_of_spatial hmeas hK hfin (fun ε hε s hs => ?_) (fun s hs => ?_)
    · exact ((spatial_riesz_cross_lim hc hα0 hα hD' (incr_pos hs 0).le
        (incr_pos hs 1).le).2 ε hε).trans (rieszBound_mono hc hα
          (incr_lt_of_mem hs 0).le (incr_pos hs 1).le (incr_lt_of_mem hs 1).le)
    · exact (spatial_riesz_cross_lim hc hα0 hα hD' (incr_pos hs 0).le (incr_pos hs 1).le).1
  · obtain rfl : n = 0 := by omega
    refine tendsto_diagram_of_spatial hmeas hK hfin (fun ε hε s hs => ?_) (fun s hs => ?_)
    · exact ((spatial_riesz_self_lim (Or.inr rfl) hc hα0 hα hD' (incr_pos hs 0).le
        (incr_pos hs 1).le).2 ε hε).trans (rieszBound_mono hc hα
          (incr_lt_of_mem hs 0).le (incr_pos hs 1).le (incr_lt_of_mem hs 1).le)
    · exact (spatial_riesz_self_lim (Or.inr rfl) hc hα0 hα hD' (incr_pos hs 0).le
        (incr_pos hs 1).le).1

/-- **`RieszDiagramLimit` is proved** (it was a supplied input of
`OrderTwoDiagrams.riesz_small_paper`): for `c ≥ 0`, `0 ≤ α < 1`, `0 ≤ α₀ < 1` and
`t ≥ 0`. -/
theorem rieszDiagramLimit {c α α₀ t : ℝ} (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα : α < 1)
    (h0 : 0 ≤ α₀) (h1 : α₀ < 1) (ht : 0 ≤ t) : RieszDiagramLimit c α α₀ t :=
  fun _ _ _ hmn hD => (tendsto_riesz_two hc hα0 hα h0 h1 ht hmn hD).limUnder_eq

/-! ### The time chain sums and the change of variables `s ↦ h` -/

/-- The chain sums `S_l(h) = Σ_{i=b(l)}^{l} h_i` of `E:riesz-four` (main TeX lines
5150-5154), `b(l)` the first label of the chain of `l`: the time of label `l` from
the time increments `h`. -/
def timePos (m : ℕ) {N : ℕ} (h : Fin N → ℝ) (i : Fin N) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => SameChain m j i ∧ j ≤ i), h j

/-- Auxiliary: `S_l = h_l + S_{p(l)}` (root value `0`). -/
theorem timePos_eq_add_predVal (m : ℕ) {N : ℕ} (h : Fin N → ℝ) (i : Fin N) :
    timePos m h i = h i + predVal m (timePos m h) i := by
  rcases hp : pred m i with _ | j
  · rw [predVal_of_none m _ i hp, add_zero]
    have h0 := (pred_eq_none_iff m i).1 hp
    unfold timePos
    rw [show Finset.univ.filter (fun j => SameChain m j i ∧ j ≤ i) = {i} by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        SameChain, Fin.le_def, Fin.ext_iff]
      omega]
    simp
  · rw [predVal_of_some m _ i j hp]
    have hj := pred_eq_some_val m i j hp
    unfold timePos
    rw [show Finset.univ.filter (fun l => SameChain m l i ∧ l ≤ i) =
        insert i (Finset.univ.filter fun l => SameChain m l j ∧ l ≤ j) by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        SameChain, Fin.le_def, Fin.ext_iff]
      omega]
    rw [Finset.sum_insert]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def, not_and]
    intro _
    omega

/-- Auxiliary: the increments of the chain sums are the original increments. -/
theorem incr_timePos (m : ℕ) {N : ℕ} (h : Fin N → ℝ) : incr m (timePos m h) = h := by
  funext i
  rw [incr, timePos_eq_add_predVal m h i, add_sub_cancel_right]

/-- Auxiliary: the chain sums of the increments are the original times. -/
theorem timePos_incr (m : ℕ) {N : ℕ} (s : Fin N → ℝ) : timePos m (incr m s) = s := by
  funext i
  induction' hk : (i : ℕ) using Nat.strong_induction_on with k ih generalizing i
  rw [timePos_eq_add_predVal, incr]
  rcases hp : pred m i with _ | j
  · simp [predVal_of_none m _ i hp]
  · have hj := pred_eq_some_val m i j hp
    rw [predVal_of_some m _ i j hp, predVal_of_some m _ i j hp, ih j (by omega) j rfl,
      sub_add_cancel]

/-- Auxiliary: the chain sums are measurable. -/
theorem measurable_timePos (m : ℕ) {N : ℕ} : Measurable (timePos m (N := N)) :=
  measurable_pi_iff.2 fun _ => Finset.measurable_sum _ fun j _ => measurable_pi_apply j

/-- Auxiliary: the chain sums are linear. -/
theorem timePos_smul (m : ℕ) {N : ℕ} (a : ℝ) (h : Fin N → ℝ) :
    timePos m (a • h) = a • timePos m h := by
  funext i
  simp [timePos, Finset.mul_sum]

/-- Auxiliary: the time increments preserve Lebesgue measure (the increment
matrix is unipotent lower triangular, `DiagramBridge.det_incrMatrix`; "the time
increments give the domain `H_m`", main TeX lines 5205-5206). -/
theorem measurePreserving_incr (m N : ℕ) : MeasurePreserving (incr m (N := N)) volume volume := by
  have e : incr m (N := N) = Matrix.toLin' (DiagramBridge.incrMatrix m N) := by
    funext s
    rw [Matrix.toLin'_apply, DiagramBridge.incrMatrix_mulVec]
    rfl
  rw [e]
  exact DiagramBridge.measurePreserving_incrMatrix m N

/-- Auxiliary: the time increments of the simplices `[0,t]^m_< × [0,t]^n_<`:
`h_l > 0` and `S_l(h) < t`. -/
def hSet (m : ℕ) {N : ℕ} (t : ℝ) : Set (Fin N → ℝ) := {h | ∀ i, 0 < h i ∧ timePos m h i < t}

/-- Auxiliary: `hSet` is measurable. -/
theorem measurableSet_hSet (m : ℕ) {N : ℕ} (t : ℝ) : MeasurableSet (hSet m (N := N) t) := by
  have : hSet m (N := N) t = ⋂ i, ({h | 0 < h i} ∩ {h | timePos m h i < t}) := by
    ext h; simp [hSet]
  rw [this]
  exact MeasurableSet.iInter fun i =>
    (measurableSet_lt measurable_const (measurable_pi_apply i)).inter
    (measurableSet_lt ((measurable_pi_apply i).comp (measurable_timePos m)) measurable_const)

/-- Auxiliary: `s` is in the time simplices iff its increments are in `hSet`. -/
theorem mem_twoSimplex_iff_incr {m n : ℕ} {t : ℝ} (s : Fin (m + n) → ℝ) :
    s ∈ twoSimplex m n t ↔ incr m s ∈ hSet m t := by
  show (∀ i, predVal m s i < s i ∧ s i < t) ↔ ∀ i, 0 < incr m s i ∧ timePos m (incr m s) i < t
  rw [timePos_incr]
  simp only [incr, sub_pos]

/-- Auxiliary: the diagram in the time increments `h_l = s_l - s_{p(l)}`. -/
theorem diagram_eq_lintegral_hSet {γ : Rd 1 → ℝ≥0∞} (hγ : Measurable γ) (α₀ : ℝ) (m n : ℕ)
    (D : Fin (m + n) → Fin (m + n)) (t : ℝ) :
    diagram (waveGreen 1) γ α₀ m n D t =
      ∫⁻ h in hSet m t, timeWeight α₀ D (timePos m h) * spatial (waveGreen 1) γ m D h := by
  have hg : Measurable ((hSet m t).indicator fun h : Fin (m + n) → ℝ =>
      timeWeight α₀ D (timePos m h) * spatial (waveGreen 1) γ m D h) :=
    (((measurable_timeWeight α₀ D).comp (measurable_timePos m)).mul
      (measurable_spatial_one hγ m D)).indicator (measurableSet_hSet m t)
  unfold diagram
  rw [← lintegral_indicator (measurableSet_twoSimplex m n t),
    ← lintegral_indicator (measurableSet_hSet m t),
    ← (measurePreserving_incr m (m + n)).lintegral_comp hg]
  refine lintegral_congr fun s => ?_
  by_cases hs : s ∈ twoSimplex m n t
  · rw [indicator_of_mem hs, indicator_of_mem ((mem_twoSimplex_iff_incr s).1 hs), timePos_incr]
  · rw [indicator_of_notMem hs, indicator_of_notMem (mt (mem_twoSimplex_iff_incr s).2 hs)]

/-- Auxiliary: scaling `h = t h'` in `ℝ^N`: `∫ f = t^N ∫ f(t ·)`. -/
theorem lintegral_comp_smul_pos {N : ℕ} {t : ℝ} (ht : 0 < t) {f : (Fin N → ℝ) → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ h, f h = ENNReal.ofReal t ^ N * ∫⁻ h, f (t • h) := by
  have hmap := lintegral_map hf (measurable_const_smul t) (μ := (volume : Measure (Fin N → ℝ)))
  rw [Measure.map_addHaar_smul _ ht.ne', lintegral_smul_measure] at hmap
  simp only [Module.finrank_fin_fun, smul_eq_mul] at hmap
  rw [← hmap, ← mul_assoc, abs_of_pos (inv_pos.2 (pow_pos ht N)), ← ENNReal.ofReal_pow ht.le,
    ← ENNReal.ofReal_mul (pow_pos ht N).le, mul_inv_cancel₀ (pow_ne_zero _ ht.ne'),
    ENNReal.ofReal_one, one_mul]

/-! ### The spatial part in uniform variables -/

/-- The uniform law on `[-1, 1]` (as `½ 1_{|y|<1} dy` on `ℝ^1`; it is the Green
measure `G_1`).  `map_e1_unifLaw` identifies it with `½ 1_{(-1,1)}(u) du` on `ℝ`. -/
def unifLaw : Measure (Rd 1) := waveGreen 1 1

/-- `unifLaw` in the coordinate is `½ 1_{(-1,1)}(u) du`. -/
theorem map_e1_unifLaw :
    unifLaw.map e1 = ENNReal.ofReal (1 / 2) • (volume : Measure ℝ).restrict (Ioo (-1) 1) := by
  ext A hA
  rw [Measure.map_apply e1.measurable hA, Measure.smul_apply, smul_eq_mul, unifLaw,
    show waveGreen 1 1 = ENNReal.ofReal (1 / 2) • volume.restrict (Metric.ball (0 : Rd 1) 1)
      from rfl, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply (e1.measurable hA),
    Measure.restrict_apply hA, ← e1_preimage_Ioo, ← Set.preimage_inter,
    DiagramBridge.measurePreserving_e1.measure_preimage
      (hA.inter measurableSet_Ioo).nullMeasurableSet]

/-- `unifLaw` is a probability measure. -/
theorem unifLaw_univ : unifLaw Set.univ = 1 := by
  rw [unifLaw, WaveGreen.waveGreen_mass 1 (Or.inl rfl) _ zero_le_one, ENNReal.ofReal_one]

/-- `unifLaw` is a probability measure (instance form). -/
instance instIsProbabilityMeasureUnifLaw : IsProbabilityMeasure unifLaw := ⟨unifLaw_univ⟩

/-- Auxiliary: `∏_l G_{h_l} = (∏_l h_l) · (U ↦ (h_l U_l))_* unif^{⊗N}` for `h_l > 0`
("the Green factor `½ 1_{[-h_l,h_l]}` is `h_l` times the law of `h_l U_l`", main TeX
lines 5201-5202). -/
theorem pi_waveGreen_eq_smul_map {N : ℕ} {h : Fin N → ℝ} (hh : ∀ i, 0 < h i) :
    Measure.pi (fun i => waveGreen 1 (h i)) =
      (∏ i, ENNReal.ofReal (h i)) •
        (Measure.pi fun _ : Fin N => unifLaw).map (fun U i => h i • U i) := by
  have hmeas : Measurable fun U : Fin N → Rd 1 => fun i => h i • U i :=
    measurable_pi_iff.2 fun i => (measurable_const_smul _).comp (measurable_pi_apply i)
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.map_apply hmeas (MeasurableSet.univ_pi hs), smul_eq_mul]
  have hpre : (fun U : Fin N → Rd 1 => fun i => h i • U i) ⁻¹' Set.univ.pi s =
      Set.univ.pi fun i => (fun y : Rd 1 => h i • y) ⁻¹' s i := by
    ext U; simp
  rw [hpre, Measure.pi_pi, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [HigherRieszTwo.waveGreen_eq_smul_map (Or.inl rfl) (hh i), Measure.smul_apply,
    Measure.map_apply (measurable_const_smul _) (hs i), smul_eq_mul]
  rfl

/-- Auxiliary: `γ(t x) = t^{-α} γ(x)` for the Riesz density and `t > 0`. -/
theorem riesz_smul (c α : ℝ) {t : ℝ} (ht : 0 < t) (x : Rd 1) :
    riesz c α (t • x) = ENNReal.ofReal (t ^ (-α)) * riesz c α x := by
  unfold riesz
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, Real.mul_rpow ht.le (norm_nonneg _),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
  congr 1
  ring

/-- Auxiliary: `∏_D γ(t y_j - t y_h) = t^{-kα} ∏_D γ(y_j - y_h)`. -/
theorem covWeight_riesz_smul (c α : ℝ) {t : ℝ} (ht : 0 < t) {N : ℕ} (D : Fin N → Fin N)
    (y : Fin N → Rd 1) :
    covWeight (riesz c α) D (t • y) =
      ENNReal.ofReal (t ^ (-α)) ^ (openers D).card * covWeight (riesz c α) D y := by
  unfold covWeight
  simp only [Pi.smul_apply, ← smul_sub, riesz_smul c α ht]
  rw [Finset.prod_mul_distrib, Finset.prod_const]

/-- Auxiliary: the positions are linear in the increments. -/
theorem pos_smul (m : ℕ) {N : ℕ} (a : ℝ) (w : Fin N → Rd 1) : pos m (a • w) = a • pos m w := by
  funext i
  simp [pos, Finset.smul_sum]

/-- Auxiliary: `∏_D |s_j - s_h|^{-α₀}` at `t s` is `t^{-kα₀}` times its value at `s`. -/
theorem timeWeight_smul (α₀ : ℝ) {t : ℝ} (ht : 0 < t) {N : ℕ} (D : Fin N → Fin N)
    (s : Fin N → ℝ) :
    timeWeight α₀ D (t • s) =
      ENNReal.ofReal (t ^ (-α₀)) ^ (openers D).card * timeWeight α₀ D s := by
  unfold timeWeight
  have e : ∀ a b : ℝ, timeCov α₀ (t * a) (t * b) = ENNReal.ofReal (t ^ (-α₀)) * timeCov α₀ a b := by
    intro a b
    rw [timeCov, timeCov, ← mul_sub, abs_mul, abs_of_pos ht, ENNReal.ofReal_mul ht.le,
      ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.ofReal_rpow_of_pos ht]
  simp only [Pi.smul_apply, smul_eq_mul, e]
  rw [Finset.prod_mul_distrib, Finset.prod_const]

/-- The positions `Y_l(h, U) = Σ_{i=b(l)}^{l} h_i U_i` of `E:riesz-four` (main TeX lines
5151-5154): the chain sums of the spatial increments `h_i U_i`. -/
def yPos (m : ℕ) {N : ℕ} (h : Fin N → ℝ) (U : Fin N → Rd 1) : Fin N → Rd 1 :=
  pos m fun i => h i • U i

/-- Auxiliary: the Riesz spatial part at the scaled increments `t h`, `h_l > 0`:
`t^N t^{-kα} (∏_l h_l) E_U[∏_D γ(Y_j - Y_h)]`. -/
theorem spatial_riesz_smul {c α : ℝ} (m : ℕ) {N : ℕ} (D : Fin N → Fin N) {t : ℝ} (ht : 0 < t)
    {h : Fin N → ℝ} (hh : ∀ i, 0 < h i) :
    spatial (waveGreen 1) (riesz c α) m D (t • h) =
      ENNReal.ofReal t ^ N * ENNReal.ofReal (t ^ (-α)) ^ (openers D).card *
        ((∏ i, ENNReal.ofReal (h i)) *
          ∫⁻ U, covWeight (riesz c α) D (yPos m h U) ∂Measure.pi fun _ => unifLaw) := by
  have hth : ∀ i, 0 < (t • h) i := fun i => mul_pos ht (hh i)
  have hmeas : Measurable fun U : Fin N → Rd 1 => fun i => (t • h) i • U i :=
    measurable_pi_iff.2 fun i => (measurable_const_smul _).comp (measurable_pi_apply i)
  unfold spatial
  rw [pi_waveGreen_eq_smul_map hth, lintegral_smul_measure,
    lintegral_map (measurable_covWeight_pos m (measurable_riesz c α) D) hmeas, smul_eq_mul]
  have e : ∀ U : Fin N → Rd 1, covWeight (riesz c α) D (pos m fun i => (t • h) i • U i) =
      ENNReal.ofReal (t ^ (-α)) ^ (openers D).card * covWeight (riesz c α) D (yPos m h U) := by
    intro U
    have : (fun i => (t • h) i • U i) = t • fun i => h i • U i := by
      funext i; simp [mul_smul]
    rw [this, pos_smul, covWeight_riesz_smul c α ht]
    rfl
  simp_rw [e]
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
  have hp : ∏ i, ENNReal.ofReal ((t • h) i) = ENNReal.ofReal t ^ N * ∏ i, ENNReal.ofReal (h i) := by
    simp only [Pi.smul_apply, smul_eq_mul, ENNReal.ofReal_mul ht.le, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hp]
  ring

/-! ### The unit-domain representation `E:riesz-four` -/

/-- The unit time domain `H_m = {h ∈ (0,∞)^{m+n} : Σ_{l < m} h_l < 1, Σ_{l ≥ m} h_l < 1}`
of `E:riesz-four` (main TeX lines 5146-5150; an empty sum is zero).  Labels are
0-based: the first chain is `{i : i < m}`. -/
def hm (m n : ℕ) : Set (Fin (m + n) → ℝ) :=
  {h | (∀ i, 0 < h i) ∧ ∑ i ∈ Finset.univ.filter (fun i : Fin (m + n) => (i : ℕ) < m), h i < 1 ∧
    ∑ i ∈ Finset.univ.filter (fun i : Fin (m + n) => m ≤ (i : ℕ)), h i < 1}

/-- Auxiliary: the increments of `[0,1]^m_< × [0,1]^n_<` are exactly `H_m`. -/
theorem hSet_one_eq (m n : ℕ) : hSet m (N := m + n) 1 = hm m n := by
  ext h
  constructor
  · intro H
    refine ⟨fun i => (H i).1, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · have : Finset.univ.filter (fun i : Fin (m + n) => (i : ℕ) < m) = ∅ := by
          ext i; simp [hm0]
        rw [this, Finset.sum_empty]
        norm_num
      · have hL := (H ⟨m - 1, by omega⟩).2
        unfold timePos at hL
        convert hL using 2
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, SameChain, Fin.le_def]
        omega
    · rcases Nat.eq_zero_or_pos n with hn0 | hn0
      · have : Finset.univ.filter (fun i : Fin (m + n) => m ≤ (i : ℕ)) = ∅ := by
          ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.notMem_empty, iff_false, not_le]
          have := i.isLt; omega
        rw [this, Finset.sum_empty]
        norm_num
      · have hL := (H ⟨m + n - 1, by omega⟩).2
        unfold timePos at hL
        convert hL using 2
        ext j
        have := j.isLt
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, SameChain, Fin.le_def]
        omega
  · rintro ⟨hpos, h1, h2⟩ i
    refine ⟨hpos i, ?_⟩
    unfold timePos
    by_cases hi : (i : ℕ) < m
    · refine lt_of_le_of_lt (Finset.sum_le_sum_of_subset_of_nonneg ?_
        fun j _ _ => (hpos j).le) h1
      refine Finset.subset_iff.2 fun j hj => ?_
      rw [Finset.mem_filter] at hj ⊢
      exact ⟨Finset.mem_univ _, hj.2.1.2 hi⟩
    · refine lt_of_le_of_lt (Finset.sum_le_sum_of_subset_of_nonneg ?_
        fun j _ _ => (hpos j).le) h2
      refine Finset.subset_iff.2 fun j hj => ?_
      rw [Finset.mem_filter] at hj ⊢
      exact ⟨Finset.mem_univ _, not_lt.1 fun h => hi (hj.2.1.1 h)⟩

/-- Auxiliary: `t h ∈ hSet m t` iff `h ∈ hSet m 1` (`t > 0`). -/
theorem smul_mem_hSet {m N : ℕ} {t : ℝ} (ht : 0 < t) (h : Fin N → ℝ) :
    t • h ∈ hSet m t ↔ h ∈ hSet m 1 := by
  simp only [hSet, Set.mem_ofPred_eq, timePos_smul, Pi.smul_apply, smul_eq_mul]
  exact forall_congr' fun i => and_congr (mul_pos_iff_of_pos_left ht)
    (mul_lt_iff_lt_one_right ht)

/-- Auxiliary: `∏_D c|y_j - y_h|^{-α} = c^k ∏_D |y_j - y_h|^{-α}` (`c ≥ 0`). -/
theorem covWeight_riesz_eq {c α : ℝ} (hc : 0 ≤ c) {N : ℕ} (D : Fin N → Fin N)
    (y : Fin N → Rd 1) :
    covWeight (riesz c α) D y = ENNReal.ofReal c ^ (openers D).card *
      ∏ j ∈ openers D, ENNReal.ofReal (‖y j - y (D j)‖ ^ (-α)) := by
  unfold covWeight riesz
  simp only [ENNReal.ofReal_mul hc]
  rw [Finset.prod_mul_distrib, Finset.prod_const]

/-- The unit-domain integral of `E:riesz-four` (main TeX lines 5155-5163), for any
split `(m, n)` and pairing `D`:
`∫_{H_m} (∏_l h_l) ∏_{(j,q) ∈ D} |S_j(h) - S_q(h)|^{-α₀}
  E_U[∏_{(j,q) ∈ D} |Y_j(h,U) - Y_q(h,U)|^{-α}] dh`,
with `U_l` independent uniform on `[-1,1]` (`unifLaw`), `S = timePos`, `Y = yPos`.
The time factor is the model's `timeWeight`; at zero it is `∞` for `α₀ > 0`, `1` for `α₀ = 0`
and `0` for `α₀ < 0` (the diagonal is a null set). -/
def rieszUnit (α α₀ : ℝ) (m n : ℕ) (D : Fin (m + n) → Fin (m + n)) : ℝ≥0∞ :=
  ∫⁻ h in hm m n, (∏ i, ENNReal.ofReal (h i)) * timeWeight α₀ D (timePos m h) *
    ∫⁻ U, ∏ j ∈ openers D, ENNReal.ofReal (‖yPos m h U j - yPos m h U (D j)‖ ^ (-α))
      ∂Measure.pi fun _ => unifLaw

/-- Auxiliary: the scaling constant `t^N t^{-kα₀} t^N t^{-kα} c^k = c^k t^{kβ}`,
`N = 2k`, `β = 4 - α - α₀`. -/
theorem scaling_const {c α α₀ t : ℝ} (hc : 0 ≤ c) (ht : 0 < t) {N k : ℕ} (hk : N = 2 * k) :
    ENNReal.ofReal (c ^ k * t ^ ((k : ℝ) * (4 - α - α₀))) =
      ENNReal.ofReal t ^ N * (ENNReal.ofReal (t ^ (-α₀)) ^ k *
        (ENNReal.ofReal t ^ N * ENNReal.ofReal (t ^ (-α)) ^ k) * ENNReal.ofReal c ^ k) := by
  have h1 : 0 ≤ t ^ N := pow_nonneg ht.le _
  have h2 : 0 ≤ t ^ (-α₀) := Real.rpow_nonneg ht.le _
  have h3 : 0 ≤ t ^ (-α) := Real.rpow_nonneg ht.le _
  have hreal : c ^ k * t ^ ((k : ℝ) * (4 - α - α₀)) =
      t ^ N * ((t ^ (-α₀)) ^ k * (t ^ N * (t ^ (-α)) ^ k)) * c ^ k := by
    rw [← Real.rpow_natCast (t ^ (-α₀)) k, ← Real.rpow_mul ht.le, ← Real.rpow_natCast (t ^ (-α)) k,
      ← Real.rpow_mul ht.le, ← Real.rpow_natCast t N, ← Real.rpow_add ht, ← Real.rpow_add ht,
      ← Real.rpow_add ht, mul_comm (c ^ k)]
    congr 2
    subst hk
    push_cast
    ring
  rw [hreal, ENNReal.ofReal_mul (mul_nonneg h1 (mul_nonneg (pow_nonneg h2 _)
      (mul_nonneg h1 (pow_nonneg h3 _)))), ENNReal.ofReal_mul h1,
    ENNReal.ofReal_mul (pow_nonneg h2 _), ENNReal.ofReal_mul h1, ENNReal.ofReal_pow ht.le,
    ENNReal.ofReal_pow h2, ENNReal.ofReal_pow h3, ENNReal.ofReal_pow hc]
  ring

/-- **The unit-domain representation** (`E:riesz-four` for every order; main TeX
lines 5144-5163, proof 5199-5213): for `d = 1`, `γ(y) = c|y|^{-α}` with `c ≥ 0`, a
pairing `D ∈ Π_k` of the two chains with `m + n = 2k` and `t > 0`,
`J_{m,n,D}(t) = c^k t^{kβ} ∫_{H_m} (∏_l h_l) ∏_D |S_j - S_q|^{-α₀}
E_U[∏_D |Y_j - Y_q|^{-α}] dh`, `β = 4 - α - α₀`.  The TeX's case is `k = 2`
(`riesz_four`).  Proof as in the TeX: time increments (determinant one), spatial
increments `h_l U_l` (`G_{h_l}` is `h_l` times the law of `h_l U_l`), positions
(triangular, determinant one, already built into `pos`), and the scaling of time
and space by `t`. -/
theorem diagram_riesz_eq {c α α₀ : ℝ} (hc : 0 ≤ c) {m n k : ℕ} (hk : m + n = 2 * k)
    {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n) {t : ℝ} (ht : 0 < t) :
    diagram (waveGreen 1) (riesz c α) α₀ m n D t =
      ENNReal.ofReal (c ^ k * t ^ ((k : ℝ) * (4 - α - α₀))) * rieszUnit α α₀ m n D := by
  have hcard : (openers D).card = k := card_openers hD hk
  have hΦm : Measurable ((hSet m t).indicator fun h : Fin (m + n) → ℝ =>
      timeWeight α₀ D (timePos m h) * spatial (waveGreen 1) (riesz c α) m D h) :=
    (((measurable_timeWeight α₀ D).comp (measurable_timePos m)).mul
      (measurable_spatial_one (measurable_riesz c α) m D)).indicator (measurableSet_hSet m t)
  have hpt : ∀ h : Fin (m + n) → ℝ, (hSet m t).indicator (fun h : Fin (m + n) → ℝ =>
      timeWeight α₀ D (timePos m h) * spatial (waveGreen 1) (riesz c α) m D h) (t • h) =
      (hSet m 1).indicator (fun h => (ENNReal.ofReal (t ^ (-α₀)) ^ k *
        (ENNReal.ofReal t ^ (m + n) * ENNReal.ofReal (t ^ (-α)) ^ k) * ENNReal.ofReal c ^ k) *
        ((∏ i, ENNReal.ofReal (h i)) * timeWeight α₀ D (timePos m h) *
          ∫⁻ U, ∏ j ∈ openers D, ENNReal.ofReal (‖yPos m h U j - yPos m h U (D j)‖ ^ (-α))
            ∂Measure.pi fun _ => unifLaw)) h := by
    intro h
    by_cases hh : h ∈ hSet m 1
    · rw [indicator_of_mem hh, indicator_of_mem ((smul_mem_hSet ht h).2 hh)]
      rw [timePos_smul, timeWeight_smul α₀ ht, spatial_riesz_smul m D ht (fun i => (hh i).1),
        hcard]
      simp_rw [covWeight_riesz_eq hc D, hcard]
      rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
      ring
    · rw [indicator_of_notMem hh, indicator_of_notMem (mt (smul_mem_hSet ht h).1 hh)]
  rw [diagram_eq_lintegral_hSet (measurable_riesz c α), ← lintegral_indicator
    (measurableSet_hSet m t), lintegral_comp_smul_pos ht hΦm]
  simp_rw [hpt]
  rw [lintegral_indicator (measurableSet_hSet m 1),
    lintegral_const_mul' _ _ (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (ENNReal.mul_ne_top
        (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)))
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)), hSet_one_eq, scaling_const hc ht hk]
  unfold rieszUnit
  ring

/-! ### Finiteness -/

/-- Auxiliary: positions whose increments are below `t` satisfy
`|y_l| < (l + 1) t` ("on the unit-time domain all vertex positions lie in
`[-1, 1]`", main TeX lines 5213-5214, with the crude per-label bound). -/
theorem norm_lt_of_incr_lt {m N : ℕ} {t : ℝ} (ht : 0 ≤ t) {y : Fin N → Rd 1}
    (hy : ∀ i, ‖y i - predVal m y i‖ < t) (i : Fin N) : ‖y i‖ < ((i : ℕ) + 1) * t := by
  induction' hk : (i : ℕ) using Nat.strong_induction_on with k ih generalizing i
  have h := hy i
  rcases hp : pred m i with _ | j
  · rw [predVal_of_none m y i hp, sub_zero] at h
    have : t ≤ ((k : ℝ) + 1) * t := by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith
    linarith
  · rw [predVal_of_some m y i j hp] at h
    have hj := pred_eq_some_val m i j hp
    have hlt := ih j (by omega) j rfl
    have hk' : (k : ℝ) = (j : ℕ) + 1 := by
      rw [← hk, ← hj.1]; push_cast; ring
    have := norm_sub_norm_le (y i) (y j)
    rw [hk']
    linarith

/-- Auxiliary: the uniform bound of the Riesz spatial part over the time simplices:
for increments `0 ≤ h_l ≤ t`, bound the Green indicators by `½ 1_{|y_l| < N t}`
(main TeX lines 5213-5216: "enlarge ... the spatial domain ... and bound the
Green indicators"). -/
theorem spatial_le_cube {γ : Rd 1 → ℝ≥0∞} (m : ℕ) {N : ℕ} (D : Fin N → Fin N) {t : ℝ}
    (ht : 0 ≤ t) {h : Fin N → ℝ} (hh : ∀ i, h i ≤ t) :
    spatial (waveGreen 1) γ m D h ≤ ENNReal.ofReal (1 / 2) ^ N *
      ∫⁻ y in Set.univ.pi (fun _ : Fin N => Metric.ball (0 : Rd 1) (N * t)), covWeight γ D y := by
  have hB : MeasurableSet (Set.univ.pi fun _ : Fin N => Metric.ball (0 : Rd 1) (N * t)) :=
    MeasurableSet.univ_pi fun _ => Metric.isOpen_ball.measurableSet
  rw [DiagramBridge.spatial_waveGreen_one_eq_spatialPos, spatialPos, ← lintegral_indicator hB,
    ← lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
  refine lintegral_mono fun y => ?_
  by_cases hall : ∀ i, ‖y i - predVal m y i‖ < h i
  · have hy : y ∈ Set.univ.pi fun _ : Fin N => Metric.ball (0 : Rd 1) (N * t) := by
      intro i _
      rw [mem_ball_zero_iff]
      have h1 := norm_lt_of_incr_lt ht (fun j => (hall j).trans_le (hh j)) i
      have h2 : ((i : ℕ) + 1 : ℝ) * t ≤ N * t := by
        have : ((i : ℕ) + 1 : ℝ) ≤ N := by exact_mod_cast i.isLt
        nlinarith
      linarith
    rw [indicator_of_mem hy]
    refine le_of_eq ?_
    congr 1
    calc ∏ i, green1 (h i) (y i - predVal m y i) = ∏ _i : Fin N, ENNReal.ofReal (1 / 2) :=
          Finset.prod_congr rfl fun i _ => by
            rw [green1, indicator_of_mem (by rw [mem_ball_zero_iff]; exact hall i)]
      _ = ENNReal.ofReal (1 / 2) ^ N := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · obtain ⟨i, hi⟩ := not_forall.1 hall
    have h0 : ∏ j, green1 (h j) (y j - predVal m y j) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [green1, indicator_of_notMem (by rw [mem_ball_zero_iff]; exact hi)]
    rw [h0, zero_mul]
    exact bot_le

/-- Auxiliary: the Riesz pairing weight is integrable over a cube:
`∫_{B_R^N} ∏_D c|y_j - y_h|^{-α} dy ≤ (2c(2R)^{1-α}/(1-α))^k (2R)^k` (main TeX
lines 5215-5216: "the same is true of the two spatial factors since `α < 1`"). -/
theorem lintegral_cube_covWeight_le {c α : ℝ} (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα : α < 1) {R : ℝ}
    (hR : 0 ≤ R) {N : ℕ} {D : Fin N → Fin N} (hD : ∀ i, D i ≠ i ∧ D (D i) = i) :
    ∫⁻ y in Set.univ.pi (fun _ : Fin N => Metric.ball (0 : Rd 1) R), covWeight (riesz c α) D y ≤
      ENNReal.ofReal (2 * (c * (2 * R) ^ (1 - α) / (1 - α))) ^ (openers D).card *
        volume (Metric.ball (0 : Rd 1) R) ^ (openers D).card := by
  rw [MeasureTheory.volume_pi, Measure.restrict_pi_pi]
  refine (lintegral_pi_matching_le _ hD (f := fun a b => riesz c α (a - b))
    ((measurable_riesz c α).comp (measurable_fst.sub measurable_snd))
    (lintegral_ball_riesz_le hc hα0 hα hR)).trans (le_of_eq ?_)
  rw [Measure.restrict_apply_univ]

/-- **Finiteness of the Riesz diagrams** (main TeX lines 5207-5219, for every
order): for `d = 1`, `γ(y) = c|y|^{-α}`, `c ≥ 0`, `0 ≤ α < 1`, `0 ≤ α₀ < 1`, `t ≥ 0`
and every pairing `D ∈ Π`, `J_{m,n,D}(t) < ∞`.  As in the TeX: enlarge the time
domain to a cube and the spatial domain to a box, bound the Green indicators,
and integrate the disjoint pair factors one at a time (Tonelli). -/
theorem diagram_riesz_ne_top {c α α₀ : ℝ} (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα : α < 1)
    (h0 : 0 ≤ α₀) (h1 : α₀ < 1) {m n : ℕ} {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n)
    {t : ℝ} (ht : 0 ≤ t) : diagram (waveGreen 1) (riesz c α) α₀ m n D t ≠ ⊤ := by
  have hD' := mem_Pi2.1 hD
  have hR : (0 : ℝ) ≤ (m + n : ℕ) * t := mul_nonneg (Nat.cast_nonneg _) ht
  set Csp := ENNReal.ofReal (1 / 2) ^ (m + n) *
    (ENNReal.ofReal (2 * (c * (2 * ((m + n : ℕ) * t)) ^ (1 - α) / (1 - α))) ^ (openers D).card *
      volume (Metric.ball (0 : Rd 1) ((m + n : ℕ) * t)) ^ (openers D).card) with hCsp
  have hCne : Csp ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.pow_ne_top measure_ball_lt_top.ne))
  have hle : ∀ s ∈ twoSimplex m n t,
      timeWeight α₀ D s * spatial (waveGreen 1) (riesz c α) m D (incr m s) ≤
        timeWeight α₀ D s * Csp := by
    intro s hs
    gcongr
    refine (spatial_le_cube m D ht fun i => (incr_lt_of_mem hs i).le).trans ?_
    rw [hCsp]
    gcongr
    exact lintegral_cube_covWeight_le hc hα0 hα hR hD'
  refine ne_top_of_le_ne_top ?_ (setLIntegral_mono' (measurableSet_twoSimplex m n t) hle)
  rw [lintegral_mul_const _ (measurable_timeWeight α₀ D)]
  exact ENNReal.mul_ne_top (lintegral_twoSimplex_timeWeight_ne_top h0 h1 ht hD') hCne

/-- The unit-domain integral of `E:riesz-four` is finite ("This is a finite
nonnegative integral", main TeX line 5164), for `0 ≤ α < 1`, `0 ≤ α₀ < 1`, every
split and every pairing (every order `m + n = 2k`). -/
theorem rieszUnit_ne_top {α α₀ : ℝ} (hα0 : 0 ≤ α) (hα : α < 1) (h0 : 0 ≤ α₀) (h1 : α₀ < 1)
    {m n k : ℕ} (hk : m + n = 2 * k) {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n) :
    rieszUnit α α₀ m n D ≠ ⊤ := by
  have h := diagram_riesz_eq (c := 1) (α := α) (α₀ := α₀) zero_le_one hk hD one_pos
  rw [one_pow, Real.one_rpow, mul_one, ENNReal.ofReal_one, one_mul] at h
  rw [← h]
  exact diagram_riesz_ne_top zero_le_one hα0 hα h0 h1 hD zero_le_one

/-! ### Order four -/

/-- `P:riesz-small`, the order-four representation `E:riesz-four` on the model (main TeX
lines 5144-5163, proof 5199-5219): for `d = 1`, `γ(y) = c|y|^{-α}` with `c ≥ 0`,
`0 ≤ α < 1`, `0 ≤ α₀ < 1`, `t > 0`, every split `m + n = 4` and every pairing
`D ∈ Π_2`, `J_{m,n,D}(t) = c^2 t^{2β} ∫_{H_m} (∏ h_l) ∏_D |S_j - S_q|^{-α₀}
E_U[∏_D |Y_j - Y_q|^{-α}] dh` with `β = 4 - α - α₀`, the integral is finite, and
there are exactly three pairings ("all three pairings"). -/
theorem riesz_four {c α α₀ : ℝ} (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα : α < 1) (h0 : 0 ≤ α₀)
    (h1 : α₀ < 1) {m n : ℕ} (hmn : m + n = 4) {t : ℝ} (ht : 0 < t) :
    (Pi2 m n).card = 3 ∧ ∀ D ∈ Pi2 m n,
      diagram (waveGreen 1) (riesz c α) α₀ m n D t =
        ENNReal.ofReal (c ^ 2 * t ^ (2 * (4 - α - α₀))) * rieszUnit α α₀ m n D ∧
      rieszUnit α α₀ m n D ≠ ⊤ := by
  refine ⟨by rw [card_Pi2 (k := 2) hmn]; rfl, fun D hD => ⟨?_, rieszUnit_ne_top hα0 hα h0 h1
    (k := 2) hmn hD⟩⟩
  rw [diagram_riesz_eq hc (k := 2) hmn hD ht]
  norm_num

/-- The total-order-four coefficient `A_2(t) = Σ_{m=0}^{4} Σ_{D ∈ Π_2} J_{m,4-m,D}(t)`
for the Riesz density (main TeX lines 5446-5451 and 5163: "the total coefficient
uses the multiplicities"): `A_2(t) = c^2 t^{2β} Σ_m Σ_D I_{m,D}` with the
unit-domain integrals `I_{m,D}` of `E:riesz-four`, and it is finite. -/
theorem riesz_coeffA_two {c α α₀ : ℝ} (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα : α < 1) (h0 : 0 ≤ α₀)
    (h1 : α₀ < 1) {t : ℝ} (ht : 0 < t) :
    coeffA (waveGreen 1) (riesz c α) α₀ 2 t =
        ENNReal.ofReal (c ^ 2 * t ^ (2 * (4 - α - α₀))) *
          ∑ m ∈ Finset.range (2 * 2 + 1), ∑ D ∈ Pi2 m (2 * 2 - m), rieszUnit α α₀ m (2 * 2 - m) D ∧
      coeffA (waveGreen 1) (riesz c α) α₀ 2 t ≠ ⊤ := by
  refine ⟨?_, ?_⟩
  · unfold coeffA
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun D hD => ?_
    have hm' : m + (2 * 2 - m) = 4 := by
      have := Finset.mem_range.1 hm; omega
    exact ((riesz_four hc hα0 hα h0 h1 hm' ht).2 D hD).1
  · unfold coeffA
    exact ENNReal.sum_ne_top.2 fun m _ => ENNReal.sum_ne_top.2 fun D hD =>
      diagram_riesz_ne_top hc hα0 hα h0 h1 hD ht.le

/-! ### Positivity (used by the refutations) -/

/-- Auxiliary: the position difference `w ↦ y_i - y_{D i}` of an opener `i` as a linear
map of the increments. -/
def posDiff (m : ℕ) {N : ℕ} (i j : Fin N) : (Fin N → Rd 1) →ₗ[ℝ] Rd 1 where
  toFun w := pos m w i - pos m w j
  map_add' w v := by simp only [pos, Pi.add_apply, Finset.sum_add_distrib]; abel
  map_smul' a w := by simp [pos, Finset.smul_sum, smul_sub]

/-- Auxiliary: for an opener `i` the coincidence set `{y_i = y_{D i}}` is a null
set of increments (a proper hyperplane: the increment of `D i` enters `y_{D i}`
but not `y_i`). -/
theorem volume_pos_eq_null {m N : ℕ} {D : Fin N → Fin N} {i : Fin N} (hi : i ∈ openers D) :
    volume {w : Fin N → Rd 1 | pos m w i = pos m w (D i)} = 0 := by
  have hlt : i < D i := (Finset.mem_filter.1 hi).2
  have hset : {w : Fin N → Rd 1 | pos m w i = pos m w (D i)} =
      (LinearMap.ker (posDiff m i (D i)) : Set (Fin N → Rd 1)) := by
    ext w; simp [posDiff, sub_eq_zero]
  rw [hset]
  refine Measure.addHaar_submodule _ _ fun htop => ?_
  set v : Rd 1 := EuclideanSpace.single (0 : Fin 1) (1 : ℝ) with hv
  have hv0 : v ≠ 0 := by
    intro h
    have := congrArg (fun x : Rd 1 => x 0) h
    simp [hv] at this
  have hmem : (Pi.single (D i) v : Fin N → Rd 1) ∈ LinearMap.ker (posDiff m i (D i)) := by
    rw [htop]; exact Submodule.mem_top
  rw [LinearMap.mem_ker] at hmem
  simp only [posDiff, LinearMap.coe_mk, AddHom.coe_mk, pos, Finset.sum_pi_single',
    Finset.mem_filter, Finset.mem_univ, true_and, le_refl, and_true] at hmem
  have hn : ¬ (SameChain m (D i) i ∧ D i ≤ i) := fun h => absurd h.2 (not_le.2 hlt)
  have hs : SameChain m (D i) (D i) := Iff.rfl
  rw [ite_eq_right hn, ite_eq_left hs, zero_sub, neg_eq_zero] at hmem
  exact hv0 hmem

/-- Auxiliary: the Riesz spatial part is positive for `c > 0` and positive
increments. -/
theorem spatial_riesz_pos {c α : ℝ} (hc : 0 < c) (m : ℕ) {N : ℕ} (D : Fin N → Fin N)
    {h : Fin N → ℝ} (hh : ∀ i, 0 < h i) : 0 < spatial (waveGreen 1) (riesz c α) m D h := by
  have hB : MeasurableSet (Set.univ.pi fun i => Metric.ball (0 : Rd 1) (h i)) :=
    MeasurableSet.univ_pi fun _ => Metric.isOpen_ball.measurableSet
  have hF := measurable_covWeight_pos m (measurable_riesz c α) D
  unfold spatial
  rw [DiagramBridge.pi_waveGreen_one, lintegral_smul_measure, smul_eq_mul]
  refine ENNReal.mul_pos (pow_ne_zero _ (by simp)) ?_
  rw [← pos_iff_ne_zero, setLIntegral_pos_iff hF]
  set Hyp := ⋃ i ∈ openers D, {w : Fin N → Rd 1 | pos m w i = pos m w (D i)} with hHyp
  have hnull : volume Hyp = 0 := by
    refine le_antisymm ((measure_biUnion_finset_le _ _).trans (le_of_eq ?_)) bot_le
    exact Finset.sum_eq_zero fun i hi => volume_pos_eq_null hi
  have hsub : (Set.univ.pi fun i => Metric.ball (0 : Rd 1) (h i)) \ Hyp ⊆
      Function.support (fun w : Fin N → Rd 1 => covWeight (riesz c α) D (pos m w)) ∩
        Set.univ.pi fun i => Metric.ball (0 : Rd 1) (h i) := by
    rintro w ⟨hwB, hwH⟩
    refine ⟨?_, hwB⟩
    rw [Function.mem_support, covWeight]
    refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
    have hne : pos m w i - pos m w (D i) ≠ 0 := fun h0 =>
      hwH (Set.mem_biUnion hi (sub_eq_zero.1 h0))
    rw [riesz, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact mul_pos hc (Real.rpow_pos_of_pos (norm_pos_iff.2 hne) _)
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [measure_sdiff_null hnull, MeasureTheory.volume_pi, Measure.pi_pi]
  refine pos_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => ?_)
  rw [volume_ball_rd1]
  exact (ENNReal.ofReal_pos.2 (by linarith [hh i])).ne'

/-- Auxiliary: the time simplices are open. -/
theorem isOpen_twoSimplex (m n : ℕ) (t : ℝ) : IsOpen (twoSimplex m n t) := by
  have : twoSimplex m n t = ⋂ i, ({s | predVal m s i < s i} ∩ {s | s i < t}) := by
    ext s; simp [twoSimplex]
  rw [this]
  refine isOpen_iInter_of_finite fun i => IsOpen.inter ?_
    (isOpen_lt (continuous_apply i) continuous_const)
  rcases hp : pred m i with _ | j
  · simp_rw [predVal_of_none m _ i hp]; exact isOpen_lt continuous_const (continuous_apply i)
  · simp_rw [predVal_of_some m _ i j hp]; exact isOpen_lt (continuous_apply j) (continuous_apply i)

/-- Auxiliary: the time simplices are nonempty for `t > 0`. -/
theorem twoSimplex_nonempty (m n : ℕ) {t : ℝ} (ht : 0 < t) : (twoSimplex m n t).Nonempty := by
  refine ⟨fun i => ((i : ℕ) + 1) * t / ((m + n : ℕ) + 1), fun i => ⟨?_, ?_⟩⟩
  · rcases hp : pred m i with _ | j
    · rw [predVal_of_none m _ i hp]; positivity
    · rw [predVal_of_some m _ i j hp]
      have hj := pred_eq_some_val m i j hp
      have hji : ((j : ℕ) : ℝ) + 1 = (i : ℕ) := by exact_mod_cast hj.1
      have hpos : (0 : ℝ) < (m + n : ℕ) + 1 := by positivity
      rw [div_lt_div_iff_of_pos_right hpos, ← hji]
      nlinarith
  · have hpos : (0 : ℝ) < (m + n : ℕ) + 1 := by positivity
    rw [div_lt_iff₀ hpos]
    have : ((i : ℕ) : ℝ) + 1 < (m + n : ℕ) + 1 := by
      have := i.isLt; push_cast; exact_mod_cast (by omega : (i : ℕ) + 1 < m + n + 1)
    nlinarith

/-- The Riesz diagrams are positive: `J_{m,n,D}(t) > 0` for `c > 0`, `0 ≤ α₀`, `t > 0`
and every pairing (an auxiliary fact used to make the refutations of
`E:riesz-four` non-vacuous; the TeX states nonnegativity). -/
theorem diagram_riesz_pos {c α α₀ : ℝ} (hc : 0 < c) (h0 : 0 ≤ α₀) {m n : ℕ}
    (D : Fin (m + n) → Fin (m + n)) {t : ℝ} (ht : 0 < t) :
    0 < diagram (waveGreen 1) (riesz c α) α₀ m n D t := by
  have hm : Measurable fun s : Fin (m + n) → ℝ =>
      timeWeight α₀ D s * spatial (waveGreen 1) (riesz c α) m D (incr m s) :=
    (measurable_timeWeight α₀ D).mul
      ((measurable_spatial_one (measurable_riesz c α) m D).comp (measurable_incr m))
  unfold diagram
  rw [setLIntegral_pos_iff hm]
  have hsub : twoSimplex m n t ⊆ Function.support (fun s : Fin (m + n) → ℝ =>
      timeWeight α₀ D s * spatial (waveGreen 1) (riesz c α) m D (incr m s)) ∩
        twoSimplex m n t := by
    intro s hs
    refine ⟨?_, hs⟩
    rw [Function.mem_support]
    refine mul_ne_zero ?_ (spatial_riesz_pos hc m D (incr_pos hs)).ne'
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    rw [timeCov, ne_eq, ENNReal.rpow_eq_zero_iff]
    push Not
    exact ⟨fun _ => by linarith, fun h => absurd h ENNReal.ofReal_ne_top⟩
  exact lt_of_lt_of_le ((isOpen_twoSimplex m n t).measure_pos volume
    (twoSimplex_nonempty m n ht)) (measure_mono hsub)

/-! ### The proposition as stated -/

/-- `P:riesz-small`, the order-two part `E:riesz-two` (main TeX lines 5125-5142) about
the chaos terms, through the supplied input `MixedMoment` (`P:mixed`) alone: the
successor of `OrderTwoDiagrams.riesz_small_paper` with its input
`RieszDiagramLimit` now proved (`rieszDiagramLimit`).  For `d = 1`, `0 < α < 1`,
`0 < α₀ < 1`, `γ(y) = c|y|^{-α}`, `c > 0`, `X_0 = 1`, `t ≥ 0`: `E X_2(t,x)` and
`E X_1(t,x)²` are the two displays of `E:riesz-two`, and the total
`Σ_{m=0}^{2} E[X_m X_{2-m}]` is `E X_1² + 2 E X_2`.  Carried but unused: `H:homog`
(`hH`); `0 < α`, `0 < α₀`, `c > 0` are used only as `≥ 0`. -/
theorem riesz_small_paper' {c α α₀ : ℝ} {μ : Measure (Rd 1)}
    (_hH : HomogHypothesis.HomogCovariance 1 α α₀
      ((volume : Measure (Rd 1)).withDensity (riesz c α)) μ)
    (hc : 0 < c) (hα : 0 < α) (hα1 : α < 1) (hα0 : 0 < α₀) (hα01 : α₀ < 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ} {u : Ω → ℝ} {t : ℝ}
    (ht : 0 ≤ t) (hM : MixedMoment 1 α₀ ((volume : Measure (Rd 1)).withDensity (riesz c α)) P X u t)
    (hX0 : ∀ ω, X 0 ω = 1) :
    ∫ ω, X 2 ω ∂P = c * t ^ (4 - α - α₀) /
        ((1 - α) * (2 - α - α₀) * (3 - α - α₀) * (4 - α - α₀)) ∧
      ∫ ω, X 1 ω ^ 2 ∂P =
        c / ((1 - α) * (2 - α)) * ∫ v in (0 : ℝ)..t, v ^ (-α₀) * rbr t α v ∧
      ∑ m ∈ Finset.range 3, ∫ ω, X m ω * X (2 - m) ω ∂P =
        ∫ ω, X 1 ω ^ 2 ∂P + 2 * ∫ ω, X 2 ω ∂P :=
  riesz_small_paper _hH hc hα hα1 hα0 hα01 ht hM
    (rieszDiagramLimit hc.le hα.le hα1 hα0.le hα01 ht) hX0

/-- `P:riesz-small`, the order-four part (main TeX lines 5144-5171, proof 5199-5219),
with the TeX's hypotheses (`d = 1`, `0 < α < 1`, `0 < α₀ < 1`, `γ(y) = c|y|^{-α}`,
`c > 0`, `H:homog`), on the model's diagrams for the density: for every split
`m + n = 4` there are exactly three pairings, and for each of them and every `t > 0`,
`J_{m,n,D}(t) = c^2 t^{2β} I_{m,D}` with the unit-domain integral `I_{m,D}`
(`rieszUnit`) of `E:riesz-four`, which is finite; and the total coefficient is
`A_2(t) = c^2 t^{2β} Σ_m Σ_D I_{m,D} < ∞`.  Carried but unused: `H:homog` (`hH`);
`0 < α`, `0 < α₀`, `c > 0` are used only as `≥ 0`. -/
theorem riesz_four_paper {c α α₀ : ℝ} {μ : Measure (Rd 1)}
    (_hH : HomogHypothesis.HomogCovariance 1 α α₀
      ((volume : Measure (Rd 1)).withDensity (riesz c α)) μ)
    (hc : 0 < c) (hα : 0 < α) (hα1 : α < 1) (hα0 : 0 < α₀) (hα01 : α₀ < 1) {t : ℝ}
    (ht : 0 < t) :
    (∀ m n : ℕ, m + n = 4 → (Pi2 m n).card = 3 ∧ ∀ D ∈ Pi2 m n,
      diagram (waveGreen 1) (riesz c α) α₀ m n D t =
        ENNReal.ofReal (c ^ 2 * t ^ (2 * (4 - α - α₀))) * rieszUnit α α₀ m n D ∧
      rieszUnit α α₀ m n D ≠ ⊤) ∧
    coeffA (waveGreen 1) (riesz c α) α₀ 2 t =
        ENNReal.ofReal (c ^ 2 * t ^ (2 * (4 - α - α₀))) *
          ∑ m ∈ Finset.range (2 * 2 + 1), ∑ D ∈ Pi2 m (2 * 2 - m), rieszUnit α α₀ m (2 * 2 - m) D ∧
      coeffA (waveGreen 1) (riesz c α) α₀ 2 t ≠ ⊤ :=
  ⟨fun _ _ hmn => riesz_four hc.le hα.le hα1 hα0.le hα01 hmn ht,
    riesz_coeffA_two hc.le hα.le hα1 hα0.le hα01 ht⟩

end StratonovichHAMSecondMoment.RieszFourDiagrams
