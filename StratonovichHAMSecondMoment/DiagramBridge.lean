module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

The `d = 1` positions/increments bridge for the two-chain diagram model (wave
L13 item DM0b; a foundation for `DiagramModel`).  Main TeX file
`notes/notes_stratonovich_ham_second_moment.tex` at revision 39f2597a:
* the diagram integral `E:mixed-diagram` (lines 808-824) in the position
  variables `y_l`, with the Green factors `G(s_l - s_{p(l)}, y_l - y_{p(l)})`
  and a separate root `(0, 0)` for each chain (lines 811-813);
* the increment variables set up before `L:d1-spatial` (lines 5338-5355):
  "`x_l` is the sum of increments in its own chain up to label `l`.  The
  spatial change of variables has determinant one" (lines 5340-5341), and the
  increments form
  `S_{D,ε}(h)` with `G(h, y) = ½ 1_{|y|<h}` (lines 5351-5355; also line
  952).

`DiagramModel.spatial` reads the Green kernels as measures of the increments
(`Measure.pi` of `G_{h_l}`, positions `pos m w`), while `DiagramModel.spatialPos`
is the literal positions integral `∫ ∏_l g(h_l, y_l - y_{p(l)}) ∏_D γ dy`.  This
module proves that the two agree in `d = 1`, for every covariance `γ : Rd 1 →
ℝ≥0∞` (no measurability needed) and every real `h` (no sign condition: for
`h_l ≤ 0` both sides vanish), and hence that `diagram (waveGreen 1) γ =
diagramPos green1 γ`.  This is the TeX's change of variables at line 5341.

Formalized (all proved, no supplied input):
* `incrOfPos`: the increments `y_l - y_{p(l)}` of positions `y`;
  `pos_eq_add_predVal` (`y_l = w_l + y_{p(l)}` for `y = pos w`), `incrOfPos_pos`,
  `pos_incrOfPos` (the two maps are mutually inverse, any `d`);
* `measurePreserving_incrOfPos`: in `d = 1` the increment map preserves
  Lebesgue measure on `(ℝ)^{m+n}` (a unipotent lower-triangular matrix,
  determinant one), via `Real.map_matrix_volume_pi_eq_smul_volume_pi` and
  `Matrix.det_of_isLowerTriangular`; `posEquiv` is the measurable equivalence;
* `pi_waveGreen_one`: `⊗_l G_{h_l} = 2^{-N} Lebesgue` restricted to the box
  `∏_l (-h_l, h_l)`; `lintegral_pi_waveGreen_one`: its integrals against any
  function are `∫ ∏_l g(h_l, w_l) F(w) dw`;
* headline: `spatial_waveGreen_one_eq_spatialPos`,
  `diagram_waveGreen_one_eq_diagramPos`; wrappers `spatial_bridge_paper`,
  `diagram_bridge_paper` with the manuscript's hypotheses `D ∈ Π`, `h_l > 0`
  (carried, unused: the identity holds without them).

Readings: the TeX's statement at line 5341 is the determinant-one change of
variables itself; the Lean conclusions are the resulting identities of the
spatial integrals and the diagrams, which is the use the TeX makes of it.  The
covariance enters only through `covWeight` evaluated at the positions; the
orientation of the pairs is the one fixed in `DiagramModel` (not changed here).
The covariance is any `γ : Rd 1 → ℝ≥0∞`, so it covers the TeX's smoothed
`γ_ε = p_ε * γ` (as `DiagramModel.covEps Γ ε`, line 5348) at a common width.
The pairwise widths `ε_e` of `S_{D,ε}` (line 5349) are not modelled in
`DiagramModel`; the change of variables itself does not involve the covariance
factor (`posEquiv`, `measurePreserving_incrOfPos` hold for any integrand).
Category: whole for the unlabelled `d = 1` claim at line 5341 (the change of
variables, determinant one), stated as the identity of the model's two forms.
The `d = 2, 3` analogue (line 5748, vectors in `ℝ^d`) is not formalized.

Lemmas marked "Auxiliary" serve only the Lean route.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.DiagramModel

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped ENNReal

namespace StratonovichHAMSecondMoment.DiagramBridge

open HomogHypothesis (Rd)
open WaveGreen (waveGreen)
open DiagramModel

/-! ### Positions and increments -/

/-- The increments `y_l - y_{p(l)}` of positions `y`, with the root value `0` at
the first vertex of each chain (main TeX lines 811-813 and 5339). -/
def incrOfPos (m : ℕ) {d N : ℕ} (y : Fin N → Rd d) (i : Fin N) : Rd d :=
  y i - predVal m y i

/-- Auxiliary: the predecessor of a label has the label just before. -/
theorem pred_eq_some_val (m : ℕ) {N : ℕ} (i j : Fin N) (h : pred m i = some j) :
    (j : ℕ) + 1 = i ∧ (i : ℕ) ≠ m := by
  unfold pred at h
  split_ifs at h with h0
  cases h
  simp only
  omega

/-- The positions satisfy `y_l = w_l + y_{p(l)}` (root value `0` at a first
vertex): the recursion behind "`x_l` is the sum of increments in its own chain
up to label `l`" (main TeX lines 5340-5341). -/
theorem pos_eq_add_predVal (m : ℕ) {d N : ℕ} (w : Fin N → Rd d) (i : Fin N) :
    pos m w i = w i + predVal m (pos m w) i := by
  rcases hp : pred m i with _ | j
  · rw [predVal_of_none m _ i hp, add_zero]
    have h0 := (pred_eq_none_iff m i).1 hp
    unfold pos
    rw [show Finset.univ.filter (fun j => SameChain m j i ∧ j ≤ i) = {i} by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        SameChain, Fin.le_def, Fin.ext_iff]
      omega]
    simp
  · rw [predVal_of_some m _ i j hp]
    have hj := pred_eq_some_val m i j hp
    unfold pos
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

/-- The increments of the positions are the original increments. -/
theorem incrOfPos_pos (m : ℕ) {d N : ℕ} (w : Fin N → Rd d) : incrOfPos m (pos m w) = w := by
  funext i
  rw [incrOfPos, pos_eq_add_predVal m w i, add_sub_cancel_right]

/-- The positions of the increments are the original positions. -/
theorem pos_incrOfPos (m : ℕ) {d N : ℕ} (y : Fin N → Rd d) : pos m (incrOfPos m y) = y := by
  funext i
  induction' hk : (i : ℕ) using Nat.strong_induction_on with k ih generalizing i
  rw [pos_eq_add_predVal, incrOfPos]
  rcases hp : pred m i with _ | j
  · simp [predVal_of_none m _ i hp]
  · have hj := pred_eq_some_val m i j hp
    rw [predVal_of_some m _ i j hp, predVal_of_some m _ i j hp, ih j (by omega) j rfl,
      sub_add_cancel]

/-- The increment map is measurable. -/
theorem measurable_incrOfPos (m : ℕ) {d N : ℕ} :
    Measurable (incrOfPos m (d := d) (N := N)) := by
  refine measurable_pi_iff.2 fun i => ?_
  unfold incrOfPos
  rcases hp : pred m i with _ | j
  · simp_rw [predVal_of_none m _ i hp]; exact (measurable_pi_apply i).sub measurable_const
  · simp_rw [predVal_of_some m _ i j hp]
    exact (measurable_pi_apply i).sub (measurable_pi_apply j)

/-- The positions/increments change of variables as a measurable equivalence:
increments `w ↦` positions `pos m w`, inverse `incrOfPos m`. -/
def posEquiv (m : ℕ) (d N : ℕ) : (Fin N → Rd d) ≃ᵐ (Fin N → Rd d) where
  toFun := pos m
  invFun := incrOfPos m
  left_inv := incrOfPos_pos m
  right_inv := pos_incrOfPos m
  measurable_toFun := measurable_pi_iff.2 fun i => measurable_pos m i
  measurable_invFun := measurable_incrOfPos m

/-! ### Determinant one in `d = 1` -/

/-- Auxiliary: the identification `ℝ^1 ≃ ℝ`, `y ↦ y_0`. -/
def e1 : Rd 1 ≃ᵐ ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm.trans (MeasurableEquiv.funUnique (Fin 1) ℝ)

/-- Auxiliary: `e1` preserves Lebesgue measure. -/
theorem measurePreserving_e1 : MeasurePreserving e1 volume volume :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 1)).trans
    (volume_preserving_funUnique (Fin 1) ℝ)

/-- Auxiliary: `e1` is additive. -/
theorem e1_sub (a b : Rd 1) : e1 (a - b) = e1 a - e1 b := by
  simp [e1, MeasurableEquiv.funUnique]

/-- Auxiliary: `e1` sends `0` to `0`. -/
theorem e1_zero : e1 0 = 0 := by
  simp [e1, MeasurableEquiv.funUnique]

/-- Auxiliary: the coordinatewise identification `(ℝ^1)^N ≃ ℝ^N`. -/
def eN (N : ℕ) : (Fin N → Rd 1) ≃ᵐ (Fin N → ℝ) :=
  MeasurableEquiv.piCongrRight fun _ => e1

/-- Auxiliary: `eN` preserves Lebesgue measure. -/
theorem measurePreserving_eN (N : ℕ) : MeasurePreserving (eN N) volume volume :=
  volume_preserving_pi fun _ => measurePreserving_e1

/-- Auxiliary: the matrix of the increment map in `ℝ^N`: `1` on the diagonal,
`-1` at `(l, p(l))`. -/
def incrMatrix (m N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => (if j = i then 1 else 0) - (if pred m i = some j then 1 else 0)

/-- Auxiliary: the increment matrix is lower triangular with unit diagonal, so
its determinant is one ("the spatial change of variables has determinant one",
main TeX line 5341). -/
theorem det_incrMatrix (m N : ℕ) : (incrMatrix m N).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    have : pred m i ≠ some i := fun h => by
      have := pred_eq_some_val m i i h; omega
    simp [incrMatrix, this]
  · intro i j hij
    have hij' : i < j := hij
    have h1 : j ≠ i := ne_of_gt hij'
    have h2 : pred m i ≠ some j := fun h => by
      have := pred_eq_some_val m i j h
      have : (i : ℕ) < j := hij'
      omega
    simp [incrMatrix, h1, h2]

/-- Auxiliary: the increments `v_l - v_{p(l)}` of a real vector. -/
def incrVec (m : ℕ) {N : ℕ} (v : Fin N → ℝ) (i : Fin N) : ℝ := v i - predVal m v i

/-- Auxiliary: the increment matrix acts as `v ↦ v_l - v_{p(l)}`. -/
theorem incrMatrix_mulVec (m N : ℕ) (v : Fin N → ℝ) :
    (incrMatrix m N).mulVec v = incrVec m v := by
  funext i
  simp only [Matrix.mulVec, dotProduct, incrMatrix, sub_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ]
  rcases hp : pred m i with _ | j
  · simp [incrVec, predVal_of_none m _ i hp]
  · simp [incrVec, predVal_of_some m _ i j hp]

/-- Auxiliary: the increment map in `ℝ^N` (the linear map of `incrMatrix`)
preserves Lebesgue measure. -/
theorem measurePreserving_incrMatrix (m N : ℕ) :
    MeasurePreserving (Matrix.toLin' (incrMatrix m N)) volume volume := by
  refine ⟨(Matrix.toLin' (incrMatrix m N)).continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi (by rw [det_incrMatrix]; norm_num),
    det_incrMatrix]
  simp

/-- Auxiliary: in `d = 1` the increment map is conjugate to `incrMatrix`. -/
theorem incrOfPos_eq_conj (m N : ℕ) :
    incrOfPos m (d := 1) (N := N) = (eN N).symm ∘ Matrix.toLin' (incrMatrix m N) ∘ eN N := by
  funext y
  apply (eN N).injective
  simp only [Function.comp_apply, MeasurableEquiv.apply_symm_apply, Matrix.toLin'_apply,
    incrMatrix_mulVec]
  funext i
  change e1 (incrOfPos m y i) = incrVec m (fun j => e1 (y j)) i
  rw [incrOfPos, incrVec, e1_sub]
  rcases hp : pred m i with _ | j
  · simp [predVal_of_none m _ i hp, e1_zero]
  · simp [predVal_of_some m _ i j hp]

/-- The `d = 1` increment map preserves Lebesgue measure on `(ℝ^1)^N`: the
spatial change of variables of main TeX lines 5338-5341 has determinant one. -/
theorem measurePreserving_incrOfPos (m N : ℕ) :
    MeasurePreserving (incrOfPos m (d := 1) (N := N)) volume volume := by
  rw [incrOfPos_eq_conj]
  exact (measurePreserving_eN N).symm.comp
    ((measurePreserving_incrMatrix m N).comp (measurePreserving_eN N))

/-! ### The product of the `d = 1` Green measures -/

/-- The product of the `d = 1` wave Green measures `G_{h_l} = ½ 1_{|y|<h_l} dy`
is `2^{-N}` times Lebesgue measure on the box `∏_l (-h_l, h_l)`. -/
theorem pi_waveGreen_one {N : ℕ} (h : Fin N → ℝ) :
    Measure.pi (fun i => waveGreen 1 (h i)) =
      ENNReal.ofReal (1 / 2) ^ N •
        (volume : Measure (Fin N → Rd 1)).restrict
          (Set.univ.pi fun i => Metric.ball (0 : Rd 1) (h i)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply (MeasurableSet.univ_pi hs),
    ← Set.pi_inter_distrib, volume_pi_pi]
  simp only [show ∀ i, waveGreen 1 (h i) = ENNReal.ofReal (1 / 2) •
      volume.restrict (Metric.ball (0 : Rd 1) (h i)) from fun i => rfl,
    Measure.smul_apply, smul_eq_mul, Measure.restrict_apply (hs _)]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The `d = 1` Green kernel products: `∏_l g(h_l, w_l)` is `2^{-N}` on the box
`∏_l (-h_l, h_l)` and `0` off it. -/
theorem prod_green1 {N : ℕ} (h : Fin N → ℝ) (w : Fin N → Rd 1) :
    ∏ i, green1 (h i) (w i) =
      (Set.univ.pi fun i => Metric.ball (0 : Rd 1) (h i)).indicator
        (fun _ => ENNReal.ofReal (1 / 2) ^ N) w := by
  by_cases hw : w ∈ Set.univ.pi fun i => Metric.ball (0 : Rd 1) (h i)
  · rw [Set.indicator_of_mem hw]
    simp only [green1, Set.mem_univ_pi] at hw ⊢
    simp [Set.indicator_of_mem (hw _)]
  · rw [Set.indicator_of_notMem hw]
    simp only [Set.mem_univ_pi, not_forall] at hw
    obtain ⟨i, hi⟩ := hw
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [green1, hi])

/-- Integrals against the product of the `d = 1` Green measures are integrals
against Lebesgue measure with the density `∏_l g(h_l, w_l)`, for any integrand
(no measurability needed). -/
theorem lintegral_pi_waveGreen_one {N : ℕ} (h : Fin N → ℝ)
    (F : (Fin N → Rd 1) → ℝ≥0∞) :
    ∫⁻ w, F w ∂(Measure.pi fun i => waveGreen 1 (h i)) =
      ∫⁻ w, (∏ i, green1 (h i) (w i)) * F w := by
  have hB : MeasurableSet (Set.univ.pi fun i => Metric.ball (0 : Rd 1) (h i)) :=
    MeasurableSet.univ_pi fun _ => Metric.isOpen_ball.measurableSet
  simp_rw [prod_green1, ← Set.indicator_mul_left]
  rw [pi_waveGreen_one, lintegral_smul_measure, lintegral_indicator hB,
    lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
  rfl

/-! ### The bridge -/

/-- **The `d = 1` bridge for the spatial part.**  For every covariance
`γ : Rd 1 → ℝ≥0∞` and all real time increments `h`, the increments form
`spatial (waveGreen 1) γ` (independent increments with laws `G_{h_l}`) equals the
literal positions integral `∫ ∏_l ½ 1_{|y_l - y_{p(l)}| < h_l} ∏_D γ dy`
(`E:mixed-diagram`, main TeX lines 814-824; the change of variables of
`L:d1-spatial`, lines 5338-5341). -/
theorem spatial_waveGreen_one_eq_spatialPos (γ : Rd 1 → ℝ≥0∞) (m : ℕ) {N : ℕ}
    (D : Fin N → Fin N) (h : Fin N → ℝ) :
    spatial (waveGreen 1) γ m D h = spatialPos green1 γ m D h := by
  unfold spatial spatialPos
  rw [lintegral_pi_waveGreen_one,
    ← (measurePreserving_incrOfPos m N).lintegral_comp_emb
      (posEquiv m 1 N).symm.measurableEmbedding]
  refine lintegral_congr fun y => ?_
  rw [pos_incrOfPos]
  rfl

/-- **The `d = 1` bridge for the diagrams.**  `J_{m,n,D}(t)` of
`E:mixed-diagram` (main TeX lines 814-824) in the model's increments form equals
the literal positions form, for every covariance density `γ` and every `t`. -/
theorem diagram_waveGreen_one_eq_diagramPos (γ : Rd 1 → ℝ≥0∞) (α₀ : ℝ) (m n : ℕ)
    (D : Fin (m + n) → Fin (m + n)) (t : ℝ) :
    diagram (waveGreen 1) γ α₀ m n D t = diagramPos green1 γ α₀ m n D t := by
  unfold diagram diagramPos
  simp_rw [spatial_waveGreen_one_eq_spatialPos]

/-- The spatial bridge under the manuscript's hypotheses of `L:d1-spatial`
(main TeX lines 5338-5341 and 5359-5362): `D` a pairing of the two chains and
`h_l > 0`.  Both hypotheses are carried and unused. -/
theorem spatial_bridge_paper (γ : Rd 1 → ℝ≥0∞) (m n : ℕ)
    (D : Fin (m + n) → Fin (m + n)) (_hD : D ∈ Pi2 m n) (h : Fin (m + n) → ℝ)
    (_hh : ∀ i, 0 < h i) :
    spatial (waveGreen 1) γ m D h = spatialPos green1 γ m D h :=
  spatial_waveGreen_one_eq_spatialPos γ m D h

/-- The diagram bridge for a pairing `D ∈ Π_k` (main TeX lines 814-824);
the hypothesis is carried and unused. -/
theorem diagram_bridge_paper (γ : Rd 1 → ℝ≥0∞) (α₀ : ℝ) (m n : ℕ)
    (D : Fin (m + n) → Fin (m + n)) (_hD : D ∈ Pi2 m n) (t : ℝ) :
    diagram (waveGreen 1) γ α₀ m n D t = diagramPos green1 γ α₀ m n D t :=
  diagram_waveGreen_one_eq_diagramPos γ α₀ m n D t

end StratonovichHAMSecondMoment.DiagramBridge
