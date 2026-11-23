module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

The white-noise collapse of the `d = 1` two-chain diagrams (wave L13 item D6,
part 1; the analytic half of `P:white-four`).  Main TeX file
`notes/notes_stratonovich_ham_second_moment.tex` at revision edf7085f:
* the diagram integral `E:mixed-diagram` (lines 808-824) and its
  regularization convention (lines 825-832), modelled by
  `DiagramModel.diagramLim` (the limit, as the noise width `ε ↓ 0`, of the
  diagrams with the smoothed covariance `p_ε * Γ`);
* the proof of `P:white-four` (lines 4993-5015): "identify its first pair's
  spatial positions with `x` and the other pair's positions with `y`.  The
  two delta covariances have unit mass, so spatial integration leaves `1/16`
  times the area allowed by the four Green indicators" (lines 4994-4996), and
  "the distributional delta integrations can equivalently be obtained by
  convolution with the source's spatial approximate identity: for positive
  increments the remaining bounded interval indicators have only boundary
  discontinuities, and those boundaries have two-dimensional measure zero.
  The resulting areas converge to the displayed areas" (lines 5003-5010);
  "Integrability of the time weights follows from the disjoint-pair bound"
  (lines 5013-5014).

This module proves that limit for white noise `Γ = δ₀` in `d = 1` for EVERY
diagram (all chain lengths `m, n` and every pairing `D ∈ Π`), not only for
total order four:
`diagramLim 1 δ₀ α₀ m n D t = whiteDiagram α₀ m n D t`, where
`whiteDiagram` is the time integral of `∏_{pairs} |s_j - s_h|^{-α₀}` against
the collapsed spatial factor `whiteSpatial m D h`: the Green product with the
two positions of every pair identified (one free position per pair, the
paired positions equal).  `whiteSpatial` integrates the free positions
against Lebesgue measure and, in a form convenient for the limit, carries one
standard Gaussian density per pair in the (dummy) closer coordinate, which
integrates to one (`lintegral_phi_one`; `WhiteFour.lintegral_A`/`lintegral_BC`
integrate it out for four labels).  The value is finite (`whiteDiagram_lt_top`).

Route (Lean's, following the TeX's approximate-identity remark):
* `spatialPos_white`: in `d = 1` the positions integral with `γ_ε = p_ε * δ₀ =
  p_ε` is an integral over `ℝ^N` (transport by `DiagramBridge.eN`);
* `shear`: the volume-preserving linear involution `y ↦ v` with `v_j = y_j` at
  an opener `j` and `v_c = y_{D c} - y_c` at a closer `c`, so the pair
  differences become coordinates; `scale ε` multiplies the closer coordinates by
  `√ε`, and `p_ε(√ε w) √ε = p_1(w)`: `spatialPos_white_eq` (for `ε > 0`);
* dominated convergence in `v` (bound `2^{-N} 1{|v_j| ≤ Σ h} p_1`), with the
  exceptional set `{|L_i(v)| = h_i}` null: either the linear form `L_i` is a
  coordinate or a difference of two coordinates (null by a transvection), or it
  vanishes identically and `h_i > 0` (`tendsto_spatialPos_white`);
* dominated convergence in the times, with the disjoint-pair bound
  `timeWeight_integral_lt_top` (`α₀ < 1`), taken from `TwoSimplexTime` (the
  cube integral of one pairing; L13 integration replaced this module's own
  shear proof of it) (`tendsto_diagram_white`, `diagramLim_white`).

Hypotheses: `α₀ < 1` (the manuscript's `0 < α₀ < 1`, `E:cov`, `H:homog`, main
TeX lines 379-394; positivity is not needed and is carried unused by
`diagramLim_white_paper`), `D ∈ Π` (as `IsPairing D`), `d = 1`, `Γ = δ₀` (the
white-noise case `d = α = 1`, `γ = δ₀` of `P:white-four`).  The TeX proves the
limit only for `m + n = 4`; the Lean statement covers every `m, n` (a
generalization; the TeX's own approximate-identity remark applies verbatim).
Class: whole on the model (registered model choice `DiagramModel`): the TeX's
`J_{m,n,D}(t)` for white noise IS `diagramLim 1 δ₀`.  Nothing is supplied.

Lemmas marked "Auxiliary" serve only the Lean route.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.DiagramModel
public import StratonovichHAMSecondMoment.DiagramBridge
public import StratonovichHAMSecondMoment.TwoSimplexTime

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace StratonovichHAMSecondMoment.WhiteCollapse

open HomogHypothesis (Rd)
open WaveGreen (waveGreen)
open LowAlphaConvolution (heatDens)
open DiagramModel
open DiagramBridge (e1 eN measurePreserving_eN e1_sub e1_zero pred_eq_some_val)

/-! ### The real-line integrands -/

/-- The `d = 1` Green kernel on the real line: `g(s, r) = ½ 1_{|r| < s}`
(main TeX lines 952 and 5354). -/
def g1 (s r : ℝ) : ℝ≥0∞ := if |r| < s then ENNReal.ofReal (1 / 2) else 0

/-- The centered Gaussian density of variance `ε` on the real line,
`p_ε(r) = (2πε)^{-1/2} e^{-r²/(2ε)}` (main TeX lines 5346-5348; the `d = 1` case
of `LowAlphaConvolution.heatDens`). -/
def phi (ε r : ℝ) : ℝ := (2 * π * ε) ^ (-(1 / 2 : ℝ)) * Real.exp (-(r ^ 2 / (2 * ε)))

/-- The Green product `∏_l g(h_l, y_l - y_{p(l)})` at real positions `y`. -/
def greenProd (m : ℕ) {N : ℕ} (h y : Fin N → ℝ) : ℝ≥0∞ :=
  ∏ i, g1 (h i) (y i - predVal m y i)

/-- The smoothed white-noise pair weight `∏_{(j,h) ∈ D} p_ε(y_j - y_h)`. -/
def pairDens {N : ℕ} (ε : ℝ) (D : Fin N → Fin N) (y : Fin N → ℝ) : ℝ≥0∞ :=
  ∏ j ∈ openers D, ENNReal.ofReal (phi ε (y j - y (D j)))

/-! ### Transport to `ℝ^N` -/

/-- Auxiliary: `e1 w = w 0`. -/
theorem e1_apply (w : Rd 1) : e1 w = w 0 := rfl

/-- Auxiliary: the norm on `ℝ^1` is the absolute value of `e1`. -/
theorem norm_eq_abs_e1 (w : Rd 1) : ‖w‖ = |e1 w| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs, Real.sqrt_sq_eq_abs]
  rfl

/-- Auxiliary: `green1` is `g1` after `e1`. -/
theorem green1_eq (s : ℝ) (w : Rd 1) : green1 s w = g1 s (e1 w) := by
  unfold green1 g1
  by_cases hw : w ∈ Metric.ball (0 : Rd 1) s
  · rw [Set.indicator_of_mem hw]
    rw [mem_ball_zero_iff, norm_eq_abs_e1] at hw
    simp [hw]
  · rw [Set.indicator_of_notMem hw]
    rw [mem_ball_zero_iff, norm_eq_abs_e1] at hw
    simp [hw]

/-- Auxiliary: the `d = 1` heat density is `phi` after `e1`. -/
theorem heatDens_eq (ε : ℝ) (w : Rd 1) : heatDens ε w = phi ε (e1 w) := by
  simp only [heatDens, phi, norm_eq_abs_e1, sq_abs, Nat.cast_one]

/-- Auxiliary: `p_ε * δ₀ = p_ε` for the covariance of white noise. -/
theorem covEps_dirac (ε : ℝ) (w : Rd 1) :
    covEps (Measure.dirac (0 : Rd 1)) ε w = ENNReal.ofReal (phi ε (e1 w)) := by
  rw [covEps, lintegral_dirac, sub_zero, heatDens_eq]

/-- Auxiliary: `eN` acts coordinatewise by `e1`. -/
theorem eN_apply {N : ℕ} (y : Fin N → Rd 1) (i : Fin N) : eN N y i = e1 (y i) := rfl

/-- Auxiliary: `e1` commutes with the predecessor value. -/
theorem predVal_eN (m : ℕ) {N : ℕ} (y : Fin N → Rd 1) (i : Fin N) :
    e1 (predVal m y i) = predVal m (eN N y) i := by
  rcases hp : pred m i with _ | j
  · rw [predVal_of_none m _ i hp, predVal_of_none m _ i hp, e1_zero]
  · rw [predVal_of_some m _ i j hp, predVal_of_some m _ i j hp, eN_apply]

/-- **The `d = 1` white-noise positions integral on `ℝ^N`.**  With
`γ_ε = p_ε * δ₀`, the literal positions form of the spatial part of
`E:mixed-diagram` (main TeX lines 818-822) is
`∫_{ℝ^N} ∏_l ½ 1_{|y_l - y_{p(l)}| < h_l} ∏_{(j,h) ∈ D} p_ε(y_j - y_h) dy`. -/
theorem spatialPos_white (ε : ℝ) (m : ℕ) {N : ℕ} (D : Fin N → Fin N) (h : Fin N → ℝ) :
    spatialPos green1 (covEps (Measure.dirac (0 : Rd 1)) ε) m D h =
      ∫⁻ y : Fin N → ℝ, greenProd m h y * pairDens ε D y := by
  unfold spatialPos
  rw [← (measurePreserving_eN N).lintegral_comp_emb (eN N).measurableEmbedding]
  refine lintegral_congr fun y => ?_
  unfold greenProd pairDens covWeight
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [green1_eq, e1_sub, predVal_eN, eN_apply]
  · refine Finset.prod_congr rfl fun j _ => ?_
    rw [covEps_dirac, e1_sub, eN_apply, eN_apply]

/-! ### Measurability -/

/-- Auxiliary: `g1` is jointly measurable. -/
theorem measurable_g1_uncurry : Measurable fun p : ℝ × ℝ => g1 p.1 p.2 := by
  unfold g1
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_lt (measurable_snd.abs) measurable_fst

/-- Auxiliary: the predecessor value is measurable. -/
theorem measurable_predVal (m : ℕ) {N : ℕ} (i : Fin N) :
    Measurable fun y : Fin N → ℝ => predVal m y i := by
  rcases hp : pred m i with _ | j
  · simp_rw [predVal_of_none m _ i hp]; exact measurable_const
  · simp_rw [predVal_of_some m _ i j hp]; exact measurable_pi_apply j

/-- Auxiliary: the Green product is jointly measurable in `(h, y)`. -/
theorem measurable_greenProd_uncurry (m : ℕ) {N : ℕ} :
    Measurable fun p : (Fin N → ℝ) × (Fin N → ℝ) => greenProd m p.1 p.2 := by
  unfold greenProd
  refine Finset.measurable_prod _ fun i _ => ?_
  have hm : Measurable fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      (p.1 i, p.2 i - predVal m p.2 i) :=
    ((measurable_pi_apply i).comp measurable_fst).prodMk
      (((measurable_pi_apply i).comp measurable_snd).sub
        ((measurable_predVal m i).comp measurable_snd))
  exact measurable_g1_uncurry.comp hm

/-- Auxiliary: the Green product is measurable in `y`. -/
theorem measurable_greenProd (m : ℕ) {N : ℕ} (h : Fin N → ℝ) :
    Measurable fun y : Fin N → ℝ => greenProd m h y :=
  (measurable_greenProd_uncurry m).comp (measurable_const.prodMk measurable_id)

/-- Auxiliary: `phi ε` is continuous. -/
theorem continuous_phi (ε : ℝ) : Continuous (phi ε) := by
  unfold phi; fun_prop

/-- Auxiliary: the pair weight is measurable. -/
theorem measurable_pairDens {N : ℕ} (ε : ℝ) (D : Fin N → Fin N) :
    Measurable (pairDens ε D) := by
  unfold pairDens
  refine Finset.measurable_prod _ fun j _ => ?_
  exact ENNReal.measurable_ofReal.comp ((continuous_phi ε).measurable.comp
    ((measurable_pi_apply j).sub (measurable_pi_apply (D j))))

/-! ### A product formula on `ℝ^n` -/

/-- Auxiliary: Tonelli for a product of one-variable functions on `ℝ^n`:
`∫ ∏_i f_i(v_i) dv = ∏_i ∫ f_i`. -/
theorem lintegral_pi_prod {n : ℕ} (f : Fin n → ℝ → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ v : Fin n → ℝ, ∏ i, f i (v i) = ∏ i, ∫⁻ r, f i r := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    rw [lintegral_const, one_mul, show (volume : Measure (Fin 0 → ℝ)) =
      Measure.pi fun _ => volume from rfl, Measure.pi_of_empty, measure_univ]
  | succ n ih =>
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure ℝ)) 0
    have he : ∀ v : Fin (n + 1) → ℝ,
        MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0 v = (v 0, fun j => v j.succ) := by
      intro v; ext <;> simp [MeasurableEquiv.piFinSuccAbove]; rfl
    have key : ∀ v : Fin (n + 1) → ℝ, ∏ i, f i (v i) =
        (fun p : ℝ × (Fin n → ℝ) => f 0 p.1 * ∏ j, f j.succ (p.2 j))
          (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0 v) := by
      intro v; rw [he, Fin.prod_univ_succ]
    rw [lintegral_congr key,
      show (volume : Measure (Fin (n + 1) → ℝ)) = Measure.pi fun _ => volume from rfl,
      hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)
        (fun p : ℝ × (Fin n → ℝ) => f 0 p.1 * ∏ j, f j.succ (p.2 j))]
    rw [lintegral_prod_mul (f := f 0) (g := fun w : Fin n → ℝ => ∏ j, f j.succ (w j))
      (hf 0).aemeasurable
      (Finset.measurable_prod _ fun j _ => (hf j.succ).comp (measurable_pi_apply j)).aemeasurable]
    rw [show (Measure.pi fun _ : Fin n => (volume : Measure ℝ)) = volume from rfl,
      ih (fun j => f j.succ) (fun j => hf j.succ), Fin.prod_univ_succ]

/-! ### Openers, closers and the shear -/

/-- Auxiliary: the opener of the pair containing `i`, `min(i, D i)`. -/
def opener {N : ℕ} (D : Fin N → Fin N) (i : Fin N) : Fin N := if i < D i then i else D i

/-- Auxiliary: the pairing facts used below, in the form of `mem_Pi2`. -/
def IsPairing {N : ℕ} (D : Fin N → Fin N) : Prop := ∀ i, D i ≠ i ∧ D (D i) = i

/-- Auxiliary: a closer's partner is an opener. -/
theorem lt_of_not_lt {N : ℕ} {D : Fin N → Fin N} (hD : IsPairing D) {i : Fin N}
    (hi : ¬ i < D i) : D i < D (D i) := by
  rw [(hD i).2]
  exact lt_of_le_of_ne (not_lt.1 hi) (hD i).1

/-- Auxiliary: an opener's partner is a closer. -/
theorem not_lt_of_lt {N : ℕ} {D : Fin N → Fin N} (hD : IsPairing D) {j : Fin N}
    (hj : j < D j) : ¬ D j < D (D j) := by
  rw [(hD j).2]; exact not_lt.2 hj.le

/-- The shear `v_j = y_j` at an opener `j`, `v_c = y_{D c} - y_c` at a closer
`c` (an involution; with `y = shear v`, `y_j - y_{D j} = v_{D j}`). -/
def shear {N : ℕ} (D : Fin N → Fin N) (v : Fin N → ℝ) (i : Fin N) : ℝ :=
  if i < D i then v i else v (D i) - v i

/-- Auxiliary: the shear is an involution. -/
theorem shear_shear {N : ℕ} {D : Fin N → Fin N} (hD : IsPairing D) (v : Fin N → ℝ) :
    shear D (shear D v) = v := by
  funext i
  by_cases hi : i < D i
  · simp [shear, hi]
  · have h1 := lt_of_not_lt hD hi
    simp only [shear, hi, h1, ite_false, ite_true]
    ring

/-- Auxiliary: the matrix of the shear. -/
def shearMatrix {N : ℕ} (D : Fin N → Fin N) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => if i < D i then (if j = i then 1 else 0)
    else (if j = D i then 1 else 0) - (if j = i then 1 else 0)

/-- Auxiliary: the shear is the linear map of `shearMatrix`. -/
theorem shearMatrix_mulVec {N : ℕ} (D : Fin N → Fin N) (v : Fin N → ℝ) :
    Matrix.toLin' (shearMatrix D) v = shear D v := by
  funext i
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, shearMatrix, shear]
  split_ifs
  · simp
  · simp [sub_mul, Finset.sum_sub_distrib]

/-- Auxiliary: the shear preserves Lebesgue measure (its matrix squares to the
identity, so its determinant is `±1`). -/
theorem measurePreserving_shear {N : ℕ} {D : Fin N → Fin N} (hD : IsPairing D) :
    MeasurePreserving (shear D) volume volume := by
  have hsq : shearMatrix D * shearMatrix D = 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_mul, LinearMap.comp_apply, shearMatrix_mulVec, shearMatrix_mulVec,
      shear_shear hD, Matrix.toLin'_one, LinearMap.id_apply]
  have hdet : (shearMatrix D).det * (shearMatrix D).det = 1 := by
    rw [← Matrix.det_mul, hsq, Matrix.det_one]
  have habs : |(shearMatrix D).det| = 1 := by
    have h2 : |(shearMatrix D).det| * |(shearMatrix D).det| = 1 := by
      rw [← abs_mul, hdet, abs_one]
    nlinarith [abs_nonneg (shearMatrix D).det]
  have hne : (shearMatrix D).det ≠ 0 := fun h0 => by simp [h0] at hdet
  have hfun : (Matrix.toLin' (shearMatrix D) : (Fin N → ℝ) → Fin N → ℝ) = shear D :=
    funext (shearMatrix_mulVec D)
  refine ⟨?_, ?_⟩
  · rw [← hfun]; exact (Matrix.toLin' (shearMatrix D)).continuous_of_finiteDimensional.measurable
  · rw [← hfun, Real.map_matrix_volume_pi_eq_smul_volume_pi hne, abs_inv, habs]
    simp

/-- Auxiliary: the shear is measurable. -/
theorem measurable_shear {N : ℕ} {D : Fin N → Fin N} (hD : IsPairing D) :
    Measurable (shear D) := (measurePreserving_shear hD).measurable

/-- Auxiliary: the shear at an opener and at its closer. -/
theorem shear_opener {N : ℕ} {D : Fin N → Fin N} {j : Fin N} (hj : j < D j)
    (v : Fin N → ℝ) : shear D v j = v j := by simp [shear, hj]

/-- Auxiliary: the shear at the closer of an opener `j`. -/
theorem shear_closer {N : ℕ} {D : Fin N → Fin N} (hD : IsPairing D) {j : Fin N}
    (hj : j < D j) (v : Fin N → ℝ) : shear D v (D j) = v j - v (D j) := by
  have h1 : ¬ D j < D (D j) := not_lt_of_lt hD hj
  rw [(hD j).2] at h1
  simp [shear, h1, (hD j).2]

/-- Auxiliary: the pair differences of the sheared vector are the closer
coordinates: `(shear v)_j - (shear v)_{D j} = v_{D j}`. -/
theorem shear_sub {N : ℕ} {D : Fin N → Fin N} (hD : IsPairing D) {j : Fin N}
    (hj : j < D j) (v : Fin N → ℝ) : shear D v j - shear D v (D j) = v (D j) := by
  rw [shear_opener hj, shear_closer hD hj]; ring

/-- Auxiliary: reindexing a product over the closers by the openers, and
splitting a product of one-variable factors into openers and closers. -/
theorem prod_openers_mul {N : ℕ} {D : Fin N → Fin N} (hD : IsPairing D) (a b : ℝ → ℝ≥0∞)
    (v : Fin N → ℝ) :
    (∏ j ∈ openers D, a (v j)) * ∏ j ∈ openers D, b (v (D j)) =
      ∏ i, (if i < D i then a else b) (v i) := by
  simp only [ite_apply]
  rw [Finset.prod_ite]
  congr 1
  refine Finset.prod_nbij' D D ?_ ?_ ?_ ?_ ?_
  · intro j hj
    have hj' : j < D j := by simpa [openers] using hj
    simpa using not_lt_of_lt hD hj'
  · intro i hi
    have hi' : ¬ i < D i := by simpa using hi
    simpa [openers] using lt_of_not_lt hD hi'
  · intro j _; exact (hD j).2
  · intro i _; exact (hD i).2
  · intro j _; rfl

/-- Auxiliary: the number of closers equals the number of openers. -/
theorem card_closers {N : ℕ} {D : Fin N → Fin N} (hD : IsPairing D) :
    (Finset.univ.filter fun i => ¬ i < D i).card = (openers D).card := by
  refine Finset.card_nbij' D D ?_ ?_ ?_ ?_
  · intro i hi
    have hi' : ¬ i < D i := by simpa using hi
    simpa [openers] using lt_of_not_lt hD hi'
  · intro j hj
    have hj' : j < D j := by simpa [openers] using hj
    simpa using not_lt_of_lt hD hj'
  · intro i _; exact (hD i).2
  · intro j _; exact (hD j).2

/-! ### Scaling the closer coordinates -/

/-- The scaling `v_j ↦ v_j` at an opener, `v_c ↦ √ε v_c` at a closer. -/
def scale {N : ℕ} (ε : ℝ) (D : Fin N → Fin N) (v : Fin N → ℝ) (i : Fin N) : ℝ :=
  (if i < D i then 1 else √ε) * v i

/-- Auxiliary: the scaling is the diagonal linear map. -/
theorem scale_eq_toLin' {N : ℕ} (ε : ℝ) (D : Fin N → Fin N) :
    scale ε D = Matrix.toLin' (Matrix.diagonal fun i => if i < D i then 1 else √ε) := by
  funext v i
  simp [scale, Matrix.mulVec_diagonal]

/-- Auxiliary: change of variables for the scaling, `ε > 0`:
`∫ f = (∏_i c_i) ∫ f ∘ scale`. -/
theorem lintegral_scale {N : ℕ} {ε : ℝ} (hε : 0 < ε) (D : Fin N → Fin N)
    {f : (Fin N → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ v, f v = ENNReal.ofReal (∏ i, if i < D i then (1 : ℝ) else √ε) *
      ∫⁻ v, f (scale ε D v) := by
  set M : Matrix (Fin N) (Fin N) ℝ := Matrix.diagonal fun i => if i < D i then 1 else √ε
  have hpos : 0 < ∏ i, (if i < D i then (1 : ℝ) else √ε) :=
    Finset.prod_pos fun i _ => by split_ifs <;> positivity
  have hdet : M.det = ∏ i, (if i < D i then (1 : ℝ) else √ε) := Matrix.det_diagonal
  have hmeas : Measurable (Matrix.toLin' M : (Fin N → ℝ) → Fin N → ℝ) :=
    (Matrix.toLin' M).continuous_of_finiteDimensional.measurable
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi (M := M) (by rw [hdet]; exact hpos.ne')
  have h1 : ∫⁻ v, f (scale ε D v) =
      ENNReal.ofReal |M.det⁻¹| * ∫⁻ v, f v := by
    rw [scale_eq_toLin', ← lintegral_map hf hmeas, hmap, lintegral_smul_measure, smul_eq_mul]
  rw [h1, hdet, abs_inv, abs_of_pos hpos, ← mul_assoc, ← ENNReal.ofReal_mul hpos.le,
    mul_inv_cancel₀ hpos.ne', ENNReal.ofReal_one, one_mul]

/-- Auxiliary: the scaled Gaussian, `p_ε(√ε x) = ε^{-1/2} p_1(x)` for `ε > 0`. -/
theorem phi_scale {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    phi ε (√ε * x) = ε ^ (-(1 / 2 : ℝ)) * phi 1 x := by
  unfold phi
  rw [mul_pow, Real.sq_sqrt hε.le, show 2 * π * ε = (2 * π * 1) * ε by ring,
    Real.mul_rpow (by positivity) hε.le]
  have : ε * x ^ 2 / (2 * ε) = x ^ 2 / (2 * 1) := by field_simp
  rw [this]; ring

/-- The standard Gaussian weight in the closer coordinates,
`∏_{(j, D j)} p_1(v_{D j})` (one per pair; it integrates to one). -/
def gaussW {N : ℕ} (D : Fin N → Fin N) (v : Fin N → ℝ) : ℝ≥0∞ :=
  ∏ j ∈ openers D, ENNReal.ofReal (phi 1 (v (D j)))

/-- Auxiliary: `gaussW` is measurable. -/
theorem measurable_gaussW {N : ℕ} (D : Fin N → Fin N) : Measurable (gaussW D) := by
  unfold gaussW
  refine Finset.measurable_prod _ fun j _ => ?_
  exact ENNReal.measurable_ofReal.comp ((continuous_phi 1).measurable.comp
    (measurable_pi_apply (D j)))

/-- **Change of variables for the smoothed white-noise spatial part** (`ε > 0`):
`∫ ∏ g(h_l, y_l - y_{p(l)}) ∏_D p_ε(y_j - y_h) dy =
∫ ∏ g(h_l, ·)(shear (scale ε v)) ∏_D p_1(v_{D j}) dv`. -/
theorem spatial_white_eq {N : ℕ} {ε : ℝ} (hε : 0 < ε) (m : ℕ) {D : Fin N → Fin N}
    (hD : IsPairing D) (h : Fin N → ℝ) :
    ∫⁻ y, greenProd m h y * pairDens ε D y =
      ∫⁻ v, greenProd m h (shear D (scale ε D v)) * gaussW D v := by
  have hF : Measurable fun y => greenProd m h y * pairDens ε D y :=
    (measurable_greenProd m h).mul (measurable_pairDens ε D)
  rw [← (measurePreserving_shear hD).lintegral_comp hF]
  have hpair : ∀ v, pairDens ε D (shear D v) =
      ∏ j ∈ openers D, ENNReal.ofReal (phi ε (v (D j))) := by
    intro v
    refine Finset.prod_congr rfl fun j hj => ?_
    have hj' : j < D j := by simpa [openers] using hj
    rw [shear_sub hD hj']
  simp_rw [hpair]
  have hG : Measurable fun v => greenProd m h (shear D v) *
      ∏ j ∈ openers D, ENNReal.ofReal (phi ε (v (D j))) :=
    ((measurable_greenProd m h).comp (measurable_shear hD)).mul
      (Finset.measurable_prod _ fun j _ => ENNReal.measurable_ofReal.comp
        ((continuous_phi ε).measurable.comp (measurable_pi_apply (D j))))
  rw [lintegral_scale hε D hG, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun v => ?_
  have hsc : ∀ j ∈ openers D, scale ε D v (D j) = √ε * v (D j) := by
    intro j hj
    have hj' : j < D j := by simpa [openers] using hj
    simp [scale, not_lt_of_lt hD hj']
  have hprod : ∏ j ∈ openers D, ENNReal.ofReal (phi ε (scale ε D v (D j))) =
      ENNReal.ofReal (ε ^ (-(1 / 2 : ℝ))) ^ (openers D).card * gaussW D v := by
    rw [Finset.prod_congr rfl fun j hj => by rw [hsc j hj, phi_scale hε,
      ENNReal.ofReal_mul (by positivity)], Finset.prod_mul_distrib, Finset.prod_const]
    rfl
  have hc : ENNReal.ofReal (∏ i, if i < D i then (1 : ℝ) else √ε) *
      ENNReal.ofReal (ε ^ (-(1 / 2 : ℝ))) ^ (openers D).card = 1 := by
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const, card_closers hD,
      ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← mul_pow, Real.sqrt_eq_rpow,
      ← Real.rpow_add hε, show (1 / 2 : ℝ) + -(1 / 2) = 0 by ring, Real.rpow_zero, one_pow,
      ENNReal.ofReal_one]
  rw [hprod]
  calc ENNReal.ofReal (∏ i, if i < D i then (1 : ℝ) else √ε) *
        (greenProd m h (shear D (scale ε D v)) *
          (ENNReal.ofReal (ε ^ (-(1 / 2 : ℝ))) ^ (openers D).card * gaussW D v))
      = (ENNReal.ofReal (∏ i, if i < D i then (1 : ℝ) else √ε) *
          ENNReal.ofReal (ε ^ (-(1 / 2 : ℝ))) ^ (openers D).card) *
          (greenProd m h (shear D (scale ε D v)) * gaussW D v) := by ring
    _ = _ := by rw [hc, one_mul]

/-- Auxiliary: the scaling is measurable. -/
theorem measurable_scale {N : ℕ} (ε : ℝ) (D : Fin N → Fin N) : Measurable (scale ε D) := by
  rw [scale_eq_toLin']
  exact (Matrix.toLin' (Matrix.diagonal fun i => if i < D i then (1 : ℝ) else √ε)
    ).continuous_of_finiteDimensional.measurable

/-! ### The collapsed spatial factor and the uniform bound -/

/-- Auxiliary: at `ε = 0` the closer coordinates are removed and every label
carries the coordinate of its pair's opener (the paired positions coincide). -/
theorem shear_scale_zero {N : ℕ} {D : Fin N → Fin N} (hD : IsPairing D) (v : Fin N → ℝ) :
    shear D (scale 0 D v) = fun i => v (opener D i) := by
  funext i
  by_cases hi : i < D i
  · simp [shear, scale, opener, hi]
  · have h1 := lt_of_not_lt hD hi
    simp [shear, scale, opener, hi, h1]

/-- **The collapsed white-noise spatial factor**: the Green product with the two
positions of every pair identified (`y_l = v_{opener(l)}`, one free coordinate
per pair), integrated over the free coordinates; the closer coordinates carry a
standard Gaussian weight of total mass one (`lintegral_phi_one`).  This is
"identify its first pair's spatial positions with `x` and the other pair's
positions with `y`" (main TeX lines 4993-4996) for every diagram. -/
def whiteSpatial (m : ℕ) {N : ℕ} (D : Fin N → Fin N) (h : Fin N → ℝ) : ℝ≥0∞ :=
  ∫⁻ v, greenProd m h (fun i => v (opener D i)) * gaussW D v

/-- Auxiliary: the indicator `1{|r| ≤ H}`. -/
def ind (H r : ℝ) : ℝ≥0∞ := if |r| ≤ H then 1 else 0

/-- Auxiliary: `ind H` is measurable. -/
theorem measurable_ind (H : ℝ) : Measurable (ind H) :=
  Measurable.ite (measurableSet_le measurable_id.abs measurable_const) measurable_const
    measurable_const

/-- Auxiliary: `∫ 1{|r| ≤ H} dr = 2H`. -/
theorem lintegral_ind (H : ℝ) : ∫⁻ r, ind H r = ENNReal.ofReal (2 * H) := by
  have : ind H = (Metric.closedBall (0 : ℝ) H).indicator 1 := by
    funext r
    simp [ind, Set.indicator]
  rw [this, lintegral_indicator_one Metric.isClosed_closedBall.measurableSet,
    Real.volume_closedBall]

/-- Auxiliary: `p_1` is the standard Gaussian density. -/
theorem phi_one_eq (r : ℝ) : phi 1 r = ProbabilityTheory.gaussianPDFReal 0 1 r := by
  simp only [phi, ProbabilityTheory.gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [Real.sqrt_eq_rpow, Real.rpow_neg (by positivity), neg_div]

/-- Auxiliary: `∫ p_1 = 1`. -/
theorem lintegral_phi_one : ∫⁻ r, ENNReal.ofReal (phi 1 r) = 1 := by
  simp_rw [phi_one_eq]
  exact ProbabilityTheory.lintegral_gaussianPDFReal_eq_one 0 one_ne_zero

/-- Auxiliary: if the Green product does not vanish, every position is bounded
by the sum of the time increments: `|y_i| ≤ Σ_l h_l`. -/
theorem abs_le_sum_of_greenProd_ne_zero (m : ℕ) {N : ℕ} {h y : Fin N → ℝ}
    (hg : greenProd m h y ≠ 0) (i : Fin N) : |y i| ≤ ∑ l, h l := by
  have hlt : ∀ i, |y i - predVal m y i| < h i := by
    intro i
    by_contra hc
    exact hg (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [g1, hc]))
  set hs : ℕ → ℝ := fun l => if hl : l < N then h ⟨l, hl⟩ else 0 with hs_def
  have hs_nonneg : ∀ l, 0 ≤ hs l := by
    intro l
    simp only [hs_def]
    split_ifs with hl
    · exact (abs_nonneg _).trans (hlt _).le
    · exact le_rfl
  have hs_val : ∀ j : Fin N, hs j = h j := fun j => by simp [hs_def, j.isLt]
  have key : ∀ k (i : Fin N), (i : ℕ) = k → |y i| ≤ ∑ l ∈ Finset.range (k + 1), hs l := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro i hik
      subst hik
      rw [Finset.sum_range_succ, hs_val]
      rcases hp : pred m i with _ | p
      · have := hlt i
        rw [predVal_of_none m _ i hp, sub_zero] at this
        have h0 := Finset.sum_nonneg fun l (_ : l ∈ Finset.range (i : ℕ)) => hs_nonneg l
        linarith
      · have hpv := pred_eq_some_val m i p hp
        have h1 := hlt i
        rw [predVal_of_some m _ i p hp] at h1
        have h2 := ih p (by omega) p rfl
        rw [show (i : ℕ) = (p : ℕ) + 1 from hpv.1.symm]
        calc |y i| ≤ |y i - y p| + |y p| := by
              have := abs_add_le (y i - y p) (y p); simpa using this
          _ ≤ _ := by linarith
  calc |y i| ≤ ∑ l ∈ Finset.range ((i : ℕ) + 1), hs l := key _ i rfl
    _ ≤ ∑ l ∈ Finset.range N, hs l :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 i.isLt)
          fun l _ _ => hs_nonneg l
    _ = ∑ l, h l := by
        rw [← Fin.sum_univ_eq_sum_range]
        exact Finset.sum_congr rfl fun j _ => hs_val j

/-- Auxiliary: `∏_l g(h_l, ·) ≤ 2^{-N} ∏_{openers} 1{|y_j| ≤ Σ h}`. -/
theorem greenProd_le (m : ℕ) {N : ℕ} (D : Fin N → Fin N) (h y : Fin N → ℝ) :
    greenProd m h y ≤
      ENNReal.ofReal (1 / 2) ^ N * ∏ j ∈ openers D, ind (∑ l, h l) (y j) := by
  by_cases hg : greenProd m h y = 0
  · rw [hg]; exact bot_le
  · have hb := abs_le_sum_of_greenProd_ne_zero m hg
    rw [Finset.prod_eq_one fun j _ => by simp [ind, hb j], mul_one]
    calc greenProd m h y ≤ ∏ _i : Fin N, ENNReal.ofReal (1 / 2) :=
          Finset.prod_le_prod fun i _ => by unfold g1; split_ifs <;> simp
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The uniform spatial bound `2^{-N} (2H + 1)^N`. -/
def whiteBound (N : ℕ) (H : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / 2) ^ N * (ENNReal.ofReal (2 * H) + 1) ^ N

/-- Auxiliary: the uniform bound is finite. -/
theorem whiteBound_lt_top (N : ℕ) (H : ℝ) : whiteBound N H < ⊤ := by
  unfold whiteBound
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
    (ENNReal.pow_lt_top (ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.one_lt_top⟩))

/-- Auxiliary: the uniform bound is monotone in `H`. -/
theorem whiteBound_mono (N : ℕ) {H H' : ℝ} (hH : H ≤ H') : whiteBound N H ≤ whiteBound N H' := by
  unfold whiteBound
  gcongr

/-- Auxiliary: the dominating function. -/
def domFun {N : ℕ} (D : Fin N → Fin N) (H : ℝ) (v : Fin N → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / 2) ^ N * (∏ j ∈ openers D, ind H (v j)) * gaussW D v

/-- Auxiliary: the dominating function has integral at most `whiteBound`. -/
theorem lintegral_domFun_le {N : ℕ} {D : Fin N → Fin N} (hD : IsPairing D) (H : ℝ) :
    ∫⁻ v, domFun D H v ≤ whiteBound N H := by
  set f : Fin N → ℝ → ℝ≥0∞ :=
    fun i => if i < D i then ind H else fun r => ENNReal.ofReal (phi 1 r) with hf_def
  have hf : ∀ i, Measurable (f i) := by
    intro i
    simp only [hf_def]
    split_ifs
    · exact measurable_ind H
    · exact ENNReal.measurable_ofReal.comp (continuous_phi 1).measurable
  have hdom : ∀ v, domFun D H v = ENNReal.ofReal (1 / 2) ^ N * ∏ i, f i (v i) := by
    intro v
    have hp := prod_openers_mul hD (ind H) (fun r => ENNReal.ofReal (phi 1 r)) v
    rw [domFun, mul_assoc, gaussW]
    exact congrArg _ hp
  simp_rw [hdom]
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top),
    lintegral_pi_prod f hf, whiteBound]
  gcongr
  calc ∏ i, ∫⁻ r, f i r ≤ ∏ _i : Fin N, (ENNReal.ofReal (2 * H) + 1) := by
        refine Finset.prod_le_prod fun i _ => ?_
        simp only [hf_def]
        split_ifs
        · rw [lintegral_ind]; exact le_self_add
        · rw [lintegral_phi_one]; exact le_add_self
    _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Auxiliary: the integrand is dominated, for every `ε`. -/
theorem integrand_le {N : ℕ} (m : ℕ) (ε : ℝ) {D : Fin N → Fin N} (h v : Fin N → ℝ) :
    greenProd m h (shear D (scale ε D v)) * gaussW D v ≤ domFun D (∑ l, h l) v := by
  unfold domFun
  gcongr
  refine (greenProd_le m D h _).trans (le_of_eq ?_)
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  have hj' : j < D j := by simpa [openers] using hj
  rw [shear_opener hj']
  simp [scale, hj']

/-- **Uniform bound for the smoothed spatial part** (`ε > 0`): the white-noise
positions integral is at most `2^{-N}(2 Σ h + 1)^N`, uniformly in `ε`. -/
theorem spatialPos_white_le {N : ℕ} {ε : ℝ} (hε : 0 < ε) (m : ℕ) {D : Fin N → Fin N}
    (hD : IsPairing D) (h : Fin N → ℝ) :
    spatialPos green1 (covEps (Measure.dirac (0 : Rd 1)) ε) m D h ≤ whiteBound N (∑ l, h l) := by
  rw [spatialPos_white, spatial_white_eq hε m hD h]
  exact (lintegral_mono fun v => integrand_le m ε h v).trans (lintegral_domFun_le hD _)

/-- The collapsed spatial factor obeys the same bound. -/
theorem whiteSpatial_le (m : ℕ) {N : ℕ} {D : Fin N → Fin N} (hD : IsPairing D)
    (h : Fin N → ℝ) : whiteSpatial m D h ≤ whiteBound N (∑ l, h l) := by
  unfold whiteSpatial
  refine (lintegral_mono fun v => ?_).trans (lintegral_domFun_le hD _)
  rw [← shear_scale_zero hD]
  exact integrand_le m 0 h v

/-! ### The exceptional set is null -/

/-- Auxiliary: `{v : v_a - v_b ∈ S}` is null for `a ≠ b` and a null Borel `S`
(a transvection preserves Lebesgue measure). -/
theorem null_sub {N : ℕ} {a b : Fin N} (hab : a ≠ b) {S : Set ℝ} (hS : MeasurableSet S)
    (h0 : volume S = 0) : volume {v : Fin N → ℝ | v a - v b ∈ S} = 0 := by
  set T := Matrix.toLin'
    (Matrix.TransvectionStruct.toMatrix (⟨a, b, hab, -1⟩ : Matrix.TransvectionStruct (Fin N) ℝ))
  have hT : ∀ v, T v a = v a - v b := by
    intro v
    simp [T, Matrix.TransvectionStruct.toMatrix, Matrix.transvection,
      Matrix.mulVec, dotProduct, Matrix.single_apply]
    ring
  have hset : {v : Fin N → ℝ | v a - v b ∈ S} = T ⁻¹' (Function.eval a ⁻¹' S) := by
    ext v; simp [hT]
  rw [hset, (Real.volume_preserving_transvectionStruct _).measure_preimage
    (measurableSet_preimage (measurable_pi_apply a) hS).nullMeasurableSet]
  exact Measure.pi_eval_preimage_null (fun _ : Fin N => (volume : Measure ℝ)) (i := a) h0

/-- Auxiliary: `{r : |r| = c}` is Lebesgue-null. -/
theorem volume_abs_eq (c : ℝ) : volume {r : ℝ | |r| = c} = 0 := by
  refine measure_mono_null (t := {c, -c}) (fun r hr => ?_) ((Set.toFinite _).measure_zero volume)
  simp only [Set.mem_ofPred_eq] at hr
  rcases abs_choice r with h | h
  · left; linarith
  · right; simp; linarith

/-- Auxiliary: `{r : |r| = c}` is closed. -/
theorem measurableSet_abs_eq (c : ℝ) : MeasurableSet {r : ℝ | |r| = c} :=
  (isClosed_eq continuous_abs continuous_const).measurableSet

/-- Auxiliary: for positive increments, almost every `v` avoids every boundary
`|L_i(v)| = h_i` of the collapsed Green indicators ("those boundaries have
two-dimensional measure zero", main TeX lines 5005-5006). -/
theorem ae_good (m : ℕ) {N : ℕ} (D : Fin N → Fin N) {h : Fin N → ℝ} (hh : ∀ i, 0 < h i) :
    ∀ᵐ v : Fin N → ℝ, ∀ i,
      |v (opener D i) - predVal m (fun j => v (opener D j)) i| ≠ h i := by
  rw [ae_all_iff]
  intro i
  rw [ae_iff]
  simp only [ne_eq, not_not]
  rcases hp : pred m i with _ | p
  · simp_rw [predVal_of_none m _ i hp, sub_zero]
    exact Measure.pi_eval_preimage_null (fun _ : Fin N => (volume : Measure ℝ))
      (i := opener D i) (volume_abs_eq (h i))
  · simp_rw [predVal_of_some m _ i p hp]
    by_cases heq : opener D i = opener D p
    · simp [heq, (hh i).ne]
    · exact null_sub heq (measurableSet_abs_eq (h i)) (volume_abs_eq (h i))

/-! ### The spatial limit -/

/-- Auxiliary: one scaled coordinate is continuous in `ε`. -/
theorem continuous_scale_apply {N : ℕ} (D : Fin N → Fin N) (v : Fin N → ℝ) (j : Fin N) :
    Continuous fun ε => scale ε D v j := by
  unfold scale
  split_ifs
  · exact continuous_const
  · exact Real.continuous_sqrt.mul continuous_const

/-- Auxiliary: one sheared coordinate is continuous in `ε`. -/
theorem continuous_shear_scale {N : ℕ} (D : Fin N → Fin N) (v : Fin N → ℝ) (i : Fin N) :
    Continuous fun ε => shear D (scale ε D v) i := by
  unfold shear
  split_ifs
  · exact continuous_scale_apply D v i
  · exact (continuous_scale_apply D v (D i)).sub (continuous_scale_apply D v i)

/-- Auxiliary: the pointwise limit of the integrand away from the boundaries. -/
theorem tendsto_integrand (m : ℕ) {N : ℕ} {D : Fin N → Fin N} (hD : IsPairing D)
    (h v : Fin N → ℝ)
    (hv : ∀ i, |v (opener D i) - predVal m (fun j => v (opener D j)) i| ≠ h i) :
    Tendsto (fun ε => greenProd m h (shear D (scale ε D v)) * gaussW D v) (𝓝[>] 0)
      (𝓝 (greenProd m h (fun i => v (opener D i)) * gaussW D v)) := by
  set L : ℝ → Fin N → ℝ :=
    fun ε i => shear D (scale ε D v) i - predVal m (shear D (scale ε D v)) i with hL
  have hcont : ∀ i, Continuous fun ε => L ε i := by
    intro i
    refine (continuous_shear_scale D v i).sub ?_
    rcases hp : pred m i with _ | p
    · simp_rw [predVal_of_none m _ i hp]; exact continuous_const
    · simp_rw [predVal_of_some m _ i p hp]; exact continuous_shear_scale D v p
  have hL0 : ∀ i, L 0 i = v (opener D i) - predVal m (fun j => v (opener D j)) i := by
    intro i; simp only [hL, shear_scale_zero hD]
  have heach : ∀ i, ∀ᶠ ε in 𝓝 (0 : ℝ), g1 (h i) (L ε i) = g1 (h i) (L 0 i) := by
    intro i
    have hta : Tendsto (fun ε => |L ε i|) (𝓝 0) (𝓝 |L 0 i|) :=
      (continuous_abs.comp (hcont i)).tendsto 0
    rcases lt_or_gt_of_ne (hL0 i ▸ hv i) with hlt | hgt
    · filter_upwards [hta.eventually (gt_mem_nhds hlt)] with ε hε
      simp [g1, hε, hlt]
    · filter_upwards [hta.eventually (lt_mem_nhds hgt)] with ε hε
      simp [g1, not_lt.2 hε.le, not_lt.2 hgt.le]
  have hall : ∀ᶠ ε in 𝓝 (0 : ℝ),
      greenProd m h (shear D (scale ε D v)) = greenProd m h (shear D (scale 0 D v)) := by
    filter_upwards [eventually_all.2 heach] with ε hε
    exact Finset.prod_congr rfl fun i _ => hε i
  refine tendsto_nhdsWithin_of_tendsto_nhds ?_
  rw [← shear_scale_zero hD]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hall] with ε hε
  rw [hε]

/-- **The white-noise spatial limit.**  For a pairing `D` and positive time
increments `h`, the smoothed spatial part of `E:mixed-diagram` with
`γ_ε = p_ε * δ₀` converges, as `ε ↓ 0`, to the collapsed factor `whiteSpatial`
(main TeX lines 4993-5010). -/
theorem tendsto_spatial_white (m : ℕ) {N : ℕ} {D : Fin N → Fin N} (hD : IsPairing D)
    {h : Fin N → ℝ} (hh : ∀ i, 0 < h i) :
    Tendsto (fun ε => spatialPos green1 (covEps (Measure.dirac (0 : Rd 1)) ε) m D h)
      (𝓝[>] 0) (𝓝 (whiteSpatial m D h)) := by
  have heq : (fun ε => ∫⁻ v, greenProd m h (shear D (scale ε D v)) * gaussW D v) =ᶠ[𝓝[>] 0]
      fun ε => spatialPos green1 (covEps (Measure.dirac (0 : Rd 1)) ε) m D h := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [spatialPos_white, spatial_white_eq hε m hD h]
  refine Tendsto.congr' heq ?_
  unfold whiteSpatial
  refine tendsto_lintegral_filter_of_dominated_convergence (domFun D (∑ l, h l))
    (Eventually.of_forall fun ε => ((measurable_greenProd m h).comp
      ((measurable_shear hD).comp (measurable_scale ε D))).mul (measurable_gaussW D))
    (Eventually.of_forall fun ε => Eventually.of_forall fun v => integrand_le m ε h v)
    ((lintegral_domFun_le hD _).trans_lt (whiteBound_lt_top N _)).ne
    ((ae_good m D hh).mono fun v hv => tendsto_integrand m hD h v hv)

/-! ### The time weights: the disjoint-pair bound -/

/-- **The disjoint-pair bound** (main TeX lines 5013-5014): for `α₀ < 1`
the time weight `∏_{(j,h) ∈ D} |s_j - s_h|^{-α₀}` is integrable over the two
time simplices.  (L13 integration: proved through `TwoSimplexTime`, the shared
time-simplex facts: the simplices lie in the cube `(0, |t|)^{m+n}`, on which one
pairing integrates to `pairInt^k` (`lintegral_cube_timeWeight`, main TeX lines
5497-5500), finite by `pairInt_eq` (lines 5494-5497).) -/
theorem timeWeight_integral_lt_top {α₀ : ℝ} (hα1 : α₀ < 1) (m n : ℕ)
    {D : Fin (m + n) → Fin (m + n)} (hD : IsPairing D) (t : ℝ) :
    ∫⁻ s in twoSimplex m n t, timeWeight α₀ D s < ⊤ := by
  have hP : D ∈ Pi2 m n := mem_Pi2.2 hD
  obtain ⟨k, hk⟩ : Even (m + n) := by
    by_contra hodd
    rw [Pi2_odd (Nat.not_even_iff_odd.1 hodd)] at hP
    exact Finset.notMem_empty _ hP
  have hsub : twoSimplex m n t ⊆ TwoSimplexTime.cube (m + n) |t| := by
    intro s hs i _
    exact ⟨pos_of_mem_twoSimplex hs i, (hs i).2.trans_le (le_abs_self t)⟩
  calc ∫⁻ s in twoSimplex m n t, timeWeight α₀ D s
      ≤ ∫⁻ s in TwoSimplexTime.cube (m + n) |t|, timeWeight α₀ D s := lintegral_mono_set hsub
    _ = TwoSimplexTime.pairInt α₀ |t| ^ k :=
        TwoSimplexTime.lintegral_cube_timeWeight hP (by omega) α₀ |t|
    _ < ⊤ := by
        rw [TwoSimplexTime.pairInt_eq hα1 (abs_nonneg t)]
        exact (ENNReal.pow_ne_top ENNReal.ofReal_ne_top).lt_top

/-- Auxiliary: almost every time vector has distinct paired times, so its
time weight is finite. -/
theorem ae_timeWeight_ne_top {N : ℕ} (α₀ : ℝ) {D : Fin N → Fin N} (hD : IsPairing D) :
    ∀ᵐ s : Fin N → ℝ, timeWeight α₀ D s ≠ ⊤ := by
  have hall : ∀ᵐ s : Fin N → ℝ, ∀ i, s i ≠ s (D i) := by
    rw [ae_all_iff]
    intro i
    rw [ae_iff]
    simp only [ne_eq, not_not]
    have := null_sub (a := i) (b := D i) (Ne.symm (hD i).1) (measurableSet_singleton 0)
      (measure_singleton 0)
    simpa [sub_eq_zero] using this
  filter_upwards [hall] with s hs
  exact (timeWeight_lt_top α₀ D s (fun i => Or.inl (hs i)) fun i => (hD i).1).ne

/-- Auxiliary: on the simplices the increments sum to at most `(m + n) t`. -/
theorem sum_incr_le {m n : ℕ} {t : ℝ} {s : Fin (m + n) → ℝ} (hs : s ∈ twoSimplex m n t) :
    ∑ l, incr m s l ≤ ((m + n : ℕ) : ℝ) * t := by
  have h : ∀ l, incr m s l ≤ t := by
    intro l
    have hp : 0 ≤ predVal m s l := by
      rcases hp : pred m l with _ | p
      · rw [predVal_of_none m _ l hp]
      · rw [predVal_of_some m _ l p hp]; exact (pos_of_mem_twoSimplex hs p).le
    have := (hs l).2
    unfold incr; linarith
  calc ∑ l, incr m s l ≤ ∑ _l : Fin (m + n), t := Finset.sum_le_sum fun l _ => h l
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ### The white-noise diagrams -/

/-- **The white-noise diagram** `J_{m,n,D}(t)` for `d = 1`, `γ = δ₀`: the time
integral over `[0,t]^m_< × [0,t]^n_<` of `∏_{(j,h) ∈ D} |s_j - s_h|^{-α₀}` times
the collapsed spatial factor `whiteSpatial` at the increments
`h_l = s_l - s_{p(l)}` (main TeX lines 814-824 and 4993-4996). -/
def whiteDiagram (α₀ : ℝ) (m n : ℕ) (D : Fin (m + n) → Fin (m + n)) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in twoSimplex m n t, timeWeight α₀ D s * whiteSpatial m D (incr m s)

/-- Auxiliary: the smoothed spatial part is measurable in the increments. -/
theorem measurable_spatialPos_white (ε : ℝ) (m : ℕ) {N : ℕ} (D : Fin N → Fin N) :
    Measurable fun h : Fin N → ℝ =>
      spatialPos green1 (covEps (Measure.dirac (0 : Rd 1)) ε) m D h := by
  simp_rw [spatialPos_white]
  exact Measurable.lintegral_prod_right'
    (f := fun p : (Fin N → ℝ) × (Fin N → ℝ) => greenProd m p.1 p.2 * pairDens ε D p.2)
    ((measurable_greenProd_uncurry m).mul ((measurable_pairDens ε D).comp measurable_snd))

/-- **The white-noise limit of every `d = 1` diagram** (`P:white-four`'s
analytic step, main TeX lines 4993-5014, for all `m, n` and `D ∈ Π`): the
diagrams with the smoothed covariance `p_ε * δ₀` converge, as `ε ↓ 0`, to
`whiteDiagram`. -/
theorem tendsto_diagram_white {α₀ : ℝ} (hα1 : α₀ < 1) (m n : ℕ)
    {D : Fin (m + n) → Fin (m + n)} (hD : IsPairing D) (t : ℝ) :
    Tendsto (fun ε => diagram (waveGreen 1) (covEps (Measure.dirac (0 : Rd 1)) ε) α₀ m n D t)
      (𝓝[>] 0) (𝓝 (whiteDiagram α₀ m n D t)) := by
  simp_rw [DiagramBridge.diagram_waveGreen_one_eq_diagramPos]
  unfold diagramPos whiteDiagram
  set C := whiteBound (m + n) (((m + n : ℕ) : ℝ) * t)
  refine tendsto_lintegral_filter_of_dominated_convergence (fun s => timeWeight α₀ D s * C)
    (Eventually.of_forall fun ε => (measurable_timeWeight α₀ D).mul
      ((measurable_spatialPos_white ε m D).comp (measurable_incr m))) ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards [ae_restrict_mem (measurableSet_twoSimplex m n t)] with s hs
    exact mul_le_mul_right ((spatialPos_white_le hε m hD _).trans
      (whiteBound_mono _ (sum_incr_le hs))) _
  · rw [lintegral_mul_const' _ _ (whiteBound_lt_top _ _).ne]
    exact ENNReal.mul_ne_top (timeWeight_integral_lt_top hα1 m n hD t).ne
      (whiteBound_lt_top _ _).ne
  · filter_upwards [ae_restrict_mem (measurableSet_twoSimplex m n t),
      ae_restrict_of_ae (ae_timeWeight_ne_top α₀ hD)] with s hs htop
    exact ENNReal.Tendsto.const_mul (tendsto_spatial_white m hD (incr_pos hs)) (Or.inr htop)

/-- **`J_{m,n,D}(t)` for white noise in `d = 1`.**  The model's diagram limit
for `Γ = δ₀` is the collapsed white-noise diagram. -/
theorem diagramLim_white {α₀ : ℝ} (hα1 : α₀ < 1) (m n : ℕ)
    {D : Fin (m + n) → Fin (m + n)} (hD : IsPairing D) (t : ℝ) :
    diagramLim 1 (Measure.dirac 0) α₀ m n D t = whiteDiagram α₀ m n D t :=
  (tendsto_diagram_white hα1 m n hD t).limUnder_eq

/-- The white-noise diagrams are finite. -/
theorem whiteDiagram_lt_top {α₀ : ℝ} (hα1 : α₀ < 1) (m n : ℕ)
    {D : Fin (m + n) → Fin (m + n)} (hD : IsPairing D) (t : ℝ) :
    whiteDiagram α₀ m n D t < ⊤ := by
  set C := whiteBound (m + n) (((m + n : ℕ) : ℝ) * t)
  calc whiteDiagram α₀ m n D t ≤ ∫⁻ s in twoSimplex m n t, timeWeight α₀ D s * C := by
        refine setLIntegral_mono' (measurableSet_twoSimplex m n t) fun s hs => ?_
        exact mul_le_mul_right ((whiteSpatial_le m hD _).trans
          (whiteBound_mono _ (sum_incr_le hs))) _
    _ = (∫⁻ s in twoSimplex m n t, timeWeight α₀ D s) * C :=
        lintegral_mul_const' _ _ (whiteBound_lt_top _ _).ne
    _ < ⊤ := ENNReal.mul_lt_top (timeWeight_integral_lt_top hα1 m n hD t)
        (whiteBound_lt_top _ _)

/-- Auxiliary: a pairing in `Π` is a fixed-point-free involution. -/
theorem isPairing_of_mem {m n : ℕ} {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n) :
    IsPairing D := mem_Pi2.1 hD

/-- The white-noise limit under the manuscript's hypotheses (`P:white-four`,
main TeX lines 4946-4948, with `E:cov`: `d = α = 1`, `γ = δ₀`, `0 < α₀ < 1`,
`D ∈ Π`): the TeX's `J_{m,n,D}(t)` exists, equals `whiteDiagram` and is
finite, for every `m, n` (not only `m + n = 4`). -/
theorem diagramLim_white_paper {α₀ : ℝ} (hα : 0 < α₀ ∧ α₀ < 1) (m n : ℕ)
    {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n) (t : ℝ) :
    Tendsto (fun ε => diagram (waveGreen 1) (covEps (Measure.dirac (0 : Rd 1)) ε) α₀ m n D t)
      (𝓝[>] 0) (𝓝 (diagramLim 1 (Measure.dirac 0) α₀ m n D t)) ∧
    diagramLim 1 (Measure.dirac 0) α₀ m n D t = whiteDiagram α₀ m n D t ∧
    diagramLim 1 (Measure.dirac 0) α₀ m n D t < ⊤ := by
  have hP := isPairing_of_mem hD
  rw [diagramLim_white hα.2 m n hP t]
  exact ⟨tendsto_diagram_white hα.2 m n hP t, rfl,
    whiteDiagram_lt_top hα.2 m n hP t⟩

end StratonovichHAMSecondMoment.WhiteCollapse
