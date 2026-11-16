module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

`L:d1-spatial` (Spatial estimate) of the main TeX file
`notes/notes_stratonovich_ham_second_moment.tex` at revision 39f2597a (wave L13
item D1): statement at main TeX lines 5359-5379 (`E:d1-spatial-product`, lines
5364-5373, and `E:d1-spatial-max`, lines 5374-5378), proof at lines 5381-5442;
the covariances `E:d1-covariances` (lines 5317-5322), the constant `K_sp` of
`E:d1-constants` (lines 5324-5332), the standing `0 < α₀ < 1` (line 5315), and
the increment variables and `S_{D,ε}(h)` (lines 5338-5356).

How the TeX's objects map to the model (`DiagramModel`, a registered model
choice; `DiagramBridge`):
* labels are 0-based (`i : Fin N` is the TeX label `i + 1`); the two chains,
  their separate roots and the positions `x_l` (sums of the increments of the
  own chain up to `l`, lines 5338-5341) are `DiagramModel.pos m`;
* `G(h, y) = ½ 1_{|y|<h}` (line 5354) is `waveGreen 1 h` as a measure of the
  increment (`DiagramModel.waveGreen_one_eq`), and the TeX's `dy`-integral over
  the increments is the product measure `Measure.pi`;
* `S_{D,ε}(h)` with a separate width `ε_e > 0` for every pair (lines
  5348-5355) is `spatialPair (waveGreen 1) (fun i => covEps Γ (εs i)) m D h`
  (new definition `spatialPair`; the pair is named by its opening label `i`,
  and `covEps Γ ε = p_ε * Γ` is the model's `γ_ε`).  With one width for all
  pairs it is the model's `DiagramModel.spatial (waveGreen 1) (covEps Γ ε)`
  (`spatialPair_const`, definitional), the form in `DiagramModel.diagram`.
  Nothing is narrower for distinct widths: the theorems hold for every family
  `εs` and the bounds do not depend on it ("uniformly in `ε`", line 5362);
* the Riesz case of `E:d1-covariances` is `Γ = c|y|^{-α} dy`, i.e.
  `volume.withDensity (HigherRieszTwo.riesz c α)`; the white case is
  `Γ = c δ₀ = WhiteModel.whiteCov c`, so `γ_ε = c p_ε` (`covEps_whiteCov`);
* the TeX evaluates the pair `(i, j)`, `i < j`, as `γ_ε(x_j - x_i)`; the model
  (`DiagramModel.covWeight`, frozen) as `γ_ε(x_i - x_j)`.  Both covariances are
  even (`covEps_riesz_neg`, `covEps_white_neg`), so the two integrands agree;
* `O_D` is `DiagramModel.openers D` and `C_D` is the new `closers D`; a pairing
  is a `FiniteWick` fixed-point-free involution (`D ∈ Pi2 m n`), with
  self-pairings inside one chain (lines 809-810).

Formalized (all proved, nothing supplied):
* `spatialPair_le` (the integration in descending label order, lines
  5411-5425), for any dimension, any σ-finite Green family and one covariance
  per pair: if every closing label `l` has the convolution bound
  `∫ γ_{D l}(z - v) G_{h_l}(dv) ≤ c_l` for all `z`, then
  `S ≤ ∏_{C_D} c_l ∏_{O_D} G_{h_i}(ℝ^d)`; with `pos_update_of_lt`,
  `pos_update_self` (lines 5415-5418) and `card_closers` (`k` labels of each
  type, line 5424);
* the convolution bounds (lines 5389-5405): `lintegral_shift_le` (the
  rearrangement, by the layer-cake formula), `lintegral_centered_le`,
  `riesz_conv_le` (`≤ c h^{1-α}/(1-α)`), `smoothCov_conv_le` (Tonelli,
  mass one), `riesz_eps_conv_le`, `white_eps_conv_le` (`≤ c/2`), all uniform
  in `ε > 0`;
* headline: `d1_spatial_riesz`, `d1_spatial_white` (`E:d1-spatial-product`)
  and `d1_spatial_riesz_max`, `d1_spatial_white_max` (`E:d1-spatial-max`, via
  `amgm_riesz`, `riesz_constant_eq`, `amgm_white`), with separate widths;
* model forms with one common width (for `P:d1-upper`): `spatial_riesz_le`,
  `spatial_white_le` (both displays), and the positions forms
  `spatialPos_riesz_le`, `spatialPos_white_le` through `DiagramBridge`;
* wrappers with the manuscript's hypotheses: `d1_spatial_paper_riesz`,
  `d1_spatial_paper_white` (carried and unused: `0 < α₀ < 1`; `c > 0`,
  `h_l > 0` used only as `≥ 0`; `k ≥ 1` used only for `E:d1-spatial-max`);
* refutation support: `selfPair`, `spatialPair_selfPair` (the exact value of
  the smallest diagram).

Differences from the TeX's route (statements unchanged): the TeX states the
Riesz supremum as an equality (line 5394); only the upper bound is used and
proved.  The rearrangement is proved by comparing level sets.  The white
constant is stated in the TeX's unified form with `b = 1`, `K_sp = c_δ` as
`c^k t^k / k^k`.  The lemma's hypotheses `h_l > 0` and `c > 0` are weakened to
`≥ 0`.

Category: whole on the model.  Every conclusion of `L:d1-spatial` (both
displays, both covariance cases, every pairing and split, separate widths,
uniformity in the widths) is a Lean conclusion under the TeX's hypotheses.

Lemmas marked "Auxiliary" serve only the Lean route.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.DiagramModel
public import StratonovichHAMSecondMoment.DiagramBridge
public import StratonovichHAMSecondMoment.HigherRieszTwo
public import StratonovichHAMSecondMoment.WhiteModel

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace StratonovichHAMSecondMoment.D1Spatial

open HomogHypothesis (Rd)
open WaveGreen (waveGreen waveGreen_mass coordOne coordOne_mp norm_coord_one
  ball_eq_preimage_coordOne)
open DiagramModel
open FiniteWick (pairings mem_pairings)
open LowAlphaConvolution (heatDens lintegral_rpow_Ioc)
open VariationalMean (heatK)
open HigherRieszTwo (riesz smoothCov smoothCov_eq measurable_riesz measurable_smoothCov
  measurable_heatK lintegral_heatK)
open WhiteModel (whiteCov)

/-! ### Closing labels and the spatial integral with one covariance per pair -/

/-- The closing labels `C_D` of a pairing: each pair `{i, j} ∈ D`, oriented by
`i < j` (main TeX lines 5361-5362), is represented by its larger label
`j = D i`.  The opening labels `O_D` are `DiagramModel.openers D`. -/
def closers {N : ℕ} (D : Fin N → Fin N) : Finset (Fin N) :=
  Finset.univ.filter fun i => D i < i

/-- `S_{D,ε}(h)` of main TeX lines 5346-5356, with a separate covariance for every
pair: the increments `w_l` are independent with laws `G_{h_l}`, and the pair
`{i, D i}` with opener `i < D i` carries the factor `γ_i(x_i - x_{D i})` at the
positions `x = pos m w`.  With `G = waveGreen 1` (`G_h(dy) = ½ 1_{|y|<h} dy`,
`DiagramModel.waveGreen_one_eq`) and `γ_i = γ_{ε_i} = p_{ε_i} * γ`
(`DiagramModel.covEps`) this is the TeX's integral with the separate widths
`ε_e`, the pair `e` being named by its opening label.  With one covariance for
all pairs it is `DiagramModel.spatial` (`spatialPair_const`). -/
def spatialPair {d : ℕ} (G : ℝ → Measure (Rd d)) {N : ℕ} (γs : Fin N → Rd d → ℝ≥0∞)
    (m : ℕ) (D : Fin N → Fin N) (h : Fin N → ℝ) : ℝ≥0∞ :=
  ∫⁻ w, ∏ i ∈ openers D, γs i (pos m w i - pos m w (D i)) ∂(Measure.pi fun i => G (h i))

/-- With the same covariance for every pair, `spatialPair` is the model's
`DiagramModel.spatial`. -/
theorem spatialPair_const {d : ℕ} (G : ℝ → Measure (Rd d)) {N : ℕ} (γ : Rd d → ℝ≥0∞)
    (m : ℕ) (D : Fin N → Fin N) (h : Fin N → ℝ) :
    spatialPair G (fun _ => γ) m D h = spatial G γ m D h := rfl

/-- The Riesz constant `K_sp` of `E:d1-constants` (main TeX lines
5326-5329), `c 2^{2-α} (1-α)^{-α} / (2-α)^{2-α}`. -/
def Ksp (c α : ℝ) : ℝ := c * 2 ^ (2 - α) * (1 - α) ^ (-α) / (2 - α) ^ (2 - α)

/-! ### Pairings -/

/-- Auxiliary to the Lean proof route: a pairing in `FiniteWick` form is a
fixed-point-free involution. -/
theorem pairing_inv {N : ℕ} {D : Fin N → Fin N} (hD : D ∈ pairings (Finset.univ : Finset (Fin N)))
    (i : Fin N) : D i ≠ i ∧ D (D i) = i :=
  ⟨((mem_pairings.1 hD).1 i (Finset.mem_univ _)).2.1,
    ((mem_pairings.1 hD).1 i (Finset.mem_univ _)).2.2⟩

/-- Auxiliary to the Lean proof route: the labels that are not closing are the
opening labels. -/
theorem filter_not_closing {N : ℕ} {D : Fin N → Fin N} (hne : ∀ i, D i ≠ i) :
    (Finset.univ.filter fun i => ¬ D i < i) = openers D := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, openers, not_lt]
  exact ⟨fun h => lt_of_le_of_ne h (hne i).symm, fun h => h.le⟩

/-- A pairing of `2k` labels has `k` closing labels (and `k` opening labels,
`DiagramModel.card_openers`), as used at main TeX line 5424 ("there are `k` labels
of each type"). -/
theorem card_closers {N k : ℕ} {D : Fin N → Fin N}
    (hD : D ∈ pairings (Finset.univ : Finset (Fin N))) (hN : N = 2 * k) :
    (closers D).card = k := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin N))) (fun i => D i < i)
  rw [filter_not_closing fun i => (pairing_inv hD i).1, card_openers hD hN, Finset.card_univ,
    Fintype.card_fin] at hsplit
  change (closers D).card + k = N at hsplit
  omega

/-! ### Positions under a change of one increment -/

/-- Changing the increment at label `l` does not move the positions at earlier
labels: positions involve only earlier increments of their own chain (main TeX
lines 5416-5418). -/
theorem pos_update_of_lt (m : ℕ) {d N : ℕ} (w : Fin N → Rd d) {l i : Fin N} (hi : i < l)
    (v : Rd d) : pos m (Function.update w l v) i = pos m w i := by
  unfold pos
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ i := (Finset.mem_filter.1 hj).2.2
  exact Function.update_of_ne (ne_of_lt (lt_of_le_of_lt hj' hi)) _ _

/-- Changing the increment at label `l` shifts the position at `l` by the change:
`x_l = (x_l - y_l) + y_l` with `x_l - y_l` independent of `y_l` (main TeX line
5415, "`x_l - x_i = y_l + z`, where `z` is independent of `y_l`"). -/
theorem pos_update_self (m : ℕ) {d N : ℕ} (w : Fin N → Rd d) (l : Fin N) (v : Rd d) :
    pos m (Function.update w l v) l = (pos m w l - w l) + v := by
  have hmem : l ∈ Finset.univ.filter (fun j => SameChain m j l ∧ j ≤ l) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, Iff.rfl, le_rfl⟩
  unfold pos
  rw [Finset.sum_update_of_mem hmem, ← Finset.add_sum_erase _ w hmem,
    Finset.sdiff_singleton_eq_erase]
  abel

/-! ### The integration in descending label order -/

/-- **The integration step of `L:d1-spatial`** (main TeX lines 5411-5425), for any
dimension, any family `G` of σ-finite measures and one covariance `γ_i` per pair:
if for every closing label `l` (its pair is `(D l, l)`, `D l < l`) the convolution
bound `∫ γ_{D l}(z - v) G_{h_l}(dv) ≤ c_l` holds for every shift `z`, then
`S ≤ ∏_{l ∈ C_D} c_l ∏_{i ∈ O_D} G_{h_i}(ℝ^d)`.  The proof integrates the
increments in descending label order `N-1, …, 0`, keeping the TeX's invariant:
before label `L` the remaining covariance factors are exactly the pairs whose
closing label is below `L` (here through the iterated marginals
`MeasureTheory.lmarginal`). -/
theorem spatialPair_le {d : ℕ} (G : ℝ → Measure (Rd d)) [∀ s, SigmaFinite (G s)] {N : ℕ}
    (γs : Fin N → Rd d → ℝ≥0∞) (hγ : ∀ i, Measurable (γs i)) (m : ℕ) (D : Fin N → Fin N)
    (hD : ∀ i, D i ≠ i ∧ D (D i) = i) (h : Fin N → ℝ) (c : Fin N → ℝ≥0∞)
    (hconv : ∀ l, D l < l → ∀ z, ∫⁻ v, γs (D l) (z - v) ∂G (h l) ≤ c l) :
    spatialPair G γs m D h ≤ (∏ l ∈ closers D, c l) * ∏ i ∈ openers D, G (h i) Set.univ := by
  classical
  let μ : Fin N → Measure (Rd d) := fun i => G (h i)
  let Q : (Fin N → Rd d) → Fin N → ℝ≥0∞ := fun x i => γs i (pos m x i - pos m x (D i))
  have hQm : ∀ i, Measurable fun x => Q x i := fun i =>
    (hγ i).comp ((measurable_pos m i).sub (measurable_pos m (D i)))
  have hPm : ∀ s : Finset (Fin N), Measurable fun x => ∏ i ∈ s, Q x i := fun s =>
    Finset.measurable_prod _ fun i _ => hQm i
  let e : Fin N → ℝ≥0∞ := fun l => if D l < l then c l else μ l Set.univ
  let T : ℕ → Finset (Fin N) := fun L => Finset.univ.filter fun l => L ≤ (l : ℕ)
  let R : ℕ → Finset (Fin N) := fun L => (openers D).filter fun i => ((D i : Fin N) : ℕ) < L
  let F : (Fin N → Rd d) → ℝ≥0∞ := fun y => ∏ i ∈ openers D, Q y i
  have key : ∀ j L, L + j = N → ∀ x,
      lmarginal μ (T L) F x ≤ (∏ l ∈ T L, e l) * ∏ i ∈ R L, Q x i := by
    intro j
    induction j with
    | zero =>
      intro L hL x
      have hT : T L = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun l _ => ?_
        have := l.isLt; omega
      have hR : R L = openers D := by
        refine Finset.filter_true_of_mem fun i _ => ?_
        have := (D i).isLt; omega
      rw [hT, hR, lmarginal_empty, Finset.prod_empty, one_mul]
    | succ j ih =>
      intro L hL x
      have hLN : L < N := by omega
      let l : Fin N := ⟨L, hLN⟩
      have hnot : l ∉ T (L + 1) := by simp [T, l]
      have hT : T L = insert l (T (L + 1)) := by
        ext a
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, l,
          Fin.ext_iff]
        omega
      rw [hT, lmarginal_insert _ (hPm _) hnot, Finset.prod_insert hnot]
      have hRL : ∀ i ∈ R L, ∀ v, Q (Function.update x l v) i = Q x i := by
        intro i hi v
        obtain ⟨hio, hiL⟩ := Finset.mem_filter.1 hi
        have hlt : i < D i := (Finset.mem_filter.1 hio).2
        have h1 : D i < l := by rw [Fin.lt_def]; exact hiL
        have h2 : i < l := lt_trans hlt h1
        simp only [Q, pos_update_of_lt m x h1, pos_update_of_lt m x h2]
      have step : ∫⁻ v, ∏ i ∈ R (L + 1), Q (Function.update x l v) i ∂μ l ≤
          e l * ∏ i ∈ R L, Q x i := by
        rcases lt_or_gt_of_ne (hD l).1 with hcl | hop
        · -- `l` closes the pair `(D l, l)`: its covariance is removed by `hconv`
          have hDl : D l ∉ R L := by
            intro hm
            have := (Finset.mem_filter.1 hm).2
            rw [(hD l).2] at this
            simp [l] at this
          have hRs : R (L + 1) = insert (D l) (R L) := by
            ext i
            simp only [R, Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨hi, hiL⟩
              by_cases hd : ((D i : Fin N) : ℕ) = L
              · left
                have : D i = l := Fin.ext hd
                rw [← this, (hD i).2]
              · right; exact ⟨hi, by omega⟩
            · rintro (rfl | ⟨hi, hiL⟩)
              · refine ⟨?_, ?_⟩
                · simp only [openers, Finset.mem_filter, Finset.mem_univ, true_and]
                  rw [(hD l).2]; exact hcl
                · rw [(hD l).2]; simp [l]
              · exact ⟨hi, by omega⟩
          have hfac : ∀ v, ∏ i ∈ R (L + 1), Q (Function.update x l v) i =
              γs (D l) ((pos m x (D l) - (pos m x l - x l)) - v) * ∏ i ∈ R L, Q x i := by
            intro v
            rw [hRs, Finset.prod_insert hDl]
            congr 1
            · simp only [Q, (hD l).2, pos_update_of_lt m x hcl, pos_update_self, sub_add_eq_sub_sub]
            · exact Finset.prod_congr rfl fun i hi => hRL i hi v
          simp_rw [hfac]
          have hm : Measurable fun v => γs (D l) ((pos m x (D l) - (pos m x l - x l)) - v) :=
            (hγ _).comp (measurable_const.sub measurable_id)
          rw [lintegral_mul_const _ hm]
          have hel : e l = c l := by simp [e, hcl]
          rw [hel]
          exact mul_le_mul_left (hconv l hcl _) _
        · -- `l` opens a pair whose closing factor is already removed
          have hRs : R (L + 1) = R L := by
            ext i
            simp only [R, Finset.mem_filter]
            refine and_congr_right fun hi => ?_
            have hne : ((D i : Fin N) : ℕ) ≠ L := by
              intro hd
              have hDi : D i = l := Fin.ext hd
              have hi' : i < D i := (Finset.mem_filter.1 hi).2
              have : D l = i := by rw [← hDi, (hD i).2]
              rw [hDi] at hi'
              rw [this] at hop
              exact lt_asymm hi' hop
            omega
          have hel : e l = μ l Set.univ := by simp [e, not_lt.2 hop.le]
          rw [hRs, hel]
          simp_rw [fun v => Finset.prod_congr rfl fun i hi => hRL i hi v]
          rw [lintegral_const, mul_comm]
      calc ∫⁻ v, lmarginal μ (T (L + 1)) F (Function.update x l v) ∂μ l
          ≤ ∫⁻ v, (∏ a ∈ T (L + 1), e a) * ∏ i ∈ R (L + 1), Q (Function.update x l v) i ∂μ l :=
            lintegral_mono fun v => ih (L + 1) (by omega) _
        _ = (∏ a ∈ T (L + 1), e a) * ∫⁻ v, ∏ i ∈ R (L + 1), Q (Function.update x l v) i ∂μ l :=
            lintegral_const_mul _ ((hPm _).comp (measurable_update x))
        _ ≤ (∏ a ∈ T (L + 1), e a) * (e l * ∏ i ∈ R L, Q x i) := mul_le_mul_right step _
        _ = e l * (∏ a ∈ T (L + 1), e a) * ∏ i ∈ R L, Q x i := by ring
  have h0 := key N 0 (by simp) 0
  have hT0 : T 0 = Finset.univ := by ext; simp [T]
  have hR0 : R 0 = ∅ := by ext; simp [R]
  rw [hT0, hR0, Finset.prod_empty, mul_one] at h0
  unfold spatialPair
  rw [lintegral_eq_lmarginal_univ (0 : Fin N → Rd d)]
  refine h0.trans (le_of_eq ?_)
  simp only [e]
  rw [Finset.prod_ite, filter_not_closing fun i => (hD i).1]
  rfl

/-! ### The one-dimensional convolution bounds -/

/-- Auxiliary to the Lean proof route (layer comparison for the rearrangement at
main TeX lines 5389-5396): for every level `t > 0`, the level set of
`u ↦ |z - u|^{-α}` inside `(-h, h)` is no larger than the level set of the
centered `u ↦ |u|^{-α}` inside `(-h, h)`. -/
theorem levelset_shift_le {α : ℝ} (hα0 : 0 < α) {h : ℝ} (hh : 0 < h) (z : ℝ) {t : ℝ}
    (ht : 0 < t) :
    volume ({u : ℝ | t < |z - u| ^ (-α)} ∩ Ioo (-h) h) ≤
      volume ({u : ℝ | t < |u| ^ (-α)} ∩ Ioo (-h) h) := by
  set r : ℝ := t ^ (-1 / α) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos ht _
  have hrt : r ^ (-α) = t := by
    rw [hr, ← Real.rpow_mul ht.le, show -1 / α * -α = 1 by field_simp, Real.rpow_one]
  have hsub : ∀ a : ℝ, 0 ≤ a → t < a ^ (-α) → a < r := by
    intro a ha0 ha
    by_contra hc
    have := Real.rpow_le_rpow_of_nonpos hr0 (not_lt.1 hc) (by linarith : -α ≤ 0)
    linarith
  set a : ℝ := min r h with ha
  have ha0 : 0 < a := lt_min hr0 hh
  -- the centered level set contains `(-a, a) \ {0}`
  have hlow : ENNReal.ofReal (2 * a) ≤ volume ({u : ℝ | t < |u| ^ (-α)} ∩ Ioo (-h) h) := by
    have hsup : Ioo (-a) a \ {0} ⊆ {u : ℝ | t < |u| ^ (-α)} ∩ Ioo (-h) h := by
      rintro u ⟨hu, hu0⟩
      have hu0' : u ≠ 0 := hu0
      have hua : |u| < a := abs_lt.2 hu
      refine ⟨?_, ?_⟩
      · show t < |u| ^ (-α)
        rw [← hrt]
        exact Real.rpow_lt_rpow_of_neg (abs_pos.2 hu0') (lt_of_lt_of_le hua (min_le_left _ _))
          (by linarith)
      · have := min_le_right r h
        exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    calc ENNReal.ofReal (2 * a) = volume (Ioo (-a) a \ {0}) := by
          rw [measure_sdiff_null (measure_singleton 0), Real.volume_Ioo]
          congr 1; ring
      _ ≤ _ := measure_mono hsup
  -- the shifted level set lies in `(z - r, z + r) ∩ (-h, h)`
  have hup : volume ({u : ℝ | t < |z - u| ^ (-α)} ∩ Ioo (-h) h) ≤ ENNReal.ofReal (2 * a) := by
    have hsub' : {u : ℝ | t < |z - u| ^ (-α)} ⊆ Ioo (z - r) (z + r) := by
      intro u hu
      have := abs_lt.1 (hsub _ (abs_nonneg _) hu)
      exact ⟨by linarith [this.2], by linarith [this.1]⟩
    rcases le_total r h with hrh | hhr
    · have : a = r := min_eq_left hrh
      calc volume ({u : ℝ | t < |z - u| ^ (-α)} ∩ Ioo (-h) h)
          ≤ volume (Ioo (z - r) (z + r)) := measure_mono (inter_subset_left.trans hsub')
        _ = ENNReal.ofReal (2 * a) := by rw [Real.volume_Ioo, this]; congr 1; ring
    · have : a = h := min_eq_right hhr
      calc volume ({u : ℝ | t < |z - u| ^ (-α)} ∩ Ioo (-h) h)
          ≤ volume (Ioo (-h) h) := measure_mono inter_subset_right
        _ = ENNReal.ofReal (2 * a) := by rw [Real.volume_Ioo, this]; congr 1; ring
  exact hup.trans hlow

/-- The rearrangement step of main TeX lines 5389-5392: the integral of the even
decreasing function `|u|^{-α}` over an interval of length `2h` is largest for the
centered interval, `∫_{(-h,h)} |z - u|^{-α} du ≤ ∫_{(-h,h)} |u|^{-α} du`.  Proved
by the layer-cake formula and `levelset_shift_le`. -/
theorem lintegral_shift_le {α : ℝ} (hα0 : 0 < α) {h : ℝ} (hh : 0 < h) (z : ℝ) :
    ∫⁻ u in Ioo (-h) h, ENNReal.ofReal (|z - u| ^ (-α)) ≤
      ∫⁻ u in Ioo (-h) h, ENNReal.ofReal (|u| ^ (-α)) := by
  have hm1 : Measurable fun u : ℝ => |z - u| ^ (-α) :=
    (measurable_id.const_sub z).abs.pow_const (-α)
  have hm2 : Measurable fun u : ℝ => |u| ^ (-α) := measurable_id.abs.pow_const (-α)
  rw [lintegral_eq_lintegral_meas_lt _
      (ae_of_all _ fun u => Real.rpow_nonneg (abs_nonneg _) _) hm1.aemeasurable,
    lintegral_eq_lintegral_meas_lt _
      (ae_of_all _ fun u => Real.rpow_nonneg (abs_nonneg _) _) hm2.aemeasurable]
  refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
  rw [Measure.restrict_apply' measurableSet_Ioo, Measure.restrict_apply' measurableSet_Ioo]
  exact levelset_shift_le hα0 hh z ht

/-- The centered value at main TeX lines 5394-5395:
`∫_{(-h,h)} |u|^{-α} du ≤ 2 h^{1-α}/(1-α)` (an equality; only `≤` is used). -/
theorem lintegral_centered_le {α : ℝ} (hα1 : α < 1) {h : ℝ} (hh : 0 < h) :
    ∫⁻ u in Ioo (-h) h, ENNReal.ofReal (|u| ^ (-α)) ≤
      ENNReal.ofReal (2 * (h ^ (1 - α) / (1 - α))) := by
  have hX : 0 ≤ h ^ (1 - α) / (1 - α) :=
    div_nonneg (Real.rpow_nonneg hh.le _) (by linarith)
  have hpos : ∫⁻ u in Ioc 0 h, ENNReal.ofReal (|u| ^ (-α)) =
      ENNReal.ofReal (h ^ (1 - α) / (1 - α)) := by
    rw [← lintegral_rpow_Ioc hα1 hh.le]
    refine setLIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    rw [abs_of_pos hu.1]
  have hpre : (fun u : ℝ => -u) ⁻¹' Ioc (-h) 0 = Ico 0 h := by
    ext u
    simp only [mem_preimage, mem_Ioc, mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  have hneg : ∫⁻ u in Ioc (-h) 0, ENNReal.ofReal (|u| ^ (-α)) =
      ENNReal.ofReal (h ^ (1 - α) / (1 - α)) := by
    have := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage_emb
      (MeasurableEquiv.neg ℝ).measurableEmbedding (fun u => ENNReal.ofReal (|u| ^ (-α)))
      (Ioc (-h) 0)
    rw [← this]
    erw [hpre]
    simp only [abs_neg]
    rw [setLIntegral_congr Ico_ae_eq_Ioc]
    exact hpos
  have hsub : Ioo (-h) h ⊆ Ioc (-h) 0 ∪ Ioc 0 h := by
    intro u hu
    rcases le_or_gt u 0 with h0 | h0
    · exact Or.inl ⟨hu.1, h0⟩
    · exact Or.inr ⟨h0, hu.2.le⟩
  calc ∫⁻ u in Ioo (-h) h, ENNReal.ofReal (|u| ^ (-α))
      ≤ ∫⁻ u in Ioc (-h) 0 ∪ Ioc 0 h, ENNReal.ofReal (|u| ^ (-α)) := lintegral_mono_set hsub
    _ ≤ _ := lintegral_union_le _ _ _
    _ = ENNReal.ofReal (2 * (h ^ (1 - α) / (1 - α))) := by
        rw [hneg, hpos, ← ENNReal.ofReal_add hX hX, two_mul]

/-- **The unsmoothed Riesz convolution bound** (main TeX lines 5389-5396): for
`0 < α < 1`, `c ≥ 0`, `h ≥ 0` and every shift `z`,
`∫ G_h(dv) c|z - v|^{-α} ≤ c h^{1-α}/(1-α)`, with `G_h = waveGreen 1 h`
(`½ 1_{|v|<h} dv`).  The TeX writes the shift as `y + z`; the model's pair
orientation gives `z - v`, the same bound since `G_h` is symmetric (the proof
covers every `z`). -/
theorem riesz_conv_le {c α : ℝ} (hc : 0 ≤ c) (hα0 : 0 < α) (hα1 : α < 1) {h : ℝ}
    (hh : 0 ≤ h) (z : Rd 1) :
    ∫⁻ v, riesz c α (z - v) ∂waveGreen 1 h ≤ ENNReal.ofReal (c * h ^ (1 - α) / (1 - α)) := by
  rcases hh.eq_or_lt with rfl | hh
  · rw [WaveGreen.waveGreen_of_nonpos 1 0 le_rfl, lintegral_zero_measure]; exact zero_le
  rw [show waveGreen 1 h = ENNReal.ofReal (1 / 2) • volume.restrict (Metric.ball 0 h) from rfl,
    lintegral_smul_measure, ball_eq_preimage_coordOne]
  have hpt : ∀ v : Rd 1, riesz c α (z - v) =
      ENNReal.ofReal c * ENNReal.ofReal (|coordOne z - coordOne v| ^ (-α)) := by
    intro v
    rw [riesz, norm_coord_one, ENNReal.ofReal_mul hc]
    simp [WaveGreen.coordOne_apply]
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    coordOne_mp.setLIntegral_comp_preimage_emb coordOne.measurableEmbedding
      (fun u => ENNReal.ofReal (|coordOne z - u| ^ (-α))) (Ioo (-h) h)]
  calc ENNReal.ofReal (1 / 2) *
        (ENNReal.ofReal c * ∫⁻ u in Ioo (-h) h, ENNReal.ofReal (|coordOne z - u| ^ (-α)))
      ≤ ENNReal.ofReal (1 / 2) *
          (ENNReal.ofReal c * ENNReal.ofReal (2 * (h ^ (1 - α) / (1 - α)))) := by
        gcongr
        exact (lintegral_shift_le hα0 hh _).trans (lintegral_centered_le hα1 hh)
    _ = ENNReal.ofReal (c * h ^ (1 - α) / (1 - α)) := by
        rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1; ring

/-- Auxiliary to the Lean proof route: `p_ε` of `DiagramModel.covEps` is the heat
kernel `VariationalMean.heatK` (the same formula). -/
theorem heatDens_eq_heatK {d : ℕ} (ε : ℝ) : (heatDens ε : Rd d → ℝ) = heatK ε := rfl

/-- `p_ε * Γ` for a covariance with density `g` is `HigherRieszTwo.smoothCov g ε`
(main TeX line 5348, `γ_ε = p_ε * γ`). -/
theorem covEps_withDensity {d : ℕ} {g : Rd d → ℝ≥0∞} (hg : Measurable g) (ε : ℝ) :
    covEps (volume.withDensity g) ε = smoothCov g ε := by
  funext x
  unfold covEps smoothCov
  have hm : Measurable fun z : Rd d => ENNReal.ofReal (heatDens ε (x - z)) :=
    ((measurable_heatK ε).comp (measurable_id.const_sub x)).ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul _ hg hm]
  refine lintegral_congr fun y => ?_
  simp only [Pi.mul_apply]
  rw [mul_comm]
  rfl

/-- `p_ε * (c δ₀) = c p_ε` (main TeX line 5400: "in the white case,
`γ_ε = c_δ p_ε`"). -/
theorem covEps_whiteCov (c ε : ℝ) (x : Rd 1) :
    covEps (whiteCov c) ε x = ENNReal.ofReal c * ENNReal.ofReal (heatDens ε x) := by
  unfold covEps whiteCov
  rw [lintegral_smul_measure, lintegral_dirac, sub_zero, smul_eq_mul]

/-- Auxiliary to the Lean proof route: `p_ε` is even. -/
theorem heatDens_neg {d : ℕ} (ε : ℝ) (x : Rd d) : heatDens ε (-x) = heatDens ε x := by
  simp [heatDens, norm_neg]

/-- The smoothed Riesz covariance is even, so the TeX's pair orientation
`γ_ε(x_j - x_i)` (line 5353) and the model's `γ_ε(x_i - x_j)` agree. -/
theorem covEps_riesz_neg (c α ε : ℝ) (x : Rd 1) :
    covEps (volume.withDensity (riesz c α)) ε (-x) =
      covEps (volume.withDensity (riesz c α)) ε x := by
  rw [covEps_withDensity (measurable_riesz c α), smoothCov_eq, smoothCov_eq,
    ← lintegral_neg_eq_self]
  refine lintegral_congr fun b => ?_
  rw [← heatDens_eq_heatK, heatDens_neg, show -x - -b = -(x - b) by abel]
  simp only [riesz, norm_neg]

/-- The smoothed white covariance `c p_ε` is even. -/
theorem covEps_white_neg (c ε : ℝ) (x : Rd 1) :
    covEps (whiteCov c) ε (-x) = covEps (whiteCov c) ε x := by
  rw [covEps_whiteCov, covEps_whiteCov, heatDens_neg]

/-- The Gaussian average of main TeX lines 5397-5399 (Tonelli; mass one): if
`∫ γ(x - v) ν(dv) ≤ B` for every shift `x`, then `∫ γ_ε(z - v) ν(dv) ≤ B` for every
`z` and `ε > 0`.  The analogue of `HigherRieszTwo.average_le` in the model's
pair orientation. -/
theorem smoothCov_conv_le {d : ℕ} {ν : Measure (Rd d)} [SFinite ν] {g : Rd d → ℝ≥0∞}
    (hg : Measurable g) {ε : ℝ} (hε : 0 < ε) {B : ℝ≥0∞} (hB : ∀ x, ∫⁻ v, g (x - v) ∂ν ≤ B)
    (z : Rd d) : ∫⁻ v, smoothCov g ε (z - v) ∂ν ≤ B := by
  have hmeas : Measurable (Function.uncurry fun (v b : Rd d) =>
      ENNReal.ofReal (heatK ε b) * g ((z - b) - v)) :=
    ((measurable_heatK ε).comp measurable_snd).ennreal_ofReal.mul
      (hg.comp ((measurable_const.sub measurable_snd).sub measurable_fst))
  calc ∫⁻ v, smoothCov g ε (z - v) ∂ν
      = ∫⁻ v, (∫⁻ b, ENNReal.ofReal (heatK ε b) * g ((z - b) - v)) ∂ν := by
        refine lintegral_congr fun v => ?_
        rw [smoothCov_eq]
        simp only [sub_right_comm]
    _ = ∫⁻ b, (∫⁻ v, ENNReal.ofReal (heatK ε b) * g ((z - b) - v) ∂ν) :=
        lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ b, ENNReal.ofReal (heatK ε b) * ∫⁻ v, g ((z - b) - v) ∂ν := by
        refine lintegral_congr fun b => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ∫⁻ b, ENNReal.ofReal (heatK ε b) * B :=
        lintegral_mono fun b => mul_le_mul_right (hB _) _
    _ = B := by
        rw [lintegral_mul_const _ (measurable_heatK ε).ennreal_ofReal, lintegral_heatK hε,
          one_mul]

/-- **The smoothed Riesz convolution bound, uniform in `ε`** (main TeX lines
5389-5399): `∫ G_h(dv) γ_ε(z - v) ≤ c h^{1-α}/(1-α)` for `γ_ε = p_ε * (c|·|^{-α})`,
every `ε > 0`, `h ≥ 0` and `z`. -/
theorem riesz_eps_conv_le {c α : ℝ} (hc : 0 ≤ c) (hα0 : 0 < α) (hα1 : α < 1) {ε : ℝ}
    (hε : 0 < ε) {h : ℝ} (hh : 0 ≤ h) (z : Rd 1) :
    ∫⁻ v, covEps (volume.withDensity (riesz c α)) ε (z - v) ∂waveGreen 1 h ≤
      ENNReal.ofReal (c * h ^ (1 - α) / (1 - α)) := by
  rw [covEps_withDensity (measurable_riesz c α)]
  exact smoothCov_conv_le (measurable_riesz c α) hε
    (fun x => riesz_conv_le hc hα0 hα1 hh x) z

/-- **The white convolution bound, uniform in `ε`** (main TeX lines 5399-5405):
`∫ G_h(dv) γ_ε(z - v) ≤ c/2` for `γ_ε = p_ε * (c δ₀) = c p_ε`, every `ε > 0`,
every `h` and `z`. -/
theorem white_eps_conv_le (c : ℝ) {ε : ℝ} (hε : 0 < ε) (h : ℝ) (z : Rd 1) :
    ∫⁻ v, covEps (whiteCov c) ε (z - v) ∂waveGreen 1 h ≤ ENNReal.ofReal (c / 2) := by
  rw [show waveGreen 1 h = ENNReal.ofReal (1 / 2) • volume.restrict (Metric.ball 0 h) from rfl,
    lintegral_smul_measure]
  simp_rw [covEps_whiteCov]
  calc ENNReal.ofReal (1 / 2) * ∫⁻ v in Metric.ball 0 h,
        ENNReal.ofReal c * ENNReal.ofReal (heatDens ε (z - v))
      ≤ ENNReal.ofReal (1 / 2) * ∫⁻ v, ENNReal.ofReal c * ENNReal.ofReal (heatDens ε (z - v)) := by
        gcongr; exact Measure.restrict_le_self
    _ = ENNReal.ofReal (1 / 2) * (ENNReal.ofReal c * 1) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_sub_left_eq_self (fun y => ENNReal.ofReal (heatDens ε y)) z,
          heatDens_eq_heatK, lintegral_heatK hε]
    _ = ENNReal.ofReal (c / 2) := by
        rw [mul_one, ← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring

/-- Auxiliary to the Lean proof route: `γ_ε = p_ε * (c|·|^{-α})` is measurable. -/
theorem measurable_covEps_riesz (c α ε : ℝ) :
    Measurable (covEps (volume.withDensity (riesz c α)) ε : Rd 1 → ℝ≥0∞) := by
  rw [covEps_withDensity (measurable_riesz c α)]
  exact measurable_smoothCov (measurable_riesz c α) ε

/-- Auxiliary to the Lean proof route: `γ_ε = c p_ε` is measurable. -/
theorem measurable_covEps_white (c ε : ℝ) : Measurable (covEps (whiteCov c) ε) := by
  have : covEps (whiteCov c) ε = fun x => ENNReal.ofReal c * ENNReal.ofReal (heatDens ε x) :=
    funext (covEps_whiteCov c ε)
  rw [this, heatDens_eq_heatK]
  exact measurable_const.mul (measurable_heatK ε).ennreal_ofReal

/-! ### `E:d1-spatial-product` -/

/-- **`E:d1-spatial-product`, Riesz case** (main TeX lines 5364-5373; proof lines
5389-5425): for `γ(y) = c|y|^{-α}` with `0 < α < 1`, `c ≥ 0`, any pairing `D` of
`N = 2k` labels, separate widths `ε_i > 0` (one per pair, named by its opening
label) and increments `h_l ≥ 0`,
`S_{D,ε}(h) ≤ (c/(1-α))^k ∏_{i ∈ O_D} h_i ∏_{j ∈ C_D} h_j^{1-α}`, uniformly in
the widths (the bound does not depend on them). -/
theorem d1_spatial_riesz {c α : ℝ} (hc : 0 ≤ c) (hα0 : 0 < α) (hα1 : α < 1) {N k : ℕ}
    (hN : N = 2 * k) (m : ℕ) {D : Fin N → Fin N}
    (hD : D ∈ pairings (Finset.univ : Finset (Fin N))) {εs : Fin N → ℝ} (hε : ∀ i, 0 < εs i)
    {h : Fin N → ℝ} (hh : ∀ i, 0 ≤ h i) :
    spatialPair (waveGreen 1) (fun i => covEps (volume.withDensity (riesz c α)) (εs i)) m D h ≤
      ENNReal.ofReal ((c / (1 - α)) ^ k * (∏ i ∈ openers D, h i) *
        ∏ j ∈ closers D, h j ^ (1 - α)) := by
  have hb : 0 < 1 - α := by linarith
  have hnn : ∀ j, 0 ≤ c * h j ^ (1 - α) / (1 - α) := fun j =>
    div_nonneg (mul_nonneg hc (Real.rpow_nonneg (hh j) _)) hb.le
  refine (spatialPair_le (waveGreen 1) _ (fun i => measurable_covEps_riesz c α (εs i)) m D
    (pairing_inv hD) h (fun l => ENNReal.ofReal (c * h l ^ (1 - α) / (1 - α)))
    (fun l _ z => riesz_eps_conv_le hc hα0 hα1 (hε _) (hh l) z)).trans (le_of_eq ?_)
  rw [Finset.prod_congr rfl fun i _ => waveGreen_mass 1 (Or.inl rfl) (h i) (hh i),
    ← ENNReal.ofReal_prod_of_nonneg fun i _ => hnn i,
    ← ENNReal.ofReal_prod_of_nonneg fun i _ => hh i,
    ← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => hnn i)]
  congr 1
  have e : ∀ j, c * h j ^ (1 - α) / (1 - α) = (c / (1 - α)) * h j ^ (1 - α) := fun j => by
    ring
  simp_rw [e]
  rw [Finset.prod_mul_distrib, Finset.prod_const, card_closers hD hN]
  ring

/-- **`E:d1-spatial-product`, white case** (main TeX lines 5364-5373 with
`α = 1`; proof lines 5399-5425): for `γ = c δ₀`, `c ≥ 0`, any pairing `D` of
`N = 2k` labels, widths `ε_i > 0` and increments `h_l ≥ 0`,
`S_{D,ε}(h) ≤ (c/2)^k ∏_{i ∈ O_D} h_i`, uniformly in the widths. -/
theorem d1_spatial_white {c : ℝ} (hc : 0 ≤ c) {N k : ℕ} (hN : N = 2 * k) (m : ℕ)
    {D : Fin N → Fin N} (hD : D ∈ pairings (Finset.univ : Finset (Fin N)))
    {εs : Fin N → ℝ} (hε : ∀ i, 0 < εs i) {h : Fin N → ℝ} (hh : ∀ i, 0 ≤ h i) :
    spatialPair (waveGreen 1) (fun i => covEps (whiteCov c) (εs i)) m D h ≤
      ENNReal.ofReal ((c / 2) ^ k * ∏ i ∈ openers D, h i) := by
  refine (spatialPair_le (waveGreen 1) _ (fun i => measurable_covEps_white c (εs i)) m D
    (pairing_inv hD) h (fun _ => ENNReal.ofReal (c / 2))
    (fun l _ z => white_eps_conv_le c (hε _) (h l) z)).trans (le_of_eq ?_)
  rw [Finset.prod_congr rfl fun i _ => waveGreen_mass 1 (Or.inl rfl) (h i) (hh i),
    ← ENNReal.ofReal_prod_of_nonneg fun i _ => hh i, Finset.prod_const, card_closers hD hN,
    ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]

/-! ### `E:d1-spatial-max`: the weighted arithmetic-geometric mean step -/

/-- The weighted arithmetic-geometric mean step of main TeX lines 5430-5437:
with weight one at the `k` openings and `1 - α` at the `k` closings (total
`(2-α)k`), if `Σ_l h_l ≤ 2t` then
`∏_{O_D} h_i ∏_{C_D} h_j^{1-α} ≤ (1-α)^{(1-α)k} (2t/((2-α)k))^{(2-α)k}`. -/
theorem amgm_riesz {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {N k : ℕ} (hk : 1 ≤ k)
    (hN : N = 2 * k) {D : Fin N → Fin N} (hD : D ∈ pairings (Finset.univ : Finset (Fin N)))
    {h : Fin N → ℝ} (hh : ∀ i, 0 ≤ h i) {t : ℝ} (hsum : ∑ i, h i ≤ 2 * t) :
    (∏ i ∈ openers D, h i) * ∏ j ∈ closers D, h j ^ (1 - α) ≤
      (1 - α) ^ ((1 - α) * k) * (2 * t / ((2 - α) * k)) ^ ((2 - α) * k) := by
  classical
  have hβ : 0 < 1 - α := by linarith
  have hK : (0 : ℝ) < k := by exact_mod_cast hk
  have hne := fun i => (pairing_inv hD i).1
  let a : Fin N → ℝ := fun i => if D i < i then 1 - α else 1
  have ha : ∀ i, 0 < a i := fun i => by simp only [a]; split_ifs <;> linarith
  have hS : ∑ i, a i = (2 - α) * k := by
    simp only [a]
    rw [Finset.sum_ite, filter_not_closing hne]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [show (Finset.univ.filter fun i => D i < i) = closers D from rfl, card_closers hD hN,
      card_openers hD hN]
    ring
  have hSpos : 0 < ∑ i, a i := by rw [hS]; nlinarith
  have hsplit : ∏ i, h i ^ a i = (∏ i ∈ openers D, h i) * ∏ j ∈ closers D, h j ^ (1 - α) := by
    have : ∀ i, h i ^ a i = if D i < i then h i ^ (1 - α) else h i := fun i => by
      simp only [a]; split_ifs <;> simp
    simp_rw [this]
    rw [Finset.prod_ite, filter_not_closing hne, mul_comm]
    rfl
  have hfac : ∏ i, h i ^ a i = (∏ i, a i ^ a i) * ∏ i, (h i / a i) ^ a i := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Real.mul_rpow (ha i).le (div_nonneg (hh i) (ha i).le), mul_div_cancel₀ _ (ha i).ne']
  have haa : ∏ i, a i ^ a i = (1 - α) ^ ((1 - α) * k) := by
    have : ∀ i, a i ^ a i = if D i < i then (1 - α) ^ (1 - α) else 1 := fun i => by
      simp only [a]; split_ifs <;> simp
    simp_rw [this]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one,
      show (Finset.univ.filter fun i => D i < i) = closers D from rfl, card_closers hD hN,
      ← Real.rpow_natCast, ← Real.rpow_mul hβ.le]
  have hgm := Real.geom_mean_le_arith_mean Finset.univ a (fun i => h i / a i)
    (fun i _ => (ha i).le) hSpos (fun i _ => div_nonneg (hh i) (ha i).le)
  have hcancel : ∑ i, a i * (h i / a i) = ∑ i, h i :=
    Finset.sum_congr rfl fun i _ => mul_div_cancel₀ _ (ha i).ne'
  rw [hcancel, hS] at hgm
  set P := ∏ i, (h i / a i) ^ a i with hP
  have hP0 : 0 ≤ P := Finset.prod_nonneg fun i _ => Real.rpow_nonneg (div_nonneg (hh i) (ha i).le) _
  have hSne : (2 - α) * (k : ℝ) ≠ 0 := by nlinarith
  have hPle : P ≤ (2 * t / ((2 - α) * k)) ^ ((2 - α) * k) := by
    have h1 : P ^ ((2 - α) * (k : ℝ))⁻¹ ≤ 2 * t / ((2 - α) * k) :=
      hgm.trans (div_le_div_of_nonneg_right hsum (by nlinarith))
    calc P = (P ^ ((2 - α) * (k : ℝ))⁻¹) ^ ((2 - α) * (k : ℝ)) :=
          (Real.rpow_inv_rpow hP0 hSne).symm
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hP0 _) h1 (by nlinarith)
  rw [← hsplit, hfac, haa]
  exact mul_le_mul_of_nonneg_left hPle (Real.rpow_nonneg hβ.le _)

/-- The constant algebra of main TeX lines 5438-5439: multiplying the bound of
`amgm_riesz` by `(c/(1-α))^k` gives `K_sp^k t^{bk}/k^{bk}` with `b = 2 - α` and
`K_sp` of `E:d1-constants`. -/
theorem riesz_constant_eq {c α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {k : ℕ} (hk : 1 ≤ k)
    {t : ℝ} (ht : 0 ≤ t) :
    (c / (1 - α)) ^ k * ((1 - α) ^ ((1 - α) * k) * (2 * t / ((2 - α) * k)) ^ ((2 - α) * k)) =
      Ksp c α ^ k * t ^ ((2 - α) * k) / (k : ℝ) ^ ((2 - α) * k) := by
  have hβ : 0 < 1 - α := by linarith
  have hb : 0 < 2 - α := by linarith
  have hK : (0 : ℝ) < k := by exact_mod_cast hk
  rw [Real.div_rpow (by positivity) (by positivity), Real.mul_rpow (by norm_num) ht,
    Real.mul_rpow hb.le hK.le, Ksp, div_pow, div_pow, mul_pow, mul_pow,
    ← Real.rpow_natCast (2 ^ (2 - α)), ← Real.rpow_natCast ((1 - α) ^ (-α)),
    ← Real.rpow_natCast ((2 - α) ^ (2 - α)), ← Real.rpow_natCast (1 - α),
    ← Real.rpow_mul (by norm_num), ← Real.rpow_mul hβ.le, ← Real.rpow_mul hb.le,
    show -α * (k : ℝ) = (1 - α) * k - k by ring, Real.rpow_sub hβ]
  have h1 : 0 < (1 - α) ^ (k : ℝ) := Real.rpow_pos_of_pos hβ _
  have h2 : 0 < (2 - α) ^ ((2 - α) * (k : ℝ)) := Real.rpow_pos_of_pos hb _
  have h3 : 0 < (k : ℝ) ^ ((2 - α) * (k : ℝ)) := Real.rpow_pos_of_pos hK _
  field_simp

/-- **`E:d1-spatial-max`, Riesz case** (main TeX lines 5374-5378, proof lines
5430-5439): under the hypotheses of `d1_spatial_riesz`, `k ≥ 1` and
`Σ_l h_l ≤ 2t`, `S_{D,ε}(h) ≤ K_sp^k t^{bk}/k^{bk}` with `b = 2 - α`. -/
theorem d1_spatial_riesz_max {c α : ℝ} (hc : 0 ≤ c) (hα0 : 0 < α) (hα1 : α < 1) {N k : ℕ}
    (hk : 1 ≤ k) (hN : N = 2 * k) (m : ℕ) {D : Fin N → Fin N}
    (hD : D ∈ pairings (Finset.univ : Finset (Fin N))) {εs : Fin N → ℝ} (hε : ∀ i, 0 < εs i)
    {h : Fin N → ℝ} (hh : ∀ i, 0 ≤ h i) {t : ℝ} (hsum : ∑ i, h i ≤ 2 * t) :
    spatialPair (waveGreen 1) (fun i => covEps (volume.withDensity (riesz c α)) (εs i)) m D h ≤
      ENNReal.ofReal (Ksp c α ^ k * t ^ ((2 - α) * k) / (k : ℝ) ^ ((2 - α) * k)) := by
  have ht : 0 ≤ t := by
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hh i
    linarith
  refine (d1_spatial_riesz hc hα0 hα1 hN m hD hε hh).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [mul_assoc, ← riesz_constant_eq hα0 hα1 hk ht]
  exact mul_le_mul_of_nonneg_left (amgm_riesz hα0 hα1 hk hN hD hh hsum)
    (pow_nonneg (div_nonneg hc (by linarith)) _)

/-- The arithmetic-geometric mean step of the white case (main TeX lines
5439-5441): if `Σ_l h_l ≤ 2t` then `∏_{O_D} h_i ≤ (2t/k)^k`. -/
theorem amgm_white {N k : ℕ} (hk : 1 ≤ k) (hN : N = 2 * k) {D : Fin N → Fin N}
    (hD : D ∈ pairings (Finset.univ : Finset (Fin N))) {h : Fin N → ℝ} (hh : ∀ i, 0 ≤ h i)
    {t : ℝ} (hsum : ∑ i, h i ≤ 2 * t) :
    ∏ i ∈ openers D, h i ≤ (2 * t / k) ^ k := by
  have hK : (0 : ℝ) < k := by exact_mod_cast hk
  have hcard : ∑ _i ∈ openers D, (1 : ℝ) = k := by
    rw [Finset.sum_const, card_openers hD hN, nsmul_eq_mul, mul_one]
  have hgm := Real.geom_mean_le_arith_mean (openers D) (fun _ => (1 : ℝ)) h
    (fun _ _ => zero_le_one) (by rw [hcard]; exact hK) (fun i _ => hh i)
  simp only [Real.rpow_one, one_mul] at hgm
  rw [hcard] at hgm
  have hO : ∑ i ∈ openers D, h i ≤ 2 * t :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => hh i).trans hsum
  have hP0 : 0 ≤ ∏ i ∈ openers D, h i := Finset.prod_nonneg fun i _ => hh i
  have h1 : (∏ i ∈ openers D, h i) ^ (k : ℝ)⁻¹ ≤ 2 * t / k :=
    hgm.trans (div_le_div_of_nonneg_right hO hK.le)
  calc ∏ i ∈ openers D, h i = ((∏ i ∈ openers D, h i) ^ (k : ℝ)⁻¹) ^ (k : ℝ) :=
        (Real.rpow_inv_rpow hP0 hK.ne').symm
    _ ≤ (2 * t / k) ^ (k : ℝ) := Real.rpow_le_rpow (Real.rpow_nonneg hP0 _) h1 hK.le
    _ = (2 * t / k) ^ k := Real.rpow_natCast _ _

/-- **`E:d1-spatial-max`, white case** (main TeX lines 5374-5378 with `b = 1`,
`K_sp = c`; proof lines 5439-5441): under the hypotheses of `d1_spatial_white`,
`k ≥ 1` and `Σ_l h_l ≤ 2t`, `S_{D,ε}(h) ≤ c^k t^k / k^k`. -/
theorem d1_spatial_white_max {c : ℝ} (hc : 0 ≤ c) {N k : ℕ} (hk : 1 ≤ k) (hN : N = 2 * k)
    (m : ℕ) {D : Fin N → Fin N} (hD : D ∈ pairings (Finset.univ : Finset (Fin N)))
    {εs : Fin N → ℝ} (hε : ∀ i, 0 < εs i) {h : Fin N → ℝ} (hh : ∀ i, 0 ≤ h i) {t : ℝ}
    (hsum : ∑ i, h i ≤ 2 * t) :
    spatialPair (waveGreen 1) (fun i => covEps (whiteCov c) (εs i)) m D h ≤
      ENNReal.ofReal (c ^ k * t ^ k / (k : ℝ) ^ k) := by
  have hK : (0 : ℝ) < k := by exact_mod_cast hk
  refine (d1_spatial_white hc hN m hD hε hh).trans (ENNReal.ofReal_le_ofReal ?_)
  calc (c / 2) ^ k * ∏ i ∈ openers D, h i ≤ (c / 2) ^ k * (2 * t / k) ^ k :=
        mul_le_mul_of_nonneg_left (amgm_white hk hN hD hh hsum) (by positivity)
    _ = c ^ k * t ^ k / (k : ℝ) ^ k := by
        rw [← mul_pow, ← mul_pow, ← div_pow]
        congr 1
        field_simp

/-! ### The model's common-width spatial part (the form consumed by `P:d1-upper`) -/

/-- `L:d1-spatial`, Riesz case, on `DiagramModel.spatial` with one common width
`ε` (the model's `covEps Γ ε` for `Γ = c|y|^{-α} dy`): both displays,
`E:d1-spatial-product` and, if `k ≥ 1` and `Σ_l h_l ≤ 2t`,
`E:d1-spatial-max`. -/
theorem spatial_riesz_le {c α : ℝ} (hc : 0 ≤ c) (hα0 : 0 < α) (hα1 : α < 1) {m n k : ℕ}
    (hmn : m + n = 2 * k) {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n) {ε : ℝ}
    (hε : 0 < ε) {h : Fin (m + n) → ℝ} (hh : ∀ i, 0 ≤ h i) :
    spatial (waveGreen 1) (covEps (volume.withDensity (riesz c α)) ε) m D h ≤
        ENNReal.ofReal ((c / (1 - α)) ^ k * (∏ i ∈ openers D, h i) *
          ∏ j ∈ closers D, h j ^ (1 - α)) ∧
      (1 ≤ k → ∀ t : ℝ, ∑ i, h i ≤ 2 * t →
        spatial (waveGreen 1) (covEps (volume.withDensity (riesz c α)) ε) m D h ≤
          ENNReal.ofReal (Ksp c α ^ k * t ^ ((2 - α) * k) / (k : ℝ) ^ ((2 - α) * k))) :=
  ⟨d1_spatial_riesz (εs := fun _ => ε) hc hα0 hα1 hmn m hD (fun _ => hε) hh,
    fun hk _ hsum =>
      d1_spatial_riesz_max (εs := fun _ => ε) hc hα0 hα1 hk hmn m hD (fun _ => hε) hh hsum⟩

/-- `L:d1-spatial`, white case, on `DiagramModel.spatial` with one common width
`ε` (`covEps (c δ₀) ε = c p_ε`): `E:d1-spatial-product` and, if `k ≥ 1` and
`Σ_l h_l ≤ 2t`, `E:d1-spatial-max` with `b = 1`, `K_sp = c`. -/
theorem spatial_white_le {c : ℝ} (hc : 0 ≤ c) {m n k : ℕ} (hmn : m + n = 2 * k)
    {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n) {ε : ℝ} (hε : 0 < ε)
    {h : Fin (m + n) → ℝ} (hh : ∀ i, 0 ≤ h i) :
    spatial (waveGreen 1) (covEps (whiteCov c) ε) m D h ≤
        ENNReal.ofReal ((c / 2) ^ k * ∏ i ∈ openers D, h i) ∧
      (1 ≤ k → ∀ t : ℝ, ∑ i, h i ≤ 2 * t →
        spatial (waveGreen 1) (covEps (whiteCov c) ε) m D h ≤
          ENNReal.ofReal (c ^ k * t ^ k / (k : ℝ) ^ k)) :=
  ⟨d1_spatial_white (εs := fun _ => ε) hc hmn m hD (fun _ => hε) hh,
    fun hk _ hsum => d1_spatial_white_max (εs := fun _ => ε) hc hk hmn m hD (fun _ => hε) hh hsum⟩

/-- The positions form (`DiagramModel.spatialPos green1`, the literal integral of
`E:mixed-diagram`) of the Riesz bound, through `DiagramBridge`. -/
theorem spatialPos_riesz_le {c α : ℝ} (hc : 0 ≤ c) (hα0 : 0 < α) (hα1 : α < 1) {m n k : ℕ}
    (hmn : m + n = 2 * k) {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n) {ε : ℝ}
    (hε : 0 < ε) {h : Fin (m + n) → ℝ} (hh : ∀ i, 0 ≤ h i) :
    spatialPos green1 (covEps (volume.withDensity (riesz c α)) ε) m D h ≤
      ENNReal.ofReal ((c / (1 - α)) ^ k * (∏ i ∈ openers D, h i) *
        ∏ j ∈ closers D, h j ^ (1 - α)) := by
  rw [← DiagramBridge.spatial_waveGreen_one_eq_spatialPos]
  exact (spatial_riesz_le hc hα0 hα1 hmn hD hε hh).1

/-- The positions form of the white bound, through `DiagramBridge`. -/
theorem spatialPos_white_le {c : ℝ} (hc : 0 ≤ c) {m n k : ℕ} (hmn : m + n = 2 * k)
    {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n) {ε : ℝ} (hε : 0 < ε)
    {h : Fin (m + n) → ℝ} (hh : ∀ i, 0 ≤ h i) :
    spatialPos green1 (covEps (whiteCov c) ε) m D h ≤
      ENNReal.ofReal ((c / 2) ^ k * ∏ i ∈ openers D, h i) := by
  rw [← DiagramBridge.spatial_waveGreen_one_eq_spatialPos]
  exact (spatial_white_le hc hmn hD hε hh).1

/-! ### Wrappers with the manuscript's hypotheses -/

/-- **`L:d1-spatial`, Riesz case of `E:d1-covariances`** (main TeX lines 5359-5379)
with the manuscript's hypotheses: `0 < α₀ < 1` (standing, line 5315),
`γ = c_α|y|^{-α}` with `0 < α < 1`, `c_α > 0`, `k ≥ 1`, `D` a pairing of the two
chains (`m + n = 2k`), separate widths `ε_e > 0` (line 5349; named by the opening
label of the pair) and `h_l > 0` (line 5339).  Conclusions: `E:d1-spatial-product`
and `E:d1-spatial-max`.  Carried but unused: `0 < α₀ < 1`; `c_α > 0` and
`h_l > 0` are used only as `c_α ≥ 0`, `h_l ≥ 0`; `k ≥ 1` is used only for
`E:d1-spatial-max`. -/
theorem d1_spatial_paper_riesz {c α α₀ : ℝ} (_hα₀0 : 0 < α₀) (_hα₀1 : α₀ < 1) (hc : 0 < c)
    (hα0 : 0 < α) (hα1 : α < 1) {m n k : ℕ} (hk : 1 ≤ k) (hmn : m + n = 2 * k)
    {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n) {εs : Fin (m + n) → ℝ}
    (hε : ∀ i, 0 < εs i) {h : Fin (m + n) → ℝ} (hh : ∀ i, 0 < h i) :
    spatialPair (waveGreen 1) (fun i => covEps (volume.withDensity (riesz c α)) (εs i)) m D h ≤
        ENNReal.ofReal ((c / (1 - α)) ^ k * (∏ i ∈ openers D, h i) *
          ∏ j ∈ closers D, h j ^ (1 - α)) ∧
      ∀ t : ℝ, ∑ i, h i ≤ 2 * t →
        spatialPair (waveGreen 1) (fun i => covEps (volume.withDensity (riesz c α)) (εs i))
            m D h ≤
          ENNReal.ofReal (Ksp c α ^ k * t ^ ((2 - α) * k) / (k : ℝ) ^ ((2 - α) * k)) :=
  ⟨d1_spatial_riesz hc.le hα0 hα1 hmn m hD hε fun i => (hh i).le,
    fun _ hsum => d1_spatial_riesz_max hc.le hα0 hα1 hk hmn m hD hε (fun i => (hh i).le) hsum⟩

/-- **`L:d1-spatial`, white case of `E:d1-covariances`** (`α = 1`,
`γ = c_δ δ₀`, main TeX lines 5359-5379) with the manuscript's hypotheses
(`0 < α₀ < 1`, `c_δ > 0`, `k ≥ 1`, `D` a pairing, `ε_e > 0`, `h_l > 0`):
`S_{D,ε}(h) ≤ (c_δ/2)^k ∏_{O_D} h_i` and, if `Σ_l h_l ≤ 2t`,
`S_{D,ε}(h) ≤ c_δ^k t^k/k^k` (`E:d1-spatial-max` with `b = 1`, `K_sp = c_δ`).
Carried but unused: `0 < α₀ < 1`; `c_δ > 0` and `h_l > 0` are used as
`≥ 0`; `k ≥ 1` only for the second display. -/
theorem d1_spatial_paper_white {c α₀ : ℝ} (_hα₀0 : 0 < α₀) (_hα₀1 : α₀ < 1) (hc : 0 < c)
    {m n k : ℕ} (hk : 1 ≤ k) (hmn : m + n = 2 * k) {D : Fin (m + n) → Fin (m + n)}
    (hD : D ∈ Pi2 m n) {εs : Fin (m + n) → ℝ} (hε : ∀ i, 0 < εs i) {h : Fin (m + n) → ℝ}
    (hh : ∀ i, 0 < h i) :
    spatialPair (waveGreen 1) (fun i => covEps (whiteCov c) (εs i)) m D h ≤
        ENNReal.ofReal ((c / 2) ^ k * ∏ i ∈ openers D, h i) ∧
      ∀ t : ℝ, ∑ i, h i ≤ 2 * t →
        spatialPair (waveGreen 1) (fun i => covEps (whiteCov c) (εs i)) m D h ≤
          ENNReal.ofReal (c ^ k * t ^ k / (k : ℝ) ^ k) :=
  ⟨d1_spatial_white hc.le hmn m hD hε fun i => (hh i).le,
    fun _ hsum => d1_spatial_white_max hc.le hk hmn m hD hε (fun i => (hh i).le) hsum⟩

/-! ### The smallest diagram (refutation support) -/

/-- The self-pairing of the two labels of one chain (`m = 2`, `n = 0`, `k = 1`):
the pairing `{1, 2}` of main TeX lines 809-810 (0-based `{0, 1}`). -/
def selfPair : Fin 2 → Fin 2 := ![1, 0]

/-- Auxiliary (refutation support): the self-pairing is a pairing. -/
theorem selfPair_mem : selfPair ∈ pairings (Finset.univ : Finset (Fin 2)) := by
  rw [mem_pairings]; refine ⟨fun x _ => ?_, fun x hx => absurd (Finset.mem_univ x) hx⟩
  fin_cases x <;> simp [selfPair]

/-- Auxiliary (refutation support): its opening label is `0`. -/
theorem openers_selfPair : openers selfPair = {0} := by decide

/-- Auxiliary (refutation support): its closing label is `1`. -/
theorem closers_selfPair : closers selfPair = {1} := by decide

/-- Auxiliary (refutation support): the exact value of the smallest diagram,
`S = G_{h_0}(ℝ^d) ∫ γ(-v) G_{h_1}(dv)` (the opening increment is free, the
closing increment carries the covariance, as in the proof at main TeX lines
5411-5425). -/
theorem spatialPair_selfPair {d : ℕ} (G : ℝ → Measure (Rd d)) [∀ s, SigmaFinite (G s)]
    (γs : Fin 2 → Rd d → ℝ≥0∞) (hγ : Measurable (γs 0)) (h : Fin 2 → ℝ) :
    spatialPair G γs 2 selfPair h = G (h 0) Set.univ * ∫⁻ v, γs 0 (-v) ∂G (h 1) := by
  have hpos : ∀ w : Fin 2 → Rd d, pos 2 w 0 - pos 2 w (selfPair 0) = -(w 1) := by
    intro w
    simp [pos, selfPair, Finset.sum_filter, Fin.sum_univ_two, SameChain]
  unfold spatialPair
  rw [openers_selfPair]
  simp only [Finset.prod_singleton, hpos]
  have hmp := (measurePreserving_piFinTwo fun i => G (h i)).symm
  rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  simp only [MeasurableEquiv.piFinTwo_symm_apply, Fin.cons_one, Fin.cons_zero]
  have hm : Measurable fun a : Rd d × Rd d => γs 0 (-a.2) := hγ.comp measurable_snd.neg
  rw [lintegral_prod _ hm.aemeasurable]
  simp only [lintegral_const]
  rw [mul_comm]

end StratonovichHAMSecondMoment.D1Spatial
