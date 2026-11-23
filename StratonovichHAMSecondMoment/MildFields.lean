module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L20, item L20-C (`P:mild-construction`, Step 2; TeX lines 2204-2230 at revision edf7085f
(book 1.1.3)): measurable fields and spatial mean-square continuity.

Proved here, for every source field under `H:homog`:
* `joint_meas : JointMeasTarget d` (TeX 2213-2219): the total fields `Wa`, `Yf`, `Xf`, `uf` on
  `ℝ × ℝ^d` are strongly measurable as `L²(Ω)`-valued maps;
* `field_cont : FieldContTarget d` (TeX 2219-2230, stationarity 2224-2227): at each fixed time
  `s ≥ 0` the maps `y ↦ Y_n^b(s,y)`, `y ↦ X_n(s,y)`, `y ↦ u(s,y)` are continuous into `L²(Ω)`,
  and `‖Y_n^b(s,y) - X_n(s,y)‖₂ = ‖Y_n^b(s,0) - X_n(s,0)‖₂`;
* `field_meas : FieldMeasTarget d`, their conjunction.
No named input is used (the fallback `JointMeasurability` is not needed).

Route (disclosed differences from the TeX's wording, same mathematics):
* Joint measurability (2213-2219).  Instead of rescaling to a unit-time domain (2207-2210), the
  chain measure is unfolded to its definition: `g_n^{t,x}` is the image of
  `timeMeasure n t ⊗ G_1^{⊗n}` under `chainMap t x` (then `toPt`), and `timeMeasure n t` is
  Lebesgue measure with the density `chainWeightReal n t`.  Hence
  `Y_n^b(t,x) = ∫ w_t(s) · ∏_j W(z_j(t,x,s,v), b_j) d(ds ⊗ G_1^{⊗n}(dv))` over a FIXED
  σ-finite measure, with an integrand jointly measurable in `((t,x),(s,v))` (`Ya_eq_integral`);
  parameter integration (`StronglyMeasurable.integral_prod_right`) gives the joint strong
  measurability in `(t,x)`.  This is the TeX's "parameter integration", with the time variable
  carried by the density instead of by a rescaling.  `X_n` is the pointwise `L²` limit along the
  fixed countable common-width sequence `(1/(k+1), 1/(k+1))` (`stronglyMeasurable_of_tendsto`;
  at `s = 0` all positive orders vanish, 2210), `u` the pointwise limit of the partial sums.
* Spatial continuity (2219-2222).  `g_n^{t,x}` is the image of `g_n^{t,0}` under the spatial
  translation by `x` (`chainMeasure_shift`), so `Y_n^b(t,x)` is the integral against a fixed
  finite measure of an integrand continuous in `x` and bounded (dominated convergence).
* Stationarity (2224-2227).  The covariance depends on spatial differences only, so the
  inner products `⟪Y_m^b(t,x), Y_m^c(t,x)⟫ = ∫∫ ⟪∏ W, ∏ W⟫` do not depend on `x`
  (`inner_Ya_shift`; Wick's formula `TerminalWick.inner_prodL2` for the inner integrand);
  hence `‖Y^b(t,x) - Y^c(t,x)‖ = ‖Y^b(t,0) - Y^c(t,0)‖`, and the limit along the common widths
  (`fixed_order_l2_l19`) gives the identity with `X_n`.  Uniform convergence in `y` then gives
  the continuity of `X_n(s,·)`; the continuity of `u(s,·)` follows by the Weierstrass test with
  `E:vertex-crude` (`vertex_crude_l19`).
-/
public import Mathlib
public import StratonovichHAMSecondMoment.MildInterface

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal Real Nat

namespace StratonovichHAMSecondMoment.MildFields

universe u

open HomogHypothesis (Rd HomogCovariance)
open WaveGreen (waveGreen)
open FiniteWick (CenteredGaussianField)
open TerminalWick (Pt prodL2 chainWeightReal)
open TerminalWickInputs (chainMeasure chainMeasureRaw chainMap chainPoint toPt timeMeasure
  fieldL2 gap)
open SourceInterface
open MildInterface
open SourceFinal (fixed_order_l2_l19 expansion_l2_l19 vertex_crude_l19)

variable {d : ℕ}

/-! ### Spatial translation of chains -/

/-- Spatial translation by `x` of a chain in `[0,t] × ℝ^d`. -/
def shiftC {t : ℝ} {n : ℕ} (x : Rd d) (z : Fin n → Pt d t) : Fin n → Pt d t :=
  fun j => ((z j).1, (z j).2 + x)

/-- Spatial translation by `x` of a raw chain in `ℝ × ℝ^d`. -/
def shiftR {n : ℕ} (x : Rd d) (z : Fin n → ℝ × Rd d) : Fin n → ℝ × Rd d :=
  fun j => ((z j).1, (z j).2 + x)

/-- Spatial translation by `x` of a source point. -/
def shiftS (x : Rd d) (p : SrcPt d) : SrcPt d := ((p.1.1, p.1.2 + x), p.2)

/-- Auxiliary: the translation of chains is jointly continuous. -/
theorem continuous_shiftC {t : ℝ} {n : ℕ} :
    Continuous fun q : Rd d × (Fin n → Pt d t) => shiftC q.1 q.2 :=
  continuous_pi fun j =>
    (((continuous_apply j).comp continuous_snd).fst).prodMk
      ((((continuous_apply j).comp continuous_snd).snd).add continuous_fst)

/-- Auxiliary: the translation by a fixed `x` is continuous. -/
theorem continuous_shiftC_left {t : ℝ} {n : ℕ} (x : Rd d) :
    Continuous (shiftC (t := t) (n := n) x) :=
  continuous_shiftC.comp (continuous_const.prodMk continuous_id)

/-- Auxiliary: the translation of raw chains is continuous. -/
theorem continuous_shiftR {n : ℕ} (x : Rd d) : Continuous (shiftR (n := n) x) :=
  continuous_pi fun j =>
    ((continuous_apply j).fst).prodMk (((continuous_apply j).snd).add continuous_const)

/-- `chainMap t x` is `chainMap t 0` followed by the translation by `x`. -/
theorem chainMap_eq_shiftR (t : ℝ) (x : Rd d) {n : ℕ} (q : (Fin n → ℝ) × (Fin n → Rd d)) :
    chainMap t x q = shiftR x (chainMap t 0 q) := by
  funext j
  simp only [chainMap, chainPoint, shiftR, zero_sub, neg_add_eq_sub]

/-- **Spatial stationarity of the terminal chain measure**: `g_n^{t,x}` is the image of
`g_n^{t,0}` under the translation by `x` (TeX 4283-4285: `y_j = x - Σ_{l ≥ j} w_l`). -/
theorem chainMeasure_shift (n : ℕ) (t : ℝ) (ht : 0 ≤ t) (x : Rd d) :
    chainMeasure d n t ht x = (chainMeasure d n t ht 0).map (shiftC x) := by
  have hR : Measurable (shiftR (d := d) (n := n) x) := (continuous_shiftR x).measurable
  have hC : Measurable (shiftC (d := d) (t := t) (n := n) x) :=
    (continuous_shiftC_left x).measurable
  have hm0 := TerminalWickInputs.measurable_chainMap (d := d) (n := n) t 0
  have hpt := TerminalWickInputs.measurable_toPt (d := d) (n := n) ht
  set M := (timeMeasure n t).prod (Measure.pi fun _ : Fin n => waveGreen d 1)
  have e1 : M.map (chainMap t x) = (M.map (chainMap t 0)).map (shiftR x) := by
    rw [Measure.map_map hR hm0]
    congr 1
    funext q
    exact chainMap_eq_shiftR t x q
  have e2 : (toPt ht ∘ shiftR x : (Fin n → ℝ × Rd d) → Fin n → Pt d t) =
      shiftC x ∘ toPt ht := rfl
  rw [chainMeasure, chainMeasure, chainMeasureRaw, chainMeasureRaw]
  change (M.map (chainMap t x)).map (toPt ht) =
    ((M.map (chainMap t 0)).map (toPt ht)).map (shiftC x)
  rw [e1, Measure.map_map hpt hR, e2, ← Measure.map_map hC hpt]

/-- The source covariance depends on spatial differences only. -/
theorem srcCov_shiftS (α₀ : ℝ) (Γ : Measure (Rd d)) (x : Rd d) (p q : SrcPt d) :
    srcCov α₀ Γ (shiftS x p) (shiftS x q) = srcCov α₀ Γ p q := by
  simp only [srcCov, shiftS, add_sub_add_right_eq_sub]

section Field

variable {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : SrcPt d → Ω → ℝ}

/-- The covariance continuity of `SourceFeatures.source_cov_continuous` in the form used by
`SourceWick`. -/
theorem hcov (hH : HomogCovariance d alpha α₀ Γ μ) (w w' : PosW) :
    Continuous fun pq : (↥(Ici (0 : ℝ)) × Rd d) × (↥(Ici (0 : ℝ)) × Rd d) =>
      srcCov α₀ Γ (pq.1, w) (pq.2, w') :=
  SourceFeatures.source_cov_continuous d hH w w'

/-- Wick inner products are invariant under a common spatial translation. -/
theorem inner_prodL2_shiftS (hW : SourceField α₀ Γ P W) (x : Rd d) {m n : ℕ}
    (p : Fin m → SrcPt d) (q : Fin n → SrcPt d) :
    inner ℝ (prodL2 hW fun j => shiftS x (p j)) (prodL2 hW fun j => shiftS x (q j)) =
      inner ℝ (prodL2 hW p) (prodL2 hW q) := by
  rw [TerminalWick.inner_prodL2, TerminalWick.inner_prodL2]
  have h : ∀ i, Fin.append (fun j => shiftS x (p j)) (fun j => shiftS x (q j)) i =
      shiftS x (Fin.append p q i) := by
    intro i
    induction i using Fin.addCases with
    | left j => simp only [Fin.append_left]
    | right j => simp only [Fin.append_right]
  congr 1
  funext a b
  rw [h, h, srcCov_shiftS]

/-- `Y_n^b(t,x)` as an integral against the fixed measure `g_n^{t,0}`. -/
theorem Ya_shift (hH : HomogCovariance d alpha α₀ Γ μ) (hW : SourceField α₀ Γ P W) (t : ℝ)
    (ht : 0 ≤ t) (x : Rd d) {n : ℕ} (b : Fin n → PosW) :
    Ya hW t ht x b =
      ∫ z, prodL2 hW (attach b (shiftC x z)) ∂chainMeasure d n t ht 0 := by
  have hF := SourceWick.continuous_prodL2_attach hW (hcov hH) (t := t) b
  rw [Ya, chainMeasure_shift n t ht x,
    integral_map (continuous_shiftC_left x).measurable.aemeasurable hF.aestronglyMeasurable]

/-- The shifted integrand is continuous jointly in the shift and the chain. -/
theorem continuous_prodL2_shift (hH : HomogCovariance d alpha α₀ Γ μ)
    (hW : SourceField α₀ Γ P W) {t : ℝ} {n : ℕ} (b : Fin n → PosW) :
    Continuous fun q : Rd d × (Fin n → Pt d t) => prodL2 hW (attach b (shiftC q.1 q.2)) :=
  (SourceWick.continuous_prodL2_attach hW (hcov hH) (t := t) b).comp continuous_shiftC

/-- Auxiliary: the shifted integrand is integrable (bounded, finite chain measure). -/
theorem integrable_prodL2_shift (hH : HomogCovariance d alpha α₀ Γ μ)
    (hW : SourceField α₀ Γ P W) (t : ℝ) (ht : 0 ≤ t) (x : Rd d) {n : ℕ} (b : Fin n → PosW) :
    Integrable (fun z => prodL2 hW (attach b (shiftC x z))) (chainMeasure d n t ht 0) :=
  Integrable.of_bound
    ((continuous_prodL2_shift hH hW b).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    _ (ae_of_all _ fun z => SourceWick.norm_prodL2_attach_le hW b (shiftC x z))

/-- **Spatial `L²` continuity of the positive-width terminal integrals** (TeX 2219-2222):
`y ↦ Y_n^b(t,y)` is continuous into `L²(Ω)`. -/
theorem continuous_Ya (hH : HomogCovariance d alpha α₀ Γ μ) (hW : SourceField α₀ Γ P W)
    (t : ℝ) (ht : 0 ≤ t) {n : ℕ} (b : Fin n → PosW) :
    Continuous fun y : Rd d => Ya hW t ht y b := by
  have he : (fun y : Rd d => Ya hW t ht y b) =
      fun y => ∫ z, prodL2 hW (attach b (shiftC y z)) ∂chainMeasure d n t ht 0 :=
    funext fun y => Ya_shift hH hW t ht y b
  rw [he]
  have hF := continuous_prodL2_shift hH hW (t := t) b
  refine continuous_of_dominated
    (bound := fun _ => Real.sqrt ((2 * n - 1).doubleFactorial) *
      Real.sqrt (SourceWick.varB α₀ Γ b) ^ n)
    (fun y => (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (fun y => ae_of_all _ fun z => SourceWick.norm_prodL2_attach_le hW b (shiftC y z))
    (integrable_const _) (ae_of_all _ fun z => ?_)
  exact hF.comp (continuous_id.prodMk continuous_const)

/-- `⟪∫ f, ∫ g⟫ = ∫∫ ⟪f z, g z'⟫` for integrable `L²`-valued maps. -/
theorem inner_integral_integral {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {f g : α → Lp ℝ 2 P} (hf : Integrable f ν) (hg : Integrable g ν) :
    inner ℝ (∫ z, f z ∂ν) (∫ z, g z ∂ν) = ∫ z', ∫ z, inner ℝ (f z) (g z') ∂ν ∂ν := by
  rw [← integral_inner hg]
  refine integral_congr_ae (ae_of_all _ fun z' => ?_)
  simp only
  rw [real_inner_comm, ← integral_inner hf]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [real_inner_comm]

/-- **Spatial stationarity of the inner products** (TeX 2222-2227): `⟪Y_m^b(t,x), Y_m^c(t,x)⟫`
does not depend on `x`. -/
theorem inner_Ya_shift (hH : HomogCovariance d alpha α₀ Γ μ) (hW : SourceField α₀ Γ P W)
    (t : ℝ) (ht : 0 ≤ t) (x : Rd d) {m : ℕ} (b : Fin m → PosW) (c : Fin m → PosW) :
    inner ℝ (Ya hW t ht x b) (Ya hW t ht x c) = inner ℝ (Ya hW t ht 0 b) (Ya hW t ht 0 c) := by
  rw [Ya_shift hH hW t ht x b, Ya_shift hH hW t ht x c, Ya_shift hH hW t ht 0 b,
    Ya_shift hH hW t ht 0 c,
    inner_integral_integral (integrable_prodL2_shift hH hW t ht x b)
      (integrable_prodL2_shift hH hW t ht x c),
    inner_integral_integral (integrable_prodL2_shift hH hW t ht 0 b)
      (integrable_prodL2_shift hH hW t ht 0 c)]
  refine integral_congr_ae (ae_of_all _ fun z' => integral_congr_ae (ae_of_all _ fun z => ?_))
  have e : ∀ (y : Rd d) (a : Fin m → PosW) (w : Fin m → Pt d t),
      attach a (shiftC y w) = fun j => shiftS y (attach a w j) := fun _ _ _ => rfl
  simp only [e]
  rw [inner_prodL2_shiftS hW x, inner_prodL2_shiftS hW 0]

/-- **Spatial stationarity of the distances** between terminal integrals of one order. -/
theorem norm_sub_Ya_shift (hH : HomogCovariance d alpha α₀ Γ μ) (hW : SourceField α₀ Γ P W)
    (t : ℝ) (ht : 0 ≤ t) (x : Rd d) {m : ℕ} (b c : Fin m → PosW) :
    ‖Ya hW t ht x b - Ya hW t ht x c‖ = ‖Ya hW t ht 0 b - Ya hW t ht 0 c‖ := by
  have hsq : ‖Ya hW t ht x b - Ya hW t ht x c‖ ^ 2 = ‖Ya hW t ht 0 b - Ya hW t ht 0 c‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_sub_sq_real, ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq (Ya hW t ht 0 b),
      ← real_inner_self_eq_norm_sq (Ya hW t ht 0 c), inner_Ya_shift hH hW t ht x b b,
      inner_Ya_shift hH hW t ht x c c, inner_Ya_shift hH hW t ht x b c]
  rw [← Real.sqrt_sq (norm_nonneg (Ya hW t ht x b - Ya hW t ht x c)), hsq,
    Real.sqrt_sq (norm_nonneg _)]

/-! ### Time zero: the positive orders vanish (TeX 2210) -/

/-- At time `0` the chain measure of a positive order is zero (mass `0^{2(n+1)}/(2(n+1))!`). -/
theorem chainMeasure_time_zero (n : ℕ) (h0 : (0 : ℝ) ≤ 0) (x : Rd d) :
    chainMeasure d (n + 1) 0 h0 x = 0 := by
  have hn : 2 * (n + 1) ≠ 0 := by omega
  rw [← Measure.measure_univ_eq_zero, TerminalWickInputs.chainMeasure_univ_eq,
    TerminalWickInputs.chainMeasureRaw_univ_eq, TerminalWick.chainMassReal_eq (n + 1) 0 le_rfl]
  simp [zero_pow hn]

/-- At time `0` the positive-order terminal integrals vanish (TeX 2210). -/
theorem Ya_time_zero (hW : SourceField α₀ Γ P W) {s : ℝ} (hs : 0 ≤ s) (h0 : s = 0) (y : Rd d)
    {n : ℕ} (b : Fin (n + 1) → PosW) : Ya hW s hs y b = 0 := by
  subst h0
  rw [Ya, chainMeasure_time_zero, integral_zero_measure]

/-- At time `0` the positive-order chaos terms `X_n` vanish (TeX 2210). -/
theorem XL2_time_zero (hW : SourceField α₀ Γ P W) {s : ℝ} (hs : 0 ≤ s) (h0 : s = 0) (y : Rd d)
    (n : ℕ) : XL2 hW s hs y (n + 1) = 0 := by
  have he : Ycom hW s hs y (n + 1) = fun _ => 0 :=
    funext fun _ => Ya_time_zero hW hs h0 y _
  rw [XL2_succ, stratInt, he]
  exact tendsto_const_nhds.limUnder_eq

/-! ### The time-density representation (joint measurability, TeX 2213-2217) -/

/-- The time `max 0 (min t r)` as a point of `[0,∞)` (the value of `toPt`). -/
def clampT (t r : ℝ) : ↥(Ici (0 : ℝ)) := ⟨max 0 (min t r), le_max_left _ _⟩

/-- Auxiliary: `clampT` is continuous. -/
theorem continuous_clampT : Continuous fun p : ℝ × ℝ => clampT p.1 p.2 :=
  (continuous_const.max (continuous_fst.min continuous_snd)).subtype_mk _

/-- The width-attached chain points as a total function of `(t, x)` and the raw variables. -/
def chainPtT {n : ℕ} (b : Fin n → PosW) (p : ℝ × Rd d)
    (q : (Fin n → ℝ) × (Fin n → Rd d)) : Fin n → SrcPt d :=
  fun j => ((clampT p.1 (chainMap p.1 p.2 q j).1, (chainMap p.1 p.2 q j).2), b j)

/-- Auxiliary: `(T, s) ↦ (s_1, …, s_n, T)_k` is jointly continuous. -/
theorem continuous_snoc_apply₂ {n : ℕ} (k : Fin (n + 1)) :
    Continuous fun p : ℝ × (Fin n → ℝ) => (Fin.snoc p.2 p.1 : Fin (n + 1) → ℝ) k := by
  induction k using Fin.lastCases with
  | last => simp only [Fin.snoc_last]; exact continuous_fst
  | cast i => simp only [Fin.snoc_castSucc]; exact (continuous_apply i).comp continuous_snd

/-- Auxiliary: the gaps are jointly continuous in the terminal time and the times. -/
theorem continuous_gap₂ {n : ℕ} (j : Fin n) :
    Continuous fun p : ℝ × (Fin n → ℝ) => gap p.1 p.2 j :=
  (continuous_snoc_apply₂ j.succ).sub ((continuous_apply j).comp continuous_snd)

/-- Auxiliary: `chainMap T x q` is jointly continuous in `(T, x, q)`. -/
theorem continuous_chainMap₂ {n : ℕ} :
    Continuous fun w : (ℝ × Rd d) × ((Fin n → ℝ) × (Fin n → Rd d)) =>
      chainMap w.1.1 w.1.2 w.2 := by
  refine continuous_pi fun j => ?_
  have hT : Continuous fun w : (ℝ × Rd d) × ((Fin n → ℝ) × (Fin n → Rd d)) => w.1.1 :=
    continuous_fst.comp continuous_fst
  have hs : Continuous fun w : (ℝ × Rd d) × ((Fin n → ℝ) × (Fin n → Rd d)) => w.2.1 :=
    continuous_fst.comp continuous_snd
  have hv : Continuous fun w : (ℝ × Rd d) × ((Fin n → ℝ) × (Fin n → Rd d)) => w.2.2 :=
    continuous_snd.comp continuous_snd
  simp only [chainMap, chainPoint]
  refine ((continuous_apply j).comp hs).prodMk ?_
  refine (continuous_snd.comp continuous_fst).sub (continuous_finsetSum _ fun l _ => ?_)
  exact ((continuous_gap₂ l).comp (hT.prodMk hs)).smul ((continuous_apply l).comp hv)

/-- Auxiliary: the integrand of the representation is jointly continuous. -/
theorem continuous_prodL2_chainPtT (hH : HomogCovariance d alpha α₀ Γ μ)
    (hW : SourceField α₀ Γ P W) {n : ℕ} (b : Fin n → PosW) :
    Continuous fun w : (ℝ × Rd d) × ((Fin n → ℝ) × (Fin n → Rd d)) =>
      prodL2 hW (chainPtT b w.1 w.2) := by
  refine SourceWick.continuous_prodL2_of hW
    (fun w : (ℝ × Rd d) × ((Fin n → ℝ) × (Fin n → Rd d)) => chainPtT b w.1 w.2) fun j => ?_
  have hcm := (continuous_apply j).comp (continuous_chainMap₂ (d := d) (n := n))
  have hpt : Continuous fun w : (ℝ × Rd d) × ((Fin n → ℝ) × (Fin n → Rd d)) =>
      ((clampT w.1.1 (chainMap w.1.1 w.1.2 w.2 j).1, (chainMap w.1.1 w.1.2 w.2 j).2) :
        ↥(Ici (0 : ℝ)) × Rd d) :=
    (continuous_clampT.comp ((continuous_fst.comp continuous_fst).prodMk hcm.fst)).prodMk
      hcm.snd
  exact (SourceWick.continuous_fieldL2_w hW (b j) (hcov hH (b j) (b j))).comp hpt

/-- The fixed σ-finite measure `ds ⊗ G_1^{⊗n}(dv)` of the representation. -/
def baseM (d n : ℕ) : Measure ((Fin n → ℝ) × (Fin n → Rd d)) :=
  (volume : Measure (Fin n → ℝ)).prod (Measure.pi fun _ : Fin n => waveGreen d 1)

/-- `baseM` is σ-finite. -/
instance instSFiniteBaseM (d n : ℕ) : SFinite (baseM d n) :=
  Measure.prod.instSFinite (μ := (volume : Measure (Fin n → ℝ)))
    (ν := Measure.pi fun _ : Fin n => waveGreen d 1)

/-- Auxiliary: the time density is finite. -/
theorem chainWeightReal_lt_top (n : ℕ) (T : ℝ) (s : Fin n → ℝ) : chainWeightReal n T s < ∞ := by
  rw [TerminalWickInputs.chainWeightReal_eq_ite]
  split_ifs
  · exact ENNReal.prod_lt_top fun _ _ => ENNReal.ofReal_lt_top
  · exact ENNReal.zero_lt_top

/-- **`Y_n^b(t,x)` over a fixed measure** (the parameter integral of TeX 2213-2217): the
integral of `w_t(s) ∏_j W(z_j(t,x,s,v), b_j)` against `ds ⊗ G_1^{⊗n}(dv)`, with the time
density `w_t = chainWeightReal n t` of `timeMeasure n t`. -/
theorem Ya_eq_integral (hH : HomogCovariance d alpha α₀ Γ μ) (hW : SourceField α₀ Γ P W)
    (t : ℝ) (ht : 0 ≤ t) (x : Rd d) {n : ℕ} (b : Fin n → PosW) :
    Ya hW t ht x b =
      ∫ q, (chainWeightReal n t q.1).toReal • prodL2 hW (chainPtT b (t, x) q) ∂baseM d n := by
  have hF := SourceWick.continuous_prodL2_attach hW (hcov hH) (t := t) b
  have hF' : Continuous fun z : Fin n → ℝ × Rd d => prodL2 hW (attach b (toPt ht z)) :=
    hF.comp (TerminalWickRegularization.continuous_toPt ht)
  have hw := TerminalWickInputs.measurable_chainWeightReal_right n t
  rw [Ya, chainMeasure, chainMeasureRaw,
    integral_map (TerminalWickInputs.measurable_toPt ht).aemeasurable hF.aestronglyMeasurable,
    integral_map (TerminalWickInputs.measurable_chainMap t x).aemeasurable
      hF'.aestronglyMeasurable,
    timeMeasure, prod_withDensity_left hw,
    integral_withDensity_eq_integral_toReal_smul
      (f := fun z : (Fin n → ℝ) × (Fin n → Rd d) => chainWeightReal n t z.1)
      (hw.comp measurable_fst)
      (ae_of_all _ fun q => chainWeightReal_lt_top n t q.1)]
  rfl

/-- Parameter integration: the representation is strongly measurable in `(t, x)`. -/
theorem stronglyMeasurable_Yrep (hH : HomogCovariance d alpha α₀ Γ μ)
    (hW : SourceField α₀ Γ P W) {n : ℕ} (b : Fin n → PosW) :
    StronglyMeasurable fun p : ℝ × Rd d =>
      ∫ q, (chainWeightReal n p.1 q.1).toReal • prodL2 hW (chainPtT b p q) ∂baseM d n := by
  have hw : Measurable fun w : (ℝ × Rd d) × ((Fin n → ℝ) × (Fin n → Rd d)) =>
      (chainWeightReal n w.1.1 w.2.1).toReal :=
    ((TerminalWick.measurable_chainWeightReal n).comp
      ((measurable_fst.comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd))).ennreal_toReal
  have hΦ : StronglyMeasurable fun w : (ℝ × Rd d) × ((Fin n → ℝ) × (Fin n → Rd d)) =>
      (chainWeightReal n w.1.1 w.2.1).toReal • prodL2 hW (chainPtT b w.1 w.2) :=
    hw.stronglyMeasurable.smul (continuous_prodL2_chainPtT hH hW b).stronglyMeasurable
  exact StronglyMeasurable.integral_prod_right
    (f := fun (p : ℝ × Rd d) (q : (Fin n → ℝ) × (Fin n → Rd d)) =>
      (chainWeightReal n p.1 q.1).toReal • prodL2 hW (chainPtT b p q)) hΦ

/-- `(s, y) ↦ Y_n^b(s, y)` (total, `0` for `s < 0`) is strongly measurable. -/
theorem stronglyMeasurable_Yf (hH : HomogCovariance d alpha α₀ Γ μ) (hW : SourceField α₀ Γ P W)
    {n : ℕ} (b : Fin n → PosW) : StronglyMeasurable (Yf hW b) := by
  have he : Yf hW b = fun p : ℝ × Rd d => if 0 ≤ p.1 then
      ∫ q, (chainWeightReal n p.1 q.1).toReal • prodL2 hW (chainPtT b p q) ∂baseM d n
      else 0 := by
    funext p
    by_cases h : 0 ≤ p.1
    · rw [Yf, dite_eq_left h, ite_eq_left h]
      exact Ya_eq_integral hH hW p.1 h p.2 b
    · rw [Yf, dite_eq_right h, ite_eq_right h]
  rw [he]
  exact (stronglyMeasurable_Yrep hH hW b).ite (measurableSet_le measurable_const measurable_fst)
    stronglyMeasurable_const

/-- `(s, y) ↦ W_a(s, y)` (total, `0` for `s < 0`) is strongly measurable. -/
theorem stronglyMeasurable_Wa (hH : HomogCovariance d alpha α₀ Γ μ) (hW : SourceField α₀ Γ P W)
    (a : PosW) : StronglyMeasurable (Wa hW a) := by
  have hg : Continuous fun p : ℝ × Rd d =>
      fieldL2 hW (((⟨max p.1 0, le_max_right _ _⟩ : ↥(Ici (0 : ℝ))), p.2), a) := by
    refine (SourceWick.continuous_fieldL2_w hW a (hcov hH a a)).comp
      (f := fun p : ℝ × Rd d => ((⟨max p.1 0, le_max_right _ _⟩ : ↥(Ici (0 : ℝ))), p.2)) ?_
    exact ((continuous_fst.max continuous_const).subtype_mk _).prodMk continuous_snd
  have he : Wa hW a = fun p : ℝ × Rd d => if 0 ≤ p.1 then
      fieldL2 hW (((⟨max p.1 0, le_max_right _ _⟩ : ↥(Ici (0 : ℝ))), p.2), a) else 0 := by
    funext p
    by_cases h : 0 ≤ p.1
    · rw [Wa, dite_eq_left h, ite_eq_left h]
      congr 3
      exact Subtype.ext (max_eq_left h).symm
    · rw [Wa, dite_eq_right h, ite_eq_right h]
  rw [he]
  exact hg.stronglyMeasurable.ite (measurableSet_le measurable_const measurable_fst)
    stronglyMeasurable_const

/-! ### The countable common-width sequence -/

/-- The common widths `1/(k+1)`. -/
def epsK (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

/-- Auxiliary: the common widths are positive. -/
theorem epsK_pos (k : ℕ) : 0 < epsK k := by unfold epsK; positivity

/-- Auxiliary: the common widths tend to `(0,0)` within the positive quadrant. -/
theorem tendsto_epsK :
    Tendsto (fun k => (epsK k, epsK k)) atTop (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) := by
  have h : Tendsto epsK atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun k => Set.mem_Ioi.2 (epsK_pos k)⟩
  exact h.prodMk h

end Field

/-! ### The targets -/

/-- **Joint measurability** (`JointMeasTarget`; TeX 2213-2219 at revision edf7085f (book
1.1.3)): `W_a`, `Y_n^b`, `X_n` and `u` are strongly measurable in `(s,y)` as `L²(Ω)`-valued
maps (total fields, `0` for `s < 0`).  Route: the time-density representation
(`Ya_eq_integral`) and parameter integration; `X_n` the pointwise limit along the common widths
`1/(k+1)` (`fixed_order_l2_l19`), `u` the pointwise limit of the partial sums
(`expansion_l2_l19`); at `s = 0` the positive orders vanish (2210). -/
theorem joint_meas (d : ℕ) : JointMeasTarget.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW
  -- the order-`n` fields
  have hX : ∀ n : ℕ, StronglyMeasurable (Xf hW n) := by
    intro n
    cases n with
    | zero =>
      have he : Xf hW 0 = Yf hW (Fin.elim0 : Fin 0 → PosW) := by
        funext p
        by_cases h : 0 ≤ p.1
        · rw [Xf, Yf, dite_eq_left h, dite_eq_left h, XL2_zero]
        · rw [Xf, Yf, dite_eq_right h, dite_eq_right h]
      rw [he]
      exact stronglyMeasurable_Yf hH hW _
    | succ n =>
      set bk : ℕ → Fin (n + 1) → PosW := fun k => posW (fun _ => epsK k) (fun _ => epsK k)
      refine stronglyMeasurable_of_tendsto atTop (f := fun k => Yf hW (bk k))
        (fun k => stronglyMeasurable_Yf hH hW (bk k)) (tendsto_pi_nhds.2 fun p => ?_)
      by_cases h : 0 ≤ p.1
      · simp only [Yf, Xf, dite_eq_left h]
        rcases h.eq_or_lt with h0 | hpos
        · have h0' : p.1 = 0 := h0.symm
          simp only [Ya_time_zero hW h h0', XL2_time_zero hW h h0']
          exact tendsto_const_nhds
        · have hT := ((fixed_order_l2_l19.{u} d hH P W hW p.1 hpos p.2 (n + 1)
            (by omega)).2).comp tendsto_epsK
          exact hT
      · simp only [Yf, Xf, dite_eq_right h]
        exact tendsto_const_nhds
  refine ⟨fun a => stronglyMeasurable_Wa hH hW a, fun n b => stronglyMeasurable_Yf hH hW b, hX,
    ?_⟩
  -- the series
  refine stronglyMeasurable_of_tendsto atTop
    (f := fun N p => ∑ n ∈ Finset.range N, Xf hW n p)
    (fun N => Finset.stronglyMeasurable_fun_sum _ fun n _ => hX n)
    (tendsto_pi_nhds.2 fun p => ?_)
  by_cases h : 0 ≤ p.1
  · simp only [Xf, uf, dite_eq_left h]
    rcases h.eq_or_lt with h0 | hpos
    · have h0' : p.1 = 0 := h0.symm
      have hz : ∀ n ≠ 0, XL2 hW p.1 h p.2 n = 0 := by
        intro n hn
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
        exact XL2_time_zero hW h h0' p.2 m
      have hs : HasSum (XL2 hW p.1 h p.2) (uL2 hW p.1 h p.2) := by
        rw [uL2, tsum_eq_single 0 hz]
        exact hasSum_single 0 hz
      exact hs.tendsto_sum_nat
    · exact (expansion_l2_l19.{u} d hH P W hW p.1 hpos p.2).2.tendsto_sum_nat
  · simp only [Xf, uf, dite_eq_right h, Finset.sum_const_zero]
    exact tendsto_const_nhds

/-- **Spatial continuity and stationarity** (`FieldContTarget`; TeX 2219-2230 at revision
edf7085f (book 1.1.3), stationarity 2224-2227).  Route: translation of the chain measure
(`chainMeasure_shift`) and dominated convergence; the stationarity of the inner products
(`inner_Ya_shift`) and the common-width limit (`fixed_order_l2_l19`); uniform convergence for
`X_n(s,·)`; the Weierstrass test with `E:vertex-crude` (`vertex_crude_l19`) for `u(s,·)`. -/
theorem field_cont (d : ℕ) : FieldContTarget.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW s hs
  -- the stationarity identity
  have hstat : ∀ (n : ℕ) (b : Fin n → PosW) (y : Rd d),
      ‖Ya hW s hs y b - XL2 hW s hs y n‖ = ‖Ya hW s hs 0 b - XL2 hW s hs 0 n‖ := by
    intro n b y
    cases n with
    | zero =>
      have hb : b = Fin.elim0 := Subsingleton.elim _ _
      subst hb
      rw [XL2_zero, XL2_zero, sub_self, sub_self]
    | succ n =>
      rcases hs.eq_or_lt with h0 | hpos
      · rw [Ya_time_zero hW hs h0.symm, Ya_time_zero hW hs h0.symm, XL2_time_zero hW hs h0.symm,
          XL2_time_zero hW hs h0.symm]
      · have hy := (fixed_order_l2_l19.{u} d hH P W hW s hpos y (n + 1) (by omega)).2
        have h0 := (fixed_order_l2_l19.{u} d hH P W hW s hpos 0 (n + 1) (by omega)).2
        have l1 : Tendsto (fun p => ‖Ya hW s hs y b - Ycom hW s hs y (n + 1) p‖)
            (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 ‖Ya hW s hs y b - XL2 hW s hs y (n + 1)‖) :=
          (tendsto_const_nhds.sub hy).norm
        have l2 : Tendsto (fun p => ‖Ya hW s hs 0 b - Ycom hW s hs 0 (n + 1) p‖)
            (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 ‖Ya hW s hs 0 b - XL2 hW s hs 0 (n + 1)‖) :=
          (tendsto_const_nhds.sub h0).norm
        have he : (fun p => ‖Ya hW s hs y b - Ycom hW s hs y (n + 1) p‖) =
            fun p => ‖Ya hW s hs 0 b - Ycom hW s hs 0 (n + 1) p‖ :=
          funext fun p => norm_sub_Ya_shift hH hW s hs y b _
        rw [he] at l1
        exact tendsto_nhds_unique l1 l2
  -- continuity of `X_n(s,·)`
  have hXc : ∀ n : ℕ, Continuous fun y : Rd d => XL2 hW s hs y n := by
    intro n
    cases n with
    | zero =>
      simp only [XL2_zero]
      exact continuous_Ya hH hW s hs _
    | succ n =>
      rcases hs.eq_or_lt with h0 | hpos
      · have he : (fun y : Rd d => XL2 hW s hs y (n + 1)) = fun _ => 0 :=
          funext fun y => XL2_time_zero hW hs h0.symm y n
        rw [he]
        exact continuous_const
      · have h0 := (fixed_order_l2_l19.{u} d hH P W hW s hpos 0 (n + 1) (by omega)).2
        have hU : TendstoUniformly (fun p y => Ycom hW s hs y (n + 1) p)
            (fun y => XL2 hW s hs y (n + 1)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) := by
          rw [Metric.tendstoUniformly_iff]
          intro ε hε
          have hn : Tendsto (fun p => ‖Ycom hW s hs 0 (n + 1) p - XL2 hW s hs 0 (n + 1)‖)
              (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 0) := by
            exact tendsto_iff_norm_sub_tendsto_zero.1 h0
          filter_upwards [hn.eventually (gt_mem_nhds hε)] with p hp y
          rw [dist_eq_norm, norm_sub_rev]
          exact (hstat (n + 1) _ y).trans_lt hp
        exact hU.continuous (Frequently.of_forall fun p => continuous_Ya hH hW s hs _)
  refine ⟨fun n b => continuous_Ya hH hW s hs b, hstat, hXc, ?_⟩
  -- continuity of `u(s,·)`
  rcases hs.eq_or_lt with h0 | hpos
  · have hz : ∀ (y : Rd d) (n : ℕ), n ≠ 0 → XL2 hW s hs y n = 0 := by
      intro y n hn
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      exact XL2_time_zero hW hs h0.symm y m
    have he : (fun y : Rd d => uL2 hW s hs y) = fun y => XL2 hW s hs y 0 :=
      funext fun y => tsum_eq_single 0 (hz y)
    rw [he]
    exact hXc 0
  · obtain ⟨C, θ₀, _, _, _, hXb, hsum⟩ := vertex_crude_l19.{u} d hH
    have hq : Summable fun n : ℕ => qn C θ₀ n s := by
      refine (hsum s).of_nonneg_of_le (fun n => qn_nonneg hs n) fun n => ?_
      have h1 : 1 ≤ Real.sqrt ((n : ℝ) + 1) := by
        rw [Real.one_le_sqrt]; linarith [n.cast_nonneg (α := ℝ)]
      nlinarith [qn_nonneg (C := C) (θ₀ := θ₀) hs n]
    exact continuous_tsum hXc hq fun n y => hXb P W hW s hpos y n

/-- **`P:mild-construction`, Step 2** (`FieldMeasTarget`; TeX 2204-2230 at revision edf7085f
(book 1.1.3)): joint measurability, spatial continuity and stationarity. -/
theorem field_meas (d : ℕ) : FieldMeasTarget.{u} d :=
  ⟨joint_meas d, field_cont d⟩

end StratonovichHAMSecondMoment.MildFields
