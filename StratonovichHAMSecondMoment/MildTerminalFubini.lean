module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L20, item D (first module): `TerminalFubiniTarget`, the terminal-kernel Fubini of
`P:mild-construction` Step 3 (TeX lines 2257-2260 at revision edf7085f (book 1.1.3)) with the
last-vertex disintegration of `E:terminal-chain-measure` (TeX lines 4276-4285 at revision
edf7085f (book 1.1.3)).

Route (probe D, `L20ProbeD.lean`, never committed, FEASIBLE; the named input
`TerminalFubini` is not used):
* `lintegral_chainMeasureRaw_succ`, `chainMeasureRaw_succ_eq`, `integral_chainMeasureRaw_succ`:
  `g_{n+1}^{T,x}` is the image of the last vertex `(s, x - (T - s) v)` (weight
  `1_{0<s<T} (T - s)`, `v ∼ G_1`) and the earlier chain `g_n^{s, x - (T-s) v}` (no dependent
  type: the decomposition is on `chainMeasureRaw`, transferred by `toPt`);
* `mildMeasure_eq`: the order-one chain measure mapped by `mildPt` is the image of
  `1_{0<s<t}(t-s) ds ⊗ G_1(dv)` under a measurable equivalence `mildEquiv` (equal to
  `(s, v) ↦ (s, x - (t - s) v)` off the null line `s = t`), so the mild integral needs no
  measurability of its integrand;
* `ae_mul_integral_eq`: multiplying an `L²`-valued Bochner integral by a fixed `L²` class `H`
  commutes with the integral whenever the products are `L²` and integrable (route: test against
  the bounded functions `1_A 1_{|H| ≤ N} H`; no closed-graph or operator argument);
* the terminal product: `∏_{j ≤ m} W(z_j, c_j) = W(p, a) ∏_{j < m} W(z_j, b_j)` for
  `c = Fin.snoc b a`, `z_m = p` (`coeFn_prodL2_snoc`).

The `MemLp` clause for points with negative time is the junk zero of the total fields (`Wa` is
`0` there).  No hypothesis beyond `H:homog` is taken (L19-B's continuity of the covariance at fixed
widths, `SourceFeatures.source_cov_continuous`, is a proved L19 theorem).
-/
public import Mathlib
public import StratonovichHAMSecondMoment.MildInterface

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal Real Nat

namespace StratonovichHAMSecondMoment.MildTerminalFubini

universe u

open HomogHypothesis (Rd HomogCovariance)
open WaveGreen (waveGreen)
open FiniteWick (CenteredGaussianField)
open TerminalWick (Pt prodL2 chainWeightReal measurable_chainWeightReal)
open TerminalWickInputs
open SourceInterface
open MildInterface

variable {d : ℕ}

/-! ### The last-vertex disintegration of `g_{n+1}^{T,x}` (TeX 4276-4285) -/

section Chain

/-- The weight of the last (terminal) vertex: `1_{0<s<T} (T - s)` (the Green mass
`G_{T-s}(ℝ^d) = T - s`, TeX 1651, also 6131-6132; the last vertex of
`E:terminal-chain-measure`, 4276-4282). -/
def lastW (T s : ℝ) : ℝ≥0∞ :=
  if 0 < s ∧ s < T then ENNReal.ofReal (T - s) else 0

theorem measurable_lastW (T : ℝ) : Measurable (lastW T) := by
  unfold lastW
  refine Measurable.ite ?_ (ENNReal.measurable_ofReal.comp (measurable_const.sub measurable_id))
    measurable_const
  exact (measurableSet_lt measurable_const measurable_id).inter
    (measurableSet_lt measurable_id measurable_const)

theorem lastW_ne_top (T s : ℝ) : lastW T s ≠ ∞ := by
  unfold lastW; split_ifs
  · exact ENNReal.ofReal_ne_top
  · exact ENNReal.zero_ne_top

theorem mem_of_lastW_ne_zero {T s : ℝ} (h : lastW T s ≠ 0) : 0 < s ∧ s < T := by
  unfold lastW at h
  by_contra h'
  exact h (ite_eq_right h')

theorem chainWeightReal_snoc (n : ℕ) (T sl : ℝ) (s : Fin n → ℝ) :
    chainWeightReal (n + 1) T (Fin.snoc s sl : Fin (n + 1) → ℝ) =
      lastW T sl * chainWeightReal n sl s := by
  simp only [chainWeightReal, Fin.snoc_last, Fin.init_snoc, lastW]

theorem chainWeightReal_ne_top (n : ℕ) (T : ℝ) (s : Fin n → ℝ) : chainWeightReal n T s ≠ ∞ := by
  classical
  rw [TerminalWickInputs.chainWeightReal_eq_ite]
  split_ifs
  · exact ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top
  · exact ENNReal.zero_ne_top

theorem gap_snoc_castSucc (T sl : ℝ) {n : ℕ} (s : Fin n → ℝ) (i : Fin n) :
    gap T (Fin.snoc s sl : Fin (n + 1) → ℝ) i.castSucc = gap sl s i := by
  rw [gap_castSucc, Fin.snoc_last, Fin.init_snoc]

theorem gap_snoc_last (T sl : ℝ) {n : ℕ} (s : Fin n → ℝ) :
    gap T (Fin.snoc s sl : Fin (n + 1) → ℝ) (Fin.last n) = T - sl := by
  rw [gap_last, Fin.snoc_last]

theorem sum_filter_le_succ {n : ℕ} (j : Fin (n + 1)) (g : Fin (n + 1) → Rd d) :
    ∑ l ∈ Finset.univ.filter (fun l => j ≤ l), g l =
      (∑ l : Fin n, if j ≤ l.castSucc then g l.castSucc else 0) + g (Fin.last n) := by
  rw [Finset.sum_filter, Fin.sum_univ_castSucc, ite_eq_left (Fin.le_last j)]

/-- The pointwise last-vertex recursion of `chainMap`: the first `n` points of an `(n+1)`-chain
ending at `(T,x)` form the `n`-chain ending at the last vertex `(s_l, x - (T - s_l) v_l)`. -/
theorem chainMap_snoc (T : ℝ) (x : Rd d) {n : ℕ} (s : Fin n → ℝ) (sl : ℝ) (v : Fin n → Rd d)
    (vl : Rd d) :
    chainMap (n := n + 1) T x ((Fin.snoc s sl : Fin (n + 1) → ℝ),
        (Fin.snoc v vl : Fin (n + 1) → Rd d)) =
      (Fin.snoc (chainMap sl (x - (T - sl) • vl) (s, v)) (sl, x - (T - sl) • vl) :
        Fin (n + 1) → ℝ × Rd d) := by
  funext j
  induction j using Fin.lastCases with
  | last =>
    simp only [chainMap, chainPoint, Fin.snoc_last, sum_filter_le_succ, gap_snoc_last]
    have : ∀ l : Fin n, ¬ (Fin.last n ≤ l.castSucc) := fun l => not_le.2 (Fin.castSucc_lt_last l)
    simp [this]
  | cast i =>
    simp only [chainMap, chainPoint, Fin.snoc_castSucc, sum_filter_le_succ, gap_snoc_last,
      Fin.castSucc_le_castSucc_iff, gap_snoc_castSucc, Fin.snoc_last]
    rw [← Finset.sum_filter]
    ext1
    · rfl
    · simp only
      abel

/-- Measurability of `(p, a) ↦ snoc p a`. -/
theorem measurable_snoc {α : Type*} [MeasurableSpace α] {n : ℕ} :
    Measurable fun q : (Fin n → α) × α => (Fin.snoc q.1 q.2 : Fin (n + 1) → α) := by
  refine measurable_pi_iff.2 fun j => ?_
  induction j using Fin.lastCases with
  | last => simpa only [Fin.snoc_last] using measurable_snd
  | cast i =>
    simp only [Fin.snoc_castSucc]
    exact (measurable_pi_apply i).comp measurable_fst

/-- **The last-vertex disintegration of `g_{n+1}^{T,x}`, lintegral form** (TeX 4276-4285): for
every measurable `f ≥ 0`,
`∫ f dg_{n+1}^{T,x} = ∫ ds 1_{0<s<T}(T-s) ∫ G_1(dv) ∫ f(z, (s, x-(T-s)v)) g_n^{s, x-(T-s)v}(dz)`.
Generic in `d`. -/
theorem lintegral_chainMeasureRaw_succ (n : ℕ) (T : ℝ) (x : Rd d)
    (f : (Fin (n + 1) → ℝ × Rd d) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z, f z ∂chainMeasureRaw d (n + 1) T x =
      ∫⁻ sl, lastW T sl * ∫⁻ vl, ∫⁻ z,
        f (Fin.snoc z (sl, x - (T - sl) • vl) : Fin (n + 1) → ℝ × Rd d)
          ∂chainMeasureRaw d n sl (x - (T - sl) • vl) ∂waveGreen d 1 := by
  set Ψ : ℝ → Rd d → (Fin n → ℝ) → (Fin n → Rd d) → ℝ≥0∞ := fun sl vl s' v' =>
    f (chainMap (n := n + 1) T x ((Fin.snoc s' sl : Fin (n + 1) → ℝ),
      (Fin.snoc v' vl : Fin (n + 1) → Rd d))) with hΨ
  have hFm : Measurable fun q : (Fin (n + 1) → ℝ) × (Fin (n + 1) → Rd d) => f (chainMap T x q) :=
    hf.comp (measurable_chainMap T x)
  have hΨm : Measurable fun p : ((ℝ × Rd d) × (Fin n → ℝ)) × (Fin n → Rd d) =>
      Ψ p.1.1.1 p.1.1.2 p.1.2 p.2 := by
    refine hFm.comp ?_
    exact (measurable_snoc.comp (measurable_fst.snd.prodMk measurable_fst.fst.fst)).prodMk
      (measurable_snoc.comp (measurable_snd.prodMk measurable_fst.fst.snd))
  have hin : ∀ sl vl, ∫⁻ z, f (Fin.snoc z (sl, x - (T - sl) • vl) : Fin (n + 1) → ℝ × Rd d)
        ∂chainMeasureRaw d n sl (x - (T - sl) • vl) =
      ∫⁻ s', chainWeightReal n sl s' *
        ∫⁻ v', Ψ sl vl s' v' ∂(Measure.pi fun _ : Fin n => waveGreen d 1) := by
    intro sl vl
    have hg : Measurable fun z : Fin n → ℝ × Rd d =>
        f (Fin.snoc z (sl, x - (T - sl) • vl) : Fin (n + 1) → ℝ × Rd d) :=
      hf.comp (measurable_snoc.comp (measurable_id.prodMk measurable_const))
    have hg2 : Measurable fun q : (Fin n → ℝ) × (Fin n → Rd d) =>
        f (Fin.snoc (chainMap sl (x - (T - sl) • vl) q) (sl, x - (T - sl) • vl) :
          Fin (n + 1) → ℝ × Rd d) := hg.comp (measurable_chainMap _ _)
    rw [chainMeasureRaw, lintegral_map hg (measurable_chainMap _ _),
      lintegral_prod _ hg2.aemeasurable, timeMeasure,
      lintegral_withDensity_eq_lintegral_mul _
        (measurable_chainWeightReal_right n sl) hg2.lintegral_prod_right']
    refine lintegral_congr fun s' => ?_
    simp only [Pi.mul_apply, hΨ, chainMap_snoc]
  simp_rw [hin]
  rw [chainMeasureRaw, lintegral_map hf (measurable_chainMap T x),
    lintegral_prod _ hFm.aemeasurable, timeMeasure,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_chainWeightReal_right (n + 1) T)
      hFm.lintegral_prod_right']
  simp only [Pi.mul_apply]
  have hmps := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure ℝ))
    (Fin.last n)
  have hmpv := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (waveGreen d 1))
    (Fin.last n)
  set es := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)
  set ev := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Rd d) (Fin.last n)
  have hes : ∀ p : ℝ × (Fin n → ℝ), es.symm p = (Fin.snoc p.2 p.1 : Fin (n + 1) → ℝ) := by
    intro p; simp [es, MeasurableEquiv.piFinSuccAbove_symm_apply]; rfl
  have hev : ∀ p : Rd d × (Fin n → Rd d),
      ev.symm p = (Fin.snoc p.2 p.1 : Fin (n + 1) → Rd d) := by
    intro p; simp [ev, MeasurableEquiv.piFinSuccAbove_symm_apply]; rfl
  have hv : ∀ s : Fin (n + 1) → ℝ,
      ∫⁻ v, f (chainMap T x (s, v)) ∂(Measure.pi fun _ : Fin (n + 1) => (waveGreen d 1)) =
        ∫⁻ vl, ∫⁻ v', f (chainMap T x (s, (Fin.snoc v' vl : Fin (n + 1) → Rd d)))
          ∂(Measure.pi fun _ : Fin n => waveGreen d 1) ∂(waveGreen d 1) := by
    intro s
    have hm : Measurable fun v => f (chainMap T x (s, v)) :=
      hFm.comp (measurable_const.prodMk measurable_id)
    calc ∫⁻ v, f (chainMap T x (s, v)) ∂(Measure.pi fun _ : Fin (n + 1) => (waveGreen d 1))
        = ∫⁻ v, (fun p => f (chainMap T x (s, ev.symm p))) (ev v)
            ∂(Measure.pi fun _ : Fin (n + 1) => (waveGreen d 1)) := by
          simp only [MeasurableEquiv.symm_apply_apply]
      _ = ∫⁻ p, f (chainMap T x (s, ev.symm p))
            ∂((waveGreen d 1).prod (Measure.pi fun _ : Fin n => waveGreen d 1)) :=
          hmpv.lintegral_comp_emb ev.measurableEmbedding
            (fun p => f (chainMap T x (s, ev.symm p)))
      _ = _ := by
          rw [lintegral_prod (fun p => f (chainMap T x (s, ev.symm p)))
            (hm.comp ev.symm.measurable).aemeasurable]
          simp only [hev]
  simp_rw [hv]
  have hHm : Measurable fun s : Fin (n + 1) → ℝ => chainWeightReal (n + 1) T s *
      ∫⁻ v, f (chainMap T x (s, v)) ∂(Measure.pi fun _ : Fin (n + 1) => (waveGreen d 1)) :=
    (measurable_chainWeightReal_right (n + 1) T).mul hFm.lintegral_prod_right'
  have hs : ∫⁻ s, chainWeightReal (n + 1) T s *
        ∫⁻ vl, ∫⁻ v', f (chainMap T x (s, (Fin.snoc v' vl : Fin (n + 1) → Rd d)))
          ∂(Measure.pi fun _ : Fin n => waveGreen d 1) ∂(waveGreen d 1) =
      ∫⁻ sl, ∫⁻ s', chainWeightReal (n + 1) T (Fin.snoc s' sl : Fin (n + 1) → ℝ) *
        ∫⁻ vl, ∫⁻ v', Ψ sl vl s' v' ∂(Measure.pi fun _ : Fin n => waveGreen d 1)
          ∂(waveGreen d 1) := by
    simp_rw [← hv]
    calc ∫⁻ s, chainWeightReal (n + 1) T s *
          ∫⁻ v, f (chainMap T x (s, v)) ∂(Measure.pi fun _ : Fin (n + 1) => (waveGreen d 1))
        = ∫⁻ s, (fun p => chainWeightReal (n + 1) T (es.symm p) *
            ∫⁻ v, f (chainMap T x (es.symm p, v))
              ∂(Measure.pi fun _ : Fin (n + 1) => (waveGreen d 1))) (es s)
            ∂(Measure.pi fun _ => volume) := by
          simp only [MeasurableEquiv.symm_apply_apply]; rfl
      _ = ∫⁻ p, chainWeightReal (n + 1) T (es.symm p) *
            ∫⁻ v, f (chainMap T x (es.symm p, v))
              ∂(Measure.pi fun _ : Fin (n + 1) => (waveGreen d 1))
            ∂((volume : Measure ℝ).prod (Measure.pi fun _ : Fin n => volume)) :=
          hmps.lintegral_comp_emb es.measurableEmbedding
            (fun p => chainWeightReal (n + 1) T (es.symm p) *
              ∫⁻ v, f (chainMap T x (es.symm p, v))
                ∂(Measure.pi fun _ : Fin (n + 1) => (waveGreen d 1)))
      _ = _ := by
          rw [lintegral_prod (fun p => chainWeightReal (n + 1) T (es.symm p) *
            ∫⁻ v, f (chainMap T x (es.symm p, v))
              ∂(Measure.pi fun _ : Fin (n + 1) => (waveGreen d 1)))
            (hHm.comp es.symm.measurable).aemeasurable]
          simp only [hes, hv]
          rfl
  rw [hs]
  refine lintegral_congr fun sl => ?_
  have hΨ3 : Measurable fun q : (Fin n → ℝ) × Rd d =>
      ∫⁻ v', Ψ sl q.2 q.1 v' ∂(Measure.pi fun _ : Fin n => waveGreen d 1) := by
    have : Measurable fun p : ((Fin n → ℝ) × Rd d) × (Fin n → Rd d) => Ψ sl p.1.2 p.1.1 p.2 :=
      hΨm.comp (((measurable_const.prodMk measurable_fst.snd).prodMk measurable_fst.fst).prodMk
        measurable_snd)
    exact this.lintegral_prod_right'
  have hcw : Measurable fun s' : Fin n → ℝ => chainWeightReal n sl s' :=
    measurable_chainWeightReal_right n sl
  simp only [chainWeightReal_snoc, mul_assoc]
  have hA : Measurable fun s' => ∫⁻ vl, ∫⁻ v', Ψ sl vl s' v'
      ∂(Measure.pi fun _ : Fin n => waveGreen d 1) ∂(waveGreen d 1) := hΨ3.lintegral_prod_right'
  have hcwA : Measurable fun s' => chainWeightReal n sl s' *
      ∫⁻ vl, ∫⁻ v', Ψ sl vl s' v' ∂(Measure.pi fun _ : Fin n => waveGreen d 1)
        ∂(waveGreen d 1) :=
    hcw.mul hA
  rw [lintegral_const_mul _ hcwA]
  congr 1
  have hB : ∀ s', Measurable fun vl =>
      ∫⁻ v', Ψ sl vl s' v' ∂(Measure.pi fun _ : Fin n => waveGreen d 1) :=
    fun s' => hΨ3.comp (measurable_const.prodMk measurable_id)
  simp_rw [← lintegral_const_mul _ (hB _)]
  have hsw : Measurable fun q : (Fin n → ℝ) × Rd d => chainWeightReal n sl q.1 *
      ∫⁻ v', Ψ sl q.2 q.1 v' ∂(Measure.pi fun _ : Fin n => waveGreen d 1) :=
    (hcw.comp measurable_fst).mul hΨ3
  exact lintegral_lintegral_swap hsw.aemeasurable

/-- The inner factor of the disintegration is s-finite (named). -/
instance instSFiniteChainInner (n : ℕ) :
    SFinite ((volume : Measure (Fin n → ℝ)).prod (Measure.pi fun _ : Fin n => waveGreen d 1)) := by
  have : SigmaFinite (volume : Measure (Fin n → ℝ)) := MeasureTheory.Measure.pi.sigmaFinite _
  have : SigmaFinite (Measure.pi fun _ : Fin n => waveGreen d 1) :=
    MeasureTheory.Measure.pi.sigmaFinite _
  infer_instance

/-- The parameter space of the last-vertex decomposition: `((s_l, v_l), (s', v'))`. -/
abbrev Q (d n : ℕ) := (ℝ × Rd d) × ((Fin n → ℝ) × (Fin n → Rd d))

/-- The chain built from the last vertex and the earlier chain. -/
def Φ (T : ℝ) (x : Rd d) {n : ℕ} (q : Q d n) : Fin (n + 1) → ℝ × Rd d :=
  chainMap (n := n + 1) T x ((Fin.snoc q.2.1 q.1.1 : Fin (n + 1) → ℝ),
    (Fin.snoc q.2.2 q.1.2 : Fin (n + 1) → Rd d))

theorem measurable_Φ (T : ℝ) (x : Rd d) (n : ℕ) : Measurable (Φ (n := n) T x) :=
  (measurable_chainMap T x).comp ((measurable_snoc.comp (measurable_snd.fst.prodMk
    measurable_fst.fst)).prodMk (measurable_snoc.comp (measurable_snd.snd.prodMk
      measurable_fst.snd)))

/-- The density of the disintegrated measure. -/
def ρ (T : ℝ) {n : ℕ} (q : Q d n) : ℝ≥0∞ := lastW T q.1.1 * chainWeightReal n q.1.1 q.2.1

theorem measurable_ρ (T : ℝ) (n : ℕ) : Measurable (ρ (d := d) (n := n) T) :=
  ((measurable_lastW T).comp measurable_fst.fst).mul
    ((measurable_chainWeightReal n).comp (measurable_fst.fst.prodMk measurable_snd.fst))

/-- The disintegrated measure on `Q`. -/
def Mq (d n : ℕ) (T : ℝ) : Measure (Q d n) :=
  (((volume : Measure ℝ).prod (waveGreen d 1)).prod
    ((volume : Measure (Fin n → ℝ)).prod (Measure.pi fun _ : Fin n => waveGreen d 1))).withDensity
    (ρ T)

/-- Inner step: integrating the earlier chain at a fixed last vertex (lintegral). -/
theorem lintegral_inner (n : ℕ) (T : ℝ) (x : Rd d) (sl : ℝ) (vl : Rd d)
    (f : (Fin (n + 1) → ℝ × Rd d) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ q, chainWeightReal n sl q.1 * f (Φ T x ((sl, vl), q))
        ∂((volume : Measure (Fin n → ℝ)).prod (Measure.pi fun _ : Fin n => waveGreen d 1)) =
      ∫⁻ z, f (Fin.snoc z (sl, x - (T - sl) • vl) : Fin (n + 1) → ℝ × Rd d)
        ∂chainMeasureRaw d n sl (x - (T - sl) • vl) := by
  have hg : Measurable fun z : Fin n → ℝ × Rd d =>
      f (Fin.snoc z (sl, x - (T - sl) • vl) : Fin (n + 1) → ℝ × Rd d) :=
    hf.comp (measurable_snoc.comp (measurable_id.prodMk measurable_const))
  have hg2 : Measurable fun q : (Fin n → ℝ) × (Fin n → Rd d) =>
      f (Fin.snoc (chainMap sl (x - (T - sl) • vl) q) (sl, x - (T - sl) • vl) :
        Fin (n + 1) → ℝ × Rd d) := hg.comp (measurable_chainMap _ _)
  have hcw1 : Measurable fun q : (Fin n → ℝ) × (Fin n → Rd d) => chainWeightReal n sl q.1 :=
    (measurable_chainWeightReal_right n sl).comp measurable_fst
  rw [chainMeasureRaw, lintegral_map hg (measurable_chainMap _ _), timeMeasure,
    prod_withDensity_left (measurable_chainWeightReal_right n sl),
    lintegral_withDensity_eq_lintegral_mul _ hcw1 hg2]
  refine lintegral_congr fun q => ?_
  simp only [Pi.mul_apply, Φ, chainMap_snoc]

/-- **The measure-level last-vertex recursion** (TeX 4276-4285):
`g_{n+1}^{T,x} = Φ_* (ρ · (Leb ⊗ G_1) ⊗ (Leb^n ⊗ G_1^n))`. -/
theorem chainMeasureRaw_succ_eq (n : ℕ) (T : ℝ) (x : Rd d) :
    chainMeasureRaw d (n + 1) T x = (Mq d n T).map (Φ T x) := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  have hfΦ : Measurable fun q : Q d n => f (Φ T x q) := hf.comp (measurable_Φ T x n)
  rw [lintegral_chainMeasureRaw_succ n T x f hf, lintegral_map hf (measurable_Φ T x n), Mq,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_ρ T n) hfΦ,
    lintegral_prod _ ((measurable_ρ T n).mul hfΦ).aemeasurable,
    lintegral_prod _ ?_]
  · refine lintegral_congr fun sl => ?_
    rw [← lintegral_const_mul' _ _ (lastW_ne_top T sl)]
    refine lintegral_congr fun vl => ?_
    rw [← lintegral_inner n T x sl vl f hf, ← lintegral_const_mul' _ _ (lastW_ne_top T sl)]
    refine lintegral_congr fun q => ?_
    simp only [Pi.mul_apply, ρ, mul_assoc]
  · exact (((measurable_ρ T n).mul hfΦ).lintegral_prod_right').aemeasurable

/-- The inner Bochner integral of the disintegration at a fixed last vertex. -/
theorem integral_inner_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (n : ℕ) (T : ℝ) (x : Rd d) (F : (Fin (n + 1) → ℝ × Rd d) → E)
    (hF : StronglyMeasurable F) (sl : ℝ) (vl : Rd d) :
    ∫ q, (ρ T ((sl, vl), q)).toReal • F (Φ T x ((sl, vl), q))
        ∂((volume : Measure (Fin n → ℝ)).prod (Measure.pi fun _ : Fin n => waveGreen d 1)) =
      (lastW T sl).toReal • ∫ z, F (Fin.snoc z (sl, x - (T - sl) • vl) :
          Fin (n + 1) → ℝ × Rd d) ∂chainMeasureRaw d n sl (x - (T - sl) • vl) := by
  simp only [ρ, ENNReal.toReal_mul, mul_smul]
  rw [integral_smul]
  congr 1
  have hg : StronglyMeasurable fun z : Fin n → ℝ × Rd d =>
      F (Fin.snoc z (sl, x - (T - sl) • vl) : Fin (n + 1) → ℝ × Rd d) :=
    hF.comp_measurable (measurable_snoc.comp (measurable_id.prodMk measurable_const))
  have hcw := measurable_chainWeightReal_right n sl
  rw [chainMeasureRaw, integral_map (measurable_chainMap _ _).aemeasurable
      hg.aestronglyMeasurable, timeMeasure,
    prod_withDensity_left hcw,
    integral_withDensity_eq_integral_toReal_smul
      (f := fun z : (Fin n → ℝ) × (Fin n → Rd d) => chainWeightReal n sl z.1)
      (hcw.comp measurable_fst)
      (Filter.Eventually.of_forall fun q => (chainWeightReal_ne_top _ _ _).lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  simp only [Φ, chainMap_snoc]

/-- **The last-vertex disintegration, Bochner form**: for strongly measurable `F` integrable
against `g_{n+1}^{T,x}`, the outer function is integrable and
`∫ F dg_{n+1}^{T,x} = ∫∫ ds G_1(dv) 1_{0<s<T}(T-s) ∫ F(z,(s, x-(T-s)v)) g_n^{s,x-(T-s)v}(dz)`. -/
theorem integral_chainMeasureRaw_succ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (n : ℕ) (T : ℝ) (x : Rd d) (F : (Fin (n + 1) → ℝ × Rd d) → E)
    (hF : StronglyMeasurable F) (hi : Integrable F (chainMeasureRaw d (n + 1) T x)) :
    Integrable (fun p : ℝ × Rd d => (lastW T p.1).toReal • ∫ z, F (Fin.snoc z
        (p.1, x - (T - p.1) • p.2) : Fin (n + 1) → ℝ × Rd d)
          ∂chainMeasureRaw d n p.1 (x - (T - p.1) • p.2))
        ((volume : Measure ℝ).prod (waveGreen d 1)) ∧
    ∫ z, F z ∂chainMeasureRaw d (n + 1) T x =
      ∫ p, (lastW T p.1).toReal • ∫ z, F (Fin.snoc z (p.1, x - (T - p.1) • p.2) :
          Fin (n + 1) → ℝ × Rd d) ∂chainMeasureRaw d n p.1 (x - (T - p.1) • p.2)
        ∂((volume : Measure ℝ).prod (waveGreen d 1)) := by
  have hρt : ∀ᵐ q ∂(((volume : Measure ℝ).prod (waveGreen d 1)).prod
      ((volume : Measure (Fin n → ℝ)).prod (Measure.pi fun _ : Fin n => waveGreen d 1))),
      ρ T q < ∞ := Filter.Eventually.of_forall fun q =>
    (ENNReal.mul_ne_top (lastW_ne_top _ _) (chainWeightReal_ne_top _ _ _)).lt_top
  rw [chainMeasureRaw_succ_eq] at hi ⊢
  rw [integrable_map_measure hF.aestronglyMeasurable (measurable_Φ T x n).aemeasurable, Mq,
    integrable_withDensity_iff_integrable_smul' (measurable_ρ T n) hρt] at hi
  simp only [Function.comp_apply] at hi
  have heq : (fun p : ℝ × Rd d => ∫ q, (ρ T (p, q)).toReal • F (Φ T x (p, q))
      ∂((volume : Measure (Fin n → ℝ)).prod (Measure.pi fun _ : Fin n => waveGreen d 1))) =
      fun p => (lastW T p.1).toReal • ∫ z, F (Fin.snoc z (p.1, x - (T - p.1) • p.2) :
          Fin (n + 1) → ℝ × Rd d) ∂chainMeasureRaw d n p.1 (x - (T - p.1) • p.2) := by
    funext p
    obtain ⟨sl, vl⟩ := p
    exact integral_inner_eq n T x F hF sl vl
  refine ⟨?_, ?_⟩
  · rw [← heq]
    exact hi.integral_prod_left
  · rw [integral_map (measurable_Φ T x n).aemeasurable hF.aestronglyMeasurable, Mq,
      integral_withDensity_eq_integral_toReal_smul (measurable_ρ T n) hρt,
      integral_prod (fun q : Q d n => (ρ T q).toReal • F (Φ T x q)) hi, heq]

/-- `g_0^{T,x}` is the unit mass on the empty tuple, for every `T`. -/
theorem chainMeasureRaw_zero (T : ℝ) (x : Rd d) :
    chainMeasureRaw d 0 T x = Measure.dirac default := by
  have hmass : chainMeasureRaw d 0 T x univ = 1 := by
    rw [chainMeasureRaw_univ_eq]
    simp [TerminalWick.chainMassReal, chainWeightReal, MeasureTheory.volume_pi]
  ext S hS
  rcases Set.Subsingleton.eq_empty_or_singleton (Set.subsingleton_of_subsingleton (s := S))
    with h | ⟨a, h⟩
  · subst h; simp
  · rw [h, Measure.dirac_apply' _ (measurableSet_singleton a), Subsingleton.elim a default,
      Set.indicator_of_mem (mem_singleton _), Pi.one_apply,
      show ({default} : Set (Fin 0 → ℝ × Rd d)) = univ from Set.eq_univ_of_forall
        fun z => Subsingleton.elim z default, hmass]

/-- Almost every chain of `g_n^{T,x}` has its times in `(0, T)`. -/
theorem ae_chainMeasureRaw_times (n : ℕ) (T : ℝ) (x : Rd d) :
    ∀ᵐ z ∂chainMeasureRaw d n T x, ∀ j, 0 < (z j).1 ∧ (z j).1 < T := by
  have hset : MeasurableSet {z : Fin n → ℝ × Rd d | ∀ j, 0 < (z j).1 ∧ (z j).1 < T} := by
    have he : {z : Fin n → ℝ × Rd d | ∀ j, 0 < (z j).1 ∧ (z j).1 < T} =
        ⋂ j, ({z : Fin n → ℝ × Rd d | 0 < (z j).1} ∩ {z | (z j).1 < T}) := by
      ext z; simp
    rw [he]
    exact MeasurableSet.iInter fun j =>
      (measurableSet_lt measurable_const (measurable_fst.comp (measurable_pi_apply j))).inter
        (measurableSet_lt (measurable_fst.comp (measurable_pi_apply j)) measurable_const)
  rw [chainMeasureRaw, ae_map_iff (measurable_chainMap T x).aemeasurable hset]
  have hT : ∀ᵐ s ∂timeMeasure n T, OpenSimplex T s := by
    rw [timeMeasure, ae_withDensity_iff (measurable_chainWeightReal_right n T)]
    refine Filter.Eventually.of_forall fun s hs => ?_
    classical
    rw [TerminalWickInputs.chainWeightReal_eq_ite] at hs
    by_contra h
    exact hs (ite_eq_right h)
  have hs : SFinite (timeMeasure n T) := by unfold timeMeasure; infer_instance
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hT] with q hq j
  exact ⟨hq.1 j, lt_of_openSimplex hq j⟩

end Chain

/-! ### The mild measure as an image of `1_{0<s<t}(t-s) ds ⊗ G_1(dv)` -/

section Mild

/-- The map `(s, v) ↦ (s, x - (t - s) v)`, modified on the null line `s = t` to a bijection. -/
def mildMap (t : ℝ) (x : Rd d) (p : ℝ × Rd d) : ℝ × Rd d :=
  if p.1 = t then (p.1, x + p.2) else (p.1, x - (t - p.1) • p.2)

/-- The inverse of `mildMap`. -/
def mildMapInv (t : ℝ) (x : Rd d) (p : ℝ × Rd d) : ℝ × Rd d :=
  if p.1 = t then (p.1, p.2 - x) else (p.1, (t - p.1)⁻¹ • (x - p.2))

theorem measurable_mildMap (t : ℝ) (x : Rd d) : Measurable (mildMap t x) := by
  unfold mildMap
  refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const) ?_ ?_
  · exact measurable_fst.prodMk (measurable_const.add measurable_snd)
  · exact measurable_fst.prodMk (measurable_const.sub
      ((measurable_const.sub measurable_fst).smul measurable_snd))

theorem measurable_mildMapInv (t : ℝ) (x : Rd d) : Measurable (mildMapInv t x) := by
  unfold mildMapInv
  refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const) ?_ ?_
  · exact measurable_fst.prodMk (measurable_snd.sub measurable_const)
  · exact measurable_fst.prodMk (((measurable_const.sub measurable_fst).inv).smul
      (measurable_const.sub measurable_snd))

/-- `mildMap` as a measurable equivalence of `ℝ × ℝ^d`. -/
def mildEquiv (t : ℝ) (x : Rd d) : (ℝ × Rd d) ≃ᵐ (ℝ × Rd d) where
  toFun := mildMap t x
  invFun := mildMapInv t x
  left_inv p := by
    obtain ⟨s, v⟩ := p
    by_cases hs : s = t
    · simp [mildMap, mildMapInv, hs]
    · have hts : t - s ≠ 0 := sub_ne_zero.2 (Ne.symm hs)
      simp [mildMap, mildMapInv, hs, smul_smul, inv_mul_cancel₀ hts]
  right_inv p := by
    obtain ⟨s, y⟩ := p
    by_cases hs : s = t
    · simp [mildMap, mildMapInv, hs]
    · have hts : t - s ≠ 0 := sub_ne_zero.2 (Ne.symm hs)
      simp [mildMap, mildMapInv, hs, smul_smul, mul_inv_cancel₀ hts]
  measurable_toFun := measurable_mildMap t x
  measurable_invFun := measurable_mildMapInv t x

theorem mildEquiv_apply (t : ℝ) (x : Rd d) (p : ℝ × Rd d) : mildEquiv t x p = mildMap t x p :=
  rfl

theorem mildMap_of_ne {t : ℝ} (x : Rd d) {p : ℝ × Rd d} (h : p.1 ≠ t) :
    mildMap t x p = (p.1, x - (t - p.1) • p.2) := by
  simp [mildMap, h]

/-- The base measure `1_{0<s<t}(t-s) ds ⊗ G_1(dv)` of the mild measure. -/
def mildBase (d : ℕ) (t : ℝ) : Measure (ℝ × Rd d) :=
  ((volume : Measure ℝ).prod (waveGreen d 1)).withDensity fun p => lastW t p.1

theorem measurable_lastW_fst (t : ℝ) : Measurable fun p : ℝ × Rd d => lastW t p.1 :=
  (measurable_lastW t).comp measurable_fst

/-- **The mild measure** (TeX 2241-2242 with 4276-4285 at `n = 1`): `g_1^{t,x}` read on
`ℝ × ℝ^d` is the image of `1_{0<s<t}(t-s) ds ⊗ G_1(dv)` under `(s, v) ↦ (s, x - (t-s) v)`. -/
theorem mildMeasure_eq (t : ℝ) (ht : 0 ≤ t) (x : Rd d) :
    mildMeasure d t ht x = (mildBase d t).map (mildEquiv t x) := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  have hmp : Measurable (mildPt (d := d) (t := t)) := by
    unfold mildPt
    exact ((measurable_subtype_coe.comp measurable_fst).comp (measurable_pi_apply 0)).prodMk
      (measurable_snd.comp (measurable_pi_apply 0))
  rw [mildMeasure, lintegral_map hf hmp, chainMeasure,
    lintegral_map (f := fun z => f (mildPt z)) (hf.comp hmp) (measurable_toPt ht),
    lintegral_chainMeasureRaw_succ 0 t x (fun z => f (mildPt (toPt ht z)))
      ((hf.comp hmp).comp (measurable_toPt ht)),
    lintegral_map hf (mildEquiv t x).measurable, mildBase,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_lastW_fst t)
      (g := fun p => f (mildEquiv t x p)) (hf.comp (mildEquiv t x).measurable)]
  symm
  refine (lintegral_prod _ ((measurable_lastW_fst t).mul
    (hf.comp (mildEquiv t x).measurable)).aemeasurable).trans ?_
  symm
  refine lintegral_congr fun sl => ?_
  simp only [Pi.mul_apply, Function.comp_apply]
  rw [← lintegral_const_mul' _ _ (lastW_ne_top t sl)]
  refine lintegral_congr fun vl => ?_
  rw [chainMeasureRaw_zero, lintegral_dirac]
  by_cases h : lastW t sl = 0
  · rw [h, zero_mul, zero_mul]
  · have hs := mem_of_lastW_ne_zero h
    congr 1
    rw [mildEquiv_apply, mildMap_of_ne x (show (sl, vl).1 ≠ t from hs.2.ne)]
    have h0 : ∀ (z : Fin 0 → ℝ × Rd d) (q : ℝ × Rd d), (Fin.snoc z q : Fin 1 → ℝ × Rd d) 0 = q :=
      fun z q => Fin.snoc_last (α := fun _ => ℝ × Rd d) (n := 0) q z
    have hmem : sl ∈ Set.Icc (0 : ℝ) t := ⟨hs.1.le, hs.2.le⟩
    simp only [mildPt, toPt, h0, Set.projIcc_of_mem ht hmem]

/-- The mild measure is finite. -/
theorem isFiniteMeasure_mildMeasure (t : ℝ) (ht : 0 ≤ t) (x : Rd d) :
    IsFiniteMeasure (mildMeasure d t ht x) := by
  unfold mildMeasure; infer_instance

/-- Almost every point of the mild measure has its time in `(0, t)`. -/
theorem ae_mildMeasure (t : ℝ) (ht : 0 ≤ t) (x : Rd d) :
    ∀ᵐ p ∂mildMeasure d t ht x, 0 < p.1 ∧ p.1 < t := by
  have hS : MeasurableSet {p : ℝ × Rd d | 0 < p.1 ∧ p.1 < t} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst measurable_const)
  rw [mildMeasure_eq, ae_map_iff (mildEquiv t x).measurable.aemeasurable hS, mildBase,
    ae_withDensity_iff (measurable_lastW_fst t)]
  refine Filter.Eventually.of_forall fun p hp => ?_
  have hs := mem_of_lastW_ne_zero hp
  rw [mildEquiv_apply, mildMap_of_ne x hs.2.ne]
  exact hs

/-- Integrability against the mild measure, as an integrability against the base measure. -/
theorem integrable_mildMeasure_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (t : ℝ)
    (ht : 0 ≤ t) (x : Rd d) (f : ℝ × Rd d → E) :
    Integrable f (mildMeasure d t ht x) ↔
      Integrable (fun p => (lastW t p.1).toReal • f (mildEquiv t x p))
        ((volume : Measure ℝ).prod (waveGreen d 1)) := by
  rw [mildMeasure_eq, integrable_map_equiv, mildBase,
    integrable_withDensity_iff_integrable_smul' (measurable_lastW_fst t)
      (Filter.Eventually.of_forall fun p => (lastW_ne_top _ _).lt_top)]
  rfl

/-- The mild integral as an integral against the base measure. -/
theorem integral_mildMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : ℝ) (ht : 0 ≤ t) (x : Rd d) (f : ℝ × Rd d → E) :
    ∫ p, f p ∂mildMeasure d t ht x =
      ∫ p, (lastW t p.1).toReal • f (mildEquiv t x p)
        ∂((volume : Measure ℝ).prod (waveGreen d 1)) := by
  rw [mildMeasure_eq, integral_map_equiv, mildBase,
    integral_withDensity_eq_integral_toReal_smul (measurable_lastW_fst t)
      (Filter.Eventually.of_forall fun p => (lastW_ne_top _ _).lt_top)]

end Mild

/-! ### Multiplication by a fixed `L²` class commutes with Bochner integration -/

section MulIntegral

variable {Z : Type*} [MeasurableSpace Z] {ν : Measure Z} {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} [IsFiniteMeasure P]

omit [IsFiniteMeasure P] in
/-- `⟪1_S H, f⟫ = ∫_S H f` for a bounded `1_S H`. -/
theorem inner_indicator_eq (H : Ω → ℝ) {S : Set Ω} (hS : MeasurableSet S)
    (hφ : MemLp (S.indicator H) 2 P) (f : Lp ℝ 2 P) :
    inner ℝ (hφ.toLp _) f = ∫ ω in S, H ω * f ω ∂P := by
  rw [← integral_indicator hS, ← UniformSeriesTail.integral_mul_eq_inner]
  refine integral_congr_ae ?_
  filter_upwards [hφ.coeFn_toLp] with ω hω
  rw [hω, Set.indicator_mul_left]

/-- **Multiplication commutes with the integral** (the TeX's "terminal-kernel Fubini" for one
extra factor, 2257-2260): if `G z = H · F z` a.e. for every `z`, with `F` and `G` Bochner
integrable in `L²`, then `H · ∫ F = ∫ G` a.e.  Route: test both sides against the bounded
functions `1_A 1_{|H| ≤ N} H` and `1_A 1_{|H| ≤ N}` (`integral_inner`), then
`ae_eq_of_forall_setIntegral_eq_of_sigmaFinite` on `{|H| ≤ N}`. -/
theorem ae_mul_integral_eq (H : Lp ℝ 2 P) {F G : Z → Lp ℝ 2 P} (hF : Integrable F ν)
    (hG : Integrable G ν) (hFG : ∀ z, (G z : Ω → ℝ) =ᵐ[P] fun ω => H ω * F z ω) :
    (fun ω => H ω * (∫ z, F z ∂ν : Lp ℝ 2 P) ω) =ᵐ[P] (∫ z, G z ∂ν : Lp ℝ 2 P) := by
  set Fi : Lp ℝ 2 P := ∫ z, F z ∂ν with hFi
  set Gi : Lp ℝ 2 P := ∫ z, G z ∂ν with hGi
  have hHm : StronglyMeasurable (H : Ω → ℝ) := Lp.stronglyMeasurable H
  have hFi1 : Integrable (Fi : Ω → ℝ) P := (Lp.memLp Fi).integrable one_le_two
  have hGi1 : Integrable (Gi : Ω → ℝ) P := (Lp.memLp Gi).integrable one_le_two
  have key : ∀ N : ℕ, ∀ᵐ ω ∂P, |(H : Ω → ℝ) ω| ≤ N → H ω * Fi ω = Gi ω := by
    intro N
    set B : Set Ω := {ω | |(H : Ω → ℝ) ω| ≤ N} with hBdef
    have hB : MeasurableSet B :=
      measurableSet_le hHm.measurable.abs measurable_const
    have hsets : ∀ A : Set Ω, MeasurableSet A →
        ∫ ω in A ∩ B, H ω * Fi ω ∂P = ∫ ω in A ∩ B, Gi ω ∂P := by
      intro A hA
      have hS : MeasurableSet (A ∩ B) := hA.inter hB
      have hφ : MemLp ((A ∩ B).indicator (H : Ω → ℝ)) 2 P := by
        refine MemLp.of_bound (hHm.indicator hS).aestronglyMeasurable N
          (Filter.Eventually.of_forall fun ω => ?_)
        by_cases hω : ω ∈ A ∩ B
        · rw [Set.indicator_of_mem hω, Real.norm_eq_abs]; exact hω.2
        · rw [Set.indicator_of_notMem hω, norm_zero]; exact Nat.cast_nonneg N
      have hψ : MemLp ((A ∩ B).indicator (fun _ => (1 : ℝ))) 2 P := by
        refine MemLp.of_bound ((stronglyMeasurable_const).indicator hS).aestronglyMeasurable 1
          (Filter.Eventually.of_forall fun ω => ?_)
        by_cases hω : ω ∈ A ∩ B
        · rw [Set.indicator_of_mem hω, norm_one]
        · rw [Set.indicator_of_notMem hω, norm_zero]; exact zero_le_one
      have hz : ∀ z, ∫ ω in A ∩ B, H ω * F z ω ∂P = ∫ ω in A ∩ B, 1 * G z ω ∂P := by
        intro z
        refine integral_congr_ae (ae_restrict_of_ae ?_)
        filter_upwards [hFG z] with ω hω
        rw [hω, one_mul]
      calc ∫ ω in A ∩ B, H ω * Fi ω ∂P = inner ℝ (hφ.toLp _) Fi :=
            (inner_indicator_eq _ hS hφ Fi).symm
        _ = ∫ z, inner ℝ (hφ.toLp _) (F z) ∂ν := (integral_inner hF _).symm
        _ = ∫ z, inner ℝ (hψ.toLp _) (G z) ∂ν := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
            simp only
            rw [inner_indicator_eq _ hS hφ, inner_indicator_eq _ hS hψ, hz]
        _ = inner ℝ (hψ.toLp _) Gi := integral_inner hG _
        _ = ∫ ω in A ∩ B, 1 * Gi ω ∂P := inner_indicator_eq _ hS hψ Gi
        _ = ∫ ω in A ∩ B, Gi ω ∂P := by simp only [one_mul]
    have hint : Integrable (fun ω => H ω * Fi ω) (P.restrict B) := by
      refine Integrable.mono' (hFi1.restrict.norm.const_mul N)
        ((hHm.aestronglyMeasurable.mul (Lp.stronglyMeasurable Fi).aestronglyMeasurable).restrict)
        ?_
      filter_upwards [ae_restrict_mem hB] with ω hω
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hω (norm_nonneg _)
    have hfin : (fun ω => H ω * Fi ω) =ᵐ[P.restrict B] fun ω => Gi ω := by
      refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
        (fun s _ _ => hint.integrableOn) (fun s _ _ => hGi1.restrict.integrableOn) ?_
      intro s hs _
      rw [Measure.restrict_restrict hs]
      exact hsets s hs
    exact (ae_restrict_iff' hB).1 hfin
  filter_upwards [ae_all_iff.2 key] with ω hω
  obtain ⟨N, hN⟩ := exists_nat_ge |(H : Ω → ℝ) ω|
  exact hω N hN

end MulIntegral

/-! ### The terminal product -/

section Product

variable {X : Type*} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : X → Ω → ℝ}
  {K : X → X → ℝ}

/-- `∏_{j ≤ m} W(snoc z p)_j = W(p) ∏_{j < m} W(z_j)` a.s. -/
theorem coeFn_prodL2_snoc (hW : CenteredGaussianField W K P) {m : ℕ} (z : Fin m → X) (p : X) :
    (prodL2 hW (Fin.snoc z p : Fin (m + 1) → X) : Ω → ℝ) =ᵐ[P]
      fun ω => fieldL2 hW p ω * prodL2 hW z ω := by
  filter_upwards [TerminalWick.coeFn_prodL2 hW (Fin.snoc z p : Fin (m + 1) → X),
    TerminalWick.coeFn_prodL2 hW ![p], TerminalWick.coeFn_prodL2 hW z] with ω h1 h2 h3
  rw [h1, fieldL2, h2, h3, Fin.prod_univ_castSucc]
  simp [mul_comm]

end Product

/-! ### `TerminalFubiniTarget` (TeX 2257-2260 with 4276-4285) -/

section Target

variable {α₀ : ℝ} {Γ : Measure (Rd d)} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : SrcPt d → Ω → ℝ}

/-- Attaching the widths `snoc b a` to the chain `snoc z q`. -/
theorem attach_snoc {t : ℝ} {m : ℕ} (b : Fin m → PosW) (a : PosW) (z : Fin m → Pt d t)
    (q : Pt d t) :
    attach (Fin.snoc b a : Fin (m + 1) → PosW) (Fin.snoc z q : Fin (m + 1) → Pt d t) =
      (Fin.snoc (attach b z) ((⟨(q.1 : ℝ), q.1.2.1⟩, q.2), a) : Fin (m + 1) → SrcPt d) := by
  funext j
  induction j using Fin.lastCases with
  | last => simp [attach]
  | cast i => simp [attach]

/-- The terminal point `(s, y)` of `Pt d s`. -/
def termPt {s : ℝ} (hs : 0 ≤ s) (y : Rd d) : Pt d s := (⟨s, hs, le_rfl⟩, y)

/-- On chains with times in `[0, s]`, `s ≤ t`, the clamping into `[0,t]` of `snoc z (s, y)` and
the clamping of `z` into `[0, s]` followed by the terminal point give the same source points. -/
theorem attach_toPt_snoc {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s ≤ t) {m : ℕ}
    (c : Fin (m + 1) → PosW) (z : Fin m → ℝ × Rd d) (y : Rd d)
    (hz : ∀ j, 0 ≤ (z j).1 ∧ (z j).1 ≤ s) :
    attach c (toPt ht (Fin.snoc z (s, y) : Fin (m + 1) → ℝ × Rd d)) =
      attach c (Fin.snoc (toPt hs z) (termPt hs y) : Fin (m + 1) → Pt d s) := by
  funext j
  induction j using Fin.lastCases with
  | last =>
    refine Prod.ext (Prod.ext (Subtype.ext ?_) ?_) rfl
    · simp [attach, toPt, termPt, Set.projIcc_of_mem ht ⟨hs, hst⟩]
    · simp [attach, toPt, termPt]
  | cast i =>
    refine Prod.ext (Prod.ext (Subtype.ext ?_) ?_) rfl
    · simp [attach, toPt, Set.projIcc_of_mem ht ⟨(hz i).1, (hz i).2.trans hst⟩,
        Set.projIcc_of_mem hs (hz i)]
    · simp [attach, toPt]

variable (hc : ∀ w w' : PosW, Continuous fun pq : (↥(Ici (0 : ℝ)) × Rd d) ×
  (↥(Ici (0 : ℝ)) × Rd d) => srcCov α₀ Γ (pq.1, w) (pq.2, w'))
include hc

/-- The extended products are continuous along the inner chain. -/
theorem continuous_snoc_prodL2 (hW : SourceField α₀ Γ P W) {s : ℝ} (hs : 0 ≤ s) (y : Rd d)
    {m : ℕ} (b : Fin m → PosW) (a : PosW) :
    Continuous fun z : Fin m → Pt d s => prodL2 hW (attach (Fin.snoc b a : Fin (m + 1) → PosW)
      (Fin.snoc z (termPt hs y) : Fin (m + 1) → Pt d s)) :=
  (SourceWick.continuous_prodL2_attach hW hc (Fin.snoc b a : Fin (m + 1) → PosW)).comp
    (f := fun z : Fin m → Pt d s => (Fin.snoc z (termPt hs y) : Fin (m + 1) → Pt d s))
    (continuous_pi fun j => by
      induction j using Fin.lastCases with
      | last => simpa only [Fin.snoc_last] using continuous_const
      | cast i => simpa only [Fin.snoc_castSucc] using continuous_apply i)

/-- The extended products are Bochner integrable along the inner chain. -/
theorem integrable_snoc (hW : SourceField α₀ Γ P W) {s : ℝ} (hs : 0 ≤ s) (y : Rd d) {m : ℕ}
    (b : Fin m → PosW) (a : PosW) :
    Integrable (fun z : Fin m → Pt d s => prodL2 hW (attach (Fin.snoc b a : Fin (m + 1) → PosW)
      (Fin.snoc z (termPt hs y) : Fin (m + 1) → Pt d s))) (chainMeasure d m s hs y) := by
  have hcont := continuous_snoc_prodL2 hc hW hs y b a
  exact Integrable.of_bound hcont.aestronglyMeasurable _
    (Filter.Eventually.of_forall fun z => SourceWick.norm_prodL2_attach_le hW _ _)

/-- **One extra terminal factor** (TeX 2257-2260): for `s ≥ 0`,
`W(s, y, a) · Y_m^b(s, y) = ∫ ∏_{j ≤ m} W(z_j, (b,a)_j) g_m^{s,y}(dz)` with `z_m = (s, y)`; the
product is in `L²` and `mulL2` is that integral. -/
theorem mul_Ya_eq (hW : SourceField α₀ Γ P W) [IsFiniteMeasure P] {s : ℝ} (hs : 0 ≤ s)
    (y : Rd d) {m : ℕ} (b : Fin m → PosW) (a : PosW) :
    MemLp (fun ω => fieldL2 hW ((⟨s, hs⟩, y), a) ω * Ya hW s hs y b ω) 2 P ∧
      mulL2 (fieldL2 hW ((⟨s, hs⟩, y), a)) (Ya hW s hs y b) =
        ∫ z, prodL2 hW (attach (Fin.snoc b a : Fin (m + 1) → PosW)
          (Fin.snoc z (termPt hs y) : Fin (m + 1) → Pt d s)) ∂chainMeasure d m s hs y := by
  have hae := ae_mul_integral_eq (ν := chainMeasure d m s hs y)
    (fieldL2 hW ((⟨s, hs⟩, y), a)) (SourceWick.integrable_prodL2_attach hW hc s hs y b)
    (integrable_snoc hc hW hs y b a) (fun z => by
      rw [attach_snoc]
      exact coeFn_prodL2_snoc hW (attach b z) _)
  have hmem : MemLp (fun ω => fieldL2 hW ((⟨s, hs⟩, y), a) ω * Ya hW s hs y b ω) 2 P :=
    (Lp.memLp _).ae_eq hae.symm
  refine ⟨hmem, ?_⟩
  rw [mulL2_of_memLp hmem]
  exact Lp.ext ((hmem.coeFn_toLp).trans hae)

end Target

/-- **`TerminalFubiniTarget`** (TeX lines 2257-2260 with 4276-4285 at revision edf7085f (book
1.1.3)): "At positive widths this identity before passage to the limit is ordinary
terminal-kernel Fubini".  Under `H:homog`, for every source field, `t > 0`, `x`, inner widths
`b` and terminal width `a`: the products `W_a Y_m^b` are in `L²` at every point, they are
Bochner integrable against the mild measure, and
`Y_{m+1}^{(b,a)}(t,x) = ∫_0^t ∫ G(t-s, x-dy) W_a(s,y) Y_m^b(s,y) ds`.  Route: the last-vertex
disintegration of `g_{m+1}^{t,x}` and `ae_mul_integral_eq` (module docstring).  The named input
`TerminalFubini` is not used. -/
theorem terminal_fubini (d : ℕ) : TerminalFubiniTarget.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW t ht x m b a
  have hc : ∀ w w' : PosW, Continuous fun pq : (↥(Ici (0 : ℝ)) × Rd d) ×
      (↥(Ici (0 : ℝ)) × Rd d) => srcCov α₀ Γ (pq.1, w) (pq.2, w') :=
    SourceFeatures.source_cov_continuous d hH
  -- (i) the products are in `L²` at every point
  have hmem : ∀ p : ℝ × Rd d, MemLp (fun ω => Wa hW a p ω * Yf hW b p ω) 2 P := by
    rintro ⟨s, y⟩
    by_cases hs : 0 ≤ s
    · rw [Wa_of_nonneg hW a hs y, Yf_of_nonneg hW b hs y]
      exact (mul_Ya_eq hc hW hs y b a).1
    · have h0 : Wa hW a (s, y) = 0 := by unfold Wa; simp [hs]
      rw [h0]
      refine (MemLp.zero (ε := ℝ)).ae_eq ?_
      filter_upwards [Lp.coeFn_zero ℝ 2 P] with ω hω
      rw [hω]; simp
  -- the pointwise identification of the two integrands on the base measure
  set F : (Fin (m + 1) → ℝ × Rd d) → Lp ℝ 2 P := fun z =>
    prodL2 hW (attach (Fin.snoc b a : Fin (m + 1) → PosW) (toPt ht.le z)) with hFdef
  have hcont := SourceWick.continuous_prodL2_attach hW hc (t := t)
    (Fin.snoc b a : Fin (m + 1) → PosW)
  have hFm : StronglyMeasurable F :=
    (hcont.comp (continuous_pi fun j =>
      (continuous_projIcc.comp ((continuous_apply j).fst)).prodMk
        (continuous_apply j).snd)).stronglyMeasurable
  have hi : Integrable F (chainMeasureRaw d (m + 1) t x) := by
    have h := SourceWick.integrable_prodL2_attach hW hc t ht.le x
      (Fin.snoc b a : Fin (m + 1) → PosW)
    rwa [chainMeasure, integrable_map_measure hcont.aestronglyMeasurable
      (measurable_toPt ht.le).aemeasurable] at h
  obtain ⟨hInt, hEq⟩ := integral_chainMeasureRaw_succ m t x F hFm hi
  have hpt : (fun p : ℝ × Rd d => (lastW t p.1).toReal •
      mulL2 (Wa hW a (mildEquiv t x p)) (Yf hW b (mildEquiv t x p))) =
      fun p => (lastW t p.1).toReal • ∫ z, F (Fin.snoc z (p.1, x - (t - p.1) • p.2) :
        Fin (m + 1) → ℝ × Rd d) ∂chainMeasureRaw d m p.1 (x - (t - p.1) • p.2) := by
    funext p
    obtain ⟨s, v⟩ := p
    by_cases h : lastW t s = 0
    · simp [h]
    · have hst := mem_of_lastW_ne_zero h
      have hs : 0 ≤ s := hst.1.le
      congr 1
      rw [mildEquiv_apply, mildMap_of_ne x (show (s, v).1 ≠ t from hst.2.ne)]
      simp only
      rw [Wa_of_nonneg hW a hs, Yf_of_nonneg hW b hs, (mul_Ya_eq hc hW hs _ b a).2,
        chainMeasure, integral_map (measurable_toPt hs).aemeasurable
          (continuous_snoc_prodL2 hc hW hs _ b a).aestronglyMeasurable]
      refine integral_congr_ae ?_
      filter_upwards [ae_chainMeasureRaw_times m s (x - (t - s) • v)] with z hz
      simp only [hFdef]
      rw [attach_toPt_snoc hs ht.le hst.2.le _ z _ fun j => ⟨(hz j).1.le, (hz j).2.le⟩]
  refine ⟨hmem, ?_, ?_⟩
  · rw [integrable_mildMeasure_iff, hpt]
    exact hInt
  · have hY : Ya hW t ht.le x (Fin.snoc b a : Fin (m + 1) → PosW) =
        ∫ z, F z ∂chainMeasureRaw d (m + 1) t x := by
      rw [Ya, chainMeasure, integral_map (measurable_toPt ht.le).aemeasurable
        hcont.aestronglyMeasurable]
    rw [hY, hEq, mildInt, integral_mildMeasure, hpt]

end StratonovichHAMSecondMoment.MildTerminalFubini
