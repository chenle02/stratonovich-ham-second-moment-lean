module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L17, item L17-E, part 1: the bridge from the diagram model M4 (`DiagramModel`) to the
label-set pairing integral `I_D` of M7 (`PairingInterface`).  Main TeX file
`notes/notes_stratonovich_ham_second_moment.tex`, TeX lines 1993-2033 at revision edf7085f
(book 1.1.3): Step 1 of the proof of `L:crude-corrected` (statement 1978-1985, proof
1987-2054), also invoked by Step 1 of the proof of `P:envelope` (2381-2406).

Formalized (all proved, nothing supplied):
* predecessors: `m4Chain_pred` (the M7 predecessor of `m4Chain m n D` is M4's `pred m`),
  `m4Chain_predTime`, `m4Chain_predPos`, `labels_m4Chain`; the edges are the openers' pairs
  (`D_m4Chain_eq_image`, `prod_edges_m4Chain`, `card_D_m4Chain`: `k` edges for `m + n = 2k`);
* the spatial change of variables of determinant one in every dimension
  (`measurePreserving_incrOfPos_d`; main TeX lines 5340-5341 and 5748; extends
  `DiagramBridge.measurePreserving_incrOfPos`, `d = 1`);
* products of measures with finite densities (`pi_withDensity`) and the spatial part with a
  Green density in position variables (`spatial_eq_of_density`);
* the Gamma mixture with `A = (0,∞)`: `κ(t) = |t|^{-a}`, also `∞ = ∞` on the diagonal
  (`kappa_Ioi`); the smoothed spectral measure `e^{-ε|ξ|²/2} μ` is finite
  (`isFiniteMeasure_smoothSpec`), has real nonnegative transform `γ_ε`
  (`specNonneg_smoothSpec`), and its covariance is M4's `covEps Γ ε` (`gammaOf_smoothSpec`);
  the edge datum `smoothEdge` (TeX 2013-2018);
* the bridge `diagram_le_pairingIntegral`: `J_{m,n,D}(t) ≤ e^{2θt} I_D(e^{-θ·}g)` for `θ ≥ 0`
  (damping telescopes to `e^{-θ(s_n+s_{2n})} ≥ e^{-2θt}`, TeX 1995-1997; extension to the
  infinite simplices, 1997-1998), and its `∃ E` form `m4_bridge_of_ne_top`.

The frozen target `PairingInterface.M4BridgeTarget` (as amended on 2026-11-20, L17 interface
amendment 1: finite densities `g s x ≠ ⊤`) is `m4_bridge`, from `m4_bridge_of_ne_top`.  Without
finiteness the measures `G_s = g(s,·) dy` need not be σ-finite, and Mathlib's `Measure.pi` of
non-σ-finite factors is not the product density.

Readings: the TeX applies the envelope "with the spatially smoothed covariance and the temporal
truncations of (2.24)" (TeX 2013-2015); M4 has no temporal truncation, so the envelope is applied
uncapped with `A_e = (0,∞)` (INTERFACE §5.2).  The noise width `ε` is M4's common width.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.PairingInterface
public import StratonovichHAMSecondMoment.DiagramBridge
public import StratonovichHAMSecondMoment.TwoSimplexTime
public import StratonovichHAMSecondMoment.LowAlphaUpper
public import StratonovichHAMSecondMoment.TimeFractional

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal Real

namespace StratonovichHAMSecondMoment.PairingBridge

open HomogHypothesis (Rd HomogCovariance)
open LowAlphaConvolution (gaussFactor gammaEps)
open DiagramModel (Pi2 diagram covEps pred predVal incr twoSimplex openers timeCov timeWeight
  covWeight pos spatial)
open DiagramBridge (incrOfPos pos_incrOfPos incrMatrix incrVec)
open PairingInterface

variable {d : ℕ}

/-! ### Predecessors on the M4 chains -/

section Pred

variable {α : Type*} [DecidableEq α]

/-- Auxiliary: one step of `listPred`. -/
theorem listPred_cons' (a : α) (l : List α) (x : α) :
    listPred (a :: l) x = if l.head? = some x then some a else listPred l x := by
  cases l with
  | nil => simp [listPred]
  | cons b l => simp [listPred, eq_comm]

/-- Auxiliary: `listPred` on `List.ofFn f` for an injective `f`. -/
theorem listPred_ofFn : ∀ {k : ℕ} (f : Fin k → α), Function.Injective f → ∀ j : Fin k,
    listPred (List.ofFn f) (f j) =
      if (j : ℕ) = 0 then none else some (f ⟨(j : ℕ) - 1, by omega⟩)
  | 0, _, _, j => j.elim0
  | k + 1, f, hf, j => by
    rw [List.ofFn_succ, listPred_cons']
    have hhead : (List.ofFn fun i : Fin k => f i.succ).head? =
        if h : k = 0 then none else some (f ⟨1, by omega⟩) := by
      rcases k with _ | k
      · simp
      · simp [List.ofFn_succ]
    rw [hhead]
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
    · have h1 : ¬ ((if h : k = 0 then none else some (f ⟨1, by omega⟩)) = some (f 0)) := by
        split_ifs with h
        · simp
        · intro h'
          have := hf (Option.some_injective _ h')
          simp [Fin.ext_iff] at this
      simp only [h1, ↓reduceIte, Fin.val_zero]
      refine listPred_eq_none_of_notMem_tail ?_
      intro hm
      have hm' := List.mem_of_mem_tail hm
      obtain ⟨i, hi⟩ := List.mem_ofFn.1 hm'
      have := hf hi
      exact Fin.succ_ne_zero i this
    · have ih := listPred_ofFn (fun i : Fin k => f i.succ) (hf.comp (Fin.succ_injective k)) j'
      by_cases hj : (j' : ℕ) = 0
      · have hk : k ≠ 0 := by have := j'.isLt; omega
        have e1 : j'.succ = (⟨1, by omega⟩ : Fin (k + 1)) := Fin.ext (by simp [hj])
        rw [e1]
        simp [hk]
      · have hne : ¬ ((if h : k = 0 then none else some (f ⟨1, by omega⟩)) = some (f j'.succ)) := by
          split_ifs with h
          · simp
          · intro h'
            have := hf (Option.some_injective _ h')
            simp [Fin.ext_iff] at this
            omega
        simp only [hne, ↓reduceIte]
        rw [ih]
        simp only [hj, ↓reduceIte, Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false]
        congr 2
        ext
        simp only [Fin.val_succ]
        omega

/-- Auxiliary: `listPred` of an element not in the list is `none`. -/
theorem listPred_of_notMem {l : List α} {x : α} (h : x ∉ l) : listPred l x = none :=
  listPred_eq_none_of_notMem_tail fun hm => h (List.mem_of_mem_tail hm)

end Pred

/-- **The M7 predecessor of the M4 chains is M4's** `DiagramModel.pred`: the label just before
in its own chain, `none` at the first vertices `0` and `m` (TeX 1462-1463; main TeX lines
810-813 for M4). -/
theorem m4Chain_pred {m n : ℕ} (D : Fin (m + n) → Fin (m + n)) (i : Fin (m + n)) :
    (m4Chain m n D).pred i = pred m i := by
  have hc1 : (m4Chain m n D).c1 = List.ofFn fun j : Fin m => Fin.castAdd n j := rfl
  have hc2 : (m4Chain m n D).c2 = List.ofFn fun j : Fin n => Fin.natAdd m j := rfl
  have hinj1 : Function.Injective fun j : Fin m => Fin.castAdd n j :=
    fun x y h => Fin.ext (by simpa using congrArg Fin.val h)
  have hinj2 : Function.Injective fun j : Fin n => Fin.natAdd m j :=
    fun x y h => Fin.ext (by simpa using congrArg Fin.val h)
  unfold TwoChain.pred pred
  by_cases hi : (i : ℕ) < m
  · have hmem : i ∈ (m4Chain m n D).c1 := by
      rw [hc1]; exact List.mem_ofFn.2 ⟨⟨i, hi⟩, Fin.ext rfl⟩
    simp only [hmem, ↓reduceIte]
    rw [hc1]
    have := listPred_ofFn (fun j : Fin m => Fin.castAdd n j) hinj1 ⟨i, hi⟩
    rw [show Fin.castAdd n (⟨i, hi⟩ : Fin m) = i from Fin.ext rfl] at this
    rw [this]
    by_cases h0 : (i : ℕ) = 0
    · simp [h0]
    · have hm : ¬ (i : ℕ) = m := by omega
      simp only [h0, hm, or_self, ↓reduceIte]
      rfl
  · have hnmem : i ∉ (m4Chain m n D).c1 := by
      rw [hc1]
      intro hm
      obtain ⟨j, hj⟩ := List.mem_ofFn.1 hm
      have := congrArg Fin.val hj
      simp at this
      omega
    simp only [hnmem, ↓reduceIte]
    rw [hc2]
    have hlt : (i : ℕ) - m < n := by have := i.isLt; omega
    have := listPred_ofFn (fun j : Fin n => Fin.natAdd m j) hinj2 ⟨(i : ℕ) - m, hlt⟩
    rw [show Fin.natAdd m (⟨(i : ℕ) - m, hlt⟩ : Fin n) = i from Fin.ext (by simp; omega)] at this
    rw [this]
    by_cases h0 : (i : ℕ) = m
    · have h1 : (i : ℕ) - m = 0 := by omega
      simp [h0]
    · have h1 : ¬ ((i : ℕ) = 0 ∨ (i : ℕ) = m) := by omega
      have h2 : ¬ ((i : ℕ) - m = 0) := by omega
      simp only [h1, h2, ↓reduceIte]
      congr 1
      ext
      simp
      omega

/-- The labels of an M4 chain are all of `Fin (m + n)`. -/
theorem labels_m4Chain {m n : ℕ} (D : Fin (m + n) → Fin (m + n)) :
    (m4Chain m n D).labels = Finset.univ :=
  Finset.eq_univ_of_forall (mem_labels_m4Chain D)

/-- On the M4 chains, `predTime` is M4's predecessor time. -/
theorem m4Chain_predTime {m n : ℕ} (D : Fin (m + n) → Fin (m + n))
    (z : Fin (m + n) → ℝ × Rd d) (i : Fin (m + n)) :
    (m4Chain m n D).predTime z i = predVal m (fun j => (z j).1) i := by
  unfold TwoChain.predTime predVal
  rw [m4Chain_pred]

/-- On the M4 chains, `predPos` is M4's predecessor position. -/
theorem m4Chain_predPos {m n : ℕ} (D : Fin (m + n) → Fin (m + n))
    (z : Fin (m + n) → ℝ × Rd d) (i : Fin (m + n)) :
    (m4Chain m n D).predPos z i = predVal m (fun j => (z j).2) i := by
  unfold TwoChain.predPos predVal
  rw [m4Chain_pred]

/-- The edges of an M4 chain are the pairs of its openers. -/
theorem D_m4Chain_eq_image {m n : ℕ} {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n) :
    (m4Chain m n D).D = (openers D).image fun i => s(i, D i) := by
  rw [DiagramModel.mem_Pi2] at hD
  ext e
  simp only [m4Chain, Finset.mem_image, Finset.mem_univ, true_and, openers,
    Finset.mem_filter]
  constructor
  · rintro ⟨i, rfl⟩
    rcases lt_or_gt_of_ne (hD i).1.symm with h | h
    · exact ⟨i, h, rfl⟩
    · exact ⟨D i, by rw [(hD i).2]; exact h, by rw [(hD i).2, Sym2.eq_swap]⟩
  · rintro ⟨i, -, rfl⟩
    exact ⟨i, rfl⟩

/-- Distinct openers give distinct edges. -/
theorem injOn_openers {m n : ℕ} (D : Fin (m + n) → Fin (m + n)) :
    Set.InjOn (fun i => s(i, D i)) (openers D) := by
  intro i hi j hj hij
  simp only [openers, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi hj
  rcases Sym2.eq_iff.1 hij with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact h1
  · exfalso
    have h3 : i < j := by rw [← h2]; exact hi
    have h4 : j < i := by rw [h1]; exact hj
    exact lt_asymm h3 h4

/-- The edges of an M4 chain are its openers' pairs: a product over the edges is a product over
`openers D`, each pair once. -/
theorem prod_edges_m4Chain {m n : ℕ} {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n)
    (F : Sym2 (Fin (m + n)) → ℝ≥0∞) :
    ∏ e ∈ (m4Chain m n D).D, F e = ∏ i ∈ openers D, F s(i, D i) := by
  rw [D_m4Chain_eq_image hD, Finset.prod_image (injOn_openers D)]

/-- An M4 chain of a pairing of `2k` labels has `k` edges. -/
theorem card_D_m4Chain {m n k : ℕ} {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n)
    (hk : m + n = 2 * k) : (m4Chain m n D).D.card = k := by
  rw [D_m4Chain_eq_image hD, Finset.card_image_of_injOn (injOn_openers D)]
  exact DiagramModel.card_openers hD hk

/-! ### The increments change of variables in every dimension -/

/-- Auxiliary: `uncurry` preserves Lebesgue measure on finite products of `ℝ`. -/
theorem measurePreserving_uncurry (ι κ : Type*) [Fintype ι] [Fintype κ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ ℝ).symm volume volume := by
  refine ⟨(MeasurableEquiv.curry ι κ ℝ).symm.measurable, ?_⟩
  show _ = Measure.pi fun _ : ι × κ => (volume : Measure ℝ)
  refine (Measure.pi_eq (μ := fun _ : ι × κ => (volume : Measure ℝ)) fun s hs => ?_).symm
  rw [MeasurableEquiv.map_apply]
  have hpre : (MeasurableEquiv.curry ι κ ℝ).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi fun i => Set.univ.pi fun j => s (i, j) := by
    ext f
    simp [MeasurableEquiv.coe_curry_symm, Set.mem_pi]
  rw [hpre]
  change (Measure.pi fun _ : ι => (Measure.pi fun _ : κ => (volume : Measure ℝ)))
    (Set.univ.pi fun i => Set.univ.pi fun j => s (i, j)) = _
  rw [Measure.pi_pi]
  simp_rw [show ∀ i, (Measure.pi fun _ : κ => (volume : Measure ℝ))
      (Set.univ.pi fun j => s (i, j)) = ∏ j, volume (s (i, j)) from fun i => Measure.pi_pi _ _]
  rw [← Finset.prod_product', Finset.univ_product_univ]

/-- Auxiliary: transposing a doubly indexed real array preserves Lebesgue measure. -/
def swapEquiv (N d : ℕ) : (Fin N → Fin d → ℝ) ≃ᵐ (Fin d → Fin N → ℝ) :=
  ((MeasurableEquiv.curry (Fin N) (Fin d) ℝ).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (Equiv.prodComm (Fin d) (Fin N)).symm)).trans
    (MeasurableEquiv.curry (Fin d) (Fin N) ℝ)

theorem swapEquiv_apply (N d : ℕ) (w : Fin N → Fin d → ℝ) (j : Fin d) (i : Fin N) :
    swapEquiv N d w j i = w i j := by
  simp [swapEquiv, MeasurableEquiv.coe_curry_symm, MeasurableEquiv.piCongrLeft]
  rfl

theorem measurePreserving_swapEquiv (N d : ℕ) :
    MeasurePreserving (swapEquiv N d) volume volume := by
  refine ((measurePreserving_uncurry (Fin N) (Fin d)).trans ?_).trans
    (measurePreserving_uncurry (Fin d) (Fin N)).symm
  exact volume_measurePreserving_piCongrLeft (fun _ => ℝ) _

/-- Auxiliary: `(ℝ^d)^N ≃ (ℝ^N)^d`, coordinates transposed. -/
def coordEquiv (N d : ℕ) : (Fin N → Rd d) ≃ᵐ (Fin d → Fin N → ℝ) :=
  (MeasurableEquiv.piCongrRight fun _ : Fin N => (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm).trans
    (swapEquiv N d)

theorem coordEquiv_apply (N d : ℕ) (y : Fin N → Rd d) (j : Fin d) (i : Fin N) :
    coordEquiv N d y j i = y i j := by
  simp only [coordEquiv, MeasurableEquiv.trans_apply, swapEquiv_apply]
  rfl

theorem measurePreserving_coordEquiv (N d : ℕ) :
    MeasurePreserving (coordEquiv N d) volume volume :=
  (volume_preserving_pi fun _ =>
    EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).trans
    (measurePreserving_swapEquiv N d)

/-- Auxiliary: in coordinates, the increment map acts as `incrMatrix` on each coordinate. -/
theorem incrOfPos_eq_coord (m N d : ℕ) :
    incrOfPos m (d := d) (N := N) = (coordEquiv N d).symm ∘
      (fun v : Fin d → Fin N → ℝ => fun j => Matrix.toLin' (incrMatrix m N) (v j)) ∘
        coordEquiv N d := by
  funext y
  apply (coordEquiv N d).injective
  simp only [Function.comp_apply, MeasurableEquiv.apply_symm_apply, Matrix.toLin'_apply,
    DiagramBridge.incrMatrix_mulVec]
  funext j i
  rw [coordEquiv_apply, incrOfPos, incrVec]
  rcases hp : pred m i with _ | k
  · simp [DiagramModel.predVal_of_none m _ i hp, coordEquiv_apply]
  · simp [DiagramModel.predVal_of_some m _ i k hp, coordEquiv_apply]

/-- **The spatial change of variables has determinant one in every dimension** (the increment
map `y ↦ (y_l - y_{p(l)})_l` preserves Lebesgue measure on `(ℝ^d)^N`; main TeX lines 5340-5341
and 5748, used at TeX 1993-2001).  Extends `DiagramBridge.measurePreserving_incrOfPos`
(`d = 1`). -/
theorem measurePreserving_incrOfPos_d (m N d : ℕ) :
    MeasurePreserving (incrOfPos m (d := d) (N := N)) volume volume := by
  rw [incrOfPos_eq_coord]
  exact (measurePreserving_coordEquiv N d).symm.comp
    ((volume_preserving_pi fun _ => DiagramBridge.measurePreserving_incrMatrix m N).comp
      (measurePreserving_coordEquiv N d))

/-! ### Products of measures with densities -/

/-- Auxiliary: the integral of a product of coordinate functions over a product measure. -/
theorem lintegral_pi_prod_hetero {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] :
    ∀ (k : ℕ) (f : Fin k → X → ℝ≥0∞), (∀ j, Measurable (f j)) →
      ∫⁻ y, ∏ j, f j (y j) ∂(Measure.pi fun _ : Fin k => μ) = ∏ j, ∫⁻ x, f j x ∂μ
  | 0, f, _ => by
    rw [Measure.pi_of_empty (x := fun i => i.elim0)]
    simp
  | k + 1, f, hf => by
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => μ) 0
    have h1 : ∀ y : Fin (k + 1) → X, ∏ j, f j (y j) =
        (fun p : X × (Fin k → X) => f 0 p.1 * ∏ j, f j.succ (p.2 j))
          (MeasurableEquiv.piFinSuccAbove (fun _ => X) 0 y) := by
      intro y
      rw [Fin.prod_univ_succ]
      rfl
    rw [lintegral_congr fun y => h1 y,
      hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)
        (fun p : X × (Fin k → X) => f 0 p.1 * ∏ j, f j.succ (p.2 j))]
    rw [lintegral_prod_mul (g := fun v : Fin k → X => ∏ j, f j.succ (v j)) (hf 0).aemeasurable
      (Finset.measurable_prod _ fun j _ => (hf j.succ).comp (measurable_pi_apply j)).aemeasurable,
      lintegral_pi_prod_hetero μ k (fun j => f j.succ) (fun j => hf j.succ),
      Fin.prod_univ_succ]

/-- **A product of measures with finite densities has the product density**:
`⊗_i f_i(w_i) dw_i = (∏_i f_i(w_i)) dw`. -/
theorem pi_withDensity {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] {N : ℕ}
    (f : Fin N → X → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) (hfin : ∀ i x, f i x ≠ ∞) :
    Measure.pi (fun i => μ.withDensity (f i)) =
      (Measure.pi fun _ : Fin N => μ).withDensity fun w => ∏ i, f i (w i) := by
  have : ∀ i, SigmaFinite (μ.withDensity (f i)) :=
    fun i => SigmaFinite.withDensity_of_ne_top' (hfin i)
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator
    (MeasurableSet.univ_pi hs)]
  have hind : (Set.univ.pi s).indicator (fun w : Fin N → X => ∏ i, f i (w i)) =
      fun w => ∏ i, (s i).indicator (f i) (w i) := by
    funext w
    by_cases hw : w ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hw]
      exact Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (hw i (Set.mem_univ i)) _).symm
    · rw [Set.indicator_of_notMem hw]
      simp only [Set.mem_univ_pi, not_forall] at hw
      obtain ⟨i, hi⟩ := hw
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  rw [hind, lintegral_pi_prod_hetero μ N _ fun i => (hf i).indicator (hs i)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [lintegral_indicator (hs i), withDensity_apply _ (hs i)]

/-! ### The Gamma mixture and the smoothed spectral measure -/

/-- **The Gamma mixture with `A = (0,∞)` is the time kernel**: for `a > 0`,
`κ(t) = Γ(a)⁻¹ ∫_0^∞ e^{-λ|t|} λ^{a-1} dλ = |t|^{-a}`, also on the diagonal where both sides
are `∞` (TeX 1442-1443 with `A_e = (0,∞)`; `|s-r|^{-α₀}` as used at TeX 2001-2003). -/
theorem kappa_Ioi {a : ℝ} (ha : 0 < a) (E : EdgeData d) (hA : E.A = Ioi 0) (t : ℝ) :
    kappa a E t = ENNReal.ofReal |t| ^ (-a) := by
  have hG : 0 < (Real.Gamma a)⁻¹ := inv_pos.2 (Real.Gamma_pos_of_pos ha)
  unfold kappa nuE
  rw [hA, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  simp only [Pi.mul_apply]
  by_cases ht : t = 0
  · subst ht
    simp only [abs_zero, mul_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one, mul_one,
      ENNReal.ofReal_zero]
    rw [ENNReal.zero_rpow_of_neg (by linarith)]
    have hsplit : ∀ l ∈ Ioi (0 : ℝ), ENNReal.ofReal ((Real.Gamma a)⁻¹ * l ^ (a - 1)) =
        ENNReal.ofReal (Real.Gamma a)⁻¹ * ENNReal.ofReal (l ^ (a - 1)) :=
      fun l _ => ENNReal.ofReal_mul hG.le
    rw [setLIntegral_congr_fun measurableSet_Ioi hsplit, lintegral_const_mul _ (by fun_prop)]
    refine ENNReal.mul_eq_top.2 (Or.inl ⟨by simpa using hG, ?_⟩)
    by_contra hne
    apply not_integrableOn_Ioi_rpow (a - 1)
    refine ⟨(by fun_prop : Measurable fun l : ℝ => l ^ (a - 1)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal]
    · exact lt_top_iff_ne_top.2 hne
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with l hl
      exact Real.rpow_nonneg (le_of_lt hl) _
  · have hr : 0 < |t| := abs_pos.2 ht
    have hcongr : ∀ l ∈ Ioi (0 : ℝ),
        ENNReal.ofReal ((Real.Gamma a)⁻¹ * l ^ (a - 1)) *
            ENNReal.ofReal (Real.exp (-(l * |t|))) =
          ENNReal.ofReal ((Real.Gamma a)⁻¹ * TimeFractional.subKernel a |t| l) := by
      intro l hl
      rw [← ENNReal.ofReal_mul (mul_nonneg hG.le (Real.rpow_nonneg (le_of_lt hl) _)),
        TimeFractional.subKernel, mul_comm l |t|]
      ring_nf
    rw [setLIntegral_congr_fun measurableSet_Ioi hcongr,
      ← ofReal_integral_eq_lintegral_ofReal]
    · rw [integral_const_mul, ← TimeFractional.rpow_neg_eq_subordination a |t| ha hr,
        ENNReal.ofReal_rpow_of_pos hr]
    · exact (TimeFractional.subKernel_integrable a |t| ha hr).const_mul _
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with l hl
      exact mul_nonneg hG.le (TimeFractional.subKernel_nonneg a |t| l (le_of_lt hl))

section Smooth

variable {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}

/-- Auxiliary: integrals against `smoothSpec μ ε` are `μ`-integrals with the Gaussian factor. -/
theorem integral_smoothSpec {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure (Rd d)) (ε : ℝ) (f : Rd d → E) :
    ∫ ξ, f ξ ∂smoothSpec μ ε = ∫ ξ, gaussFactor ε ξ • f ξ ∂μ := by
  unfold smoothSpec
  rw [integral_withDensity_eq_integral_toReal_smul (by unfold gaussFactor; fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only
  rw [ENNReal.toReal_ofReal (LowAlphaConvolution.gaussFactor_pos ε ξ).le]

/-- **The smoothed spectral measure is finite** under `H:homog` (TeX 2013-2018: "the smoothed
spectral measure is finite"). -/
theorem isFiniteMeasure_smoothSpec (hH : HomogCovariance d alpha α₀ Γ μ) {ε : ℝ} (hε : 0 < ε) :
    IsFiniteMeasure (smoothSpec μ ε) := by
  refine ⟨?_⟩
  unfold smoothSpec
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact (LowAlphaConvolution.integrable_gaussFactor hH.μ_tempered hε).lintegral_lt_top

/-- The transform of the smoothed spectral measure is `γ_ε = p_ε * Γ`
(`LowAlphaConvolution.gammaEps_spectral`). -/
theorem fourier_smoothSpec (hH : HomogCovariance d alpha α₀ Γ μ) {ε : ℝ} (hε : 0 < ε)
    (x : Rd d) :
    ∫ ξ, Complex.exp (Complex.I * (inner ℝ ξ x : ℝ)) ∂smoothSpec μ ε = (gammaEps Γ ε x : ℂ) := by
  rw [integral_smoothSpec, LowAlphaConvolution.gammaEps_spectral hH.spectral hε x]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [Complex.real_smul]
  ring

/-- **The smoothed spectral measure has a real nonnegative transform** (`SpecNonneg`). -/
theorem specNonneg_smoothSpec (hH : HomogCovariance d alpha α₀ Γ μ) {ε : ℝ} (hε : 0 < ε) :
    SpecNonneg (smoothSpec μ ε) := fun x =>
  ⟨gammaEps Γ ε x, LowAlphaConvolution.gammaEps_nonneg Γ hε.le x, fourier_smoothSpec hH hε x⟩

/-- **The covariance of the smoothed spectral measure is M4's `covEps Γ ε`** (TeX 2013-2018;
`γ_ε(x) = ∫ cos(ξ·x) e^{-ε|ξ|²/2} μ(dξ)`). -/
theorem gammaOf_smoothSpec (hH : HomogCovariance d alpha α₀ Γ μ) {ε : ℝ} (hε : 0 < ε)
    (x : Rd d) : gammaOf (smoothSpec μ ε) x = covEps Γ ε x := by
  have := isFiniteMeasure_smoothSpec hH hε
  rw [LowAlphaUpper.covEps_eq_ofReal hε.le
    (LowAlphaConvolution.integrable_heatDens hH.Γ_tempered hε) x, gammaOf]
  congr 1
  have hI : Integrable (fun ξ : Rd d => Complex.exp (Complex.I * (inner ℝ ξ x : ℝ)))
      (smoothSpec μ ε) := by
    refine Integrable.of_bound (by fun_prop : Continuous fun ξ : Rd d =>
      Complex.exp (Complex.I * (inner ℝ ξ x : ℝ))).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  have hre := integral_re hI
  rw [fourier_smoothSpec hH hε x] at hre
  have hr : RCLike.re ((gammaEps Γ ε x : ℝ) : ℂ) = gammaEps Γ ε x := Complex.ofReal_re _
  rw [hr] at hre
  rw [← hre]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [RCLike.re_to_complex]
  rw [mul_comm]
  exact (Complex.exp_ofReal_mul_I_re _).symm

/-- **The M4 edge datum at noise width `ε`**: `A = (0,∞)` and `μ_e = e^{-ε|ξ|²/2} μ(dξ)` (TeX
1993-2033). -/
def smoothEdge (hH : HomogCovariance d alpha α₀ Γ μ) {ε : ℝ} (hε : 0 < ε) : EdgeData d where
  A := Ioi 0
  measurableSet_A := measurableSet_Ioi
  A_subset := subset_rfl
  μ := smoothSpec μ ε
  isFiniteMeasure_μ := isFiniteMeasure_smoothSpec hH hε
  spec_nonneg := specNonneg_smoothSpec hH hε

end Smooth

/-! ### The spatial part with a Green density -/

/-- **The spatial part with a Green density in position variables** (main TeX lines 5338-5341,
5748, used at TeX 1993-2001): for Green measures with a finite measurable density `g`,
`spatial G γ m D h = ∫ ∏_l g(h_l, y_l - y_{p(l)}) ∏_D γ(y_j - y_h) dy`. -/
theorem spatial_eq_of_density (G : ℝ → Measure (Rd d)) (g : Kernel d)
    (hg : Measurable (Function.uncurry g)) (hfin : ∀ s x, g s x ≠ ∞)
    (hG : ∀ s, G s = volume.withDensity (g s)) {γ : Rd d → ℝ≥0∞} (hγ : Measurable γ)
    (m : ℕ) {N : ℕ} (D : Fin N → Fin N) (h : Fin N → ℝ) :
    spatial G γ m D h = ∫⁻ y, (∏ i, g (h i) (incrOfPos m y i)) * covWeight γ D y := by
  have hgs : ∀ s, Measurable (g s) := fun s => hg.comp (measurable_const.prodMk measurable_id)
  unfold spatial
  simp_rw [hG]
  rw [pi_withDensity volume (fun i => g (h i)) (fun i => hgs (h i)) (fun i x => hfin (h i) x)]
  have hmeas : Measurable fun w : Fin N → Rd d => ∏ i, g (h i) (w i) :=
    Finset.measurable_prod _ fun i _ => (hgs (h i)).comp (measurable_pi_apply i)
  rw [lintegral_withDensity_eq_lintegral_mul _ hmeas
    (DiagramModel.measurable_covWeight_pos m hγ D)]
  change ∫⁻ a, ((fun w : Fin N → Rd d => ∏ i, g (h i) (w i)) *
    fun w : Fin N → Rd d => covWeight γ D (pos m w)) a ∂(volume : Measure (Fin N → Rd d)) = _
  conv_lhs => rw [← (measurePreserving_incrOfPos_d m N d).lintegral_comp_emb
    (DiagramBridge.posEquiv m d N).symm.measurableEmbedding]
  refine lintegral_congr fun y => ?_
  simp only [Pi.mul_apply]
  rw [pos_incrOfPos]

/-! ### The bridge -/

/-- The M7 integral of an M4 chain as a Lebesgue integral over times and positions
`(s, y) ∈ ℝ^N × (ℝ^d)^N` (the base point of the `lmarginal` is immaterial: all labels are
integrated). -/
theorem pairingIntegral_m4Chain_eq (a : ℝ) {m n : ℕ} (D : Fin (m + n) → Fin (m + n))
    (ed : Sym2 (Fin (m + n)) → EdgeData d) (G : Fin (m + n) → Kernel d) :
    pairingIntegral a (m4Chain m n D) ed G =
      ∫⁻ p : (Fin (m + n) → ℝ) × (Fin (m + n) → Rd d),
        integrand a (m4Chain m n D) ed G (fun i => (p.1 i, p.2 i)) := by
  unfold pairingIntegral
  rw [labels_m4Chain, lmarginal_univ]
  have hmp := volume_measurePreserving_arrowProdEquivProdArrow ℝ (Rd d) (Fin (m + n))
  change ∫⁻ z, integrand a (m4Chain m n D) ed G z
    ∂(volume : Measure (Fin (m + n) → ℝ × Rd d)) = _
  rw [← hmp.symm.lintegral_comp_emb
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ (Rd d) (Fin (m + n))).symm.measurableEmbedding]
  rfl

section Bridge

variable {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}

/-- Auxiliary: the damping factors of the two chains are at least `e^{-2θt}` on the finite
time simplices (they telescope to `e^{-θ(s_n + s_{2n})}`, TeX 1995-1997). -/
theorem damp_prod_ge {m n : ℕ} {t θ : ℝ} (ht : 0 < t) (hθ : 0 ≤ θ) {s : Fin (m + n) → ℝ}
    (hs : s ∈ twoSimplex m n t) :
    ENNReal.ofReal (Real.exp (-(2 * θ * t))) ≤
      ∏ i, ENNReal.ofReal (Real.exp (-(θ * incr m s i))) := by
  rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => (Real.exp_pos _).le, ← Real.exp_sum]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have hsum := TwoSimplexTime.sum_incr_le ht.le hs
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
  nlinarith

/-- The pointwise comparison of the M4 integrand with the damped M7 integrand. -/
theorem integrand_ge (hH : HomogCovariance d alpha α₀ Γ μ) {ε : ℝ} (hε : 0 < ε)
    (g : Kernel d) {m n : ℕ} {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n) {t θ : ℝ}
    (ht : 0 < t) (hθ : 0 ≤ θ) (p : (Fin (m + n) → ℝ) × (Fin (m + n) → Rd d)) :
    (twoSimplex m n t).indicator
        (fun s => ENNReal.ofReal (Real.exp (-(2 * θ * t))) * timeWeight α₀ D s) p.1 *
      ((∏ i, g (incr m p.1 i) (incrOfPos m p.2 i)) * covWeight (covEps Γ ε) D p.2) ≤
    integrand α₀ (m4Chain m n D) (fun _ => smoothEdge hH hε) (fun _ => damp θ g)
      (fun i => (p.1 i, p.2 i)) := by
  by_cases hs : p.1 ∈ twoSimplex m n t
  · rw [Set.indicator_of_mem hs]
    have hz : (fun i => (p.1 i, p.2 i)) ∈ (m4Chain m n D).posSimplex := by
      intro l _
      rw [m4Chain_predTime]
      exact (hs l).1
    unfold integrand
    rw [Set.indicator_of_mem hz, labels_m4Chain, prod_edges_m4Chain hD]
    simp only [m4Chain_predTime, m4Chain_predPos, edgeWeight_mk]
    have hedge : ∏ i ∈ openers D, kappa α₀ (smoothEdge hH hε) (p.1 i - p.1 (D i)) *
        gammaOf (smoothEdge hH hε).μ (p.2 i - p.2 (D i)) =
        timeWeight α₀ D p.1 * covWeight (covEps Γ ε) D p.2 := by
      rw [timeWeight, covWeight, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [kappa_Ioi hH.alpha0_pos _ rfl]
      exact congrArg _ (gammaOf_smoothSpec hH hε _)
    rw [hedge]
    have hdamp : ∏ i, damp θ g (p.1 i - predVal m (fun j => p.1 j) i)
        (p.2 i - predVal m (fun j => p.2 j) i) =
        (∏ i, ENNReal.ofReal (Real.exp (-(θ * incr m p.1 i)))) *
          ∏ i, g (incr m p.1 i) (incrOfPos m p.2 i) := by
      rw [← Finset.prod_mul_distrib]
      rfl
    rw [hdamp]
    calc ENNReal.ofReal (Real.exp (-(2 * θ * t))) * timeWeight α₀ D p.1 *
          ((∏ i, g (incr m p.1 i) (incrOfPos m p.2 i)) * covWeight (covEps Γ ε) D p.2)
        = ENNReal.ofReal (Real.exp (-(2 * θ * t))) *
            ((∏ i, g (incr m p.1 i) (incrOfPos m p.2 i)) *
              (timeWeight α₀ D p.1 * covWeight (covEps Γ ε) D p.2)) := by ring
      _ ≤ (∏ i, ENNReal.ofReal (Real.exp (-(θ * incr m p.1 i)))) *
            ((∏ i, g (incr m p.1 i) (incrOfPos m p.2 i)) *
              (timeWeight α₀ D p.1 * covWeight (covEps Γ ε) D p.2)) := by
          gcongr
          exact damp_prod_ge ht hθ hs
      _ = _ := by ring
  · rw [Set.indicator_of_notMem hs, zero_mul]
    exact zero_le

/-- Auxiliary: the M4 lower integrand integrates to `e^{-2θt} J_{m,n,D}(t)`. -/
theorem lintegral_lower_eq (hH : HomogCovariance d alpha α₀ Γ μ) {ε : ℝ} (hε : 0 < ε)
    (G : ℝ → Measure (Rd d)) (g : Kernel d) (hg : Measurable (Function.uncurry g))
    (hfin : ∀ s x, g s x ≠ ∞) (hG : ∀ s, G s = volume.withDensity (g s))
    {m n : ℕ} (D : Fin (m + n) → Fin (m + n)) (t : ℝ) (c : ℝ≥0∞) (hc : c ≠ ∞) :
    ∫⁻ p : (Fin (m + n) → ℝ) × (Fin (m + n) → Rd d),
      (twoSimplex m n t).indicator (fun s => c * timeWeight α₀ D s) p.1 *
        ((∏ i, g (incr m p.1 i) (incrOfPos m p.2 i)) * covWeight (covEps Γ ε) D p.2) =
      c * diagram G (covEps Γ ε) α₀ m n D t := by
  have hγ : Measurable (covEps Γ ε) := LowAlphaUpper.measurable_covEps hH hε
  have hcov : Measurable fun y : Fin (m + n) → Rd d => covWeight (covEps Γ ε) D y :=
    Finset.measurable_prod _ fun i _ =>
      hγ.comp ((measurable_pi_apply i).sub (measurable_pi_apply (D i)))
  have hgi : ∀ i : Fin (m + n), Measurable fun p : (Fin (m + n) → ℝ) × (Fin (m + n) → Rd d) =>
      g (incr m p.1 i) (incrOfPos m p.2 i) := by
    intro i
    have hpair : Measurable fun p : (Fin (m + n) → ℝ) × (Fin (m + n) → Rd d) =>
        (incr m p.1 i, incrOfPos m p.2 i) :=
      (((measurable_pi_apply i).comp (DiagramModel.measurable_incr m)).comp
        measurable_fst).prodMk (((measurable_pi_apply i).comp
          (DiagramBridge.measurable_incrOfPos m)).comp measurable_snd)
    exact hg.comp hpair
  have hHm : Measurable fun p : (Fin (m + n) → ℝ) × (Fin (m + n) → Rd d) =>
      (twoSimplex m n t).indicator (fun s => c * timeWeight α₀ D s) p.1 *
        ((∏ i, g (incr m p.1 i) (incrOfPos m p.2 i)) * covWeight (covEps Γ ε) D p.2) := by
    refine Measurable.mul ?_ (Measurable.mul ?_ (hcov.comp measurable_snd))
    · exact ((measurable_const.mul (DiagramModel.measurable_timeWeight α₀ D)).indicator
        (DiagramModel.measurableSet_twoSimplex m n t)).comp measurable_fst
    · exact Finset.measurable_prod _ fun i _ => hgi i
  rw [Measure.volume_eq_prod, lintegral_prod _ hHm.aemeasurable]
  have hin : ∀ s : Fin (m + n) → ℝ,
      ∫⁻ y, (twoSimplex m n t).indicator (fun s => c * timeWeight α₀ D s) s *
        ((∏ i, g (incr m s i) (incrOfPos m y i)) * covWeight (covEps Γ ε) D y) =
      (twoSimplex m n t).indicator (fun s => c * (timeWeight α₀ D s *
          spatial G (covEps Γ ε) m D (incr m s))) s := by
    intro s
    have hm : Measurable fun y : Fin (m + n) → Rd d =>
        (∏ i, g (incr m s i) (incrOfPos m y i)) * covWeight (covEps Γ ε) D y :=
      (Finset.measurable_prod _ fun i _ => (hgi i).comp (measurable_const.prodMk measurable_id)).mul
        hcov
    rw [lintegral_const_mul _ hm, ← spatial_eq_of_density G g hg hfin hG hγ m D (incr m s)]
    by_cases hs : s ∈ twoSimplex m n t
    · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs, mul_assoc]
    · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, zero_mul]
  simp_rw [hin]
  rw [lintegral_indicator (DiagramModel.measurableSet_twoSimplex m n t),
    lintegral_const_mul' _ _ hc]
  rfl

/-- **The bridge M4 → `I_D`** (Step 1 of `L:crude-corrected`, TeX lines 1993-2033 at revision
edf7085f (book 1.1.3)): under `H:homog`, at noise width `ε > 0`, for Green measures with a finite
measurable density `g` (`G_s = g(s,·) dy`), every M4 diagram satisfies
`J_{m,n,D}(t) ≤ e^{2θt} I_D(e^{-θ·} g)` for `θ ≥ 0`, with the edge datum `A = (0,∞)`,
`μ_e = e^{-ε|ξ|²/2} μ` on every edge and the exponent `a = α₀`: the damping telescopes to
`e^{-θ(s_n+s_{2n})} ≥ e^{-2θt}`, the finite simplices extend to the infinite ones, the time
covariance is the Gamma mixture (`kappa_Ioi`) and the smoothed covariance is the transform of
`μ_e` (`gammaOf_smoothSpec`). -/
theorem diagram_le_pairingIntegral (hH : HomogCovariance d alpha α₀ Γ μ) {ε : ℝ} (hε : 0 < ε)
    (G : ℝ → Measure (Rd d)) (g : Kernel d) (hg : Measurable (Function.uncurry g))
    (hfin : ∀ s x, g s x ≠ ∞) (hG : ∀ s, G s = volume.withDensity (g s))
    {m n : ℕ} {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n) {t θ : ℝ} (ht : 0 < t)
    (hθ : 0 ≤ θ) :
    diagram G (covEps Γ ε) α₀ m n D t ≤
      ENNReal.ofReal (Real.exp (2 * θ * t)) *
        pairingIntegral α₀ (m4Chain m n D) (fun _ => smoothEdge hH hε) (fun _ => damp θ g) := by
  have key : ENNReal.ofReal (Real.exp (-(2 * θ * t))) * diagram G (covEps Γ ε) α₀ m n D t ≤
      pairingIntegral α₀ (m4Chain m n D) (fun _ => smoothEdge hH hε) (fun _ => damp θ g) := by
    rw [← lintegral_lower_eq hH hε G g hg hfin hG D t _ ENNReal.ofReal_ne_top,
      pairingIntegral_m4Chain_eq]
    exact lintegral_mono fun p => integrand_ge hH hε g hD ht hθ p
  calc diagram G (covEps Γ ε) α₀ m n D t
      = ENNReal.ofReal (Real.exp (2 * θ * t)) *
          (ENNReal.ofReal (Real.exp (-(2 * θ * t))) * diagram G (covEps Γ ε) α₀ m n D t) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        simp
    _ ≤ _ := by gcongr

end Bridge

/-- **`M4BridgeTarget` for finite Green densities** (TeX 1993-2033): the frozen statement
`PairingInterface.M4BridgeTarget` with the one added hypothesis that the density takes finite
values (`g s x ≠ ∞`; true for `green1`, `green2` and every `ofReal` density).  The frozen
target quantifies over all measurable `g : ℝ → ℝ^d → [0,∞]`; with infinite values the measures
`G_s = g(s,·) dy` need not be σ-finite, and Mathlib's `Measure.pi` of non-σ-finite factors is not
the product density (`pi_withDensity` needs σ-finiteness).  This is reported against the
interface; the interface was amended accordingly (L17 interface amendment 1, `m4_bridge`). -/
theorem m4_bridge_of_ne_top {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha α₀ Γ μ) (ε : ℝ) (hε : 0 < ε) :
    ∃ E : EdgeData d, E.A = Ioi 0 ∧ E.μ = smoothSpec μ ε ∧
      ∀ (G : ℝ → Measure (Rd d)) (g : Kernel d), Measurable (Function.uncurry g) →
        (∀ s x, g s x ≠ ∞) → (∀ s, G s = volume.withDensity (g s)) →
        ∀ (m n : ℕ) (D : Fin (m + n) → Fin (m + n)), D ∈ Pi2 m n →
        ∀ t θ : ℝ, 0 < t → 0 ≤ θ →
          diagram G (covEps Γ ε) α₀ m n D t ≤
            ENNReal.ofReal (Real.exp (2 * θ * t)) *
              pairingIntegral α₀ (m4Chain m n D) (fun _ => E) (fun _ => damp θ g) :=
  ⟨smoothEdge hH hε, rfl, rfl, fun G g hg hfin hG _ _ _ hD _ _ ht hθ =>
    diagram_le_pairingIntegral hH hε G g hg hfin hG hD ht hθ⟩

/-- **The M4 → `I_D` bridge, `M4BridgeTarget d`** (as amended 2026-11-20, L17 interface
amendment 1; TeX lines 1993-2033 at revision edf7085f (book 1.1.3)). -/
theorem m4_bridge (d : ℕ) : M4BridgeTarget d := by
  intro alpha α₀ Γ μ hH ε hε
  obtain ⟨E, hA, hμ, hE⟩ := m4_bridge_of_ne_top hH ε hε
  exact ⟨E, hA, hμ, fun G g hg hfin hG => hE G g hg hfin hG⟩

end StratonovichHAMSecondMoment.PairingBridge
