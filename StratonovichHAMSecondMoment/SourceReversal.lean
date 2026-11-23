module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L19, item C (second half): the chain reversal at positive widths (`TerminalReversalTarget`)
and the headline `TerminalMixedMomentTarget` (mixed moments of the positive-width terminal
integrals are M8 diagram sums).

TeX anchors (main file `notes/notes_stratonovich_ham_second_moment.tex` at revision 0788ddee
(book 1.1.0; the same line numbers at edf7085f, book 1.1.3), read with
`git show 0788ddee:notes/<file>.tex`):
* `P:mixed` Step 2, TeX lines 885-905: `s'_j = t - s_{m+1-j}`, `y'_j = x - y_{m+1-j}` on each
  chain (889-894), "Each transformed chain has initial root `(0,0)`" (893-894), "The differences in
  each covariance change sign, absorbed by evenness" (896-897), the vertex involution `ρ`
  (899-900), the pairing bijection `D ↦ ρDρ` (902-903), "The same transformation holds before
  removing noise smoothing" (903);
* `E:terminal-chain-measure`, TeX lines 4275-4288 (the terminal chain measures `g_n^{t,x}`);
* M8's diagram `F_{ε,δ,D}(t,t)`, TeX lines 1876-1881, with `J_{ε,D}` 1666-1669.

Route (disclosed): the identity is proved as an equality of Lebesgue integrals in `ℝ≥0∞`.  The
two terminal chains are written in time-and-unit-Green coordinates (`chainMeasureRaw`), joined
into one `(m+n)`-vertex configuration (`Fin.append`, measure preserving), and the M8 side is
brought to the same coordinates by the gap map `incr` (determinant one,
`JointFixedOrder.measurePreserving_incr`) and the affine reflection-reversal
`s ↦ (t - s_{ρ(k)})_k` (measure preserving), with the unit Green variables permuted by `ρ`.
The reversed cumulative times are `t - s_i` (the TeX's `s'`), the reversed positions `x - y_i`
(the TeX's `y'`), and the pair products agree pair by pair under `D ↦ ρDρ` (evenness of `κ` and
of `γ`).  The terminal-adjacent vertices `m-1` and `m+n-1` (0-based) go under `ρ = rev m n` to the
roots `0` and `m` of the initial chains (`incr_refl_rev`: their gaps are `t - s_{m-1}`,
`t - s_{m+n-1}`).  Measure-theoretic finiteness: every factor is bounded at positive widths and the chain
measures are finite, so `F_{ε∘ρ,δ∘ρ,ρDρ}(t,t) < ∞`.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.SourceWick

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace StratonovichHAMSecondMoment.SourceReversal

universe u

open HomogHypothesis (Rd HomogCovariance)
open WaveGreen (waveGreen)
open FiniteWick (pairWeight)
open TerminalWick (Pt chainWeightReal)
open TerminalWickInputs (chainMeasure chainMeasureRaw chainMap chainPoint timeMeasure gap toPt
  OpenSimplex)
open WickInterface (kerA capSet capDom wickF wickJ pairTime covW posOrthant horizon gapTime)
open LowAlphaConvolution (gammaEps)
open DiagramModel (Pi2 openers covEps rev revPairing SameChain pred predVal incr pos twoSimplex)
open SourceInterface SourceWick

variable {d : ℕ}

/-! ### Measure-preserving maps of tuples -/

section MeasurePreserving

variable {α : Type*} [MeasurableSpace α]

/-- Concatenation of tuples preserves the product measures. -/
theorem measurePreserving_append (μ : Measure α) [SigmaFinite μ] (m n : ℕ) :
    MeasurePreserving (fun p : (Fin m → α) × (Fin n → α) => Fin.append p.1 p.2)
      ((Measure.pi fun _ : Fin m => μ).prod (Measure.pi fun _ : Fin n => μ))
      (Measure.pi fun _ : Fin (m + n) => μ) := by
  refine ⟨TerminalWick.measurable_append, (Measure.pi_eq fun S hS => ?_).symm⟩
  rw [Measure.map_apply TerminalWick.measurable_append (MeasurableSet.univ_pi hS)]
  have hpre : (fun p : (Fin m → α) × (Fin n → α) => Fin.append p.1 p.2) ⁻¹' univ.pi S =
      (univ.pi fun j => S (Fin.castAdd n j)) ×ˢ (univ.pi fun j => S (Fin.natAdd m j)) := by
    ext p
    simp only [mem_preimage, mem_univ_pi, mem_prod]
    rw [Fin.forall_fin_add]
    simp only [Fin.append_left, Fin.append_right]
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, Fin.prod_univ_add]

/-- A permutation of the coordinates preserves a product measure. -/
theorem measurePreserving_perm (μ : Measure α) [SigmaFinite μ] {N : ℕ} (e : Fin N ≃ Fin N) :
    MeasurePreserving (fun v : Fin N → α => fun k => v (e k))
      (Measure.pi fun _ : Fin N => μ) (Measure.pi fun _ : Fin N => μ) := by
  have hm : Measurable fun v : Fin N → α => fun k => v (e k) :=
    measurable_pi_iff.mpr fun k => measurable_pi_apply (e k)
  refine ⟨hm, (Measure.pi_eq fun S hS => ?_).symm⟩
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hS)]
  have hpre : (fun v : Fin N → α => fun k => v (e k)) ⁻¹' univ.pi S =
      univ.pi fun i => S (e.symm i) := by
    ext v
    simp only [mem_preimage, mem_univ_pi]
    constructor
    · intro h i
      simpa using h (e.symm i)
    · intro h k
      simpa using h (e k)
  rw [hpre, Measure.pi_pi]
  exact Equiv.prod_comp e.symm fun i => μ (S i)

/-- Tonelli for a four-fold product: the middle factors may be exchanged. -/
theorem lintegral_prod_four {β γ δ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] (μa : Measure α) (μb : Measure β) (μc : Measure γ) (μd : Measure δ)
    [SFinite μa] [SFinite μb] [SFinite μc] [SFinite μd] {F : (α × β) × (γ × δ) → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ p, F p ∂((μa.prod μb).prod (μc.prod μd)) =
      ∫⁻ q, F ((q.1.1, q.2.1), (q.1.2, q.2.2)) ∂((μa.prod μc).prod (μb.prod μd)) := by
  have hF' : Measurable fun q : (α × γ) × (β × δ) => F ((q.1.1, q.2.1), (q.1.2, q.2.2)) :=
    hF.comp (f := fun q : (α × γ) × (β × δ) => ((q.1.1, q.2.1), (q.1.2, q.2.2))) (by fun_prop)
  rw [lintegral_prod _ hF.aemeasurable, lintegral_prod _ hF'.aemeasurable]
  have h1 : Measurable fun p : α × β => ∫⁻ r, F (p, r) ∂(μc.prod μd) := hF.lintegral_prod_right'
  have h2 : Measurable fun q : α × γ => ∫⁻ r, F ((q.1, r.1), (q.2, r.2)) ∂(μb.prod μd) :=
    hF'.lintegral_prod_right'
  rw [lintegral_prod _ h1.aemeasurable, lintegral_prod _ h2.aemeasurable]
  refine lintegral_congr fun a => ?_
  have e1 : ∀ b, ∫⁻ r, F ((a, b), r) ∂(μc.prod μd) = ∫⁻ c, ∫⁻ r, F ((a, b), (c, r)) ∂μd ∂μc :=
    fun b => lintegral_prod _ (hF.comp (f := fun r : γ × δ => ((a, b), r)) (by fun_prop)).aemeasurable
  have e2 : ∀ c, ∫⁻ r, F ((a, r.1), (c, r.2)) ∂(μb.prod μd) =
      ∫⁻ b, ∫⁻ r, F ((a, b), (c, r)) ∂μd ∂μb :=
    fun c => lintegral_prod _
      (hF.comp (f := fun r : β × δ => ((a, r.1), (c, r.2))) (by fun_prop)).aemeasurable
  simp only [e1, e2]
  refine lintegral_lintegral_swap ?_
  have hG : Measurable fun q : β × γ => ∫⁻ r, F ((a, q.1), (q.2, r)) ∂μd :=
    (hF.comp (f := fun w : (β × γ) × δ => ((a, w.1.1), (w.1.2, w.2))) (by fun_prop)).lintegral_prod_right'
  exact hG.aemeasurable

end MeasurePreserving

/-! ### The reversal involution as an equivalence; chains and the reversal -/

/-- `ρ` as a permutation. -/
def revEquiv (m n : ℕ) : Fin (m + n) ≃ Fin (m + n) where
  toFun := rev m n
  invFun := rev m n
  left_inv := DiagramModel.rev_rev m n
  right_inv := DiagramModel.rev_rev m n

theorem sameChain_rev_rev (m n : ℕ) (l i : Fin (m + n)) :
    SameChain m (rev m n l) (rev m n i) ↔ SameChain m l i := by
  have h1 := DiagramModel.sameChain_rev m n l
  have h2 := DiagramModel.sameChain_rev m n i
  unfold SameChain at h1 h2 ⊢
  rw [h1, h2]

theorem rev_le_rev (m n : ℕ) {l i : Fin (m + n)} (h : SameChain m l i) :
    rev m n l ≤ rev m n i ↔ i ≤ l := by
  have := l.isLt
  have := i.isLt
  unfold SameChain at h
  unfold rev
  split_ifs with h1 h2 h2 <;> simp only [Fin.le_def] <;> omega

/-- The first and second chain of a concatenated tuple. -/
def splitL {α : Type*} {m n : ℕ} (s : Fin (m + n) → α) : Fin m → α := fun j => s (Fin.castAdd n j)

def splitR {α : Type*} {m n : ℕ} (s : Fin (m + n) → α) : Fin n → α := fun j => s (Fin.natAdd m j)

theorem splitL_append {α : Type*} {m n : ℕ} (u : Fin m → α) (w : Fin n → α) :
    splitL (Fin.append u w) = u := funext fun j => Fin.append_left u w j

theorem splitR_append {α : Type*} {m n : ℕ} (u : Fin m → α) (w : Fin n → α) :
    splitR (Fin.append u w) = w := funext fun j => Fin.append_right u w j

theorem measurable_splitL {α : Type*} [MeasurableSpace α] {m n : ℕ} :
    Measurable (splitL (α := α) (m := m) (n := n)) :=
  measurable_pi_iff.mpr fun _ => measurable_pi_apply _

theorem measurable_splitR {α : Type*} [MeasurableSpace α] {m n : ℕ} :
    Measurable (splitR (α := α) (m := m) (n := n)) :=
  measurable_pi_iff.mpr fun _ => measurable_pi_apply _

/-- The reflected reversed times `u_k = t - s_{ρ(k)}` (the TeX's `s'`, 891). -/
def refl (m n : ℕ) (t : ℝ) (s : Fin (m + n) → ℝ) : Fin (m + n) → ℝ := fun k => t - s (rev m n k)

theorem measurePreserving_refl (m n : ℕ) (t : ℝ) :
    MeasurePreserving (refl m n t) volume volume := by
  have h1 : MeasurePreserving (fun s : Fin (m + n) → ℝ => fun k => s (revEquiv m n k))
      volume volume := measurePreserving_perm volume (revEquiv m n)
  have h2 : MeasurePreserving (fun s : Fin (m + n) → ℝ => fun k => t - s k) volume volume :=
    measurePreserving_pi (fun _ => volume) (fun _ => volume)
      (fun _ => Measure.measurePreserving_sub_left volume t)
  exact h2.comp h1

/-- The gaps of the two terminal chains, concatenated (`s_{j+1} - s_j`, `s_{m+1} = t`). -/
def gapN (m n : ℕ) (t : ℝ) (s : Fin (m + n) → ℝ) : Fin (m + n) → ℝ :=
  Fin.append (gap t (splitL s)) (gap t (splitR s))

theorem predVal_eq (m : ℕ) {N : ℕ} (f : Fin N → ℝ) (k : Fin N) :
    predVal m f k = if (k : ℕ) = 0 ∨ (k : ℕ) = m then 0 else
      f ⟨(k : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩ := by
  unfold predVal DiagramModel.pred
  split_ifs <;> rfl

theorem snoc_succ (t : ℝ) {m : ℕ} (s : Fin m → ℝ) (j : Fin m) :
    (Fin.snoc s t : Fin (m + 1) → ℝ) j.succ =
      if h : (j : ℕ) + 1 < m then s ⟨(j : ℕ) + 1, h⟩ else t := by
  split_ifs with h
  · have : j.succ = Fin.castSucc ⟨(j : ℕ) + 1, h⟩ := Fin.ext (by simp)
    rw [this, Fin.snoc_castSucc]
  · have : j.succ = Fin.last m := Fin.ext (by simp; omega)
    rw [this, Fin.snoc_last]

/-- **The gaps of the reversed chains are the terminal gaps** (TeX 894-896: "every other
factor becomes the corresponding successive increment"; the first factor `G(t - s_m, ·)`
becomes `G(s'_1, ·)`): `incr (t - s∘ρ) (ρ i) = s_{i+1} - s_i`, `s_{last+1} = t`. -/
theorem incr_refl_rev (m n : ℕ) (t : ℝ) (s : Fin (m + n) → ℝ) (i : Fin (m + n)) :
    incr m (refl m n t s) (rev m n i) = gapN m n t s i := by
  unfold incr gapN
  rw [predVal_eq]
  induction i using Fin.addCases with
  | left j =>
    rw [Fin.append_left]
    unfold gap refl
    rw [snoc_succ, DiagramModel.rev_rev]
    have hj := j.isLt
    have hr : ((rev m n (Fin.castAdd n j) : Fin (m + n)) : ℕ) = m - 1 - j := by
      unfold rev; simp [hj]
    split_ifs with h1 h2 h2
    · exfalso; rcases h1 with h1 | h1 <;> omega
    · simp only [splitL]; ring
    · have e : (⟨(rev m n (Fin.castAdd n j) : ℕ) - 1,
          lt_of_le_of_lt (Nat.sub_le _ _) (rev m n (Fin.castAdd n j)).isLt⟩ : Fin (m + n)) =
          rev m n (Fin.castAdd n ⟨(j : ℕ) + 1, h2⟩) := by
        ext; show ((rev m n (Fin.castAdd n j) : ℕ) - 1) = _; rw [hr]; unfold rev; simp only [Fin.val_castAdd]; split_ifs; simp; omega
      rw [e, DiagramModel.rev_rev]; simp only [splitL]; ring
    · exfalso; omega
  | right j =>
    rw [Fin.append_right]
    unfold gap refl
    rw [snoc_succ, DiagramModel.rev_rev]
    have hj := j.isLt
    have hr : ((rev m n (Fin.natAdd m j) : Fin (m + n)) : ℕ) = 2 * m + n - 1 - (m + j) := by
      unfold rev; simp
    split_ifs with h1 h2 h2
    · exfalso; rcases h1 with h1 | h1 <;> omega
    · simp only [splitR]; ring
    · have e : (⟨(rev m n (Fin.natAdd m j) : ℕ) - 1,
          lt_of_le_of_lt (Nat.sub_le _ _) (rev m n (Fin.natAdd m j)).isLt⟩ : Fin (m + n)) =
          rev m n (Fin.natAdd m ⟨(j : ℕ) + 1, h2⟩) := by
        ext; show ((rev m n (Fin.natAdd m j) : ℕ) - 1) = _; rw [hr]; unfold rev; simp only [Fin.val_natAdd]; split_ifs <;> simp <;> omega
      rw [e, DiagramModel.rev_rev]; simp only [splitR]; ring
    · exfalso; omega

/-! ### The ordered simplices and the time densities -/

theorem openSimplex_iff (t : ℝ) {m : ℕ} (s : Fin m → ℝ) :
    OpenSimplex t s ↔ ∀ j, 0 < s j ∧ 0 < gap t s j := by
  unfold OpenSimplex gap
  simp only [sub_pos]
  exact forall_and.symm

theorem mem_twoSimplex_refl (m n : ℕ) (t : ℝ) (s : Fin (m + n) → ℝ) :
    refl m n t s ∈ twoSimplex m n t ↔ ∀ i, 0 < s i ∧ 0 < gapN m n t s i := by
  have key : ∀ i, (predVal m (refl m n t s) (rev m n i) < refl m n t s (rev m n i) ∧
      refl m n t s (rev m n i) < t) ↔ (0 < s i ∧ 0 < gapN m n t s i) := by
    intro i
    rw [← incr_refl_rev]
    unfold incr
    have : refl m n t s (rev m n i) = t - s i := by
      unfold refl; rw [DiagramModel.rev_rev]
    rw [this]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  show (∀ k, predVal m (refl m n t s) k < refl m n t s k ∧ refl m n t s k < t) ↔ _
  constructor
  · intro h i; exact (key i).1 (h (rev m n i))
  · intro h k
    have := (key (rev m n k)).2 (h (rev m n k))
    rwa [DiagramModel.rev_rev] at this

theorem mem_twoSimplex_refl_iff_open (m n : ℕ) (t : ℝ) (s : Fin (m + n) → ℝ) :
    refl m n t s ∈ twoSimplex m n t ↔ OpenSimplex t (splitL s) ∧ OpenSimplex t (splitR s) := by
  rw [mem_twoSimplex_refl, openSimplex_iff, openSimplex_iff, Fin.forall_fin_add]
  simp only [gapN, Fin.append_left, Fin.append_right, splitL, splitR]

/-- The joint time density of the two terminal chains. -/
def rhoN (m n : ℕ) (t : ℝ) (s : Fin (m + n) → ℝ) : ℝ≥0∞ :=
  chainWeightReal m t (splitL s) * chainWeightReal n t (splitR s)

theorem measurable_rhoN (m n : ℕ) (t : ℝ) : Measurable (rhoN m n t) :=
  ((TerminalWickInputs.measurable_chainWeightReal_right m t).comp measurable_splitL).mul
    ((TerminalWickInputs.measurable_chainWeightReal_right n t).comp measurable_splitR)

theorem revEquiv_apply (m n : ℕ) (i : Fin (m + n)) : revEquiv m n i = rev m n i := rfl

theorem prod_incr_refl (m n : ℕ) (t : ℝ) (s : Fin (m + n) → ℝ) :
    ∏ k, ENNReal.ofReal (incr m (refl m n t s) k) =
      (∏ j, ENNReal.ofReal (gap t (splitL s) j)) * ∏ j, ENNReal.ofReal (gap t (splitR s) j) := by
  rw [← Equiv.prod_comp (revEquiv m n)]
  simp only [revEquiv_apply, incr_refl_rev]
  rw [Fin.prod_univ_add]
  simp only [gapN, Fin.append_left, Fin.append_right]

/-- The time density in reversed coordinates (TeX 894-896: the Green masses of the reversed
chains are the successive increments). -/
theorem rhoN_eq (m n : ℕ) (t : ℝ) (s : Fin (m + n) → ℝ) :
    rhoN m n t s = (twoSimplex m n t).indicator
      (fun u => ∏ k, ENNReal.ofReal (incr m u k)) (refl m n t s) := by
  classical
  unfold rhoN
  rw [TerminalWickInputs.chainWeightReal_eq_ite, TerminalWickInputs.chainWeightReal_eq_ite]
  by_cases h : refl m n t s ∈ twoSimplex m n t
  · obtain ⟨h1, h2⟩ := (mem_twoSimplex_refl_iff_open m n t s).1 h
    rw [indicator_of_mem h]; simp only [h1, h2, ↓reduceIte, prod_incr_refl]
  · rw [indicator_of_notMem h]
    rw [mem_twoSimplex_refl_iff_open, not_and_or] at h
    rcases h with h | h
    · simp only [h, ↓reduceIte, zero_mul]
    · simp only [h, ↓reduceIte, mul_zero]

/-! ### Positions of the reversed chains -/

/-- The concatenated terminal chains in time-and-unit-Green coordinates. -/
def Qpt (m n : ℕ) (t : ℝ) (x : Rd d) (s : Fin (m + n) → ℝ) (v : Fin (m + n) → Rd d) :
    Fin (m + n) → ℝ × Rd d :=
  Fin.append (chainMap t x (splitL s, splitL v)) (chainMap t x (splitR s, splitR v))

theorem measurable_Qpt (m n : ℕ) (t : ℝ) (x : Rd d) :
    Measurable fun p : (Fin (m + n) → ℝ) × (Fin (m + n) → Rd d) => Qpt m n t x p.1 p.2 := by
  have h1 : Measurable fun p : (Fin (m + n) → ℝ) × (Fin (m + n) → Rd d) =>
      (chainMap t x (splitL p.1, splitL p.2), chainMap t x (splitR p.1, splitR p.2)) :=
    ((TerminalWickInputs.measurable_chainMap t x).comp
      ((measurable_splitL.comp measurable_fst).prodMk (measurable_splitL.comp measurable_snd))).prodMk
    ((TerminalWickInputs.measurable_chainMap t x).comp
      ((measurable_splitR.comp measurable_fst).prodMk (measurable_splitR.comp measurable_snd)))
  exact TerminalWick.measurable_append.comp h1

theorem Qpt_fst (m n : ℕ) (t : ℝ) (x : Rd d) (s : Fin (m + n) → ℝ) (v : Fin (m + n) → Rd d)
    (i : Fin (m + n)) : (Qpt m n t x s v i).1 = s i := by
  unfold Qpt
  induction i using Fin.addCases with
  | left j => rw [Fin.append_left]; rfl
  | right j => rw [Fin.append_right]; rfl

/-- **The reversed positions** (TeX 891: `y'_j = x - y_{m+1-j}`): the M8 position of the
reversed vertex `ρ(i)`, built from the increments `r_k v_{ρ(k)}`, is `x - y_i`. -/
theorem pos_refl (m n : ℕ) (t : ℝ) (x : Rd d) (s : Fin (m + n) → ℝ) (v : Fin (m + n) → Rd d)
    (i : Fin (m + n)) :
    pos m (fun k => incr m (refl m n t s) k • v (rev m n k)) (rev m n i) =
      x - (Qpt m n t x s v i).2 := by
  unfold pos
  rw [Finset.sum_filter, ← Equiv.sum_comp (revEquiv m n)]
  have hl : ∀ l, (if SameChain m (revEquiv m n l) (rev m n i) ∧ revEquiv m n l ≤ rev m n i then
      incr m (refl m n t s) (revEquiv m n l) • v (rev m n (revEquiv m n l)) else 0) =
      if SameChain m l i ∧ i ≤ l then gapN m n t s l • v l else 0 := by
    intro l
    show (if SameChain m (rev m n l) (rev m n i) ∧ rev m n l ≤ rev m n i then
      incr m (refl m n t s) (rev m n l) • v (rev m n (rev m n l)) else 0) = _
    rw [incr_refl_rev, DiagramModel.rev_rev]
    by_cases hsc : SameChain m l i
    · simp only [sameChain_rev_rev, rev_le_rev m n hsc]
    · simp [sameChain_rev_rev, hsc]
  rw [Finset.sum_congr rfl fun l _ => hl l, Fin.sum_univ_add]
  unfold Qpt
  induction i using Fin.addCases with
  | left j =>
    rw [Fin.append_left]
    have h2 : ∀ l : Fin n, (if SameChain m (Fin.natAdd m l) (Fin.castAdd n j) ∧
        Fin.castAdd n j ≤ Fin.natAdd m l then gapN m n t s (Fin.natAdd m l) • v (Fin.natAdd m l)
        else 0) = 0 := by
      intro l
      exact ite_eq_right_iff.2 fun h => absurd h.1 (by unfold SameChain; simp)
    simp only [h2, Finset.sum_const_zero, add_zero]
    show _ = x - (x - ∑ l ∈ Finset.univ.filter (fun l => j ≤ l), gap t (splitL s) l • splitL v l)
    rw [sub_sub_cancel, Finset.sum_filter]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hs : SameChain m (Fin.castAdd n l) (Fin.castAdd n j) := by unfold SameChain; simp
    simp only [hs, true_and, Fin.le_def, Fin.val_castAdd, gapN, Fin.append_left]
    rfl
  | right j =>
    rw [Fin.append_right]
    have h1 : ∀ l : Fin m, (if SameChain m (Fin.castAdd n l) (Fin.natAdd m j) ∧
        Fin.natAdd m j ≤ Fin.castAdd n l then gapN m n t s (Fin.castAdd n l) • v (Fin.castAdd n l)
        else 0) = 0 := by
      intro l
      exact ite_eq_right_iff.2 fun h => absurd h.1 (by unfold SameChain; simp)
    simp only [h1, Finset.sum_const_zero, zero_add]
    show _ = x - (x - ∑ l ∈ Finset.univ.filter (fun l => j ≤ l), gap t (splitR s) l • splitR v l)
    rw [sub_sub_cancel, Finset.sum_filter]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hs : SameChain m (Fin.natAdd m l) (Fin.natAdd m j) := by unfold SameChain; simp
    simp only [hs, true_and, Fin.natAdd_le_natAdd_iff, gapN, Fin.append_right]
    rfl

/-! ### Pairs under the reversal -/

/-- The product over the pairs of `ρDρ` is the product over the pairs of `D` (TeX 902-903:
"It induces the pairing bijection `D ↦ {{ρ(a), ρ(b)} : {a,b} ∈ D}`"), for a symmetric factor. -/
theorem prod_openers_revPairing {M : Type*} [CommMonoid M] {m n : ℕ}
    {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n) (f : Fin (m + n) → Fin (m + n) → M)
    (hf : ∀ i j, f i j = f j i) :
    ∏ k ∈ openers (revPairing m n D), f (rev m n k) (D (rev m n k)) =
      ∏ i ∈ openers D, f i (D i) := by
  have hD' := DiagramModel.mem_Pi2.1 hD
  have hrr := DiagramModel.rev_rev m n
  have hinj : ∀ a b, rev m n a = rev m n b → a = b := fun a b h => by
    rw [← hrr a, ← hrr b, h]
  have hR : ∀ k, revPairing m n D k = rev m n (D (rev m n k)) := fun k => rfl
  have mem : ∀ {E : Fin (m + n) → Fin (m + n)} {k}, k ∈ openers E ↔ k < E k := by
    intro E k; simp [openers]
  refine Finset.prod_nbij'
    (fun k => if rev m n k < D (rev m n k) then rev m n k else D (rev m n k))
    (fun i => if rev m n i < rev m n (D i) then rev m n i else rev m n (D i)) ?_ ?_ ?_ ?_ ?_
  · intro k _
    simp only [mem]
    split_ifs with h
    · exact h
    · rw [(hD' _).2]
      exact lt_of_le_of_ne (not_lt.1 h) (hD' _).1
  · intro i _
    simp only [mem]
    split_ifs with h
    · rw [hR, hrr]; exact h
    · rw [hR, hrr, (hD' i).2]
      refine lt_of_le_of_ne (not_lt.1 h) fun he => (hD' i).1 (hinj _ _ he)
  · intro k hk
    simp only [mem, hR] at hk
    by_cases h : rev m n k < D (rev m n k)
    · simp only [h, hrr, hk, ↓reduceIte]
    · simp only [h, (hD' _).2, hrr, not_lt.2 hk.le, ↓reduceIte]
  · intro i hi
    simp only [mem] at hi
    by_cases h : rev m n i < rev m n (D i)
    · simp only [h, hrr, hi, ↓reduceIte]
    · simp only [h, hrr, (hD' i).2, not_lt.2 hi.le, ↓reduceIte]
  · intro k _
    split_ifs with h
    · rfl
    · rw [(hD' _).2]; exact hf _ _

/-! ### The integrands agree (TeX 893-903) -/

section Integrand

variable {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}

theorem kerA_neg (a : ℝ) (S : Set ℝ) (u : ℝ) : kerA a S (-u) = kerA a S u := by
  unfold kerA; rw [abs_neg]

theorem covEps_neg (hH : HomogCovariance d alpha α₀ Γ μ) {e : ℝ} (he : 0 < e) (y : Rd d) :
    covEps Γ e (-y) = covEps Γ e y := by
  rw [covEps_eq hH he, covEps_eq hH he, LowAlphaUpper.gammaEps_neg hH.Γ_even]

/-- The terminal pairing integrand in time-and-position coordinates (times moved into `[0,t]`,
the identity on the support). -/
def phiRaw (α₀ : ℝ) (Γ : Measure (Rd d)) {N : ℕ} (c : Fin N → PosW) (D : Fin N → Fin N) (t : ℝ)
    (ht : 0 ≤ t) (z : Fin N → ℝ × Rd d) : ℝ≥0∞ :=
  pairPhi α₀ Γ c D (fun i => (Set.projIcc 0 t ht (z i).1 : ℝ)) (fun i => (z i).2)

theorem measurable_phiRaw (hH : HomogCovariance d alpha α₀ Γ μ) {N : ℕ} (c : Fin N → PosW)
    (D : Fin N → Fin N) (t : ℝ) (ht : 0 ≤ t) : Measurable (phiRaw α₀ Γ c D t ht) := by
  have h : Measurable fun z : Fin N → ℝ × Rd d =>
      ((fun i => (Set.projIcc 0 t ht (z i).1 : ℝ)), (fun i => (z i).2)) := by
    refine (measurable_pi_iff.mpr fun i => ?_).prodMk (measurable_pi_iff.mpr fun i => ?_)
    · exact (continuous_subtype_val.comp continuous_projIcc).measurable.comp
        (measurable_fst.comp (measurable_pi_apply i))
    · exact measurable_snd.comp (measurable_pi_apply i)
  have e : phiRaw α₀ Γ c D t ht =
      (fun q : (Fin N → ℝ) × (Fin N → Rd d) => pairPhi α₀ Γ c D q.1 q.2) ∘
        (fun z : Fin N → ℝ × Rd d =>
          ((fun i => (Set.projIcc 0 t ht (z i).1 : ℝ)), (fun i => (z i).2))) := by
    funext z; rfl
  rw [e]
  exact (measurable_pairPhi hH c D).comp h

/-- **The M8 integrand at the reversed configuration is the terminal pairing integrand**
(TeX 893-903: the differences change sign, absorbed by evenness; the pairs correspond under
`D ↦ ρDρ`). -/
theorem integrand_eq (hH : HomogCovariance d alpha α₀ Γ μ) {m n : ℕ}
    {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n) (a : Fin m → PosW) (b : Fin n → PosW)
    (t : ℝ) (ht : 0 ≤ t) (x : Rd d) (s : Fin (m + n) → ℝ) (hs : refl m n t s ∈ twoSimplex m n t)
    (v : Fin (m + n) → Rd d) :
    pairTime α₀ (capDom fun i => delV a b (rev m n i)) m (revPairing m n D)
        (incr m (refl m n t s)) *
      covW Γ (fun i => epsV a b (rev m n i)) (revPairing m n D)
        (pos m fun k => incr m (refl m n t s) k • v (rev m n k)) =
      phiRaw α₀ Γ (Fin.append a b) D t ht (Qpt m n t x s v) := by
  set c := Fin.append a b with hc
  set Y : Fin (m + n) → Rd d := fun i => (Qpt m n t x s v i).2 with hY
  set P := pos m fun k => incr m (refl m n t s) k • v (rev m n k) with hP
  have hPY : ∀ i, P (rev m n i) = x - Y i := fun i => pos_refl m n t x s v i
  have hpos := (mem_twoSimplex_refl m n t s).1 hs
  have hsI : ∀ i, s i ∈ Icc 0 t := by
    intro i
    have h2 := (hs (rev m n i)).2
    have h1 := DiagramModel.pos_of_mem_twoSimplex hs (rev m n i)
    unfold refl at h1 h2
    rw [DiagramModel.rev_rev] at h1 h2
    exact ⟨(hpos i).1.le, by linarith⟩
  set f : Fin (m + n) → Fin (m + n) → ℝ≥0∞ := fun i j =>
    kerA α₀ (capSet (max (c i).del (c j).del)) (s i - s j) *
      covEps Γ ((c i).eps + (c j).eps) (Y i - Y j) with hf
  have hfs : ∀ i j, f i j = f j i := by
    intro i j
    simp only [hf]
    rw [max_comm, add_comm (c j).eps, ← neg_sub (s j), kerA_neg, ← neg_sub (Y j),
      covEps_neg hH (add_pos (c i).eps_pos (c j).eps_pos)]
  unfold pairTime covW
  rw [← Finset.prod_mul_distrib]
  simp only [WickInterface.gapTime_incr]
  have hlhs : ∀ k ∈ openers (revPairing m n D),
      kerA α₀ (capDom (fun i => delV a b (rev m n i)) s(k, revPairing m n D k))
          (refl m n t s k - refl m n t s (revPairing m n D k)) *
        covEps Γ (epsV a b (rev m n k) + epsV a b (rev m n (revPairing m n D k)))
          (P k - P (revPairing m n D k)) = f (rev m n k) (D (rev m n k)) := by
    intro k _
    have e1 : revPairing m n D k = rev m n (D (rev m n k)) := rfl
    have e2 : P k = x - Y (rev m n k) := by rw [← hPY, DiagramModel.rev_rev]
    rw [e1, e2, hPY]
    simp only [hf, WickInterface.capDom_mk, delV, epsV, refl, DiagramModel.rev_rev]
    rw [show t - s (rev m n k) - (t - s (D (rev m n k))) = -(s (rev m n k) - s (D (rev m n k)))
      by ring, kerA_neg,
      show x - Y (rev m n k) - (x - Y (D (rev m n k))) = -(Y (rev m n k) - Y (D (rev m n k)))
      by abel, covEps_neg hH (add_pos (c _).eps_pos (c _).eps_pos)]
  rw [Finset.prod_congr rfl hlhs, prod_openers_revPairing hD f hfs]
  unfold phiRaw pairPhi
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [hf, Qpt_fst, Set.projIcc_of_mem _ (hsI _)]
  rfl

end Integrand

/-! ### The terminal side in time-and-unit-Green coordinates -/

section Integrals

variable {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}

theorem isFiniteMeasure_raw (d n : ℕ) (t : ℝ) (ht : 0 ≤ t) (x : Rd d) :
    IsFiniteMeasure (chainMeasureRaw d n t x) := by
  have : ∀ s, IsFiniteMeasure (waveGreen d s) := WaveGreen.isFiniteMeasure_waveGreen d
  constructor
  rw [TerminalWickInputs.chainMeasureRaw_univ_eq, TerminalWick.chainMassReal_eq n t ht]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.prod_lt_top fun _ _ => measure_lt_top _ _)

theorem chainS_toPt {t : ℝ} (ht : 0 ≤ t) {m n : ℕ} (z₁ : Fin m → ℝ × Rd d)
    (z₂ : Fin n → ℝ × Rd d) :
    chainS (toPt ht z₁, toPt ht z₂) = fun i => (Set.projIcc 0 t ht (Fin.append z₁ z₂ i).1 : ℝ) := by
  funext i
  unfold chainS
  induction i using Fin.addCases with
  | left j => simp only [Fin.append_left]; rfl
  | right j => simp only [Fin.append_right]; rfl

theorem chainY_toPt {t : ℝ} (ht : 0 ≤ t) {m n : ℕ} (z₁ : Fin m → ℝ × Rd d)
    (z₂ : Fin n → ℝ × Rd d) :
    chainY (toPt ht z₁, toPt ht z₂) = fun i => (Fin.append z₁ z₂ i).2 := by
  funext i
  unfold chainY
  induction i using Fin.addCases with
  | left j => simp only [Fin.append_left]; rfl
  | right j => simp only [Fin.append_right]; rfl

theorem measurable_pairPhi_chain (hH : HomogCovariance d alpha α₀ Γ μ) {t : ℝ} {m n : ℕ}
    (c : Fin (m + n) → PosW) (D : Fin (m + n) → Fin (m + n)) :
    Measurable fun q : (Fin m → Pt d t) × (Fin n → Pt d t) =>
      pairPhi α₀ Γ c D (chainS q) (chainY q) :=
  (measurable_pairPhi hH c D).comp
    (f := fun q : (Fin m → Pt d t) × (Fin n → Pt d t) => (chainS q, chainY q)) measurable_chainSY

/-- **The terminal pairing integral in reversed-ready coordinates**: the integral over
`g_m^{t,x} ⊗ g_n^{t,x}` is the integral over the joint times (density `rhoN`, the two ordered
simplices with the Green masses) and the unit Green variables `G_1^{⊗(m+n)}`. -/
theorem lhs_lintegral (hH : HomogCovariance d alpha α₀ Γ μ) (t : ℝ) (ht : 0 ≤ t) (x : Rd d)
    {m n : ℕ} (c : Fin (m + n) → PosW) (D : Fin (m + n) → Fin (m + n)) :
    ∫⁻ q, pairPhi α₀ Γ c D (chainS q) (chainY q)
        ∂((chainMeasure d m t ht x).prod (chainMeasure d n t ht x)) =
      ∫⁻ s, rhoN m n t s * ∫⁻ v, phiRaw α₀ Γ c D t ht (Qpt m n t x s v)
        ∂(Measure.pi fun _ : Fin (m + n) => waveGreen d 1) := by
  have : ∀ s, IsFiniteMeasure (waveGreen d s) := WaveGreen.isFiniteMeasure_waveGreen d
  have := isFiniteMeasure_raw d m t ht x
  have := isFiniteMeasure_raw d n t ht x
  have hTs : ∀ k, SFinite (timeMeasure k t) := fun k => by unfold timeMeasure; infer_instance
  set G := waveGreen d 1 with hGdef
  have hF := measurable_pairPhi_chain (t := t) (m := m) (n := n) hH c D
  have hP := measurable_phiRaw hH c D t ht
  have hQ := measurable_Qpt (d := d) m n t x
  have hcm := TerminalWickInputs.measurable_chainMap (d := d) (n := m) t x
  have hcn := TerminalWickInputs.measurable_chainMap (d := d) (n := n) t x
  have hpm := TerminalWickInputs.measurable_toPt (d := d) (n := m) ht
  have hpn := TerminalWickInputs.measurable_toPt (d := d) (n := n) ht
  -- the integrand after the two maps, as a function of the two raw chains
  set H : ((Fin m → ℝ) × (Fin m → Rd d)) × ((Fin n → ℝ) × (Fin n → Rd d)) → ℝ≥0∞ :=
    fun p => phiRaw α₀ Γ c D t ht (Fin.append (chainMap t x p.1) (chainMap t x p.2)) with hH'
  have hHm : Measurable H := hP.comp (f := fun p : ((Fin m → ℝ) × (Fin m → Rd d)) ×
      ((Fin n → ℝ) × (Fin n → Rd d)) => Fin.append (chainMap t x p.1) (chainMap t x p.2))
    (TerminalWick.measurable_append.comp ((hcm.comp measurable_fst).prodMk
      (hcn.comp measurable_snd)))
  have hpt : ∀ z₁ z₂, pairPhi α₀ Γ c D (chainS (toPt ht z₁, toPt ht z₂))
      (chainY (toPt ht z₁, toPt ht z₂)) = phiRaw α₀ Γ c D t ht (Fin.append z₁ z₂) := by
    intro z₁ z₂; rw [chainS_toPt, chainY_toPt]; rfl
  -- step 1: the two chain measures as images of the raw ones, then of time × Green
  have step1 : ∫⁻ q, pairPhi α₀ Γ c D (chainS q) (chainY q)
      ∂((chainMeasure d m t ht x).prod (chainMeasure d n t ht x)) =
      ∫⁻ p, H p ∂(((timeMeasure m t).prod (Measure.pi fun _ : Fin m => G)).prod
        ((timeMeasure n t).prod (Measure.pi fun _ : Fin n => G))) := by
    rw [lintegral_prod _ hF.aemeasurable, lintegral_prod _ hHm.aemeasurable]
    unfold chainMeasure
    rw [lintegral_map (hF.lintegral_prod_right') hpm]
    unfold chainMeasureRaw
    have hin : Measurable fun z₁ : Fin m → ℝ × Rd d =>
        ∫⁻ z₂, phiRaw α₀ Γ c D t ht (Fin.append z₁ z₂)
          ∂((timeMeasure n t).prod (Measure.pi fun _ : Fin n => G)).map (chainMap t x) :=
      (hP.comp (f := fun w : (Fin m → ℝ × Rd d) × (Fin n → ℝ × Rd d) => Fin.append w.1 w.2)
        TerminalWick.measurable_append).lintegral_prod_right'
    have e1 : ∀ z₁ : Fin m → ℝ × Rd d,
        ∫⁻ z₂, pairPhi α₀ Γ c D (chainS (toPt ht z₁, z₂)) (chainY (toPt ht z₁, z₂))
          ∂(((timeMeasure n t).prod (Measure.pi fun _ : Fin n => G)).map (chainMap t x)).map
            (toPt ht) =
        ∫⁻ z₂, phiRaw α₀ Γ c D t ht (Fin.append z₁ z₂)
          ∂((timeMeasure n t).prod (Measure.pi fun _ : Fin n => G)).map (chainMap t x) := by
      intro z₁
      have hf1 : Measurable fun z₂ : Fin n → Pt d t =>
          pairPhi α₀ Γ c D (chainS (toPt ht z₁, z₂)) (chainY (toPt ht z₁, z₂)) :=
        hF.comp (f := fun z₂ : Fin n → Pt d t => (toPt ht z₁, z₂)) (by fun_prop)
      rw [lintegral_map hf1 hpn]
      exact lintegral_congr fun z₂ => hpt z₁ z₂
    refine (lintegral_congr fun z₁ => e1 z₁).trans ?_
    rw [lintegral_map hin hcm]
    refine lintegral_congr fun p₁ => ?_
    have hf2 : Measurable fun z₂ : Fin n → ℝ × Rd d =>
        phiRaw α₀ Γ c D t ht (Fin.append (chainMap t x p₁) z₂) :=
      hP.comp (f := fun z₂ : Fin n → ℝ × Rd d => Fin.append (chainMap t x p₁) z₂) (by fun_prop)
    exact lintegral_map hf2 hcn
  have hH4 : Measurable fun q : ((Fin m → ℝ) × (Fin n → ℝ)) × ((Fin m → Rd d) × (Fin n → Rd d)) =>
      H ((q.1.1, q.2.1), (q.1.2, q.2.2)) :=
    hHm.comp (f := fun q : ((Fin m → ℝ) × (Fin n → ℝ)) × ((Fin m → Rd d) × (Fin n → Rd d)) =>
      ((q.1.1, q.2.1), (q.1.2, q.2.2))) (by fun_prop)
  rw [step1, lintegral_prod_four _ _ _ _ hHm, lintegral_prod _ hH4.aemeasurable]
  unfold timeMeasure
  rw [prod_withDensity (TerminalWickInputs.measurable_chainWeightReal_right m t)
    (TerminalWickInputs.measurable_chainWeightReal_right n t)]
  have hin2 : Measurable fun s12 : (Fin m → ℝ) × (Fin n → ℝ) =>
      ∫⁻ v12, H ((s12.1, v12.1), (s12.2, v12.2))
        ∂((Measure.pi fun _ : Fin m => G).prod (Measure.pi fun _ : Fin n => G)) :=
    hH4.lintegral_prod_right'
  refine (lintegral_withDensity_eq_lintegral_mul _
    (((TerminalWickInputs.measurable_chainWeightReal_right m t).comp measurable_fst).mul
      ((TerminalWickInputs.measurable_chainWeightReal_right n t).comp measurable_snd)) hin2).trans
    ?_
  -- step 2: the inner Green integral over `G_1^{⊗(m+n)}`
  have inner : ∀ s12 : (Fin m → ℝ) × (Fin n → ℝ),
      ∫⁻ v12, H ((s12.1, v12.1), (s12.2, v12.2))
        ∂((Measure.pi fun _ : Fin m => G).prod (Measure.pi fun _ : Fin n => G)) =
      ∫⁻ v, phiRaw α₀ Γ c D t ht (Qpt m n t x (Fin.append s12.1 s12.2) v)
        ∂(Measure.pi fun _ : Fin (m + n) => G) := by
    intro s12
    have hg : Measurable fun v : Fin (m + n) → Rd d =>
        phiRaw α₀ Γ c D t ht (Qpt m n t x (Fin.append s12.1 s12.2) v) :=
      hP.comp (f := fun v => Qpt m n t x (Fin.append s12.1 s12.2) v)
        (hQ.comp (f := fun v => (Fin.append s12.1 s12.2, v)) (by fun_prop))
    refine Eq.trans ?_ ((measurePreserving_append G m n).lintegral_comp hg)
    refine lintegral_congr fun v12 => ?_
    simp only [hH', Qpt, splitL_append, splitR_append]
  -- step 3: the joint times over Lebesgue measure on `ℝ^{m+n}`
  have hK : Measurable fun s : Fin (m + n) → ℝ =>
      rhoN m n t s * ∫⁻ v, phiRaw α₀ Γ c D t ht (Qpt m n t x s v)
        ∂(Measure.pi fun _ : Fin (m + n) => G) :=
    (measurable_rhoN m n t).mul (hP.comp (f := fun p : (Fin (m + n) → ℝ) × (Fin (m + n) → Rd d) =>
      Qpt m n t x p.1 p.2) hQ).lintegral_prod_right'
  refine Eq.trans ?_ ((measurePreserving_append (volume : Measure ℝ) m n).lintegral_comp hK)
  refine lintegral_congr fun s12 => ?_
  simp only [Pi.mul_apply, Function.comp_apply]
  rw [inner]
  simp only [rhoN, splitL_append, splitR_append]

/-- **The M8 side in the same coordinates**: `F_{ε∘ρ,δ∘ρ,ρDρ}(t,t)` after the gap map `incr`
and the reflection-reversal `refl`. -/
theorem rhs_lintegral (hH : HomogCovariance d alpha α₀ Γ μ) (t : ℝ) (ht : 0 < t) {m n : ℕ}
    (a : Fin m → PosW) (b : Fin n → PosW) (D : Fin (m + n) → Fin (m + n)) :
    wickF (waveGreen d) Γ α₀ (capDom fun i => delV a b (rev m n i))
        (fun i => epsV a b (rev m n i)) m (revPairing m n D) t t =
      ∫⁻ s, (twoSimplex m n t).indicator (fun u =>
        pairTime α₀ (capDom fun i => delV a b (rev m n i)) m (revPairing m n D) (incr m u) *
          JointFixedOrder.wickJm Γ (fun i => epsV a b (rev m n i)) m (revPairing m n D)
            (incr m u)) (refl m n t s) := by
  have hε : ∀ i, 0 < epsV a b (rev m n i) := fun i => (Fin.append a b (rev m n i)).eps_pos
  set g0 : (Fin (m + n) → ℝ) → ℝ≥0∞ := fun r =>
    pairTime α₀ (capDom fun i => delV a b (rev m n i)) m (revPairing m n D) r *
      JointFixedOrder.wickJm Γ (fun i => epsV a b (rev m n i)) m (revPairing m n D) r with hg0
  have hg0m : Measurable g0 := (JointFixedOrder.measurable_pairTime α₀ _ m _).mul
    (JointFixedOrder.measurable_wickJm hH hε m _)
  have hS : MeasurableSet (posOrthant (m + n) ∩ horizon m t t) :=
    (JointFixedOrder.measurableSet_posOrthant _).inter (JointFixedOrder.measurableSet_horizon m t t)
  rw [JointFixedOrder.wickF_eq_lintegral hH hε α₀ _ m _ t t]
  rw [setLIntegral_congr_fun hS (g := g0) fun r hr => by
    simp only [hg0]
    rw [JointFixedOrder.wickJ_eq_wickJm hH hε m _ fun i => hr.1 i (mem_univ i)]]
  rw [← lintegral_indicator hS]
  have hind : Measurable ((posOrthant (m + n) ∩ horizon m t t).indicator g0) := hg0m.indicator hS
  rw [← (JointFixedOrder.measurePreserving_incr m (m + n)).lintegral_comp hind]
  have hpre := JointFixedOrder.incr_preimage (m := m) (n := n) ht
  have e : ∀ u, (posOrthant (m + n) ∩ horizon m t t).indicator g0 (incr m u) =
      (twoSimplex m n t).indicator (fun u => g0 (incr m u)) u := by
    intro u
    by_cases hu : u ∈ twoSimplex m n t
    · have : incr m u ∈ posOrthant (m + n) ∩ horizon m t t := by
        rw [← hpre] at hu; exact hu
      rw [indicator_of_mem this, indicator_of_mem hu]
    · have : incr m u ∉ posOrthant (m + n) ∩ horizon m t t := by
        rw [← hpre] at hu; exact hu
      rw [indicator_of_notMem this, indicator_of_notMem hu]
  simp_rw [e]
  have hind2 : Measurable ((twoSimplex m n t).indicator fun u => g0 (incr m u)) :=
    (hg0m.comp (DiagramModel.measurable_incr m)).indicator (DiagramModel.measurableSet_twoSimplex m n t)
  rw [← (measurePreserving_refl m n t).lintegral_comp hind2]

/-- **The reversal as an identity of `ℝ≥0∞` integrals** (TeX 888-905). -/
theorem lintegral_reversal (hH : HomogCovariance d alpha α₀ Γ μ) (t : ℝ) (ht : 0 < t)
    (x : Rd d) {m n : ℕ} (a : Fin m → PosW) (b : Fin n → PosW) {D : Fin (m + n) → Fin (m + n)}
    (hD : D ∈ Pi2 m n) :
    ∫⁻ q, pairPhi α₀ Γ (Fin.append a b) D (chainS q) (chainY q)
        ∂((chainMeasure d m t ht.le x).prod (chainMeasure d n t ht.le x)) =
      wickF (waveGreen d) Γ α₀ (capDom fun i => delV a b (rev m n i))
        (fun i => epsV a b (rev m n i)) m (revPairing m n D) t t := by
  have : ∀ s, IsFiniteMeasure (waveGreen d s) := WaveGreen.isFiniteMeasure_waveGreen d
  have hε : ∀ i, 0 < epsV a b (rev m n i) := fun i => (Fin.append a b (rev m n i)).eps_pos
  rw [lhs_lintegral hH t ht.le x, rhs_lintegral hH t ht a b D]
  refine lintegral_congr fun s => ?_
  rw [rhoN_eq]
  by_cases hs : refl m n t s ∈ twoSimplex m n t
  · rw [indicator_of_mem hs, indicator_of_mem hs]
    set r := incr m (refl m n t s) with hr
    unfold JointFixedOrder.wickJm
    have hcov : Measurable fun w : Fin (m + n) → Rd d =>
        covW Γ (fun i => epsV a b (rev m n i)) (revPairing m n D) (pos m fun i => r i • w i) :=
      (JointFixedOrder.measurable_covW_pos hH hε m _).comp
        (f := fun w : Fin (m + n) → Rd d => fun i => r i • w i) (by fun_prop)
    rw [← (measurePreserving_perm (waveGreen d 1) (revEquiv m n)).lintegral_comp hcov]
    have hcov2 : Measurable fun w : Fin (m + n) → Rd d =>
        covW Γ (fun i => epsV a b (rev m n i)) (revPairing m n D)
          (pos m fun i => r i • w (revEquiv m n i)) :=
      hcov.comp (f := fun w : Fin (m + n) → Rd d => fun k => w (revEquiv m n k))
        (measurable_pi_iff.mpr fun k => measurable_pi_apply _)
    rw [mul_left_comm, ← lintegral_const_mul _ hcov2]
    congr 1
    refine lintegral_congr fun v => ?_
    exact (integrand_eq hH hD a b t ht.le x s hs v).symm
  · rw [indicator_of_notMem hs, indicator_of_notMem hs, zero_mul]

end Integrals

/-! ### The targets -/

/-- **`TerminalReversalTarget`** (`P:mixed` Step 2, TeX 885-905 at revision edf7085f (book
1.1.3), at positive widths: "The same transformation holds before removing noise smoothing",
903): under `H:homog`, at `t > 0`, each terminal pairing integral with widths `a`, `b` is the M8
diagram `F_{ε∘ρ, δ∘ρ, ρDρ}(t,t)` (`ε, δ` the concatenated widths), and the latter is finite.
Deterministic: no field and no continuity input. -/
theorem terminal_reversal (d : ℕ) : TerminalReversalTarget d := by
  intro alpha α₀ Γ μ hH t ht x m n a b D hD
  have hm := measurable_pairPhi_chain (t := t) (m := m) (n := n) hH (Fin.append a b) D
  have hfin : ∫⁻ q, pairPhi α₀ Γ (Fin.append a b) D (chainS q) (chainY q)
      ∂((chainMeasure d m t ht.le x).prod (chainMeasure d n t ht.le x)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_mono fun q => pairPhi_le hH (Fin.append a b) D _ _)
    rw [lintegral_const]
    exact ENNReal.mul_ne_top (pairBound_ne_top hH _ D) (measure_ne_top _ _)
  have hrev := lintegral_reversal hH t ht x a b hD
  refine ⟨hrev ▸ hfin, ?_⟩
  rw [← hrev]
  unfold srcPairing
  simp_rw [pairWeight_eq_toReal hH a b D]
  exact integral_toReal hm.aemeasurable (ae_of_all _ fun q =>
    (pairPhi_le hH _ D _ _).trans_lt (pairBound_ne_top hH _ D).lt_top)

/-- **`TerminalMixedMomentTarget`, the headline** (TeX 858-905 at revision edf7085f (book
1.1.3); Step 4's first sentence 1951-1953): under `H:homog` and a covariance continuous at fixed
widths (item B), `E[Y_m^a Y_n^b] = Σ_{D ∈ Π} F_{ε∘ρ, δ∘ρ, D}(t,t)`: the Wick formula
(`terminal_wick_w`), the reversal (`terminal_reversal`) and the re-indexing `D ↦ ρDρ`
(`DiagramModel.sum_revPairing`). -/
theorem terminal_mixed_moment (d : ℕ) (hcont : SourceCovContinuousTarget d) :
    TerminalMixedMomentTarget.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW t ht x m n a b
  obtain ⟨hint, heq⟩ := terminal_wick_w.{u} d hcont hH P W hW t ht x m n a b
  refine ⟨hint, ?_⟩
  rw [heq, Finset.sum_congr rfl fun D hD => (terminal_reversal d hH t ht x m n a b D hD).2]
  exact DiagramModel.sum_revPairing (fun D => (wickF (waveGreen d) Γ α₀
    (capDom fun i => delV a b (rev m n i)) (fun i => epsV a b (rev m n i)) m D t t).toReal)

end StratonovichHAMSecondMoment.SourceReversal
