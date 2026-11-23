module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L19, item C (first half): the finite Wick formula for the positive-width terminal
integrals `Y_m^a`, `Y_n^b` of two width families on one source field (`TerminalWickWTarget`),
and the deterministic pairing integrand shared with the reversal (`SourceReversal`).

TeX anchors (main file `notes/notes_stratonovich_ham_second_moment.tex` at revision 0788ddee
(book 1.1.0; the same line numbers at edf7085f, book 1.1.3), read with
`git show 0788ddee:notes/<file>.tex`):
* `P:mixed` Step 1, TeX lines 858-882 ("At positive noise widths Wick's formula gives zero at odd
  total order and the finite pairing sum at even total order", 871-872);
* the regularization paragraph, TeX lines 1643-1650 (the Bochner integrals `Y_n^a` and the Wick
  bound, with `V` "the largest of the finitely many field variances", 1648-1650);
* `L:terminal-wick`'s formula `E:terminal-wick-formula`, TeX lines 4310-4313 (derived in its
  Step 2, 4364-4378), here with two width families;
* `E:pairing-source-covariance`, TeX lines 1352-1370 (the covariance of the source field).

Route (disclosed): the strong measurability of `z ↦ ∏_j W(z_j, a_j) ∈ L²` is obtained from the
continuity of the covariance at fixed widths (`SourceCovContinuousTarget`, item B): the field
value `y ↦ W(y, w) ∈ L²` is then continuous, and so is the chain product (the Wick formula for
`‖∏W(z) - ∏W(z₀)‖²`), with no cell partition.  The variance bound is the sum of the diagonal
covariances over the finitely many widths (the TeX's `V` at 1649-1650 is their maximum; the sum
is a larger bound), used only at the points actually
integrated (the field has unbounded variance as the widths shrink).  The integrability of each
pairing integrand is deterministic (bounded measurable factors at fixed widths).
-/
public import Mathlib
public import StratonovichHAMSecondMoment.SourceInterface

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace StratonovichHAMSecondMoment.SourceWick

universe u

open HomogHypothesis (Rd HomogCovariance)
open FiniteWick (CenteredGaussianField pairWeight wickSum pairings)
open TerminalWick (Pt prodL2)
open TerminalWickInputs (chainMeasure fieldL2)
open WickInterface (kerA capSet)
open LowAlphaConvolution (gammaEps gaussFactor)
open DiagramModel (Pi2 openers covEps)
open SourceInterface

variable {d : ℕ}

/-! ### Points of the chains as points of the source field -/

/-- A point `(s, y)` of `[0,t] × ℝ^d` as a point of `[0,∞) × ℝ^d`. -/
def ptI {t : ℝ} (p : Pt d t) : ↥(Ici (0 : ℝ)) × Rd d := (⟨(p.1 : ℝ), p.1.2.1⟩, p.2)

theorem continuous_ptI {t : ℝ} : Continuous (ptI (d := d) (t := t)) := by
  unfold ptI
  exact (continuous_subtype_val.comp continuous_fst).subtype_mk _ |>.prodMk continuous_snd

theorem measurable_ptI {t : ℝ} : Measurable (ptI (d := d) (t := t)) :=
  continuous_ptI.measurable

/-- `attach a z j = (z_j, a_j)`. -/
theorem attach_eq {t : ℝ} {n : ℕ} (a : Fin n → PosW) (z : Fin n → Pt d t) (j : Fin n) :
    attach a z j = (ptI (z j), a j) := rfl

/-- The concatenated attached chains: points `P_i` and widths `c_i = (a ++ b)_i`. -/
theorem append_attach {t : ℝ} {m n : ℕ} (a : Fin m → PosW) (b : Fin n → PosW)
    (z₁ : Fin m → Pt d t) (z₂ : Fin n → Pt d t) (i : Fin (m + n)) :
    Fin.append (attach a z₁) (attach b z₂) i =
      (Fin.append (fun j => ptI (z₁ j)) (fun j => ptI (z₂ j)) i, Fin.append a b i) := by
  induction i using Fin.addCases with
  | left j => simp only [Fin.append_left]; rfl
  | right j => simp only [Fin.append_right]; rfl

/-! ### The variance bound over finitely many widths (TeX 1649-1650) -/

section Variance

variable {α₀ : ℝ} {Γ : Measure (Rd d)}

/-- The variance `κ_δ(0) γ_{2ε}(0)` of the field at width `w = (ε, δ)` (`srcCov_diag`). -/
def diagW (α₀ : ℝ) (Γ : Measure (Rd d)) (w : PosW) : ℝ :=
  (kerA α₀ (capSet w.del) 0).toReal * gammaEps Γ (w.eps + w.eps) 0

theorem diagW_nonneg (w : PosW) : 0 ≤ diagW α₀ Γ w :=
  mul_nonneg ENNReal.toReal_nonneg
    (LowAlphaConvolution.gammaEps_nonneg Γ (add_pos w.eps_pos w.eps_pos).le _)

/-- The variance bound of the finitely many widths of a chain. -/
def varB (α₀ : ℝ) (Γ : Measure (Rd d)) {n : ℕ} (a : Fin n → PosW) : ℝ := ∑ j, diagW α₀ Γ (a j)

theorem varB_nonneg {n : ℕ} (a : Fin n → PosW) : 0 ≤ varB α₀ Γ a :=
  Finset.sum_nonneg fun _ _ => diagW_nonneg _

theorem diagW_le_varB {n : ℕ} (a : Fin n → PosW) (j : Fin n) : diagW α₀ Γ (a j) ≤ varB α₀ Γ a :=
  Finset.single_le_sum (f := fun j => diagW α₀ Γ (a j)) (fun _ _ => diagW_nonneg _)
    (Finset.mem_univ j)

theorem srcCov_attach_self {t : ℝ} {n : ℕ} (a : Fin n → PosW) (z : Fin n → Pt d t) (j : Fin n) :
    srcCov α₀ Γ (attach a z j) (attach a z j) = diagW α₀ Γ (a j) :=
  srcCov_diag _

end Variance

/-! ### Gaussian bounds with a variance bound on the points used -/

section Field

variable {X Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : X → Ω → ℝ} {K : X → X → ℝ}

/-- `|K(x,y)| ≤ V` when `K(x,x), K(y,y) ≤ V` (positive semidefiniteness of the `2 × 2` Gram
matrix; `FiniteWick.CenteredGaussianField.abs_le` with the bound only at `x`, `y`). -/
theorem abs_le_of (hW : CenteredGaussianField W K P) {V : ℝ} {x y : X} (hx : K x x ≤ V)
    (hy : K y y ≤ V) : |K x y| ≤ V := by
  have hpsd := hW.psd 2 ![x, y]
  have h1 := hpsd.dotProduct_mulVec_nonneg ![1, -1]
  have h2 := hpsd.dotProduct_mulVec_nonneg ![1, 1]
  have hs := hW.symm x y
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h1 h2
  rw [_root_.abs_le]
  constructor <;> nlinarith

/-- `‖∏_j W(z_j)‖₂ ≤ √((2n-1)!!) (√V)^n` when `K(z_j, z_j) ≤ V` for the points used
(`TerminalWick.norm_prodL2_le` with a local variance bound; TeX 1649-1650, 4351-4356). -/
theorem norm_prodL2_le_of (hW : CenteredGaussianField W K P) (V : ℝ) (hV0 : 0 ≤ V) {n : ℕ}
    (z : Fin n → X) (hz : ∀ j, K (z j) (z j) ≤ V) :
    ‖prodL2 hW z‖ ≤ Real.sqrt ((2 * n - 1).doubleFactorial) * Real.sqrt V ^ n := by
  have hz' : ∀ a : Fin (n + n), K (Fin.append z z a) (Fin.append z z a) ≤ V := by
    intro a
    induction a using Fin.addCases with
    | left j => simp only [Fin.append_left]; exact hz j
    | right j => simp only [Fin.append_right]; exact hz j
  have hsq : ‖prodL2 hW z‖ ^ 2 ≤ ((2 * n - 1).doubleFactorial : ℝ) * V ^ n := by
    rw [← real_inner_self_eq_norm_sq, TerminalWick.inner_prodL2]
    refine (le_abs_self _).trans ?_
    exact FiniteWick.wickSum_abs_le _ V (fun a b => abs_le_of hW (hz' a) (hz' b)) n _
      (by simp; ring)
  have hB : 0 ≤ Real.sqrt ((2 * n - 1).doubleFactorial) * Real.sqrt V ^ n := by positivity
  have hB2 : (Real.sqrt ((2 * n - 1).doubleFactorial) * Real.sqrt V ^ n) ^ 2 =
      ((2 * n - 1).doubleFactorial : ℝ) * V ^ n := by
    rw [mul_pow, Real.sq_sqrt (by positivity), ← pow_mul, mul_comm n 2, pow_mul,
      Real.sq_sqrt hV0]
  rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq hB]
  exact Real.sqrt_le_sqrt (hsq.trans hB2.ge)

/-- The chain product `z ↦ ∏_j W(g(z)_j) ∈ L²` is continuous when every field value
`z ↦ W(g(z)_j) ∈ L²` is (TeX 4357-4359; the argument of
`TerminalWickInputs.continuousAt_prodL2`, for a parametrized tuple). -/
theorem continuous_prodL2_of {Z : Type*} [TopologicalSpace Z] (hW : CenteredGaussianField W K P)
    {n : ℕ} (g : Z → Fin n → X) (hg : ∀ j, Continuous fun z => fieldL2 hW (g z j)) :
    Continuous fun z => prodL2 hW (g z) := by
  rw [continuous_iff_continuousAt]
  intro z₀
  set φ : Z → Fin n → Lp ℝ 2 P := fun z i => fieldL2 hW (g z i) with hφ
  have hφc : Continuous φ := continuous_pi hg
  set G : Z → ℝ := fun z =>
    TerminalWickInputs.gramWick (Fin.append (φ z) (φ z)) -
      2 * TerminalWickInputs.gramWick (Fin.append (φ z) (φ z₀)) +
      TerminalWickInputs.gramWick (Fin.append (φ z₀) (φ z₀)) with hG
  have hGc : Continuous G := by
    have h1 : Continuous fun z => TerminalWickInputs.gramWick (Fin.append (φ z) (φ z)) :=
      TerminalWickInputs.continuous_gramWick.comp
        (TerminalWickInputs.continuous_append.comp (hφc.prodMk hφc))
    have h2 : Continuous fun z => TerminalWickInputs.gramWick (Fin.append (φ z) (φ z₀)) :=
      TerminalWickInputs.continuous_gramWick.comp
        (TerminalWickInputs.continuous_append.comp (hφc.prodMk continuous_const))
    exact (h1.sub (continuous_const.mul h2)).add continuous_const
  have hG0 : G z₀ = 0 := by simp only [hG]; ring
  have hlim : Tendsto G (𝓝 z₀) (𝓝 0) := hG0 ▸ hGc.tendsto z₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have he : (fun z => ‖prodL2 hW (g z) - prodL2 hW (g z₀)‖) = fun z => Real.sqrt (G z) := by
    funext z
    rw [← Real.sqrt_sq (norm_nonneg (prodL2 hW (g z) - prodL2 hW (g z₀))),
      TerminalWickInputs.norm_sub_prodL2_sq hW (g z) (g z₀)]
  rw [he]
  have hs := (Real.continuous_sqrt.tendsto 0).comp hlim
  rw [Real.sqrt_zero] at hs
  exact hs

end Field

/-! ### Strong measurability and integrability of the chain products -/

section Chains

variable {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : SrcPt d → Ω → ℝ}

/-- At a fixed width `w`, a continuous covariance makes `y ↦ W(y, w) ∈ L²` continuous. -/
theorem continuous_fieldL2_w (hW : SourceField α₀ Γ P W) (w : PosW)
    (hc : Continuous fun pq : (↥(Ici (0 : ℝ)) × Rd d) × (↥(Ici (0 : ℝ)) × Rd d) =>
      srcCov α₀ Γ (pq.1, w) (pq.2, w)) :
    Continuous fun y : ↥(Ici (0 : ℝ)) × Rd d => fieldL2 hW (y, w) := by
  rw [continuous_iff_continuousAt]
  intro y₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  set F : (↥(Ici (0 : ℝ)) × Rd d) × (↥(Ici (0 : ℝ)) × Rd d) → ℝ :=
    fun pq => srcCov α₀ Γ (pq.1, w) (pq.2, w) with hF
  set G : ↥(Ici (0 : ℝ)) × Rd d → ℝ := fun y => F (y, y) - 2 * F (y₀, y) + F (y₀, y₀) with hG
  have he : (fun y => ‖fieldL2 hW (y, w) - fieldL2 hW (y₀, w)‖) = fun y => Real.sqrt (G y) := by
    funext y
    rw [← Real.sqrt_sq (norm_nonneg (fieldL2 hW (y, w) - fieldL2 hW (y₀, w))),
      TerminalWickInputs.norm_sub_fieldL2_sq hW (y₀, w) (y, w)]
  rw [he]
  have h1 : Continuous fun y : ↥(Ici (0 : ℝ)) × Rd d => F (y, y) :=
    hc.comp (f := fun y : ↥(Ici (0 : ℝ)) × Rd d => (y, y)) (by fun_prop)
  have h2 : Continuous fun y : ↥(Ici (0 : ℝ)) × Rd d => F (y₀, y) :=
    hc.comp (f := fun y : ↥(Ici (0 : ℝ)) × Rd d => (y₀, y)) (by fun_prop)
  have hGc : Continuous G := (h1.sub (continuous_const.mul h2)).add continuous_const
  have hG0 : G y₀ = 0 := by simp only [hG]; ring
  have hs := (Real.continuous_sqrt.tendsto 0).comp (hG0 ▸ hGc.tendsto y₀)
  rw [Real.sqrt_zero] at hs
  exact hs

/-- **Strong measurability of the integrand of `Y_n^a`** (TeX 1647-1650): with a continuous
covariance at fixed widths (`SourceCovContinuousTarget`), `z ↦ ∏_j W(z_j, a_j) ∈ L²` is
continuous, hence a.e. strongly measurable for every measure on the chains. -/
theorem continuous_prodL2_attach (hW : SourceField α₀ Γ P W)
    (hc : ∀ w w' : PosW, Continuous fun pq : (↥(Ici (0 : ℝ)) × Rd d) × (↥(Ici (0 : ℝ)) × Rd d) =>
      srcCov α₀ Γ (pq.1, w) (pq.2, w')) {t : ℝ} {n : ℕ} (a : Fin n → PosW) :
    Continuous fun z : Fin n → Pt d t => prodL2 hW (attach a z) := by
  refine continuous_prodL2_of hW (attach a) fun j => ?_
  have h := (continuous_fieldL2_w hW (a j) (hc (a j) (a j))).comp
    (f := fun z : Fin n → Pt d t => ptI (z j)) (continuous_ptI.comp (continuous_apply j))
  exact h

/-- The norm bound of the integrand of `Y_n^a` (TeX 1649-1650). -/
theorem norm_prodL2_attach_le (hW : SourceField α₀ Γ P W) {t : ℝ} {n : ℕ} (a : Fin n → PosW)
    (z : Fin n → Pt d t) :
    ‖prodL2 hW (attach a z)‖ ≤
      Real.sqrt ((2 * n - 1).doubleFactorial) * Real.sqrt (varB α₀ Γ a) ^ n :=
  norm_prodL2_le_of hW _ (varB_nonneg a) _ fun j =>
    (srcCov_attach_self a z j).trans_le (diagW_le_varB a j)

/-- **The Bochner integral `Y_n^a` exists** (TeX 1647-1650): the integrand is continuous and
bounded, the chain measure finite. -/
theorem integrable_prodL2_attach (hW : SourceField α₀ Γ P W)
    (hc : ∀ w w' : PosW, Continuous fun pq : (↥(Ici (0 : ℝ)) × Rd d) × (↥(Ici (0 : ℝ)) × Rd d) =>
      srcCov α₀ Γ (pq.1, w) (pq.2, w')) (t : ℝ) (ht : 0 ≤ t) (x : Rd d) {n : ℕ}
    (a : Fin n → PosW) :
    Integrable (fun z : Fin n → Pt d t => prodL2 hW (attach a z)) (chainMeasure d n t ht x) :=
  Integrable.of_bound (continuous_prodL2_attach hW hc a).aestronglyMeasurable _
    (ae_of_all _ fun z => norm_prodL2_attach_le hW a z)

end Chains

/-! ### The deterministic pairing integrand (TeX 4315-4328, 1360-1370) -/

section Pairing

variable {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}

/-- The pairing integrand in `ℝ≥0∞` at times `S` and positions `Y` of `N` vertices with widths
`c`: `∏_{{i,D i}, i < D i} κ_{δ_i ∨ δ_{Di}}(S_i - S_{Di}) γ_{ε_i + ε_{Di}}(Y_i - Y_{Di})`. -/
def pairPhi (α₀ : ℝ) (Γ : Measure (Rd d)) {N : ℕ} (c : Fin N → PosW) (D : Fin N → Fin N)
    (S : Fin N → ℝ) (Y : Fin N → Rd d) : ℝ≥0∞ :=
  ∏ i ∈ openers D, kerA α₀ (capSet (max (c i).del (c (D i)).del)) (S i - S (D i)) *
    covEps Γ ((c i).eps + (c (D i)).eps) (Y i - Y (D i))

/-- The constant bounding one factor of `pairPhi` (`κ_δ(u) ≤ κ_δ(0)`, `|γ_b| ≤ ∫ e^{-b|ξ|²/2} dμ`). -/
def pairBound (α₀ : ℝ) (μ : Measure (Rd d)) {N : ℕ} (c : Fin N → PosW) (D : Fin N → Fin N) :
    ℝ≥0∞ :=
  ∏ i ∈ openers D, kerA α₀ (capSet (max (c i).del (c (D i)).del)) 0 *
    ENNReal.ofReal (∫ ξ, gaussFactor ((c i).eps + (c (D i)).eps) ξ ∂μ)

theorem covEps_eq (hH : HomogCovariance d alpha α₀ Γ μ) {e : ℝ} (he : 0 < e) (y : Rd d) :
    covEps Γ e y = ENNReal.ofReal (gammaEps Γ e y) :=
  LowAlphaUpper.covEps_eq_ofReal he.le
    (LowAlphaConvolution.integrable_heatDens hH.Γ_tempered he) y

theorem covEps_le (hH : HomogCovariance d alpha α₀ Γ μ) {e : ℝ} (he : 0 < e) (y : Rd d) :
    covEps Γ e y ≤ ENNReal.ofReal (∫ ξ, gaussFactor e ξ ∂μ) := by
  have := hH.μ_radon
  rw [covEps_eq hH he]
  refine ENNReal.ofReal_le_ofReal ((le_abs_self _).trans ?_)
  rw [← Real.norm_eq_abs]
  exact (LowAlphaConvolution.gammaEps_continuous_bounded hH.μ_tempered hH.spectral he).2 y

theorem pairBound_ne_top (hH : HomogCovariance d alpha α₀ Γ μ) {N : ℕ} (c : Fin N → PosW)
    (D : Fin N → Fin N) : pairBound α₀ μ c D ≠ ⊤ :=
  ENNReal.prod_ne_top fun i _ => ENNReal.mul_ne_top
    (JointFixedOrder.kerA_capSet_zero_ne_top hH.alpha0_pos
      (lt_max_of_lt_left (c i).del_pos)) ENNReal.ofReal_ne_top

theorem pairPhi_le (hH : HomogCovariance d alpha α₀ Γ μ) {N : ℕ} (c : Fin N → PosW)
    (D : Fin N → Fin N) (S : Fin N → ℝ) (Y : Fin N → Rd d) :
    pairPhi α₀ Γ c D S Y ≤ pairBound α₀ μ c D :=
  Finset.prod_le_prod fun i _ => mul_le_mul'
    (JointFixedOrder.kerA_le_zero α₀ (WickInterface.measurableSet_capSet _)
      (WickInterface.capSet_subset_Ioi _) _)
    (covEps_le hH (add_pos (c i).eps_pos (c (D i)).eps_pos) _)

theorem measurable_pairPhi (hH : HomogCovariance d alpha α₀ Γ μ) {N : ℕ} (c : Fin N → PosW)
    (D : Fin N → Fin N) :
    Measurable fun q : (Fin N → ℝ) × (Fin N → Rd d) => pairPhi α₀ Γ c D q.1 q.2 := by
  unfold pairPhi
  refine Finset.measurable_prod _ fun i _ => ?_
  exact ((JointFixedOrder.measurable_kerA α₀ _).comp
      (((measurable_pi_apply i).comp measurable_fst).sub
        ((measurable_pi_apply (D i)).comp measurable_fst))).mul
    ((LowAlphaUpper.measurable_covEps hH (add_pos (c i).eps_pos (c (D i)).eps_pos)).comp
      (((measurable_pi_apply i).comp measurable_snd).sub
        ((measurable_pi_apply (D i)).comp measurable_snd)))

/-- One covariance factor as `toReal` of the `ℝ≥0∞` factor. -/
theorem srcCov_eq_toReal (hH : HomogCovariance d alpha α₀ Γ μ) (y y' : ↥(Ici (0 : ℝ)) × Rd d)
    (w w' : PosW) :
    srcCov α₀ Γ (y, w) (y', w') =
      (kerA α₀ (capSet (max w.del w'.del)) ((y.1 : ℝ) - (y'.1 : ℝ)) *
        covEps Γ (w.eps + w'.eps) (y.2 - y'.2)).toReal := by
  rw [ENNReal.toReal_mul, covEps_eq hH (add_pos w.eps_pos w'.eps_pos),
    ENNReal.toReal_ofReal (LowAlphaConvolution.gammaEps_nonneg Γ
      (add_pos w.eps_pos w'.eps_pos).le _)]
  rfl

/-- Times and positions of the concatenated attached chains. -/
def chainS {t : ℝ} {m n : ℕ} (q : (Fin m → Pt d t) × (Fin n → Pt d t)) (i : Fin (m + n)) : ℝ :=
  ((Fin.append (fun j => ptI (q.1 j)) (fun j => ptI (q.2 j)) i).1 : ℝ)

def chainY {t : ℝ} {m n : ℕ} (q : (Fin m → Pt d t) × (Fin n → Pt d t)) (i : Fin (m + n)) :
    Rd d :=
  (Fin.append (fun j => ptI (q.1 j)) (fun j => ptI (q.2 j)) i).2

theorem measurable_chainSY {t : ℝ} {m n : ℕ} :
    Measurable fun q : (Fin m → Pt d t) × (Fin n → Pt d t) => (chainS q, chainY q) := by
  have hP : Measurable fun q : (Fin m → Pt d t) × (Fin n → Pt d t) =>
      Fin.append (fun j => ptI (q.1 j)) (fun j => ptI (q.2 j)) := by
    have h1 : Measurable fun q : (Fin m → Pt d t) × (Fin n → Pt d t) =>
        (fun j => ptI (q.1 j), fun j => ptI (q.2 j)) := by
      refine Measurable.prodMk ?_ ?_ <;>
        refine measurable_pi_iff.mpr fun j => measurable_ptI.comp ?_ <;> fun_prop
    exact TerminalWick.measurable_append.comp h1
  refine (measurable_pi_iff.mpr fun i => ?_).prodMk (measurable_pi_iff.mpr fun i => ?_)
  · exact measurable_subtype_coe.comp (measurable_fst.comp ((measurable_pi_apply i).comp hP))
  · exact measurable_snd.comp ((measurable_pi_apply i).comp hP)

/-- **The terminal pairing integrand is `toReal` of `pairPhi`** at the concatenated widths. -/
theorem pairWeight_eq_toReal (hH : HomogCovariance d alpha α₀ Γ μ) {t : ℝ} {m n : ℕ}
    (a : Fin m → PosW) (b : Fin n → PosW) (D : Fin (m + n) → Fin (m + n))
    (q : (Fin m → Pt d t) × (Fin n → Pt d t)) :
    pairWeight (fun i j => srcCov α₀ Γ (Fin.append (attach a q.1) (attach b q.2) i)
        (Fin.append (attach a q.1) (attach b q.2) j)) Finset.univ D =
      (pairPhi α₀ Γ (Fin.append a b) D (chainS q) (chainY q)).toReal := by
  unfold pairWeight pairPhi
  rw [ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  show srcCov α₀ Γ (Fin.append (attach a q.1) (attach b q.2) i)
    (Fin.append (attach a q.1) (attach b q.2) (D i)) = _
  rw [append_attach, append_attach, srcCov_eq_toReal hH]
  rfl

theorem integrable_pairWeight_src (hH : HomogCovariance d alpha α₀ Γ μ) {t : ℝ} {m n : ℕ}
    (a : Fin m → PosW) (b : Fin n → PosW) (D : Fin (m + n) → Fin (m + n))
    (ν : Measure ((Fin m → Pt d t) × (Fin n → Pt d t))) [IsFiniteMeasure ν] :
    Integrable (fun q : (Fin m → Pt d t) × (Fin n → Pt d t) =>
      pairWeight (fun i j => srcCov α₀ Γ (Fin.append (attach a q.1) (attach b q.2) i)
        (Fin.append (attach a q.1) (attach b q.2) j)) Finset.univ D) ν := by
  simp_rw [pairWeight_eq_toReal hH a b D]
  have hm : Measurable fun q : (Fin m → Pt d t) × (Fin n → Pt d t) =>
      pairPhi α₀ Γ (Fin.append a b) D (chainS q) (chainY q) :=
    (measurable_pairPhi hH (Fin.append a b) D).comp
      (f := fun q : (Fin m → Pt d t) × (Fin n → Pt d t) => (chainS q, chainY q))
      measurable_chainSY
  refine Integrable.of_bound hm.ennreal_toReal.aestronglyMeasurable
    (pairBound α₀ μ (Fin.append a b) D).toReal (ae_of_all _ fun q => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_mono (pairBound_ne_top hH _ D) (pairPhi_le hH _ D _ _)

end Pairing

/-! ### The two-family Wick formula (TeX 858-882, 1643-1650) -/

/-- **`TerminalWickWTarget`** (`P:mixed` Step 1, TeX 871-872, and the regularization paragraph
1643-1650 at revision edf7085f (book 1.1.3); `L:terminal-wick`'s formula 4310-4313 (Step 2,
4364-4378) with two width families): under `H:homog` and a covariance continuous at fixed widths (item B's
`SourceCovContinuousTarget`), for every source field, `t > 0`, `x` and width vectors `a`, `b`,
`Y_m^a Y_n^b` is integrable and `E[Y_m^a Y_n^b] = Σ_{D ∈ Π} T^{a,b}_{m,n,D}`. -/
theorem terminal_wick_w (d : ℕ) (hcont : SourceCovContinuousTarget d) :
    TerminalWickWTarget.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW t ht x m n a b
  have hc := fun w w' : PosW => hcont hH w w'
  have hA := integrable_prodL2_attach hW hc t ht.le x a
  have hB := integrable_prodL2_attach hW hc t ht.le x b
  refine ⟨(Lp.memLp (Ya hW t ht.le x a)).integrable_mul (Lp.memLp (Ya hW t ht.le x b)), ?_⟩
  have hprod : Integrable (fun q : (Fin m → Pt d t) × (Fin n → Pt d t) =>
      inner ℝ (prodL2 hW (attach a q.1)) (prodL2 hW (attach b q.2)))
      ((chainMeasure d m t ht.le x).prod (chainMeasure d n t ht.le x)) := by
    refine Integrable.of_bound (hA.1.comp_fst.inner hB.1.comp_snd)
      ((Real.sqrt ((2 * m - 1).doubleFactorial) * Real.sqrt (varB α₀ Γ a) ^ m) *
        (Real.sqrt ((2 * n - 1).doubleFactorial) * Real.sqrt (varB α₀ Γ b) ^ n))
      (ae_of_all _ fun q => ?_)
    refine (norm_inner_le_norm _ _).trans ?_
    exact mul_le_mul (norm_prodL2_attach_le hW a _) (norm_prodL2_attach_le hW b _)
      (norm_nonneg _) (by positivity)
  rw [UniformSeriesTail.integral_mul_eq_inner]
  calc inner ℝ (Ya hW t ht.le x a) (Ya hW t ht.le x b)
      = ∫ r, inner ℝ (Ya hW t ht.le x a) (prodL2 hW (attach b r)) ∂chainMeasure d n t ht.le x :=
        (integral_inner hB _).symm
    _ = ∫ r, ∫ s, inner ℝ (prodL2 hW (attach a s)) (prodL2 hW (attach b r))
          ∂chainMeasure d m t ht.le x ∂chainMeasure d n t ht.le x := by
        refine integral_congr_ae (ae_of_all _ fun r => ?_)
        simp only
        rw [real_inner_comm, Ya, ← integral_inner hA]
        exact integral_congr_ae (ae_of_all _ fun s => real_inner_comm _ _)
    _ = ∫ q, inner ℝ (prodL2 hW (attach a q.1)) (prodL2 hW (attach b q.2))
          ∂((chainMeasure d m t ht.le x).prod (chainMeasure d n t ht.le x)) :=
        (integral_prod_symm _ hprod).symm
    _ = ∫ q, wickSum (fun i j => srcCov α₀ Γ (Fin.append (attach a q.1) (attach b q.2) i)
          (Fin.append (attach a q.1) (attach b q.2) j)) Finset.univ
          ∂((chainMeasure d m t ht.le x).prod (chainMeasure d n t ht.le x)) :=
        integral_congr_ae (ae_of_all _ fun q => TerminalWick.inner_prodL2 hW _ _)
    _ = ∑ D ∈ Pi2 m n, srcPairing α₀ Γ t ht.le x a b D := by
        unfold wickSum
        exact integral_finsetSum _ fun D _ => integrable_pairWeight_src hH a b D _

end StratonovichHAMSecondMoment.SourceWick
