module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L19, item E, first half: the identification of the diagram limits and the fixed-order mixed
moments of `P:mixed` (Steps 1-2).  Main TeX file `notes/notes_stratonovich_ham_second_moment.tex`
at revision edf7085f (book 1.1.3):
* `P:mixed` statement 834-849 (`E:mixed-moment` 836-842, the `m = n = 0` clause 843), proof
  Step 1 858-882 (product convergence in `L¹` 874-880, "a zero-order factor stays equal to one"
  881) and Step 2 885-905 (the chain reversal and the pairing bijection);
* `L:joint-fixed-order` 1853-1862 (joint diagram limit 1855-1858), with its M4 corollary.

Proved here (with the C and D targets as hypotheses, nothing else supplied):
* `diagramLim_ident` (`DiagramLimIdentTarget`, no hypothesis): the joint limit of the M8
  diagrams `wickF … (capDom δ) ε m D t t` along `widthFilter ×ˢ widthFilter` is M4's
  `diagramLim`.  Route: L18's `JointFixedOrder.joint_limit_aux` (both clauses: the joint
  limit `b`, identified through the second clause, the full-kernel limit in the spatial
  widths) with `m8_m4_identity` and `tendsto_half_widthFilter`, exactly as
  `JointFixedOrder.diagramLimits_homog` is proved;
* `inner_XL2`: `⟪X_m, X_n⟫_{L²} = Σ_{D ∈ Π} J_{m,n,D}(t)` for all `m, n` (odd total order:
  the empty sum; `m = n = 0`: one), from `TerminalMixedMomentTarget` (C) and
  `FixedOrderL2Target` (D);
* `mixed_moment_srcX` (from `srcX_ae`, `integrable_srcX_mul`, `integral_srcX_mul` and
  `inner_XL2`): the second clause of `DiagramModel.MixedMoment` for `srcX`.

Route differences (disclosed):
* Step 1 of the TeX takes the joint vertexwise width limit of `Y_m^a Y_n^b`.  Here both factors
  are taken at the *common* widths `(ε, δ)` on all `m + n` vertices (`Ycom`), which is the
  definition of `S_n(g_n)` adopted by the interface (`stratInt`, decision 5; TeX 1963-1964).
  With common widths the reversed concatenated width vectors of C's formula are constant, so no
  reindexing of the widths by `ρ` is needed, and the convergence of the diagrams is
  `diagramLim_ident` composed with the constant-vector map into the width filters
  (`tendsto_common_widths`).  Only the second clause of D's target is used.
* The `L¹` product convergence (874-880) is replaced by the continuity of the `L²` inner product
  (`Filter.Tendsto.inner`), which is the same estimate.
* The zero-order factor: `X_0 = Y_0` with `Y_0 = 1` a.s. (`SourceInterface.Ya_zero`); the
  constant-order variable `Ycom … 0` is `X_0` for all widths (there is only one width vector on
  `Fin 0`).

The headline statements (`diagramLim_ident`, `inner_Ycom`, `tendsto_Ycom_XL2`, `inner_XL2`,
`mixed_moment_srcX`) assume `t > 0` (as the frozen targets do); the auxiliary lemmas `Ycom_zero`,
`inner_XL2_zero`, `srcX_ae`, `integrable_srcX_mul` and `integral_srcX_mul` hold for `t ≥ 0`.  The
case `t = 0` of the headlines is trivial for the TeX's statements and is not needed by any
consumer (review note M9).
-/
public import Mathlib
public import StratonovichHAMSecondMoment.SourceInterface

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal Real Nat

namespace StratonovichHAMSecondMoment.SourceMixed

universe u

open HomogHypothesis (Rd HomogCovariance)
open WaveGreen (waveGreen)
open WickInterface (capDom wickF widthFilter posOrthant)
open DiagramModel (Pi2 diagram covEps diagramLim)
open SourceInterface

/-! ### The diagram limits (deterministic) -/

/-- **The joint M8 diagram limit is M4's `J_{m,n,D}(t)`** (`DiagramLimIdentTarget`; TeX lines
1855-1858 with 814-832 at revision edf7085f (book 1.1.3)): for `m + n = 2k ≥ 2`, the diagrams
`F_{ε,δ,D}(t,t) = wickF (waveGreen d) Γ α₀ (capDom δ) ε m D t t` converge, as all positive
vertexwise spatial and temporal widths tend to zero at arbitrary relative rates, to
`diagramLim d Γ α₀ m n D t`.  Proof: `JointFixedOrder.joint_limit_aux` gives one finite `b`
which is both the joint limit and the full-kernel limit in the spatial widths; the full-kernel
diagram at the common half width `ε/2` is M4's diagram at noise width `ε`
(`JointFixedOrder.m8_m4_identity`), so `b = diagramLim` (`limUnder` of a convergent map). -/
theorem diagramLim_ident (d : ℕ) : DiagramLimIdentTarget d := by
  intro alpha α₀ Γ μ hH m n k hmn hk D hD t ht
  obtain ⟨b, -, hF, hU⟩ := JointFixedOrder.joint_limit_aux hH
    (WickFinal.spatial_wick_measures_l18 d) (WickFinal.joint_temporal_tail_l18 d) hmn hk hD ht ht
  have hdiag : Tendsto (fun ε => diagram (waveGreen d) (covEps Γ ε) α₀ m n D t) (𝓝[>] 0)
      (𝓝 b) := by
    refine (hU.comp (JointFixedOrder.tendsto_half_widthFilter _)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (JointFixedOrder.m8_m4_identity d hH ε hε m n D hD t ht).symm
  have hb : diagramLim d Γ α₀ m n D t = b := by
    rw [DiagramModel.diagramLim, hdiag.limUnder_eq]
  rw [hb]
  exact hF

/-- Auxiliary: the constant width vector `ε ↦ (ε, …, ε)` sends `𝓝[>] 0` into the width
filter. -/
theorem tendsto_const_widthFilter (N : ℕ) :
    Tendsto (fun ε : ℝ => fun _ : Fin N => ε) (𝓝[>] 0) (widthFilter N) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have h : Tendsto (fun ε : ℝ => fun _ : Fin N => ε) (𝓝 0) (𝓝 fun _ => 0) :=
      (continuous_pi fun _ => continuous_id).tendsto 0
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact fun i _ => hε

/-- Auxiliary: common widths `(ε, δ)` on all `N` vertices: the map `(ε, δ) ↦ ((ε,…,ε), (δ,…,δ))`
sends the common-width filter into the joint width filter (TeX 1963-1964). -/
theorem tendsto_common_widths (N : ℕ) :
    Tendsto (fun p : ℝ × ℝ => ((fun _ : Fin N => p.1), (fun _ : Fin N => p.2)))
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (widthFilter N ×ˢ widthFilter N) :=
  Filter.Tendsto.prodMap (tendsto_const_widthFilter N) (tendsto_const_widthFilter N)

/-- Auxiliary: both common widths are eventually positive. -/
theorem eventually_pos_pair :
    ∀ᶠ p : ℝ × ℝ in 𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ), 0 < p.1 ∧ 0 < p.2 :=
  ((tendsto_fst (f := 𝓝[>] (0 : ℝ)) (g := 𝓝[>] (0 : ℝ))).eventually self_mem_nhdsWithin).and
    ((tendsto_snd (f := 𝓝[>] (0 : ℝ)) (g := 𝓝[>] (0 : ℝ))).eventually self_mem_nhdsWithin)

/-! ### Constant widths in the reversed concatenation -/

/-- Auxiliary: at common positive widths `(e, δ)` on both chains, every vertex of the
concatenation carries the spatial width `e`. -/
theorem epsV_const {m n : ℕ} {e δ : ℝ} (he : 0 < e) (hδ : 0 < δ) (i : Fin (m + n)) :
    epsV (posW (fun _ : Fin m => e) (fun _ => δ)) (posW (fun _ : Fin n => e) (fun _ => δ)) i =
      e := by
  unfold epsV
  induction i using Fin.addCases with
  | left j => rw [Fin.append_left, posW_of_pos j ⟨he, hδ⟩]; rfl
  | right j => rw [Fin.append_right, posW_of_pos j ⟨he, hδ⟩]; rfl

/-- Auxiliary: at common positive widths `(e, δ)` on both chains, every vertex of the
concatenation carries the temporal width `δ`. -/
theorem delV_const {m n : ℕ} {e δ : ℝ} (he : 0 < e) (hδ : 0 < δ) (i : Fin (m + n)) :
    delV (posW (fun _ : Fin m => e) (fun _ => δ)) (posW (fun _ : Fin n => e) (fun _ => δ)) i =
      δ := by
  unfold delV
  induction i using Fin.addCases with
  | left j => rw [Fin.append_left, posW_of_pos j ⟨he, hδ⟩]; rfl
  | right j => rw [Fin.append_right, posW_of_pos j ⟨he, hδ⟩]; rfl

/-- Auxiliary: the real inner product is the product. -/
theorem real_inner_eq (r s : ℝ) : inner ℝ r s = r * s := by
  simp only [RCLike.inner_apply, conj_trivial]
  ring

section Moments

variable {d : ℕ} {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)} {Ω : Type u} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {W : SrcPt d → Ω → ℝ}

/-- **The positive-width Wick formula at common widths** (TeX 871-872 with 885-905): at common
positive widths `p = (ε, δ)` on both chains, `E[Y_m Y_n] = Σ_{D ∈ Π} F_{ε,δ,D}(t,t)` with the
constant width vectors; this is C's `TerminalMixedMomentTarget` at the width vectors
`posW (ε,…,ε) (δ,…,δ)`, whose reversed concatenations are constant (`epsV_const`,
`delV_const`). -/
theorem inner_Ycom (hM : TerminalMixedMomentTarget.{u} d) (hH : HomogCovariance d alpha α₀ Γ μ)
    (hW : SourceField α₀ Γ P W) {t : ℝ} (ht : 0 < t) (x : Rd d) (m n : ℕ) {p : ℝ × ℝ}
    (hp : 0 < p.1 ∧ 0 < p.2) :
    inner ℝ (Ycom hW t ht.le x m p) (Ycom hW t ht.le x n p) =
      ∑ D ∈ Pi2 m n, (wickF (waveGreen d) Γ α₀ (capDom fun _ : Fin (m + n) => p.2)
        (fun _ => p.1) m D t t).toReal := by
  have h := (hM hH P W hW t ht x m n (posW (fun _ : Fin m => p.1) (fun _ => p.2))
    (posW (fun _ : Fin n => p.1) (fun _ => p.2))).2
  have hε : (fun i => epsV (posW (fun _ : Fin m => p.1) (fun _ => p.2))
      (posW (fun _ : Fin n => p.1) (fun _ => p.2)) (DiagramModel.rev m n i)) =
      fun _ => p.1 := funext fun i => epsV_const hp.1 hp.2 _
  have hδ : (fun i => delV (posW (fun _ : Fin m => p.1) (fun _ => p.2))
      (posW (fun _ : Fin n => p.1) (fun _ => p.2)) (DiagramModel.rev m n i)) =
      fun _ => p.2 := funext fun i => delV_const hp.1 hp.2 _
  rw [hε, hδ] at h
  rw [L2.inner_def]
  refine Eq.trans ?_ h
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  exact real_inner_eq _ _

omit [IsProbabilityMeasure P] in
/-- At order `0` the common-width variable is `X_0` for all widths (only one width vector on
`Fin 0`). -/
theorem Ycom_zero (hW : SourceField α₀ Γ P W) (t : ℝ) (ht : 0 ≤ t) (x : Rd d) (p : ℝ × ℝ) :
    Ycom hW t ht x 0 p = XL2 hW t ht x 0 := by
  rw [XL2_zero]
  unfold Ycom Yw
  rw [Subsingleton.elim (posW (fun _ : Fin 0 => p.1) (fun _ => p.2)) Fin.elim0]

/-- `Y_n` at common widths converges in `L²` to `X_n` for every `n` (D's target for `n ≥ 1`,
`Ycom_zero` for `n = 0`). -/
theorem tendsto_Ycom_XL2 (hX : FixedOrderL2Target.{u} d) (hH : HomogCovariance d alpha α₀ Γ μ)
    (hW : SourceField α₀ Γ P W) {t : ℝ} (ht : 0 < t) (x : Rd d) (n : ℕ) :
    Tendsto (Ycom hW t ht.le x n) (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ))
      (𝓝 (XL2 hW t ht.le x n)) := by
  rcases n with _ | n
  · have e : Ycom hW t ht.le x 0 = fun _ => XL2 hW t ht.le x 0 :=
      funext fun p => Ycom_zero hW t ht.le x p
    rw [e]
    exact tendsto_const_nhds
  · exact (hX hH P W hW t ht x (n + 1) (by omega)).2

/-- `X_0 = 1` in `L²`: `⟪X_0, X_0⟫ = 1`. -/
theorem inner_XL2_zero (hH : HomogCovariance d alpha α₀ Γ μ) (hW : SourceField α₀ Γ P W)
    {t : ℝ} (ht : 0 ≤ t) (x : Rd d) :
    inner ℝ (XL2 hW t ht x 0) (XL2 hW t ht x 0) = 1 := by
  have h0 := Ya_zero hH.dim hW t ht x (Fin.elim0 : Fin 0 → PosW)
  have hae : ∀ᵐ ω ∂P, inner ℝ ((XL2 hW t ht x 0 : Ω → ℝ) ω) ((XL2 hW t ht x 0 : Ω → ℝ) ω) =
      (1 : ℝ) := by
    filter_upwards [h0] with ω hω
    rw [XL2_zero, hω, real_inner_eq, mul_one]
  rw [L2.inner_def, integral_congr_ae hae]
  simp

/-- **`E:mixed-moment` in `L²`** (`P:mixed`, TeX lines 834-843, proof Steps 1-2 858-905 at
revision edf7085f (book 1.1.3)), for every source field, from C's positive-width formula and D's
common-width `L²` limits: `⟪X_m, X_n⟫ = Σ_{D ∈ Π} J_{m,n,D}(t)` (the empty sum `0` for odd
`m + n`; `1` for `m = n = 0`).  The left side is the limit of `E[Y_m Y_n]` at common widths
(continuity of the inner product); the right side is the limit of C's diagram sum
(`diagramLim_ident`, the limits finite by `WickFinal.diagramLimits_homog_l18`). -/
theorem inner_XL2 (hM : TerminalMixedMomentTarget.{u} d) (hX : FixedOrderL2Target.{u} d)
    (hH : HomogCovariance d alpha α₀ Γ μ) (hW : SourceField α₀ Γ P W) {t : ℝ} (ht : 0 < t)
    (x : Rd d) (m n : ℕ) :
    inner ℝ (XL2 hW t ht.le x m) (XL2 hW t ht.le x n) =
      ∑ D ∈ Pi2 m n, (diagramLim d Γ α₀ m n D t).toReal := by
  by_cases h00 : m = 0 ∧ n = 0
  · obtain ⟨rfl, rfl⟩ := h00
    rw [inner_XL2_zero hH hW ht.le x, DiagramModel.Pi2_zero_zero, Finset.sum_singleton,
      DiagramModel.diagramLim_zero_zero, ENNReal.toReal_one]
  have hlim := (tendsto_Ycom_XL2 hX hH hW ht x m).inner (𝕜 := ℝ)
    (tendsto_Ycom_XL2 hX hH hW ht x n)
  have hR : Tendsto (fun p : ℝ × ℝ => ∑ D ∈ Pi2 m n, (wickF (waveGreen d) Γ α₀
        (capDom fun _ : Fin (m + n) => p.2) (fun _ => p.1) m D t t).toReal)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ))
      (𝓝 (∑ D ∈ Pi2 m n, (diagramLim d Γ α₀ m n D t).toReal)) := by
    refine tendsto_finsetSum _ fun D hD => ?_
    rcases Nat.even_or_odd (m + n) with ⟨k, hk⟩ | hodd
    · have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with rfl | hk1
        · exact absurd (by omega : m = 0 ∧ n = 0) h00
        · exact hk1
      have hfin : diagramLim d Γ α₀ m n D t ≠ ⊤ :=
        (WickFinal.diagramLimits_homog_l18 d hH t ht).2 m n D hD
      have hJ : Tendsto (fun p : ℝ × ℝ => wickF (waveGreen d) Γ α₀
          (capDom fun _ : Fin (m + n) => p.2) (fun _ => p.1) m D t t)
          (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (diagramLim d Γ α₀ m n D t)) := by
        have hmn : m + n = 2 * k := by omega
        have h1 := diagramLim_ident d hH m n k hmn hk1 D hD t ht
        have h2 := h1.comp (tendsto_common_widths (m + n))
        exact h2
      exact (ENNReal.tendsto_toReal hfin).comp hJ
    · rw [DiagramModel.Pi2_odd hodd] at hD
      exact absurd hD (Finset.notMem_empty _)
  refine tendsto_nhds_unique (hlim.congr' ?_) hR
  filter_upwards [eventually_pos_pair] with p hp
  exact inner_Ycom hM hH hW ht x m n hp

omit [IsProbabilityMeasure P] in
/-- `srcX n` is a representative of `X_n` (`X_0 = 1` a.s. by `Ya_zero`). -/
theorem srcX_ae (hH : HomogCovariance d alpha α₀ Γ μ) (hW : SourceField α₀ Γ P W) {t : ℝ}
    (ht : 0 ≤ t) (x : Rd d) (n : ℕ) :
    srcX hW t ht x n =ᵐ[P] (XL2 hW t ht x n : Ω → ℝ) := by
  rcases n with _ | n
  · filter_upwards [Ya_zero hH.dim hW t ht x (Fin.elim0 : Fin 0 → PosW)] with ω hω
    rw [srcX_zero, XL2_zero, hω]
  · exact Eventually.of_forall fun ω => by rw [srcX_succ, XL2_succ]

omit [IsProbabilityMeasure P] in
/-- `X_m X_n` is integrable (both factors in `L²`). -/
theorem integrable_srcX_mul (hH : HomogCovariance d alpha α₀ Γ μ) (hW : SourceField α₀ Γ P W)
    {t : ℝ} (ht : 0 ≤ t) (x : Rd d) (m n : ℕ) :
    Integrable (fun ω => srcX hW t ht x m ω * srcX hW t ht x n ω) P := by
  refine (L2.integrable_inner (𝕜 := ℝ) (XL2 hW t ht x m) (XL2 hW t ht x n)).congr ?_
  filter_upwards [srcX_ae hH hW ht x m, srcX_ae hH hW ht x n] with ω hm hn
  rw [hm, hn, real_inner_eq]

omit [IsProbabilityMeasure P] in
/-- `E[X_m X_n] = ⟪X_m, X_n⟫`. -/
theorem integral_srcX_mul (hH : HomogCovariance d alpha α₀ Γ μ) (hW : SourceField α₀ Γ P W)
    {t : ℝ} (ht : 0 ≤ t) (x : Rd d) (m n : ℕ) :
    ∫ ω, srcX hW t ht x m ω * srcX hW t ht x n ω ∂P =
      inner ℝ (XL2 hW t ht x m) (XL2 hW t ht x n) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [srcX_ae hH hW ht x m, srcX_ae hH hW ht x n] with ω hm hn
  rw [hm, hn, real_inner_eq]

/-- **The second clause of `MixedMoment` for `srcX`** (`E:mixed-moment`, TeX lines 836-843 at
revision edf7085f (book 1.1.3)): for every source field, `X_m X_n` is integrable and
`E[X_m X_n] = Σ_{D ∈ Π} J_{m,n,D}(t)`. -/
theorem mixed_moment_srcX (hM : TerminalMixedMomentTarget.{u} d) (hX : FixedOrderL2Target.{u} d)
    (hH : HomogCovariance d alpha α₀ Γ μ) (hW : SourceField α₀ Γ P W) {t : ℝ} (ht : 0 < t)
    (x : Rd d) (m n : ℕ) :
    Integrable (fun ω => srcX hW t ht.le x m ω * srcX hW t ht.le x n ω) P ∧
      ∫ ω, srcX hW t ht.le x m ω * srcX hW t ht.le x n ω ∂P =
        ∑ D ∈ Pi2 m n, (diagramLim d Γ α₀ m n D t).toReal :=
  ⟨integrable_srcX_mul hH hW ht.le x m n,
    (integral_srcX_mul hH hW ht.le x m n).trans (inner_XL2 hM hX hH hW ht x m n)⟩

end Moments

end StratonovichHAMSecondMoment.SourceMixed
