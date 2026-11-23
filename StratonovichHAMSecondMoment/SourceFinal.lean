module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L19, integration (interface section 6): the hypothesis-free wrappers of the item targets
(A `SourceIsonormal`, B `SourceFeatures`, C `SourceWick`/`SourceReversal`, D
`SourceFixedOrder`/`SourceGreenFirst`, E `SourceMixed`/`SourceExpansion`, G
`SourceVertexCrude`), the M9 non-vacuity instances, and the seven consumer wrappers in which
the named inputs `DiagramModel.MixedMoment` and `LowAlphaUpper.FirstMomentSeries` are discharged
for the constructed chaos terms `X_n = srcX` and solution `u = srcU` of any source field.  Main
TeX file at revision edf7085f (book 1.1.3):
* `E:pairing-source-covariance` 1352-1370 (the source field; M9);
* `P:mixed` 834-849, proof 851-927; `E:expansion` 542-549; `X_n` 796;
* `L:joint-fixed-order` 1853-1862, proof 1864-1966 (Step 4 1949-1965);
* `L:vertex-crude` 2062-2074, proof 2076-2145;
* consumers: `L:crude-corrected` 1978-2054, `P:envelope` 2352-2433, `P:d1-upper` 5454-5466,
  `L:white-test` and `P:riesz-small` (order-two diagrams), `P:low-alpha-upper` 5711-5734 (proof
  5736-5807) and `C:d1-first-calibration` 5830-5842 (proof 5844-5864).

Route differences are those disclosed in the item modules (notably: `S_n(g_n)` is the
common-width limit, decision 5; `P:mixed` Step 1 is run at common widths; `E:full-second` by
absolute summability; norm summability from `L:crude-corrected`, not `L:vertex-crude`).  New
here: the d = 3 moment sentences of `L:crude-corrected` and `P:envelope` (decision 13 gave only
their diagram halves in L18) are obtained by re-running the moment steps of
`CrudeCorrected.crude_corrected_paper` and `HomogeneousEnvelope.envelope_paper` with the d = 3
diagram bounds of `WickFinal` (`crude_moments_of_diagrams`, `envelope_moments_of_diagrams`).

Hypotheses kept, as the consumers state them: `H:homog` (`HomogCovariance`) and the consumers'
own parameter hypotheses.  For the Riesz rows whose originals take no `HomogCovariance`
(`D1Upper.d1_upper_paper_riesz`, `LowAlphaUpper.first_calibration_riesz_paper`) the wrapper adds
`hH : HomogCovariance 1 α α₀ (volume.withDensity (riesz c α)) μ`, which `P:mixed` needs: the
Riesz instance of `H:homog` (existence of the spectral measure of `c|y|^{-α}`) is TRUE but is not
formalized in the library, so these rows (and `riesz_small_paper_l19`, whose original already
carries the same `hH`) are non-vacuous by mathematics, not yet in Lean.  The white-noise rows
discharge `H:homog` by `WhiteModel.white_homogCovariance` (with `whiteCov 1 = δ₀`).
-/
public import Mathlib
public import StratonovichHAMSecondMoment.SourceIsonormal
public import StratonovichHAMSecondMoment.SourceFeatures
public import StratonovichHAMSecondMoment.SourceWick
public import StratonovichHAMSecondMoment.SourceReversal
public import StratonovichHAMSecondMoment.SourceFixedOrder
public import StratonovichHAMSecondMoment.SourceGreenFirst
public import StratonovichHAMSecondMoment.SourceVertexCrude
public import StratonovichHAMSecondMoment.SourceMixed
public import StratonovichHAMSecondMoment.SourceExpansion
public import StratonovichHAMSecondMoment.D1Upper
public import StratonovichHAMSecondMoment.OrderTwoDiagrams
public import StratonovichHAMSecondMoment.RieszFourDiagrams

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal Real Nat

namespace StratonovichHAMSecondMoment.SourceFinal

universe u

open HomogHypothesis (Rd HomogCovariance)
open WaveGreen (waveGreen)
open DiagramModel (Pi2 diagram covEps diagramLim coeffA coeffALim MixedMoment)
open SourceInterface
open HomogeneousEnvelope (BK termBK summable_termBK_and_le le_mul_iInf moment_le_of_diagrams)
open LowAlphaUpper (FirstMomentSeries C1 C2 Kgen)
open LowAlphaConvolution (specV)
open TwoSimplexTime (Zc)
open D1Spatial (Ksp)
open HigherRieszTwo (riesz)

/-! ### Hypothesis-free item targets -/

/-- **The source field exists** (`SourceFieldTarget`, M9; TeX 1352-1370 at revision edf7085f
(book 1.1.3)): the isonormal map (A) of B's Hilbert feature space of `srcCov`. -/
theorem source_field_l19 (d : ℕ) : SourceFieldTarget d :=
  sourceField_of_parts SourceIsonormal.isonormal (SourceFeatures.source_features d)

/-- **The two-family positive-width Wick formula** (`TerminalWickWTarget`; TeX 858-882, 1643-1650),
with B's continuity discharged. -/
theorem terminal_wick_w_l19 (d : ℕ) : TerminalWickWTarget.{u} d :=
  SourceWick.terminal_wick_w d (SourceFeatures.source_cov_continuous d)

/-- **The terminal mixed moments as M8 diagrams** (`TerminalMixedMomentTarget`; `P:mixed` Steps
1-2, TeX 858-905). -/
theorem terminal_mixed_moment_l19 (d : ℕ) : TerminalMixedMomentTarget.{u} d :=
  SourceReversal.terminal_mixed_moment d (SourceFeatures.source_cov_continuous d)

/-- **`L:joint-fixed-order`, `L²` half** (`FixedOrderL2Target`; TeX 1858-1861, Step 4
1949-1965). -/
theorem fixed_order_l2_l19 (d : ℕ) : FixedOrderL2Target.{u} d :=
  SourceFixedOrder.fixed_order_l2 d (terminal_mixed_moment_l19 d)

/-- **Green width removed first** (`GreenFirstTarget`; TeX 1651-1655, 1860-1861; stated for
d = 1, 2, 3, the d = 1, 2 cases extra, interface section 5 item 5). -/
theorem green_first_l19 (d : ℕ) : GreenFirstTarget.{u} d :=
  SourceGreenFirst.green_first d (SourceFeatures.source_cov_continuous d)

/-- **`E:expansion` in `L²`** (`ExpansionL2Target`; TeX 542-549, 908-919). -/
theorem expansion_l2_l19 (d : ℕ) : ExpansionL2Target.{u} d :=
  SourceExpansion.expansion_l2 d (terminal_mixed_moment_l19 d) (fixed_order_l2_l19 d)

/-- **`P:mixed`, whole** (`MixedTermsTarget`; TeX 834-849, proof 851-927): `MixedMoment` holds
for `srcX`, `srcU` of every source field, every `t > 0` (the case `t = 0` is trivial and
unused). -/
theorem mixed_terms_l19 (d : ℕ) : MixedTermsTarget.{u} d :=
  SourceExpansion.mixed_terms d (terminal_mixed_moment_l19 d) (fixed_order_l2_l19 d)

/-- **`FirstMomentSeries`** (`FirstMomentSeriesTarget`; TeX 796, 5856-5857). -/
theorem first_moment_series_l19 (d : ℕ) : FirstMomentSeriesTarget.{u} d :=
  SourceExpansion.first_moment_series d (terminal_mixed_moment_l19 d) (fixed_order_l2_l19 d)

/-- **`L:vertex-crude`** (`VertexCrudeTarget`; TeX 2062-2074, proof 2076-2145). -/
theorem vertex_crude_l19 (d : ℕ) : VertexCrudeTarget.{u} d :=
  SourceVertexCrude.vertex_crude d (terminal_mixed_moment_l19 d) (fixed_order_l2_l19 d)

/-! ### Non-vacuity at the constructed model M9 -/

/-- **`MixedMoment` at M9** (gate): under `H:homog`, the named input `MixedMoment` holds for the
chaos terms and solution built on the constructed source field `m9`. -/
theorem mixedMoment_m9_l19 {d : ℕ} {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha α₀ Γ μ) {t : ℝ} (ht : 0 < t) (x : Rd d) :
    MixedMoment d α₀ Γ (m9 (source_field_l19 d) hH).P
      (srcX (m9 (source_field_l19 d) hH).field t ht.le x)
      (srcU (m9 (source_field_l19 d) hH).field t ht.le x) t :=
  mixed_terms_l19.{0} d hH _ _ (m9 (source_field_l19 d) hH).field t ht x

/-- **`FirstMomentSeries` at M9** (gate). -/
theorem firstMomentSeries_m9_l19 {d : ℕ} {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha α₀ Γ μ) {t : ℝ} (ht : 0 < t) (x : Rd d) :
    FirstMomentSeries (m9 (source_field_l19 d) hH).P
      (srcX (m9 (source_field_l19 d) hH).field t ht.le x)
      (srcU (m9 (source_field_l19 d) hH).field t ht.le x) :=
  first_moment_series_l19.{0} d hH _ _ (m9 (source_field_l19 d) hH).field t ht x

/-! ### The moment steps for a diagram bound (d = 1, 2, 3) -/

section MomentSteps

variable {d : ℕ} {α₀ : ℝ} {Γ : Measure (Rd d)} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
  {X : ℕ → Ω → ℝ} {v : Ω → ℝ} {t : ℝ}

/-- The moment sentences of `L:crude-corrected` (`E:crude-corrected`, TeX 1980-1984; Step 2,
2036-2053) at the horizon `t > 0`, conditional on the supplied `MixedMoment` at `t` (the first
binder `h`) and the diagram form of its first inequality at every positive noise width (`hdiag`,
constants `C, θ₀ > 0`): the steps of `CrudeCorrected.crude_corrected_paper`, for any
dimension. -/
theorem crude_moments_of_diagrams (h : MixedMoment d α₀ Γ P X v t) {C θ₀ : ℝ} (hC : 0 < C)
    (hθ₀ : 0 < θ₀) (ht : 0 < t)
    (hdiag : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, 1 ≤ n →
      ∑ D ∈ Pi2 n n, diagram (waveGreen d) (covEps Γ ε) α₀ n n D t ≤
        ENNReal.ofReal (Real.exp (2 * θ₀ * t) * C ^ n * t ^ (2 * n) / (n ! : ℝ))) :
    (∀ n : ℕ, 1 ≤ n → ∫ ω, X n ω ^ 2 ∂P ≤ Real.exp (2 * θ₀ * t) * C ^ n * t ^ (2 * n) / n !) ∧
      ∫ ω, v ω ^ 2 ∂P ≤ 2 * Real.exp (2 * θ₀ * t + 2 * C * t ^ 2) := by
  have hX : ∀ n : ℕ, 1 ≤ n → ∫ ω, X n ω * X n ω ∂P ≤
      Real.exp (2 * θ₀ * t) * C ^ n * t ^ (2 * n) / n ! := fun n hn =>
    moment_le_of_diagrams h (by positivity) fun ε hε => hdiag ε hε n hn
  refine ⟨fun n hn => ?_, CrudeCorrected.secondMoment_le_crude h hθ₀ hC ht hX⟩
  simp_rw [sq]
  exact hX n hn

/-- The moment sentences of `P:envelope` (TeX 2353-2365, proof 2398-2406) from `E:homogeneous-envelope` at the
horizon `t`: the steps of `HomogeneousEnvelope.envelope_paper`, for any dimension. -/
theorem envelope_moments_of_diagrams (h : MixedMoment d α₀ Γ P X v t) {K β : ℝ} (hK : 0 < K)
    (hβ : 2 < β) (ht : 0 < t)
    (hdiag : ∀ ε : ℝ, 0 < ε → ∀ (m n k : ℕ), m + n = 2 * k → 1 ≤ k → ∀ θ : ℝ, 0 < θ →
      ∑ D ∈ Pi2 m n, diagram (waveGreen d) (covEps Γ ε) α₀ m n D t ≤
        ENNReal.ofReal ((Pi2 m n).card * K ^ k * Real.exp (2 * θ * t) * θ ^ (-(β * k)))) :
    (∀ m n k : ℕ, m + n = 2 * k → 1 ≤ k → ∀ θ : ℝ, 0 < θ →
      ∫ ω, X m ω * X n ω ∂P ≤ (Pi2 m n).card * K ^ k * Real.exp (2 * θ * t) *
        θ ^ (-(β * k))) ∧
      ∫ ω, v ω ^ 2 ∂P ≤ BK K β t := by
  have hmix : ∀ m n k : ℕ, m + n = 2 * k → 1 ≤ k → ∀ θ : ℝ, 0 < θ →
      ∫ ω, X m ω * X n ω ∂P ≤ (Pi2 m n).card * K ^ k * Real.exp (2 * θ * t) *
        θ ^ (-(β * k)) := fun m n k hmn hk θ hθ =>
    moment_le_of_diagrams h (by positivity) fun ε hε => hdiag ε hε m n k hmn hk θ hθ
  refine ⟨hmix, ?_⟩
  obtain ⟨hsum, -⟩ := summable_termBK_and_le hK hβ ht
  have hA : ∀ k : ℕ, 1 ≤ k → (coeffALim d Γ α₀ k t).toReal ≤ termBK K β t k := by
    intro k hk
    have hk' : k ≠ 0 := by omega
    rw [h.coeffA_eq k]
    simp only [termBK, hk', ↓reduceIte]
    have hPk : (0 : ℝ) < ((2 * k - 1)‼ : ℝ) := by exact_mod_cast Nat.doubleFactorial_pos _
    calc ∑ m ∈ Finset.range (2 * k + 1), ∫ ω, X m ω * X (2 * k - m) ω ∂P
        ≤ ∑ _m ∈ Finset.range (2 * k + 1), ((2 * k - 1)‼ : ℝ) * K ^ k *
            ⨅ θ : Ioi (0 : ℝ), Real.exp (2 * θ * t) * (θ : ℝ) ^ (-(β * k)) := by
          refine Finset.sum_le_sum fun m hm => ?_
          have hm' : m + (2 * k - m) = 2 * k := by
            have := Finset.mem_range.1 hm; omega
          refine le_mul_iInf (by positivity) fun θ hθ => ?_
          have := hmix m (2 * k - m) k hm' hk θ hθ
          rw [DiagramModel.card_Pi2 hm'] at this
          linarith
      _ = _ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  rw [h.secondMoment_eq, h.2.2.2.summable.tsum_eq_zero_add, BK, hsum.tsum_eq_zero_add]
  have h0 : termBK K β t 0 = 0 := by simp [termBK]
  rw [h0, zero_add, DiagramModel.coeffALim_zero, ENNReal.toReal_one]
  have := Summable.tsum_le_tsum (fun k => hA (k + 1) (by omega))
    (h.2.2.2.summable.comp_injective (add_left_injective 1))
    (hsum.comp_injective (add_left_injective 1))
  linarith

end MomentSteps

/-- `E:homogeneous-envelope` in d = 1, 2, 3 (TeX 2354-2358, proof 2382-2397): `EnvelopeFinal` (d = 1, 2) and
`WickFinal.homogeneous_envelope_diagrams_three_l18` (d = 3). -/
theorem homogeneous_diagrams {d : ℕ} {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha α₀ Γ μ) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ∀ (m n k : ℕ), m + n = 2 * k → 1 ≤ k →
      ∀ t θ : ℝ, 0 < t → 0 < θ →
        ∑ D ∈ Pi2 m n, diagram (waveGreen d) (covEps Γ ε) α₀ m n D t ≤
          ENNReal.ofReal ((Pi2 m n).card * K ^ k * Real.exp (2 * θ * t) *
            θ ^ (-((4 - alpha - α₀) * k))) := by
  rcases hH.dim with h | h | h
  · exact EnvelopeFinal.homogeneous_envelope_diagrams_l17 hH (Or.inl h)
  · exact EnvelopeFinal.homogeneous_envelope_diagrams_l17 hH (Or.inr h)
  · subst h
    exact WickFinal.homogeneous_envelope_diagrams_three_l18 hH

/-! ### The seven consumer rows -/

/-- **`L:crude-corrected`, d = 1, 2, 3** (TeX 1978-2054 at revision edf7085f (book 1.1.3)), for
the chaos terms and solution of every source field under `H:homog`: `MixedMoment` discharged by
`mixed_terms_l19`; adds the d = 3 moment sentence (`WickFinal.crude_corrected_diagrams_three_l18`
with the moment steps of `CrudeCorrected`).  Successor of `EnvelopeFinal.crude_corrected_paper_l17`. -/
theorem crude_corrected_paper_l19 {d : ℕ} {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha α₀ Γ μ) :
    ∃ C θ₀ : ℝ, 0 < C ∧ 0 < θ₀ ∧ ∀ (t : ℝ) (ht : 0 < t) {Ω : Type u} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (W : SrcPt d → Ω → ℝ) (hW : SourceField α₀ Γ P W)
      (x : Rd d),
      (∀ n : ℕ, 1 ≤ n → ∫ ω, srcX hW t ht.le x n ω ^ 2 ∂P ≤
        Real.exp (2 * θ₀ * t) * C ^ n * t ^ (2 * n) / n !) ∧
      ∫ ω, srcU hW t ht.le x ω ^ 2 ∂P ≤ 2 * Real.exp (2 * θ₀ * t + 2 * C * t ^ 2) := by
  obtain ⟨C, θ₀, hC, hθ₀, hdiag⟩ := SourceExpansion.crude_diagrams hH
  exact ⟨C, θ₀, hC, hθ₀, fun t ht Ω _ P _ W hW x =>
    crude_moments_of_diagrams (mixed_terms_l19 d hH P W hW t ht x) hC hθ₀ ht
      fun ε hε n hn => hdiag ε hε n t hn ht⟩

/-- **`P:envelope`, d = 1, 2, 3** (TeX 2352-2433 at revision edf7085f (book 1.1.3)), for the chaos
terms and solution of every source field under `H:homog`; adds d = 3
(`WickFinal.homogeneous_envelope_diagrams_three_l18`).  Successor of
`EnvelopeFinal.envelope_paper_l17`. -/
theorem envelope_paper_l19 {d : ℕ} {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha α₀ Γ μ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (t : ℝ) (ht : 0 < t) {Ω : Type u} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (W : SrcPt d → Ω → ℝ) (hW : SourceField α₀ Γ P W)
      (x : Rd d),
      (∀ m n k : ℕ, m + n = 2 * k → 1 ≤ k → ∀ θ : ℝ, 0 < θ →
        ∫ ω, srcX hW t ht.le x m ω * srcX hW t ht.le x n ω ∂P ≤
          (Pi2 m n).card * K ^ k * Real.exp (2 * θ * t) * θ ^ (-((4 - alpha - α₀) * k))) ∧
      ∫ ω, srcU hW t ht.le x ω ^ 2 ∂P ≤ BK K (4 - alpha - α₀) t := by
  obtain ⟨K, hK, hdiag⟩ := homogeneous_diagrams hH
  have hβ : 2 < 4 - alpha - α₀ := by linarith [hH.threshold]
  exact ⟨K, hK, fun t ht Ω _ P _ W hW x =>
    envelope_moments_of_diagrams (mixed_terms_l19 d hH P W hW t ht x) hK hβ ht
      fun ε hε m n k hmn hk θ hθ => hdiag ε hε m n k hmn hk t θ ht hθ⟩

/-- **`P:d1-upper`, Riesz case** (TeX 5454-5466 at revision edf7085f (book 1.1.3)), for the chaos
terms and solution of every source field.  Successor of `D1Upper.d1_upper_paper_riesz` with
`MixedMoment` discharged; ADDS the hypothesis `hH : HomogCovariance 1 α α₀ (volume.withDensity
(riesz c α)) μ` (needed by `P:mixed`; the Riesz instance of `H:homog` was not formalized when
this wrapper was written; this wrapper keeps `hH`; since wave L20 the instance is
`RieszInstanceOne.riesz_homogCovariance_one`, and `CleanupWrappers.d1_upper_paper_closed_l20`
takes no `hH`). -/
theorem d1_upper_paper_l19 {c α α₀ t : ℝ} {μ : Measure (Rd 1)}
    (hH : HomogCovariance 1 α α₀ (volume.withDensity (riesz c α)) μ) (hα₀0 : 0 < α₀)
    (hα₀1 : α₀ < 1) (hc : 0 < c) (hα0 : 0 < α) (hα1 : α < 1) (ht : 0 < t) {Ω : Type u}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {W : SrcPt 1 → Ω → ℝ}
    (hW : SourceField α₀ (volume.withDensity (riesz c α)) P W) (x : Rd 1) :
    (∀ ε : ℝ, 0 < ε → ∀ k : ℕ, 1 ≤ k →
      coeffA (waveGreen 1) (covEps (volume.withDensity (riesz c α)) ε) α₀ k t ≤
        ENNReal.ofReal ((2 * Zc α₀ * Ksp c α) ^ k * t ^ ((4 - α - α₀) * k) /
          (k ! * (k : ℝ) ^ ((2 - α) * k))) ∧
      coeffA (waveGreen 1) (covEps (volume.withDensity (riesz c α)) ε) α₀ k t ≤
        ENNReal.ofReal ((2 * Zc α₀ * Ksp c α) ^ k * t ^ ((4 - α - α₀) * k) /
          (k ! : ℝ) ^ (3 - α))) ∧
    (∀ k : ℕ, 1 ≤ k →
      ∑ m ∈ Finset.range (2 * k + 1),
          ∫ ω, srcX hW t ht.le x m ω * srcX hW t ht.le x (2 * k - m) ω ∂P ≤
        (2 * Zc α₀ * Ksp c α) ^ k * t ^ ((4 - α - α₀) * k) /
          (k ! * (k : ℝ) ^ ((2 - α) * k)) ∧
      (2 * Zc α₀ * Ksp c α) ^ k * t ^ ((4 - α - α₀) * k) / (k ! * (k : ℝ) ^ ((2 - α) * k)) ≤
        (2 * Zc α₀ * Ksp c α) ^ k * t ^ ((4 - α - α₀) * k) / (k ! : ℝ) ^ (3 - α)) ∧
    ∫ ω, srcU hW t ht.le x ω ^ 2 ∂P ≤ Real.exp ((3 - α) * (2 * Zc α₀ * Ksp c α) ^ (1 / (3 - α)) *
      t ^ ((4 - α - α₀) / (3 - α))) :=
  D1Upper.d1_upper_paper_riesz hα₀0 hα₀1 hc hα0 hα1 ht (mixed_terms_l19 1 hH P W hW t ht x)

/-- `whiteCov 1 = δ₀`. -/
theorem whiteCov_one : WhiteModel.whiteCov 1 = Measure.dirac (0 : Rd 1) := by
  simp [WhiteModel.whiteCov]

/-- Spatial white noise in d = 1 satisfies `H:homog` with `α = 1`
(`WhiteModel.white_homogCovariance` at `c = 1`). -/
theorem white_homog {α₀ : ℝ} (h0 : 0 < α₀) (h1 : α₀ < 1) :
    HomogCovariance 1 1 α₀ (Measure.dirac 0) (WhiteModel.whiteSpectral 1) := by
  have h := WhiteModel.white_homogCovariance (c := 1) zero_le_one h0 h1
  rwa [whiteCov_one] at h

/-- **`L:white-test`** (order-two diagrams, spatial white noise in d = 1) for the chaos terms of
every source field with `Γ = δ₀`: `H:homog` is discharged (`white_homog`), `MixedMoment` by
`mixed_terms_l19`, `X_0 = 1` by `srcX_zero`.  Successor of `OrderTwoDiagrams.white_test_paper`
(which used `0 ≤ t`; here `t > 0`, as `P:mixed` is stated). -/
theorem white_test_paper_l19 {α₀ : ℝ} (h0 : 0 < α₀) (h1 : α₀ < 1) {Ω : Type u}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {W : SrcPt 1 → Ω → ℝ}
    (hW : SourceField α₀ (Measure.dirac 0) P W) {t : ℝ} (ht : 0 < t) (x : Rd 1) :
    ∫ ω, srcX hW t ht.le x 1 ω ^ 2 ∂P = OrderTwoDiagrams.c0 α₀ * t ^ (3 - α₀) ∧
      ∫ ω, srcX hW t ht.le x 2 ω ∂P = OrderTwoDiagrams.c0 α₀ / 2 * t ^ (3 - α₀) ∧
      ∑ m ∈ Finset.range 3, ∫ ω, srcX hW t ht.le x m ω * srcX hW t ht.le x (2 - m) ω ∂P =
        2 * OrderTwoDiagrams.c0 α₀ * t ^ (3 - α₀) :=
  OrderTwoDiagrams.white_test_paper (white_homog h0 h1) ht.le
    (mixed_terms_l19 1 (white_homog h0 h1) P W hW t ht x) (srcX_zero hW t ht.le x)

/-- **`P:low-alpha-upper`** (TeX 5711-5734, proof 5736-5807, at revision edf7085f (book 1.1.3)) for the chaos terms
and solution of every source field under `H:homog`, `α ≤ 1`, `V > 0`.  Successor of
`LowAlphaUpper.low_alpha_upper_moment_paper`. -/
theorem low_alpha_upper_moment_paper_l19 {d : ℕ} {α α₀ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d α α₀ Γ μ) (hα1 : α ≤ 1) (hV : 0 < (specV μ).toReal) {Ω : Type u}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {W : SrcPt d → Ω → ℝ}
    (hW : SourceField α₀ Γ P W) {t : ℝ} (ht : 0 < t) (x : Rd d) :
    (∀ k : ℕ, 1 ≤ k →
      ∑ m ∈ Finset.range (2 * k + 1),
          ∫ ω, srcX hW t ht.le x m ω * srcX hW t ht.le x (2 * k - m) ω ∂P ≤
        (2 * Zc α₀ * Kgen α (specV μ).toReal) ^ k * t ^ ((4 - α - α₀) * k) /
          ((k ! : ℝ) * (k : ℝ) ^ ((2 - α) * k))) ∧
    ∫ ω, srcU hW t ht.le x ω ^ 2 ∂P ≤
      Real.exp (C2 α α₀ (Kgen α (specV μ).toReal) * t ^ LowAlphaUpper.kappa α α₀) :=
  LowAlphaUpper.low_alpha_upper_moment_paper hH hα1 hV ht (mixed_terms_l19 d hH P W hW t ht x)

/-- **`P:riesz-small`** (order-two Riesz diagrams in d = 1) for the chaos terms of every source
field with `Γ = c|y|^{-α} dy`; the hypothesis `hH` is the original's (the Riesz instance of
`H:homog` was not formalized when this wrapper was written; this wrapper keeps `hH`; since wave
L20 the instance is `RieszInstanceOne.riesz_homogCovariance_one`, and
`CleanupWrappers.riesz_small_paper_closed_l20` takes no `hH`).  Successor of
`RieszFourDiagrams.riesz_small_paper'`
(which used `0 ≤ t`; here `t > 0`). -/
theorem riesz_small_paper_l19 {c α α₀ : ℝ} {μ : Measure (Rd 1)}
    (hH : HomogCovariance 1 α α₀ ((volume : Measure (Rd 1)).withDensity (riesz c α)) μ)
    (hc : 0 < c) (hα : 0 < α) (hα1 : α < 1) (hα0 : 0 < α₀) (hα01 : α₀ < 1) {Ω : Type u}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {W : SrcPt 1 → Ω → ℝ}
    (hW : SourceField α₀ ((volume : Measure (Rd 1)).withDensity (riesz c α)) P W) {t : ℝ}
    (ht : 0 < t) (x : Rd 1) :
    ∫ ω, srcX hW t ht.le x 2 ω ∂P = c * t ^ (4 - α - α₀) /
        ((1 - α) * (2 - α - α₀) * (3 - α - α₀) * (4 - α - α₀)) ∧
      ∫ ω, srcX hW t ht.le x 1 ω ^ 2 ∂P =
        c / ((1 - α) * (2 - α)) * ∫ v in (0 : ℝ)..t, v ^ (-α₀) * OrderTwoDiagrams.rbr t α v ∧
      ∑ m ∈ Finset.range 3, ∫ ω, srcX hW t ht.le x m ω * srcX hW t ht.le x (2 - m) ω ∂P =
        ∫ ω, srcX hW t ht.le x 1 ω ^ 2 ∂P + 2 * ∫ ω, srcX hW t ht.le x 2 ω ∂P :=
  RieszFourDiagrams.riesz_small_paper' hH hc hα hα1 hα0 hα01 ht.le
    (mixed_terms_l19 1 hH P W hW t ht x) (srcX_zero hW t ht.le x)

/-- **`C:d1-first-calibration`** (TeX 5830-5842, proof 5844-5864, at revision edf7085f (book 1.1.3)) for the chaos
terms and solution of every source field under `H:homog`, `α ≤ 1`, `V > 0`: `MixedMoment` and
`FirstMomentSeries` discharged.  Successor of `LowAlphaUpper.first_calibration_paper`. -/
theorem first_calibration_paper_l19 {d : ℕ} {α α₀ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d α α₀ Γ μ) (hα1 : α ≤ 1) (hV : 0 < (specV μ).toReal) {Ω : Type u}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {W : SrcPt d → Ω → ℝ}
    (hW : SourceField α₀ Γ P W) {t : ℝ} (ht : 0 < t) (x : Rd d) :
    (∀ k : ℕ, 1 ≤ k → ∫ ω, srcX hW t ht.le x (2 * k) ω ∂P ≤
      (Zc α₀ * Kgen α (specV μ).toReal / 2 ^ (3 - α)) ^ k * t ^ ((4 - α - α₀) * k) /
        ((k ! : ℝ) * (k : ℝ) ^ ((2 - α) * k)) ∧
      (Zc α₀ * Kgen α (specV μ).toReal / 2 ^ (3 - α)) ^ k * t ^ ((4 - α - α₀) * k) /
          ((k ! : ℝ) * (k : ℝ) ^ ((2 - α) * k)) ≤
        (Zc α₀ * Kgen α (specV μ).toReal / 2 ^ (3 - α)) ^ k * t ^ ((4 - α - α₀) * k) /
          (k ! : ℝ) ^ (3 - α)) ∧
    ∫ ω, srcU hW t ht.le x ω ∂P ≤
      Real.exp (C1 α α₀ (Kgen α (specV μ).toReal) * t ^ LowAlphaUpper.kappa α α₀) ∧
    C1 α α₀ (Kgen α (specV μ).toReal) =
      C2 α α₀ (Kgen α (specV μ).toReal) / 2 ^ ((4 - α) / (3 - α)) ∧
    2 * C1 α α₀ (Kgen α (specV μ).toReal) < C2 α α₀ (Kgen α (specV μ).toReal) :=
  LowAlphaUpper.first_calibration_paper hH hα1 hV ht (mixed_terms_l19 d hH P W hW t ht x)
    (first_moment_series_l19 d hH P W hW t ht x)

/-- **`C:d1-first-calibration`, Riesz case** for the chaos terms and solution of every source
field with `Γ = c|y|^{-α} dy`.  Successor of `LowAlphaUpper.first_calibration_riesz_paper`;
ADDS `hH : HomogCovariance 1 α α₀ (volume.withDensity (riesz c α)) μ` (needed by `P:mixed`; the
Riesz instance of `H:homog` is not formalized in the library). -/
theorem first_calibration_riesz_paper_l19 {c α α₀ : ℝ} {μ : Measure (Rd 1)}
    (hH : HomogCovariance 1 α α₀ (volume.withDensity (riesz c α)) μ) (hc : 0 < c)
    (hα0 : 0 < α) (hα1 : α < 1) (hα₀0 : 0 < α₀) (hα₀1 : α₀ < 1) {Ω : Type u}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {W : SrcPt 1 → Ω → ℝ}
    (hW : SourceField α₀ (volume.withDensity (riesz c α)) P W) {t : ℝ} (ht : 0 < t)
    (x : Rd 1) :
    (∀ k : ℕ, 1 ≤ k → ∫ ω, srcX hW t ht.le x (2 * k) ω ∂P ≤
      (Zc α₀ * Ksp c α / 2 ^ (3 - α)) ^ k * t ^ ((4 - α - α₀) * k) /
        ((k ! : ℝ) * (k : ℝ) ^ ((2 - α) * k)) ∧
      (Zc α₀ * Ksp c α / 2 ^ (3 - α)) ^ k * t ^ ((4 - α - α₀) * k) /
          ((k ! : ℝ) * (k : ℝ) ^ ((2 - α) * k)) ≤
        (Zc α₀ * Ksp c α / 2 ^ (3 - α)) ^ k * t ^ ((4 - α - α₀) * k) / (k ! : ℝ) ^ (3 - α)) ∧
    ∫ ω, srcU hW t ht.le x ω ∂P ≤ Real.exp (C1 α α₀ (Ksp c α) * t ^ LowAlphaUpper.kappa α α₀) ∧
    C1 α α₀ (Ksp c α) = C2 α α₀ (Ksp c α) / 2 ^ ((4 - α) / (3 - α)) ∧
    2 * C1 α α₀ (Ksp c α) < C2 α α₀ (Ksp c α) :=
  LowAlphaUpper.first_calibration_riesz_paper hc hα0 hα1 hα₀0 hα₀1 ht
    (mixed_terms_l19 1 hH P W hW t ht x) (first_moment_series_l19 1 hH P W hW t ht x)

/-- **`C:d1-first-calibration`, white case** (`Γ = c δ₀`, `c > 0`) for the chaos terms and
solution of every source field: `H:homog` discharged by `WhiteModel.white_homogCovariance`.
Successor of `LowAlphaUpper.first_calibration_white_paper`. -/
theorem first_calibration_white_paper_l19 {c α₀ : ℝ} (hc : 0 < c) (hα₀0 : 0 < α₀)
    (hα₀1 : α₀ < 1) {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : SrcPt 1 → Ω → ℝ} (hW : SourceField α₀ (WhiteModel.whiteCov c) P W) {t : ℝ}
    (ht : 0 < t) (x : Rd 1) :
    (∀ k : ℕ, 1 ≤ k → ∫ ω, srcX hW t ht.le x (2 * k) ω ∂P ≤
      (Zc α₀ * c / 2 ^ (3 - 1 : ℝ)) ^ k * t ^ ((4 - 1 - α₀) * k) /
        ((k ! : ℝ) * (k : ℝ) ^ ((2 - 1 : ℝ) * k)) ∧
      (Zc α₀ * c / 2 ^ (3 - 1 : ℝ)) ^ k * t ^ ((4 - 1 - α₀) * k) /
          ((k ! : ℝ) * (k : ℝ) ^ ((2 - 1 : ℝ) * k)) ≤
        (Zc α₀ * c / 2 ^ (3 - 1 : ℝ)) ^ k * t ^ ((4 - 1 - α₀) * k) / (k ! : ℝ) ^ (3 - 1 : ℝ)) ∧
    ∫ ω, srcU hW t ht.le x ω ∂P ≤ Real.exp (C1 1 α₀ c * t ^ LowAlphaUpper.kappa 1 α₀) ∧
    C1 1 α₀ c = C2 1 α₀ c / 2 ^ ((4 - 1 : ℝ) / (3 - 1)) ∧
    2 * C1 1 α₀ c < C2 1 α₀ c :=
  LowAlphaUpper.first_calibration_white_paper hc hα₀0 hα₀1 ht
    (mixed_terms_l19 1 (WhiteModel.white_homogCovariance hc.le hα₀0 hα₀1) P W hW t ht x)
    (first_moment_series_l19 1 (WhiteModel.white_homogCovariance hc.le hα₀0 hα₀1) P W hW t ht x)

end StratonovichHAMSecondMoment.SourceFinal
