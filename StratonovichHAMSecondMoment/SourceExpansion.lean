module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L19, item E, second half: the `L²` chaos expansion of the source fields and the discharge
of the named inputs `DiagramModel.MixedMoment` (`P:mixed`, whole) and
`LowAlphaUpper.FirstMomentSeries` for `X = srcX`, `u = srcU`.  Main TeX file
`notes/notes_stratonovich_ham_second_moment.tex` at revision edf7085f (book 1.1.3):
* `E:expansion` 542-549 (`u = Σ_n S_n(g_n)`), `X_n` 796;
* `P:mixed` 834-849 (`E:full-second` 844-847), proof Step 3 908-926 (norm summability 911-913,
  `U_N → u` in `L²` 916-920, expansion of `E U_N²` and regrouping 921-925);
* `L:crude-corrected` 1978-2054 (the first inequality of `E:crude-corrected`, the display
  1980-1984, derived in Step 2, 2036-2041, gives the norm summability; TeX 911-913 names it as
  one of two independent routes);
* `FirstMomentSeries`: 796 and 5856-5857 ("the `L²` expansion permits taking expectations of
  partial sums").

Proved here, with C's `TerminalMixedMomentTarget` and D's `FixedOrderL2Target` as hypotheses
(nothing else supplied):
* `norm_XL2_le`: `‖X_n‖ ≤ e^{θ₀t} √((Ct²)^n/n!)` with L17/L18's crude-corrected constants;
* `expansion_l2` (`ExpansionL2Target`): `Σ ‖X_n‖ < ∞` and `Σ X_n = u` in `L²`;
* `mixed_terms` (`MixedTermsTarget`): `DiagramModel.MixedMoment` for `srcX`, `srcU`, i.e.
  `P:mixed` whole (diagram limits, `E:mixed-moment`, `E:full-second`);
* `first_moment_series` (`FirstMomentSeriesTarget`).

Route differences (disclosed):
* Norm summability uses `L:crude-corrected` only (`EnvelopeFinal.crude_corrected_diagrams_l17`
  for d = 1, 2; `WickFinal.crude_corrected_diagrams_three_l18` for d = 3), not
  `L:vertex-crude` (item G); the TeX gives the two as independent routes (911-913).  The bound
  `E X_n² = Σ_D J_{n,n,D}(t) ≤ e^{2θ₀t} C^n t^{2n}/n!` passes to the limit `ε ↓ 0` in the
  diagram sums; summability of `√((Ct²)^n/n!)` is `CrudeCorrected.sq_sum_sqrt_le`.
* `E:full-second`: the TeX's "finite expansions increase ... independent of enumeration"
  (923-925) is replaced by absolute summability of `(m, n) ↦ ⟪X_m, X_n⟫` on `ℕ × ℕ`
  (`|⟪X_m, X_n⟫| ≤ ‖X_m‖‖X_n‖`), the fibrewise sums `Σ_n ⟪X_m, X_n⟫ = ⟪X_m, u⟫`, and the
  regrouping by antidiagonals (`hasSum_inner_antidiagonal`); odd total orders contribute `0`.
  Nonnegativity of the terms is not needed.
* `E u` (`FirstMomentSeries`): `∫ f = ⟪1, f⟫_{L²}` is a continuous linear functional on
  `L²(P)` (`L2.inner_indicatorConstLp_one`), applied to `Σ X_n = u`.

All statements assume `t > 0` (as the frozen targets do); the case `t = 0` is trivial for the
TeX's statements (review note M9: the chain measures of positive order vanish there) and is not
needed by any consumer.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.SourceMixed
public import StratonovichHAMSecondMoment.EnvelopeFinal

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal Real Nat

namespace StratonovichHAMSecondMoment.SourceExpansion

universe u

open HomogHypothesis (Rd HomogCovariance)
open WaveGreen (waveGreen)
open DiagramModel (Pi2 diagram covEps diagramLim coeffALim MixedMoment)
open SourceInterface
open SourceMixed

/-! ### Deterministic inputs -/

/-- **The first inequality of `E:crude-corrected` for the diagram sums, in d = 1, 2, 3** (TeX:
the display 1980-1984; its first inequality derived in Step 2, 2036-2041; at revision edf7085f
(book 1.1.3)): `EnvelopeFinal.crude_corrected_diagrams_l17` (d = 1, 2) and
`WickFinal.crude_corrected_diagrams_three_l18` (d = 3) under `H:homog`. -/
theorem crude_diagrams {d : ℕ} {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha α₀ Γ μ) :
    ∃ C θ₀ : ℝ, 0 < C ∧ 0 < θ₀ ∧ ∀ ε : ℝ, 0 < ε → ∀ (n : ℕ) (t : ℝ), 1 ≤ n → 0 < t →
      ∑ D ∈ Pi2 n n, diagram (waveGreen d) (covEps Γ ε) α₀ n n D t ≤
        ENNReal.ofReal (Real.exp (2 * θ₀ * t) * C ^ n * t ^ (2 * n) / (n ! : ℝ)) := by
  rcases hH.dim with h | h | h
  · exact EnvelopeFinal.crude_corrected_diagrams_l17 hH (Or.inl h)
  · exact EnvelopeFinal.crude_corrected_diagrams_l17 hH (Or.inr h)
  · subst h
    exact WickFinal.crude_corrected_diagrams_three_l18 hH

/-- The diagram limits inherit a bound valid at every noise width. -/
theorem sum_diagramLim_le {d : ℕ} {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha α₀ Γ μ) {t : ℝ} (ht : 0 < t) (m n : ℕ) {B : ℝ≥0∞}
    (hB : ∀ ε : ℝ, 0 < ε → ∑ D ∈ Pi2 m n, diagram (waveGreen d) (covEps Γ ε) α₀ m n D t ≤ B) :
    ∑ D ∈ Pi2 m n, diagramLim d Γ α₀ m n D t ≤ B := by
  refine le_of_tendsto (tendsto_finsetSum _ fun D hD =>
    (WickFinal.diagramLimits_homog_l18 d hH t ht).1 m n D hD) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hB ε hε

/-- Auxiliary: `Σ_n √(x^n/n!)` converges (partial sums bounded by `√(2e^{2x})`,
`CrudeCorrected.sq_sum_sqrt_le`). -/
theorem summable_sqrt_pow_div_factorial {x : ℝ} (hx : 0 ≤ x) :
    Summable fun n : ℕ => Real.sqrt (x ^ n / n !) := by
  refine summable_of_sum_range_le (c := Real.sqrt (2 * Real.exp (2 * x)))
    (fun n => Real.sqrt_nonneg _) fun N => ?_
  have h0 : 0 ≤ ∑ n ∈ Finset.range N, Real.sqrt (x ^ n / n !) :=
    Finset.sum_nonneg fun n _ => Real.sqrt_nonneg _
  rw [← Real.sqrt_sq h0]
  exact Real.sqrt_le_sqrt (CrudeCorrected.sq_sum_sqrt_le x hx N)

/-- Auxiliary (the regrouping of `E:full-second`, TeX 921-925): for an absolutely summable
series `Σ X_n = u` in a real inner product space, `⟪u, u⟫ = Σ_j Σ_{m+n=j} ⟪X_m, X_n⟫`. -/
theorem hasSum_inner_antidiagonal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {X : ℕ → E} {v : E} (hs : Summable fun n => ‖X n‖) (hv : HasSum X v) :
    HasSum (fun j => ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal j, inner ℝ (X ij.1) (X ij.2))
      (inner ℝ v v) := by
  set f : ℕ × ℕ → ℝ := fun ij => inner ℝ (X ij.1) (X ij.2) with hf
  have hfs : Summable f := by
    refine Summable.of_norm_bounded
      (hs.mul_of_nonneg hs (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)) fun ij => ?_
    rw [Real.norm_eq_abs]
    exact abs_real_inner_le_norm _ _
  have hrow : ∀ m, HasSum (fun n => f (m, n)) (inner ℝ (X m) v) := by
    intro m
    have h := (innerSL ℝ (X m)).hasSum hv
    simpa only [innerSL_apply_apply] using h
  have hcol : HasSum (fun m => inner ℝ (X m) v) (inner ℝ v v) := by
    have h := (innerSL ℝ v).hasSum hv
    simp only [innerSL_apply_apply] at h
    convert h using 2 with m
    exact real_inner_comm _ _
  have hsum : HasSum f (inner ℝ v v) := by
    have h1 := hfs.hasSum.prod_fiberwise hrow
    rw [hcol.unique h1]
    exact hfs.hasSum
  have h2 := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).hasSum_iff.2 hsum
  refine h2.sigma fun j => ?_
  have h3 := hasSum_fintype
    (fun c : ↥(Finset.HasAntidiagonal.antidiagonal j) => f (c : ℕ × ℕ))
  rw [Finset.sum_coe_sort] at h3
  exact h3

section Random

variable {d : ℕ} {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)} {Ω : Type u} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {W : SrcPt d → Ω → ℝ}

/-- **The norm bound behind `Σ ‖X_n‖ < ∞`** (TeX 908-913 with `E:crude-corrected`, the display
1980-1984, its first inequality derived in Step 2, 2036-2041; at revision edf7085f (book 1.1.3)):
conditional on the item targets `TerminalMixedMomentTarget` and `FixedOrderL2Target`,
`H:homog` and the positive-width diagram bound `hdiag` at every positive horizon, with constants
`C, θ₀ > 0` (those of `crude_diagrams`): `‖X_n‖ ≤ e^{θ₀t} √((Ct²)^n/n!)` for every `n` and
`t > 0` (`n = 0`: `‖X_0‖ = 1`). -/
theorem norm_XL2_le (hM : TerminalMixedMomentTarget.{u} d) (hX : FixedOrderL2Target.{u} d)
    (hH : HomogCovariance d alpha α₀ Γ μ) {C θ₀ : ℝ} (hC : 0 < C) (hθ₀ : 0 < θ₀)
    (hdiag : ∀ ε : ℝ, 0 < ε → ∀ (n : ℕ) (t : ℝ), 1 ≤ n → 0 < t →
      ∑ D ∈ Pi2 n n, diagram (waveGreen d) (covEps Γ ε) α₀ n n D t ≤
        ENNReal.ofReal (Real.exp (2 * θ₀ * t) * C ^ n * t ^ (2 * n) / (n ! : ℝ)))
    (hW : SourceField α₀ Γ P W) {t : ℝ} (ht : 0 < t) (x : Rd d) (n : ℕ) :
    ‖XL2 hW t ht.le x n‖ ≤ Real.exp (θ₀ * t) * Real.sqrt ((C * t ^ 2) ^ n / n !) := by
  have hb0 : 0 ≤ Real.exp (θ₀ * t) * Real.sqrt ((C * t ^ 2) ^ n / n !) := by positivity
  have hbsq : (Real.exp (θ₀ * t) * Real.sqrt ((C * t ^ 2) ^ n / n !)) ^ 2 =
      Real.exp (2 * θ₀ * t) * C ^ n * t ^ (2 * n) / n ! := by
    rw [mul_pow, Real.sq_sqrt (by positivity), ← Real.exp_nat_mul, mul_pow, ← pow_mul,
      mul_comm 2 n]
    push_cast
    ring_nf
  refine (sq_le_sq₀ (norm_nonneg _) hb0).1 ?_
  rw [hbsq, ← real_inner_self_eq_norm_sq, inner_XL2 hM hX hH hW ht x n n]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [DiagramModel.Pi2_zero_zero, Finset.sum_singleton, DiagramModel.diagramLim_zero_zero,
      ENNReal.toReal_one]
    simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one, mul_zero]
    exact Real.one_le_exp (by positivity)
  · have hfin : ∀ D ∈ Pi2 n n, diagramLim d Γ α₀ n n D t ≠ ⊤ := fun D hD =>
      (WickFinal.diagramLimits_homog_l18 d hH t ht).2 n n D hD
    rw [← ENNReal.toReal_sum hfin]
    have hle := sum_diagramLim_le hH ht n n fun ε hε => hdiag ε hε n t hn ht
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hle

/-- **`E:expansion` in `L²`** (`ExpansionL2Target`; TeX lines 542-549 with 796, and `P:mixed`
Step 3 908-919 at revision edf7085f (book 1.1.3)), for every source field, with C's and D's
targets as hypotheses: `Σ_n ‖X_n(t,x)‖ < ∞` and `u(t,x) = Σ_n X_n(t,x)` in `L²` (`U_N → u`).
Norm summability is from `L:crude-corrected` (`crude_diagrams`, `norm_XL2_le`). -/
theorem expansion_l2 (d : ℕ) (hM : TerminalMixedMomentTarget.{u} d)
    (hX : FixedOrderL2Target.{u} d) : ExpansionL2Target.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW t ht x
  obtain ⟨C, θ₀, hC, hθ₀, hdiag⟩ := crude_diagrams hH
  have hs : Summable fun n => ‖XL2 hW t ht.le x n‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => norm_XL2_le hM hX hH hC hθ₀ hdiag hW ht x n) ?_
    exact (summable_sqrt_pow_div_factorial (by positivity)).mul_left _
  exact ⟨hs, (Summable.of_norm hs).hasSum⟩

/-- **`E:full-second`** (TeX lines 844-847, proof Step 3 908-926 at revision edf7085f (book
1.1.3)): `E u² = Σ_k A_k(t)` with `A_k(t) = Σ_{m ≤ 2k} Σ_D J_{m,2k-m,D}(t)` (`coeffALim`). -/
theorem hasSum_coeffALim (hM : TerminalMixedMomentTarget.{u} d) (hX : FixedOrderL2Target.{u} d)
    (hH : HomogCovariance d alpha α₀ Γ μ) (hW : SourceField α₀ Γ P W) {t : ℝ} (ht : 0 < t)
    (x : Rd d) :
    HasSum (fun k => (coeffALim d Γ α₀ k t).toReal)
      (inner ℝ (uL2 hW t ht.le x) (uL2 hW t ht.le x)) := by
  obtain ⟨hs, hu⟩ := expansion_l2 d hM hX hH P W hW t ht x
  have hB := hasSum_inner_antidiagonal hs hu
  set g : ℕ × ℕ → ℝ := fun ij => ∑ D ∈ Pi2 ij.1 ij.2, (diagramLim d Γ α₀ ij.1 ij.2 D t).toReal
    with hg
  have hB' : HasSum (fun j => ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal j, g ij)
      (inner ℝ (uL2 hW t ht.le x) (uL2 hW t ht.le x)) := by
    refine hB.congr_fun fun j => ?_
    refine Finset.sum_congr rfl fun ij _ => ?_
    exact (inner_XL2 hM hX hH hW ht x ij.1 ij.2).symm
  have hodd : ∀ j ∉ Set.range (fun k : ℕ => 2 * k),
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal j, g ij = 0 := by
    intro j hj
    refine Finset.sum_eq_zero fun ij hij => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    have hO : Odd (ij.1 + ij.2) := by
      rw [hij]
      rcases Nat.even_or_odd j with ⟨k, hk⟩ | ho
      · exact absurd ⟨k, by simp only; omega⟩ hj
      · exact ho
    simp only [hg, DiagramModel.Pi2_odd hO, Finset.sum_empty]
  have hE := (Function.Injective.hasSum_iff (fun a b h => by simpa using h) hodd).2 hB'
  refine hE.congr_fun fun k => ?_
  simp only [Function.comp_apply]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, DiagramModel.coeffALim,
    ENNReal.toReal_sum fun m _ => ?_]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [ENNReal.toReal_sum fun D hD => (WickFinal.diagramLimits_homog_l18 d hH t ht).2 _ _ D hD]
  · rw [ENNReal.sum_ne_top]
    exact fun D hD => (WickFinal.diagramLimits_homog_l18 d hH t ht).2 _ _ D hD

/-- **`P:mixed`, whole** (`MixedTermsTarget`; TeX lines 834-849, proof 851-927 at revision
edf7085f (book 1.1.3)): for every source field and `t > 0`, the named input
`DiagramModel.MixedMoment` holds for `X = srcX`, `u = srcU`: (1) every diagram limit exists and
is finite (`WickFinal.diagramLimits_homog_l18`); (2) `E:mixed-moment` with integrable products
(`SourceMixed.mixed_moment_srcX`); (3) `u²` is integrable and `E:full-second`
(`hasSum_coeffALim`).  C's and D's targets are hypotheses.  `t > 0` is assumed (the case `t = 0`
is trivial for the TeX and unused). -/
theorem mixed_terms (d : ℕ) (hM : TerminalMixedMomentTarget.{u} d)
    (hX : FixedOrderL2Target.{u} d) : MixedTermsTarget.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW t ht x
  have hDL := WickFinal.diagramLimits_homog_l18 d hH t ht
  refine ⟨fun m n D hD => ⟨hDL.1 m n D hD, hDL.2 m n D hD⟩,
    fun m n => mixed_moment_srcX hM hX hH hW ht x m n,
    (Lp.memLp (uL2 hW t ht.le x)).integrable_sq, ?_⟩
  have hI : ∫ ω, srcU hW t ht.le x ω ^ 2 ∂P =
      inner ℝ (uL2 hW t ht.le x) (uL2 hW t ht.le x) := by
    rw [L2.inner_def]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    beta_reduce
    rw [real_inner_eq, sq]
    rfl
  rw [hI]
  exact hasSum_coeffALim hM hX hH hW ht x

/-- **`FirstMomentSeries` for the source fields** (`FirstMomentSeriesTarget`; TeX lines 796 and
5856-5857 at revision edf7085f (book 1.1.3)): `X_0 = 1` everywhere (`srcX_zero`), `u` is
integrable and `E u = Σ_n E X_n`, because `f ↦ E f = ⟪1, f⟫` is continuous on `L²(P)` and
`Σ X_n = u` in `L²` (`expansion_l2`).  C's and D's targets are hypotheses. -/
theorem first_moment_series (d : ℕ) (hM : TerminalMixedMomentTarget.{u} d)
    (hX : FixedOrderL2Target.{u} d) : FirstMomentSeriesTarget.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW t ht x
  obtain ⟨-, hu⟩ := expansion_l2 d hM hX hH P W hW t ht x
  refine ⟨srcX_zero hW t ht.le x, MemLp.integrable one_le_two (Lp.memLp _), ?_⟩
  set c : Lp ℝ 2 P := indicatorConstLp 2 MeasurableSet.univ (measure_ne_top P univ) (1 : ℝ)
    with hc
  have hI : ∀ f : Lp ℝ 2 P, innerSL ℝ c f = ∫ ω, f ω ∂P := fun f => by
    rw [innerSL_apply_apply, hc, L2.inner_indicatorConstLp_one, Measure.restrict_univ]
  have h := (innerSL ℝ c).hasSum hu
  simp only [hI] at h
  have e : (fun n => ∫ ω, srcX hW t ht.le x n ω ∂P) =
      fun n => ∫ ω, (XL2 hW t ht.le x n : Ω → ℝ) ω ∂P :=
    funext fun n => integral_congr_ae (srcX_ae hH hW ht.le x n)
  rw [e]
  exact h

end Random

end StratonovichHAMSecondMoment.SourceExpansion
