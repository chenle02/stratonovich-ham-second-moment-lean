module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L19, item D (second half): Green smoothing removed before noise smoothing (the regularization
paragraph, TeX lines 1651-1655, and the sentence of `L:joint-fixed-order` 1860-1861, Step 4
1960-1963 at revision edf7085f (book 1.1.3)).

Statement proved (`green_first`, the frozen `GreenFirstTarget` of `SourceInterface`): under
`H:homog`, for every source field (`SourceField`), `t > 0`, `x` and fixed positive vertexwise
widths `a`, the Green-smoothed chain integrals `Y_n^{a,η}(t,x)` (`YaReg`, the Green measures `G`
replaced by `p_η * G`, `TerminalWickRegularization.chainMeasureReg`) converge in `L²(Ω)` to
`Y_n^a(t,x)` (`Ya`) as `η ↓ 0`.

Hypothesis: B's `SourceCovContinuousTarget d` (continuity of the source covariance at fixed
widths), taken with exactly its frozen signature and discharged at integration.

Route (the L13 argument of `TerminalWickRegularization.tendsto_chainIntegral_reg` with the vertex
widths attached; disclosed): the field restricted to vertex-labelled points
`(j, s, y) ↦ W(s, y, a_j)` (`vfield`, a centered Gaussian field on `Fin n × [0,t] × ℝ^d` by
`centeredGaussianField_comp`) has variance at most the finite sum `V_a` of the `n` vertex
variances (TeX 1649-1650: "the largest of the finitely many field variances"; the sum is used
in place of the maximum), so Wick's formula bounds the product integrands by
`√((2n-1)!!) V_a^{n/2}` (`TerminalWick.norm_prodL2_le`); by `hcont` and the discreteness of the
vertex label the field is `L²`-continuous, so `z ↦ ∏_j W(z_j, a_j)` is continuous into `L²`
(`TerminalWickInputs.continuousAt_prodL2`; no cell partition is needed, unlike L13's
`MeanSquareCellContinuous`).  Both integrals are pushed to the noise space of L13
(`chainMeasureReg = noiseMeasure.map (regPt η)`, `chainMeasure_eq_map_noise`), and dominated
convergence with the constant bound and the joint continuity `continuous_regPt` gives the limit.
The statement holds for every `d` (the TeX's sentence is about d = 3, where the Green measures
are used; the cases d = 1, 2 are extra and disclosed in `GreenFirstTarget`).
-/
public import Mathlib
public import StratonovichHAMSecondMoment.SourceInterface

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal Real Nat

namespace StratonovichHAMSecondMoment.SourceGreenFirst

universe u

open HomogHypothesis (Rd HomogCovariance)
open FiniteWick (CenteredGaussianField)
open TerminalWick (Pt prodL2)
open TerminalWickInputs (chainMeasure fieldL2)
open TerminalWickRegularization (chainMeasureReg noiseMeasure regPt)
open LowAlphaConvolution (gammaEps)
open SourceInterface

variable {d : ℕ}

/-! ### Vertex-labelled points and the restricted field -/

/-- The space-time part of a chain point, as a point of `[0,∞) × ℝ^d`. -/
def stPt {t : ℝ} (y : Pt d t) : ↥(Set.Ici (0 : ℝ)) × Rd d :=
  (⟨(y.1 : ℝ), y.1.2.1⟩, y.2)

theorem continuous_stPt {t : ℝ} : Continuous (stPt (d := d) (t := t)) :=
  ((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk continuous_snd

/-- A vertex-labelled chain point `(j, (s, y))` with the width `a_j` attached. -/
def vpt {t : ℝ} {n : ℕ} (a : Fin n → PosW) (q : Fin n × Pt d t) : SrcPt d :=
  (stPt q.2, a q.1)

theorem attach_eq_vpt {t : ℝ} {n : ℕ} (a : Fin n → PosW) (z : Fin n → Pt d t) :
    attach a z = fun j => vpt a (j, z j) := rfl

section Field

variable {α₀ : ℝ} {Γ : Measure (Rd d)} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : SrcPt d → Ω → ℝ}

/-- The source field restricted to the vertex-labelled points of a width vector `a`. -/
theorem vfield (hW : SourceField α₀ Γ P W) {t : ℝ} {n : ℕ} (a : Fin n → PosW) :
    CenteredGaussianField (fun q : Fin n × Pt d t => W (vpt a q))
      (fun q q' => srcCov α₀ Γ (vpt a q) (vpt a q')) P :=
  centeredGaussianField_comp hW (vpt a)

/-- The product integrand of `Y_n^a` is the product integrand of the restricted field. -/
theorem prodL2_attach (hW : SourceField α₀ Γ P W) {t : ℝ} {n : ℕ} (a : Fin n → PosW)
    (z : Fin n → Pt d t) :
    prodL2 hW (attach a z) = prodL2 (vfield hW (t := t) a) (fun j => (j, z j)) := rfl

/-- The variance of a source point depends only on its width. -/
def wvar (α₀ : ℝ) (Γ : Measure (Rd d)) (w : PosW) : ℝ :=
  (WickInterface.kerA α₀ (WickInterface.capSet w.del) 0).toReal *
    gammaEps Γ (w.eps + w.eps) 0

theorem wvar_nonneg (w : PosW) : 0 ≤ wvar α₀ Γ w :=
  mul_nonneg ENNReal.toReal_nonneg
    (LowAlphaConvolution.gammaEps_nonneg Γ (add_pos w.eps_pos w.eps_pos).le _)

/-- **The finite variance bound** (TeX 1649-1650): the restricted field has variance at most
`V_a = Σ_j var(a_j)` (a sum of the finitely many vertex variances). -/
theorem vfield_var_le {t : ℝ} {n : ℕ} (a : Fin n → PosW) (q : Fin n × Pt d t) :
    srcCov α₀ Γ (vpt a q) (vpt a q) ≤ ∑ j, wvar α₀ Γ (a j) := by
  rw [srcCov_diag]
  exact Finset.single_le_sum (f := fun j => wvar α₀ Γ (a j)) (fun j _ => wvar_nonneg (a j))
    (Finset.mem_univ q.1)

/-- **The product integrands of `Y_n^a` are bounded in `L²`** (TeX 1647-1650): Wick's formula with
the variance bound `vfield_var_le`. -/
theorem norm_prodL2_attach_le (hW : SourceField α₀ Γ P W) {t : ℝ} {n : ℕ} (a : Fin n → PosW)
    (z : Fin n → Pt d t) :
    ‖prodL2 hW (attach a z)‖ ≤
      Real.sqrt ((2 * n - 1).doubleFactorial) * Real.sqrt (∑ j, wvar α₀ Γ (a j)) ^ n := by
  rw [prodL2_attach]
  exact TerminalWick.norm_prodL2_le (vfield hW (t := t) a) _
    (Finset.sum_nonneg fun j _ => wvar_nonneg (a j)) (vfield_var_le a) _

end Field

section Continuity

variable {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : SrcPt d → Ω → ℝ}

/-- The mean-square increment of the restricted field tends to `0` (from `hcont`; the vertex
label is discrete, so only the space-time point moves). -/
theorem tendsto_vfield_incr (hcont : SourceCovContinuousTarget d)
    (hH : HomogCovariance d alpha α₀ Γ μ) {t : ℝ} {n : ℕ} (a : Fin n → PosW) (j : Fin n)
    (y : Pt d t) :
    Tendsto (fun q : Fin n × Pt d t => srcCov α₀ Γ (vpt a q) (vpt a q) -
        2 * srcCov α₀ Γ (vpt a (j, y)) (vpt a q) + srcCov α₀ Γ (vpt a (j, y)) (vpt a (j, y)))
      (𝓝 (j, y)) (𝓝 0) := by
  rw [nhds_prod_eq, nhds_discrete, Filter.pure_prod, tendsto_map'_iff]
  set g : (↥(Set.Ici (0 : ℝ)) × Rd d) × (↥(Set.Ici (0 : ℝ)) × Rd d) → ℝ :=
    fun pq => srcCov α₀ Γ (pq.1, a j) (pq.2, a j) with hg
  have hgc : Continuous g := hcont hH (a j) (a j)
  have e : ((fun q : Fin n × Pt d t => srcCov α₀ Γ (vpt a q) (vpt a q) -
        2 * srcCov α₀ Γ (vpt a (j, y)) (vpt a q) +
          srcCov α₀ Γ (vpt a (j, y)) (vpt a (j, y))) ∘ Prod.mk j) =
      fun y' : Pt d t => g (stPt y', stPt y') - 2 * g (stPt y, stPt y') + g (stPt y, stPt y) :=
    rfl
  rw [e]
  have hc : Continuous fun y' : Pt d t =>
      g (stPt y', stPt y') - 2 * g (stPt y, stPt y') + g (stPt y, stPt y) :=
    ((hgc.comp (continuous_stPt.prodMk continuous_stPt)).sub
      (continuous_const.mul (hgc.comp (continuous_const.prodMk continuous_stPt)))).add
      continuous_const
  have h0 : g (stPt y, stPt y) - 2 * g (stPt y, stPt y) + g (stPt y, stPt y) = 0 := by ring
  have := hc.tendsto y
  rw [h0] at this
  exact this

/-- **`z ↦ ∏_j W(z_j, a_j)` is continuous into `L²`** (from `hcont`; TeX 4294-4296 at fixed
positive widths). -/
theorem continuous_prodL2_attach (hcont : SourceCovContinuousTarget d)
    (hH : HomogCovariance d alpha α₀ Γ μ) (hW : SourceField α₀ Γ P W) {t : ℝ} {n : ℕ}
    (a : Fin n → PosW) :
    Continuous fun z : Fin n → Pt d t => prodL2 hW (attach a z) := by
  rw [continuous_iff_continuousAt]
  intro z
  have e : (fun z : Fin n → Pt d t => prodL2 hW (attach a z)) =
      (fun z' : Fin n → Fin n × Pt d t => prodL2 (vfield hW (t := t) a) z') ∘
        fun z : Fin n → Pt d t => fun j => (j, z j) := rfl
  rw [e]
  have hι : Continuous fun z : Fin n → Pt d t => fun j => ((j, z j) : Fin n × Pt d t) :=
    continuous_pi fun j => continuous_const.prodMk (continuous_apply j)
  exact ContinuousAt.comp (TerminalWickInputs.continuousAt_prodL2 (vfield hW a) fun j =>
    TerminalWickInputs.continuousAt_fieldL2 (vfield hW a)
      (tendsto_vfield_incr hcont hH a j (z j))) hι.continuousAt

end Continuity

/-- **Green smoothing is removed before noise smoothing** (`GreenFirstTarget`; TeX lines
1651-1655, `L:joint-fixed-order` 1860-1861, Step 4 1960-1963 at revision edf7085f (book 1.1.3)),
with B's `SourceCovContinuousTarget` as hypothesis: at fixed positive vertexwise widths `a`,
`Y_n^{a,η}(t,x) → Y_n^a(t,x)` in `L²(Ω)` as `η ↓ 0`.  Route: L13's
`tendsto_chainIntegral_reg` with the widths attached (module docstring): dominated convergence on
L13's noise space with the constant bound `norm_prodL2_attach_le` and the continuity
`continuous_prodL2_attach`.  Stated and proved for every `d` (the TeX sentence is d = 3). -/
theorem green_first (d : ℕ) (hcont : SourceCovContinuousTarget d) : GreenFirstTarget.{u} d := by
  intro alpha α₀ Γ μ hH Ω _ P _ W hW t ht x n a
  have := TerminalWickRegularization.isFiniteMeasure_noiseMeasure d n ht.le
  set F : (Fin n → Pt d t) → Lp ℝ 2 P := fun z => prodL2 hW (attach a z) with hFdef
  have hF : Continuous F := continuous_prodL2_attach hcont hH hW a
  have hreg : ∀ η : ℝ, Continuous (regPt (n := n) ht.le x η) := fun η =>
    (TerminalWickRegularization.continuous_regPt ht.le x).comp
      (continuous_const.prodMk continuous_id)
  have e : (fun η => YaReg hW t ht.le x a η) =
      fun η => ∫ q, F (regPt ht.le x η q) ∂(noiseMeasure d n t) :=
    funext fun η => integral_map (hreg η).measurable.aemeasurable hF.aestronglyMeasurable
  have e0 : Ya hW t ht.le x a = ∫ q, F (regPt ht.le x 0 q) ∂(noiseMeasure d n t) := by
    show ∫ z, F z ∂(chainMeasure d n t ht.le x) = _
    rw [TerminalWickRegularization.chainMeasure_eq_map_noise]
    exact integral_map (hreg 0).measurable.aemeasurable hF.aestronglyMeasurable
  rw [e, e0]
  refine (tendsto_integral_filter_of_dominated_convergence
    (fun _ => Real.sqrt ((2 * n - 1).doubleFactorial) * Real.sqrt (∑ j, wvar α₀ Γ (a j)) ^ n)
    (Eventually.of_forall fun η => (hF.comp (hreg η)).aestronglyMeasurable)
    (Eventually.of_forall fun _ => ae_of_all _ fun q => norm_prodL2_attach_le hW a _)
    (integrable_const _) (ae_of_all _ fun q => ?_)).mono_left nhdsWithin_le_nhds
  exact (hF.tendsto _).comp
    (((TerminalWickRegularization.continuous_regPt ht.le x).comp
      (continuous_id.prodMk continuous_const)).tendsto 0)

end StratonovichHAMSecondMoment.SourceGreenFirst
