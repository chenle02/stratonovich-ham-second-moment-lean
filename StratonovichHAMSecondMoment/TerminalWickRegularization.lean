module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L11, item K4 (ii): the Green-regularization paragraph of the proof of `L:terminal-wick`
(The finite terminal-chain Wick formula) of the main TeX file
`notes/notes_stratonovich_ham_second_moment.tex` at revision 39f2597a, lines 4392-4398:
"In dimension three one may first replace `G` by `p_η*G`.  Those positive measures have the
same masses and converge weakly to `G`.  Off the finitely many time cut points, all finite
Gaussian moments are bounded continuous functions of the spatial variables.  Dominated
convergence for their finite Wick sums proves the same limit for the mixed second moments with
two Green widths.  It gives `L²` convergence to the Bochner integral above".

Construction.  Each spatial factor `p_η * G_h` (`h = s_{j+1} - s_j > 0`) is
`h · law(h V + √η Z)` with `V ~ G_1` (mass one) and `Z ~ N(0, I_d)` independent
(`regFactor_eq_conv`, from the scaling `G_h(hA) = h G_1(A)`).  So the regularized
terminal-chain measure `g_n^{T,x,η}` is the image of ONE fixed measure, the noise measure
`timeMeasure n T ⊗ G_1^{⊗n} ⊗ N(0,I_d)^{⊗n}` (`noiseMeasure`), under
`Φ_η(s, v, ζ) = (s_j, x - Σ_{l ≥ j} ((s_{l+1} - s_l) v_l + √η ζ_l))_j` (`regMap`, `regPt`,
`chainMeasureReg`).  At `η = 0` this is the unregularized `g_n^{T,x}` of `TerminalWickInputs`
(`chainMeasure_eq_map_noise`).  The construction is not specific to `d = 3`; it is stated
for every `d` (masses for `d ∈ {1,2,3}`).

Formalized (nothing supplied):
* same masses: `g_n^{T,x,η}(total) = T^{2n}/(2n)!` for every `η` (`chainMeasureReg_univ`,
  `chainMeasureReg_univ_eq_chainMass`); no time atoms (`timeAtomless_chainMeasureReg`);
* weak convergence: `∫ f dg_n^{T,x,η} → ∫ f dg_n^{T,x}` as `η ↓ 0` for every bounded
  continuous `f` (`tendsto_integral_chainMeasureReg`);
* `L²` convergence of the regularized terms: `Y_n^η → Y_n` in `L²(Ω)` as `η ↓ 0`
  (`tendsto_chainIntegral_reg`), by dominated convergence on the noise space (bound
  `√((2n-1)!!) V^{n/2}`; the chain product is continuous in `L²` off the cut times,
  `TerminalWickInputs.continuousAt_prodL2`);
* the mixed second moments with two Green widths: `E[Y_m^{η₁} Y_n^{η₂}] → E[Y_m Y_n]` as
  `(η₁, η₂) ↓ (0, 0)` (`tendsto_mixed_moment_reg`);
* wrapper `terminal_wick_regularization_paper`, and `L:terminal-wick` itself for the
  regularized measures (`terminal_wick_reg_paper`).

Hypotheses of the wrappers: those of `L:terminal-wick` (`d ∈ {1,2,3}`, `T > 0`, the terminal
point `x`, a centered Gaussian field with `V < ∞` and the cell continuity).  Carried but
unused: `IsProbabilityMeasure P` (as in `TerminalWick.terminal_wick_paper`).

Differences from the TeX:
* The TeX's route (dominated convergence for the finite Wick sums of the mixed moments) is
  replaced by dominated convergence of the `L²`-valued Bochner integrals on the common noise
  space; the mixed-moment limit then follows by continuity of the inner product.  Same
  conclusions.
* The limit is along `η ↓ 0` (`𝓝[>] 0`); `√η` is Mathlib's `Real.sqrt`.
* `regFactor_eq_conv` identifies each factor with `G_h * p_η` (Mathlib's `Measure.conv`,
  `p_η` the image of `N(0, I_d)` under `ζ ↦ √η ζ`); the identification of the whole chain
  measure with the TeX's `n`-fold product of the `G_{h_j} * p_η` (the analogue of
  `TerminalWickInputs.chainMeasureRaw_apply`) is not formalized.
* Not formalized: the final clause "exactly the fixed-noise Green convention used in the
  source", which concerns the source's definitions, not a statement of this lemma.
Lemmas marked "Auxiliary" serve only the Lean proof route.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.TerminalWickInputs

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal Pointwise BoundedContinuousFunction

namespace StratonovichHAMSecondMoment.TerminalWickRegularization

open TerminalWick TerminalWickInputs FiniteWick WaveGreen HomogHypothesis

/-- The standard Gaussian `N(0, I_d)` on `ℝ^d`. -/
def stdGaussian (d : ℕ) : Measure (Rd d) :=
  multivariateGaussian (0 : Rd d) (1 : Matrix (Fin d) (Fin d) ℝ)

instance instIsProbabilityMeasureStdGaussian (d : ℕ) : IsProbabilityMeasure (stdGaussian d) := by
  unfold stdGaussian; infer_instance

/-! ### One factor: `p_η * G_h` -/

/-- Auxiliary: `G_h = h · (v ↦ h v)_* G_1` for `d ∈ {1,2,3}` and `h > 0` (scaling,
`WaveGreen.waveGreen_scaling`). -/
theorem waveGreen_eq_smul_map (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) {h : ℝ} (hh : 0 < h) :
    waveGreen d h = ENNReal.ofReal h • (waveGreen d 1).map fun v => h • v := by
  have hm : Measurable fun v : Rd d => h • v := measurable_const_smul h
  ext A hA
  have hpre : (fun v : Rd d => h • v) ⁻¹' A = h⁻¹ • A := by
    ext v
    rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hh.ne'), inv_inv]
  rw [Measure.smul_apply, Measure.map_apply hm hA, hpre, smul_eq_mul,
    ← waveGreen_scaling d hd h hh _ (hA.const_smul_of_ne_zero (inv_ne_zero hh.ne')),
    smul_inv_smul₀ hh.ne']

/-- One regularized Green factor: `h · law(h V + √η Z)`, `V ~ G_1`, `Z ~ N(0, I_d)`, equals
`G_h * p_η` (Mathlib's convolution `Measure.conv`), `p_η` the law of `√η Z` (TeX line 4392). -/
theorem regFactor_eq_conv (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) {h : ℝ} (hh : 0 < h) (η : ℝ) :
    ENNReal.ofReal h • ((waveGreen d 1).prod (stdGaussian d)).map
        (fun p : Rd d × Rd d => h • p.1 + Real.sqrt η • p.2) =
      (waveGreen d h).conv ((stdGaussian d).map fun ζ => Real.sqrt η • ζ) := by
  have h1 : Measurable fun v : Rd d => h • v := measurable_const_smul h
  have h2 : Measurable fun ζ : Rd d => Real.sqrt η • ζ := measurable_const_smul _
  have hadd : Measurable fun p : Rd d × Rd d => p.1 + p.2 := measurable_fst.add measurable_snd
  rw [Measure.conv, waveGreen_eq_smul_map d hd hh, Measure.prod_smul_left,
    Measure.map_smul _ hadd.aemeasurable, Measure.map_prod_map _ _ h1 h2,
    Measure.map_map hadd (h1.prodMap h2)]
  rfl

/-! ### The regularized chain measures -/

/-- The noise space: times, unit Green variables, Gaussian variables. -/
abbrev Noise (d n : ℕ) := (Fin n → ℝ) × ((Fin n → Rd d) × (Fin n → Rd d))

/-- The noise measure `timeMeasure n T ⊗ G_1^{⊗n} ⊗ N(0,I_d)^{⊗n}`. -/
def noiseMeasure (d n : ℕ) (T : ℝ) : Measure (Noise d n) :=
  (timeMeasure n T).prod ((Measure.pi fun _ : Fin n => waveGreen d 1).prod
    (Measure.pi fun _ : Fin n => stdGaussian d))

/-- The regularized chain points
`(s_j, x - Σ_{l ≥ j} ((s_{l+1} - s_l) v_l + √η ζ_l))_j`. -/
def regMap {d n : ℕ} (T : ℝ) (x : Rd d) (η : ℝ) (q : Noise d n) : Fin n → ℝ × Rd d :=
  chainPoint x q.1 fun j => gap T q.1 j • q.2.1 j + Real.sqrt η • q.2.2 j

/-- Auxiliary: `regMap` is jointly continuous in `(η, q)`. -/
theorem continuous_regMap {d n : ℕ} (T : ℝ) (x : Rd d) :
    Continuous fun p : ℝ × Noise d n => regMap T x p.1 p.2 := by
  have hs : Continuous fun p : ℝ × Noise d n => p.2.1 := continuous_fst.comp continuous_snd
  have hv : Continuous fun p : ℝ × Noise d n => p.2.2.1 :=
    continuous_fst.comp (continuous_snd.comp continuous_snd)
  have hz : Continuous fun p : ℝ × Noise d n => p.2.2.2 :=
    continuous_snd.comp (continuous_snd.comp continuous_snd)
  have hw : Continuous fun p : ℝ × Noise d n =>
      fun j => gap T p.2.1 j • p.2.2.1 j + Real.sqrt p.1 • p.2.2.2 j :=
    continuous_pi fun j => (((continuous_gap T j).comp hs).smul
      ((continuous_apply j).comp hv)).add
      ((Real.continuous_sqrt.comp continuous_fst).smul ((continuous_apply j).comp hz))
  exact (continuous_chainPoint x).comp (hs.prodMk hw)

/-- Auxiliary: `toPt` is continuous. -/
theorem continuous_toPt {d n : ℕ} {T : ℝ} (hT : 0 ≤ T) :
    Continuous (toPt (d := d) (n := n) hT) :=
  continuous_pi fun j =>
    (continuous_projIcc.comp ((continuous_apply j).fst)).prodMk (continuous_apply j).snd

/-- The regularized chain points in `[0,T] × ℝ^d`. -/
def regPt {d n : ℕ} {T : ℝ} (hT : 0 ≤ T) (x : Rd d) (η : ℝ) (q : Noise d n) :
    Fin n → Pt d T :=
  toPt hT (regMap T x η q)

/-- Auxiliary: `regPt` is jointly continuous in `(η, q)`. -/
theorem continuous_regPt {d n : ℕ} {T : ℝ} (hT : 0 ≤ T) (x : Rd d) :
    Continuous fun p : ℝ × Noise d n => regPt hT x p.1 p.2 :=
  (continuous_toPt hT).comp (continuous_regMap T x)

/-- Auxiliary: `regPt hT x η` is measurable. -/
theorem measurable_regPt {d n : ℕ} {T : ℝ} (hT : 0 ≤ T) (x : Rd d) (η : ℝ) :
    Measurable (regPt (n := n) hT x η) :=
  ((continuous_regPt hT x).comp (continuous_const.prodMk continuous_id)).measurable

/-- The regularized terminal-chain measure `g_n^{T,x,η}` (Green measures `G` replaced by
`p_η * G`, TeX line 4392), on `n`-tuples of points of `[0,T] × ℝ^d`. -/
def chainMeasureReg (d n : ℕ) (T : ℝ) (hT : 0 ≤ T) (x : Rd d) (η : ℝ) :
    Measure (Fin n → Pt d T) :=
  (noiseMeasure d n T).map (regPt hT x η)

/-- Auxiliary: the total mass of the noise measure. -/
theorem noiseMeasure_univ (d n : ℕ) (T : ℝ) :
    noiseMeasure d n T univ = chainMassReal n T * ∏ _j : Fin n, waveGreen d 1 univ := by
  rw [noiseMeasure, ← univ_prod_univ, Measure.prod_prod, ← univ_prod_univ, Measure.prod_prod,
    Measure.pi_univ, Measure.pi_univ, timeMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  simp only [measure_univ, Finset.prod_const_one, mul_one]
  rfl

/-- Auxiliary: the noise measure is finite for `T ≥ 0`. -/
theorem isFiniteMeasure_noiseMeasure (d n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    IsFiniteMeasure (noiseMeasure d n T) :=
  ⟨by
    rw [noiseMeasure_univ, chainMassReal_eq n T hT]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.prod_lt_top fun _ _ => measure_lt_top _ _)⟩

instance instIsFiniteMeasureChainMeasureReg (d n : ℕ) (T : ℝ) (hT : 0 ≤ T) (x : Rd d)
    (η : ℝ) : IsFiniteMeasure (chainMeasureReg d n T hT x η) := by
  have := isFiniteMeasure_noiseMeasure d n hT
  unfold chainMeasureReg
  infer_instance

/-- The regularized measures have the masses of `g_n^{T,x}`: `T^{2n}/(2n)!` (TeX line 4393,
"Those positive measures have the same masses"). -/
theorem chainMeasureReg_univ (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) (n : ℕ) (T : ℝ)
    (hT : 0 ≤ T) (x : Rd d) (η : ℝ) :
    chainMeasureReg d n T hT x η univ = ENNReal.ofReal (T ^ (2 * n) / (2 * n).factorial) := by
  rw [chainMeasureReg, Measure.map_apply (measurable_regPt hT x η) MeasurableSet.univ,
    preimage_univ, noiseMeasure_univ, chainMassReal_eq n T hT,
    waveGreen_mass d hd 1 zero_le_one]
  simp

/-- The regularized masses in the form of the input `hmass` of `L:terminal-wick`. -/
theorem chainMeasureReg_univ_eq_chainMass (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) (n : ℕ)
    (T : ℝ) (hT : 0 ≤ T) (x : Rd d) (η : ℝ) :
    chainMeasureReg d n T hT x η univ = chainMass d n T := by
  rw [chainMeasureReg_univ d hd n T hT x η, chainMass_eq d hd n T hT]

/-- At `η = 0` the noise representation gives the unregularized `g_n^{T,x}`. -/
theorem chainMeasure_eq_map_noise (d n : ℕ) (T : ℝ) (hT : 0 ≤ T) (x : Rd d) :
    chainMeasure d n T hT x = (noiseMeasure d n T).map (regPt hT x 0) := by
  have hmp : Measurable fun q : Noise d n => (q.1, q.2.1) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hproj : (noiseMeasure d n T).map (fun q : Noise d n => (q.1, q.2.1)) =
      (timeMeasure n T).prod (Measure.pi fun _ : Fin n => waveGreen d 1) := by
    ext B hB
    rw [Measure.map_apply hmp hB, noiseMeasure, Measure.prod_apply (hmp hB),
      Measure.prod_apply hB]
    refine lintegral_congr fun s => ?_
    have : Prod.mk s ⁻¹' ((fun q : Noise d n => (q.1, q.2.1)) ⁻¹' B) =
        (Prod.mk s ⁻¹' B) ×ˢ (univ : Set (Fin n → Rd d)) := by
      ext v; simp
    rw [this, Measure.prod_prod, measure_univ, mul_one]
  have hfun : regPt (n := n) hT x 0 = fun q => toPt hT (chainMap T x (q.1, q.2.1)) := by
    funext q
    simp [regPt, regMap, chainMap]
  rw [hfun, chainMeasure, chainMeasureRaw, ← hproj, Measure.map_map (measurable_chainMap T x) hmp,
    Measure.map_map (measurable_toPt hT) ((measurable_chainMap T x).comp hmp)]
  rfl

/-- The regularized measures have no time atoms (the regularization moves only space). -/
theorem timeAtomless_chainMeasureReg (d : ℕ) (T : ℝ) (hT : 0 ≤ T) (x : Rd d) (η : ℝ) :
    TimeAtomless (fun n => chainMeasureReg d n T hT x η) := by
  intro n j t
  have hset : MeasurableSet {z : Fin n → Pt d T | ((z j).1 : ℝ) = t} :=
    (measurableSet_singleton t).preimage
      (measurable_subtype_coe.comp (measurable_fst.comp (measurable_pi_apply j)))
  have hpre : regPt hT x η ⁻¹' {z : Fin n → Pt d T | ((z j).1 : ℝ) = t} =
      regPt hT x 0 ⁻¹' {z : Fin n → Pt d T | ((z j).1 : ℝ) = t} := rfl
  have h0 : chainMeasure d n T hT x {z | ((z j).1 : ℝ) = t} = 0 :=
    timeAtomless_chainMeasure d T hT x n j t
  rw [chainMeasure_eq_map_noise, Measure.map_apply (measurable_regPt hT x 0) hset] at h0
  show chainMeasureReg d n T hT x η _ = 0
  rw [chainMeasureReg, Measure.map_apply (measurable_regPt hT x η) hset, hpre, h0]

/-- Weak convergence of the regularized chain measures to `g_n^{T,x}` as `η ↓ 0` (TeX line
4393, "converge weakly to `G`", at the level of the chain measures). -/
theorem tendsto_integral_chainMeasureReg (d n : ℕ) (T : ℝ) (hT : 0 ≤ T) (x : Rd d)
    (f : (Fin n → Pt d T) →ᵇ ℝ) :
    Tendsto (fun η => ∫ z, f z ∂(chainMeasureReg d n T hT x η)) (𝓝[>] 0)
      (𝓝 (∫ z, f z ∂(chainMeasure d n T hT x))) := by
  have := isFiniteMeasure_noiseMeasure d n hT
  have hf : ∀ μ : Measure (Fin n → Pt d T), AEStronglyMeasurable (fun z => f z) μ :=
    fun _ => f.continuous.aestronglyMeasurable
  have e : (fun η => ∫ z, f z ∂(chainMeasureReg d n T hT x η)) =
      fun η => ∫ q, f (regPt hT x η q) ∂(noiseMeasure d n T) :=
    funext fun η => integral_map (measurable_regPt hT x η).aemeasurable (hf _)
  rw [e, chainMeasure_eq_map_noise, integral_map (measurable_regPt hT x 0).aemeasurable (hf _)]
  refine (tendsto_integral_filter_of_dominated_convergence (fun _ => ‖f‖)
    (Eventually.of_forall fun η =>
      f.continuous.aestronglyMeasurable.comp_measurable (measurable_regPt hT x η))
    (Eventually.of_forall fun _ => ae_of_all _ fun q => f.norm_coe_le_norm _)
    (integrable_const _) (ae_of_all _ fun q => ?_)).mono_left nhdsWithin_le_nhds
  exact (f.continuous.tendsto _).comp
    (((continuous_regPt hT x).comp (continuous_id.prodMk continuous_const)).tendsto 0)

/-! ### `L²` convergence of the regularized terms -/

section Convergence
variable {d : ℕ} {T : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : Pt d T → Ω → ℝ} {K : Pt d T → Pt d T → ℝ}

/-- Auxiliary: `Y_n^η` as an integral over the noise space. -/
theorem chainIntegral_reg_eq (hW : CenteredGaussianField W K P)
    (hcell : MeanSquareCellContinuous K) (hT : 0 ≤ T) (x : Rd d) (η : ℝ) (n : ℕ) :
    chainIntegral (fun n => chainMeasureReg d n T hT x η) hW n =
      ∫ q, prodL2 hW (regPt hT x η q) ∂(noiseMeasure d n T) := by
  have hm : AEStronglyMeasurable (fun z : Fin n → Pt d T => prodL2 hW z)
      (chainMeasureReg d n T hT x η) :=
    aestronglyMeasurable_prodL2_of_cell hW hcell _ (timeAtomless_chainMeasureReg d T hT x η) n
  show ∫ z, prodL2 hW z ∂(chainMeasureReg d n T hT x η) = _
  exact integral_map (measurable_regPt hT x η).aemeasurable hm

/-- Auxiliary: `Y_n` as an integral over the noise space. -/
theorem chainIntegral_eq_noise (hW : CenteredGaussianField W K P)
    (hcell : MeanSquareCellContinuous K) (hT : 0 ≤ T) (x : Rd d) (n : ℕ) :
    chainIntegral (fun n => chainMeasure d n T hT x) hW n =
      ∫ q, prodL2 hW (regPt hT x 0 q) ∂(noiseMeasure d n T) := by
  have hm : AEStronglyMeasurable (fun z : Fin n → Pt d T => prodL2 hW z)
      (chainMeasure d n T hT x) :=
    aestronglyMeasurable_prodL2_of_cell hW hcell _ (timeAtomless_chainMeasure d T hT x) n
  rw [chainMeasure_eq_map_noise] at hm
  show ∫ z, prodL2 hW z ∂(chainMeasure d n T hT x) = _
  rw [chainMeasure_eq_map_noise]
  exact integral_map (measurable_regPt hT x 0).aemeasurable hm

/-- `L²` convergence `Y_n^η → Y_n` as `η ↓ 0` (TeX lines 4394-4398): the regularized
terminal-chain integrals converge in `L²(Ω)` to the Bochner integral of `L:terminal-wick`. -/
theorem tendsto_chainIntegral_reg (hW : CenteredGaussianField W K P)
    (hVfin : BddAbove (Set.range fun p => K p p)) (hcell : MeanSquareCellContinuous K)
    (hT : 0 ≤ T) (x : Rd d) (n : ℕ) :
    Tendsto (fun η => chainIntegral (fun n => chainMeasureReg d n T hT x η) hW n) (𝓝[>] 0)
      (𝓝 (chainIntegral (fun n => chainMeasure d n T hT x) hW n)) := by
  have := isFiniteMeasure_noiseMeasure d n hT
  set V := ⨆ p, K p p with hVdef
  have hV : ∀ p, K p p ≤ V := fun p => le_ciSup hVfin p
  have hV0 : 0 ≤ V := supVar_nonneg hW hT hVfin
  have e : (fun η => chainIntegral (fun n => chainMeasureReg d n T hT x η) hW n) =
      fun η => ∫ q, prodL2 hW (regPt hT x η q) ∂(noiseMeasure d n T) :=
    funext fun η => chainIntegral_reg_eq hW hcell hT x η n
  rw [e, chainIntegral_eq_noise hW hcell hT x n]
  obtain ⟨Z, hZ⟩ := id hcell
  have hae : ∀ᵐ q ∂(noiseMeasure d n T), ∀ j, ((regPt hT x 0 q j).1 : ℝ) ∉ Z := by
    have h' : ∀ᵐ z ∂(chainMeasure d n T hT x), ∀ j, ((z j).1 : ℝ) ∉ Z :=
      ae_times_notMem (fun n => chainMeasure d n T hT x) (timeAtomless_chainMeasure d T hT x)
        Z n
    rw [chainMeasure_eq_map_noise] at h'
    exact ae_of_ae_map (measurable_regPt hT x 0).aemeasurable h'
  refine (tendsto_integral_filter_of_dominated_convergence
    (fun _ => Real.sqrt ((2 * n - 1).doubleFactorial) * Real.sqrt V ^ n)
    (Eventually.of_forall fun η =>
      (aestronglyMeasurable_prodL2_of_cell hW hcell (fun n => chainMeasureReg d n T hT x η)
        (timeAtomless_chainMeasureReg d T hT x η) n).comp_measurable
        (measurable_regPt hT x η))
    (Eventually.of_forall fun _ => ae_of_all _ fun q => norm_prodL2_le hW V hV0 hV _)
    (integrable_const _) ?_).mono_left nhdsWithin_le_nhds
  filter_upwards [hae] with q hq
  have hc := continuousAt_prodL2 hW (z₀ := regPt hT x 0 q)
    fun j => continuousAt_fieldL2 hW (hZ _ (hq j))
  exact hc.tendsto.comp
    (((continuous_regPt hT x).comp (continuous_id.prodMk continuous_const)).tendsto 0)

/-- The mixed second moments with two Green widths (TeX lines 4395-4397):
`E[Y_m^{η₁} Y_n^{η₂}] → E[Y_m Y_n]` as `(η₁, η₂) ↓ (0, 0)`. -/
theorem tendsto_mixed_moment_reg (hW : CenteredGaussianField W K P)
    (hVfin : BddAbove (Set.range fun p => K p p)) (hcell : MeanSquareCellContinuous K)
    (hT : 0 ≤ T) (x : Rd d) (m n : ℕ) :
    Tendsto (fun p : ℝ × ℝ =>
        ∫ ω, chainIntegral (fun n => chainMeasureReg d n T hT x p.1) hW m ω *
          chainIntegral (fun n => chainMeasureReg d n T hT x p.2) hW n ω ∂P)
      (𝓝[>] 0 ×ˢ 𝓝[>] 0)
      (𝓝 (∫ ω, chainIntegral (fun n => chainMeasure d n T hT x) hW m ω *
        chainIntegral (fun n => chainMeasure d n T hT x) hW n ω ∂P)) := by
  simp_rw [UniformSeriesTail.integral_mul_eq_inner]
  exact ((tendsto_chainIntegral_reg hW hVfin hcell hT x m).comp tendsto_fst).inner
    ((tendsto_chainIntegral_reg hW hVfin hcell hT x n).comp tendsto_snd)

end Convergence

/-! ### Wrappers -/

/-- The Green-regularization paragraph of the proof of `L:terminal-wick` (main TeX lines
4392-4398 at 39f2597a), exact-hypothesis wrapper.  Hypotheses: those of `L:terminal-wick`
(`d ∈ {1,2,3}`, `T > 0`, the terminal point `x`, a centered Gaussian field with
`V = sup K(p,p) < ∞` and mean-square continuity on the open cells of a finite partition).
Conclusions, for the regularized terminal-chain measures `g_n^{T,x,η}` (Green measures `G`
replaced by `p_η * G`): (1) they have the masses of `g_n^{T,x}`; (2) they converge weakly to
`g_n^{T,x}` as `η ↓ 0`; (3) `Y_n^η → Y_n` in `L²(Ω)`; (4) the mixed second moments with two
Green widths converge, `E[Y_m^{η₁} Y_n^{η₂}] → E[Y_m Y_n]`.  `IsProbabilityMeasure P` is
carried, unused. -/
theorem terminal_wick_regularization_paper {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) (T : ℝ) (hT : 0 < T)
    (x : Rd d) (W : Pt d T → Ω → ℝ) (K : Pt d T → Pt d T → ℝ)
    (hW : CenteredGaussianField W K P) (hVfin : BddAbove (Set.range fun p => K p p))
    (hcell : MeanSquareCellContinuous K) :
    (∀ (η : ℝ) (n : ℕ), chainMeasureReg d n T hT.le x η univ = chainMass d n T) ∧
      (∀ (n : ℕ) (f : (Fin n → Pt d T) →ᵇ ℝ),
        Tendsto (fun η => ∫ z, f z ∂(chainMeasureReg d n T hT.le x η)) (𝓝[>] 0)
          (𝓝 (∫ z, f z ∂(chainMeasure d n T hT.le x)))) ∧
      (∀ n : ℕ, Tendsto (fun η => chainIntegral (fun n => chainMeasureReg d n T hT.le x η) hW n)
        (𝓝[>] 0) (𝓝 (chainIntegral (fun n => chainMeasure d n T hT.le x) hW n))) ∧
      (∀ m n : ℕ, Tendsto (fun p : ℝ × ℝ =>
          ∫ ω, chainIntegral (fun n => chainMeasureReg d n T hT.le x p.1) hW m ω *
            chainIntegral (fun n => chainMeasureReg d n T hT.le x p.2) hW n ω ∂P)
        (𝓝[>] 0 ×ˢ 𝓝[>] 0)
        (𝓝 (∫ ω, chainIntegral (fun n => chainMeasure d n T hT.le x) hW m ω *
          chainIntegral (fun n => chainMeasure d n T hT.le x) hW n ω ∂P))) :=
  ⟨fun η n => chainMeasureReg_univ_eq_chainMass d hd n T hT.le x η,
    fun n f => tendsto_integral_chainMeasureReg d n T hT.le x f,
    fun n => tendsto_chainIntegral_reg hW hVfin hcell hT.le x n,
    fun m n => tendsto_mixed_moment_reg hW hVfin hcell hT.le x m n⟩

/-- `L:terminal-wick` (main TeX lines 4291-4336) for the regularized chain measures
`g_n^{T,x,η}`, any `η`: the conclusions of `TerminalWickInputs.terminal_wick_paper_measurable`
(no mass, measurability or `hK` input).  Same hypotheses as
`terminal_wick_regularization_paper`; `IsProbabilityMeasure P` carried, unused. -/
theorem terminal_wick_reg_paper {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) (T : ℝ) (hT : 0 < T)
    (x : Rd d) (η : ℝ) (W : Pt d T → Ω → ℝ) (K : Pt d T → Pt d T → ℝ)
    (hW : CenteredGaussianField W K P) (hVfin : BddAbove (Set.range fun p => K p p))
    (hcell : MeanSquareCellContinuous K) :
    let ν : ∀ n : ℕ, Measure (Fin n → Pt d T) := fun n => chainMeasureReg d n T hT.le x η
    (∀ n, Integrable (fun z : Fin n → Pt d T => prodL2 hW z) (ν n)) ∧
      ((chainIntegral ν hW 0 : Ω → ℝ) =ᵐ[P] fun _ => 1) ∧
      (∀ n, ‖chainIntegral ν hW n‖ ≤ Real.sqrt ((2 * n - 1).doubleFactorial) *
        (⨆ p, K p p) ^ ((n : ℝ) / 2) * (T ^ (2 * n) / (2 * n).factorial)) ∧
      (∀ m n, ∫ ω, chainIntegral ν hW m ω * chainIntegral ν hW n ω ∂P =
        ∑ D ∈ pairings (Finset.univ : Finset (Fin (m + n))), pairingIntegral ν K m n D) ∧
      (∀ m n (D : Fin (m + n) → Fin (m + n)),
        Integrable (fun q : (Fin m → Pt d T) × (Fin n → Pt d T) =>
          pairWeight (fun a b => K (Fin.append q.1 q.2 a) (Fin.append q.1 q.2 b))
            Finset.univ D)
          ((ν m).prod (ν n))) ∧
      (∀ m n, Odd (m + n) → ∫ ω, chainIntegral ν hW m ω * chainIntegral ν hW n ω ∂P = 0) ∧
      ((∀ p q, 0 ≤ K p q) →
        (∀ m n (D : Fin (m + n) → Fin (m + n)), 0 ≤ pairingIntegral ν K m n D) ∧
        ∀ m n, 0 ≤ ∫ ω, chainIntegral ν hW m ω * chainIntegral ν hW n ω ∂P) ∧
      (∀ r : ℝ, Summable fun n => ‖r ^ n • chainIntegral ν hW n‖) ∧
      ((∀ p q, 0 ≤ K p q) → ∀ r : ℝ,
        UniformSeriesTail.TerminalWickInput P (fun n => chainIntegral ν hW n) r) :=
  terminal_wick_paper_measurable P d hd T hT W K hW hVfin hcell
    (fun n => chainMeasureReg d n T hT.le x η)
    (fun n => chainMeasureReg_univ_eq_chainMass d hd n T hT.le x η)
    (timeAtomless_chainMeasureReg d T hT.le x η)

end StratonovichHAMSecondMoment.TerminalWickRegularization
