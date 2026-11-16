module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Lemma `L:higher-riesz` (Riesz spatial maxima) of the main TeX file
`notes/notes_stratonovich_ham_second_moment.tex` at revision 39f2597a
(statement lines 6103-6112, proof 6114-6190), the dimension-three clause in full,
and the combined lemma in both of its dimensions; Hypothesis `H:spatial-maximum`
(lines 5919-5929) is `HigherRieszTwo.SpatialMaximum`.  All main-TeX line numbers
below are at 39f2597a.  The dimension-two clause and the shared steps are in
`HigherRieszTwo` (wave L10-R2); this module reuses them unchanged.

Definitions (new): `F3w α w = ∫ G_1^{(3)}(dy) |y + w|^{-α}` (the `F_3(w)` of
line 6134, as a lower integral); `M3 c α = c 2^{1-α}/(2-α)` (line 6106);
`Md d c α`, equal to `M3` for `d = 3` and to `HigherRieszTwo.M2` otherwise (the
`M_d` of `C:higher-riesz`, line 6196).

Formalized, nothing supplied:
* `F3w_eq`: for `α < 2` and `w ≠ 0`, `F_3(w) = ((1+ρ)^v - |1-ρ|^v)/(2vρ)`,
  `ρ = |w|`, `v = 2 - α` (spherical coordinates, lines 6134-6138); `F3w_zero`:
  `F_3(0) = 1` (the TeX's "continuous ... at zero", line 6145);
* `F3w_le`: `F_3(w) ≤ 2^{1-α}/(2-α)` for `1 < α < 2` and every `w`
  (lines 6140-6146), with `F3w_unit`: equality at `|w| = 1`;
* `higher_riesz_three`: in `d = 3`, `1 < α < 2`, `c > 0`, Hypothesis
  `H:spatial-maximum` holds with `δ = α - 1` and `M = M_3`;
* `higher_riesz_three_optimal`: `M_3 ≤ M` for every `M` with
  `H:spatial-maximum` (lines 6186-6189; Fatou at a maximizing shift `|z| = 1`,
  `h = 1`, `η = 0`, `ε ↓ 0`, with `HigherRieszTwo.approx_identity`); the point
  `y = -z` is `G_1^{(3)}`-null (`waveGreen_three_point`);
* `higher_riesz_three_paper`, `higher_riesz_paper`: the dimension-three clause
  and the whole lemma with the manuscript's hypotheses (`H:homog` for
  `Γ = γ dx`, `d ∈ {2,3}`, `c > 0`, `1 < α`, and `α < 3/2` in `d = 2`).

Route (statements as in the TeX): the spherical computation is
`PhaseContractions.sphere_convolution` with Archimedes' law discharged by
`L9Completed.archimedesLaw_holds` (wave L9); the maximum of the closed form is
`HigherRieszTwo.F3_max` (chord bound, not the TeX's monotonicity on each side
of `ρ = 1`); the value at `w = 0` is computed directly and compared through
`2^{1-α} ≥ 2 - α` (from `e^x ≥ 1 + x` and `log 2 < 1`); the Gaussian averaging
is `HigherRieszTwo.smoothed_average_le`.

Hypotheses: in `higher_riesz_three_paper` and the `d = 3` branch of
`higher_riesz_paper`, `H:homog` is used only for `α < 2` (from `α₀ > 0` and
`α₀ + α < 2`, i.e. the section's `α < 2 - α₀`); in the `d = 2` branch it is
carried but unused.  Of `1 < α` the `d = 3` clause uses it in `F3_max`; the
`d = 2` clause uses only `0 < α`.

Inherited narrowings (unchanged): the covariance is given by its density
(`HigherRieszTwo.SpatialMaximum`); the `d = 3` Green measure is the recorded
definitional choice of `WaveGreen` (`(s/(4π)) · map (ω ↦ sω) σ`,
`σ = volume.toSphere`, decision 4 of wave L6), not identified with a Hausdorff
surface measure.

Junk values: `riesz` at `0` is `0` (Lean's `0^{-α} = 0`); against
`G_1^{(3)}` this value enters only at the point `y = -z`, which is null
(`waveGreen_three_point`); `PhaseContractions.sphere_convolution` handles the
same point through Archimedes' law.  `F3 v 0 = 0` (division by zero) is never used:
`F3w_eq` assumes `w ≠ 0` and `w = 0` is `F3w_zero`.  All integrals in the
statements are lower integrals.
Lemmas marked "Auxiliary to the Lean proof route" have no manuscript label.
-/

public import Mathlib
public import StratonovichHAMSecondMoment.HigherRieszTwo
public import StratonovichHAMSecondMoment.L9Completed

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Real Metric Filter
open scoped ENNReal NNReal Topology

namespace StratonovichHAMSecondMoment.HigherRieszThree

open HomogHypothesis (Rd HomogCovariance)
open VariationalMean (heatK heatK_pos)
open WaveGreen (waveGreen isFiniteMeasure_waveGreen)
open HigherRieszTwo

/-! ### Definitions -/

/-- `F_3(w) = ∫ G_1^{(3)}(dy) |y + w|^{-α}` (main TeX line 6134), as a lower
integral. -/
def F3w (α : ℝ) (w : Rd 3) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (‖y + w‖ ^ (-α)) ∂(waveGreen 3 1)

/-- The constant `M_3 = c 2^{1-α}/(2-α)` of `L:higher-riesz` (main TeX line
6106). -/
def M3 (c α : ℝ) : ℝ :=
  c * (2 ^ (1 - α) / (2 - α))

/-- The constant `M_d` of `L:higher-riesz` and `C:higher-riesz` (main TeX lines
6106-6111, 6196): `M_3` in `d = 3`, `M_2` otherwise (the lemma has only
`d ∈ {2,3}`). -/
def Md (d : ℕ) (c α : ℝ) : ℝ :=
  if d = 3 then M3 c α else M2 c α

/-! ### The closed form of `F_3` (spherical coordinates) -/

/-- Spherical coordinates (main TeX lines 6134-6138): for `α < 2` and `w ≠ 0`,
`F_3(w) = ((1+ρ)^v - |1-ρ|^v)/(2vρ)` with `ρ = |w|`, `v = 2 - α`.  Proved by
`PhaseContractions.sphere_convolution` (Archimedes' law,
`L9Completed.archimedesLaw_holds`). -/
theorem F3w_eq {α : ℝ} (hα : α < 2) {w : Rd 3} (hw : w ≠ 0) :
    F3w α w = ENNReal.ofReal (F3 (2 - α) ‖w‖) := by
  have e : ∀ y : Rd 3, ‖y + w‖ = ‖-w - y‖ := fun y => by
    rw [← norm_neg]; congr 1; abel
  unfold F3w
  simp_rw [e]
  rw [PhaseContractions.sphere_convolution L9Completed.archimedesLaw_holds 1 one_pos α hα (-w)
    (by rw [norm_neg]; exact norm_pos_iff.2 hw), norm_neg, F3, mul_right_comm 2 ‖w‖]

/-- `F_3(0) = 1` (the value at the center; the TeX notes the closed form is
continuous at zero, main TeX line 6145): `G_1^{(3)}` has mass one on the unit
sphere. -/
theorem F3w_zero (α : ℝ) : F3w α 0 = 1 := by
  set φ : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal (u ^ (-α / 2)) with hφ_def
  have hφm : Measurable φ := by simp only [hφ_def]; fun_prop
  have hpt : ∀ y : Rd 3, ENNReal.ofReal (‖y + 0‖ ^ (-α)) = φ (‖(0 : Rd 3) - y‖ ^ 2) := by
    intro y
    simp only [hφ_def, PhaseContractions.sq_norm_rpow, add_zero, zero_sub, norm_neg]
  unfold F3w
  simp_rw [hpt]
  rw [PhaseContractions.lintegral_waveGreen_three L9Completed.archimedesLaw_holds 1 one_pos φ
    hφm 0]
  simp only [hφ_def, norm_zero, one_pow, mul_zero, zero_mul, sub_zero, lintegral_const,
    Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Icc]
  rw [show ((0 : ℝ) ^ 2 + 1) ^ (-α / 2) = 1 by simp, ENNReal.ofReal_one, one_mul,
    ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

/-- Auxiliary to the Lean proof route: `2 - α ≤ 2^{1-α}` for `α ≥ 1`
(`2^x = e^{x log 2} ≥ 1 + x log 2 ≥ 1 + x` for `x ≤ 0`). -/
theorem two_sub_le_rpow {α : ℝ} (hα : 1 ≤ α) : 2 - α ≤ (2 : ℝ) ^ (1 - α) := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  have h1 := Real.add_one_le_exp (Real.log 2 * (1 - α))
  have h2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have h3 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

/-- Step (e) of the proof (main TeX lines 6140-6146): for `1 < α < 2` and every
`w ∈ ℝ³`, `F_3(w) ≤ 2^{1-α}/(2-α)`. -/
theorem F3w_le {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (w : Rd 3) :
    F3w α w ≤ ENNReal.ofReal (2 ^ (1 - α) / (2 - α)) := by
  obtain ⟨hmax, hval⟩ := F3_max hα1 hα2
  by_cases hw : w = 0
  · rw [hw, F3w_zero, ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ (by linarith), one_mul]
    exact two_sub_le_rpow hα1.le
  · rw [F3w_eq hα2 hw, ← hval]
    exact ENNReal.ofReal_le_ofReal (hmax _ (norm_pos_iff.2 hw))

/-- The maximum is attained on the unit sphere (main TeX line 6146,
"Its maximum is therefore `F_3(e_1) = 2^{1-α}/(2-α)`"): for `1 < α < 2` and
`|w| = 1`, `F_3(w) = 2^{1-α}/(2-α)`. -/
theorem F3w_unit {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) {w : Rd 3} (hw : ‖w‖ = 1) :
    F3w α w = ENNReal.ofReal (2 ^ (1 - α) / (2 - α)) := by
  have hw0 : w ≠ 0 := by
    intro h; rw [h, norm_zero] at hw; exact zero_ne_one hw
  rw [F3w_eq hα2 hw0, hw, (F3_max hα1 hα2).2]

/-! ### `H:spatial-maximum` in `d = 3` -/

/-- The unsmoothed bound in `d = 3`: for `c ≥ 0`, `1 < α < 2`, `h > 0` and
every `z`, `∫ G_h(dy) γ(y + z) ≤ M_3 h^{-(α-1)}` (main TeX lines 6131-6146). The scaling
identity `∫ G_h(dy) γ(y + z) = c h^{1-α} F_3(z/h)` used in the proof is
`HigherRieszTwo.unsmoothed_scaling`. -/
theorem riesz_three_unsmoothed {c α : ℝ} (hc : 0 ≤ c) (hα1 : 1 < α) (hα2 : α < 2)
    {h : ℝ} (hh : 0 < h) (z : Rd 3) :
    ∫⁻ y, riesz c α (y + z) ∂(waveGreen 3 h) ≤ ENNReal.ofReal (M3 c α * h ^ (-(α - 1))) := by
  rw [unsmoothed_scaling (Or.inr (Or.inr rfl)) hc α hh z]
  calc ENNReal.ofReal (c * h ^ (1 - α)) *
        ∫⁻ y, ENNReal.ofReal (‖y + h⁻¹ • z‖ ^ (-α)) ∂(waveGreen 3 1)
      ≤ ENNReal.ofReal (c * h ^ (1 - α)) * ENNReal.ofReal (2 ^ (1 - α) / (2 - α)) :=
        mul_le_mul_right (F3w_le hα1 hα2 _) _
    _ = ENNReal.ofReal (M3 c α * h ^ (-(α - 1))) := by
        rw [← ENNReal.ofReal_mul (by positivity), M3, show -(α - 1) = 1 - α by ring]
        ring_nf

/-- `M_3 > 0` for `c > 0` and `α < 2` (the `M > 0` of `H:spatial-maximum`). -/
theorem M3_pos {c α : ℝ} (hc : 0 < c) (hα2 : α < 2) : 0 < M3 c α := by
  have : 0 < 2 - α := by linarith
  unfold M3; positivity

/-- `L:higher-riesz` in dimension three, the bound (main TeX lines 6103-6190):
for `γ(x) = c|x|^{-α}`, `c > 0`, `1 < α < 2`, Hypothesis `H:spatial-maximum`
holds with `δ = α - 1` and `M = M_3 = c 2^{1-α}/(2-α)`. -/
theorem higher_riesz_three {c α : ℝ} (hc : 0 < c) (hα1 : 1 < α) (hα2 : α < 2) :
    SpatialMaximum 3 (riesz c α) (α - 1) (M3 c α) := by
  refine ⟨M3_pos hc hα2, fun h hh z ε hε η hη => ?_⟩
  have := isFiniteMeasure_waveGreen 3 h
  exact smoothed_average_le (measurable_riesz c α) hε hη
    (fun x => riesz_three_unsmoothed hc.le hα1 hα2 hh x) z

/-! ### Optimality of `M_3` (Fatou) -/

/-- Auxiliary to the Lean proof route: a point is `G_1^{(3)}`-null (main TeX
line 6189, "the single singular point has zero sphere measure").  Proof: the
point lies in a level set of `ω ↦ ⟪e,ω⟫`, whose image measure is
`2π · Lebesgue` on `[-1,1]` (Archimedes' law). -/
theorem waveGreen_three_point (x : Rd 3) : waveGreen 3 1 {x} = 0 := by
  obtain ⟨e, he⟩ := exists_norm_eq (Rd 3) (zero_le_one : (0 : ℝ) ≤ 1)
  show (ENNReal.ofReal (1 / (4 * π)) •
      ((volume : Measure (Rd 3)).toSphere.map
        fun ω : sphere (0 : Rd 3) 1 => (1 : ℝ) • (ω : Rd 3))) {x} = 0
  rw [Measure.smul_apply, Measure.map_apply (by fun_prop) (measurableSet_singleton x),
    smul_eq_mul]
  have hsub : ((fun ω : sphere (0 : Rd 3) 1 => (1 : ℝ) • (ω : Rd 3)) ⁻¹' {x}) ⊆
      (fun ω : sphere (0 : Rd 3) 1 => inner ℝ e (ω : Rd 3)) ⁻¹' {inner ℝ e x} := by
    intro ω hω
    simp only [mem_preimage, mem_singleton_iff, one_smul] at hω ⊢
    rw [hω]
  have h0 : (volume : Measure (Rd 3)).toSphere
      ((fun ω : sphere (0 : Rd 3) 1 => inner ℝ e (ω : Rd 3)) ⁻¹' {inner ℝ e x}) = 0 := by
    rw [← Measure.map_apply (by fun_prop) (measurableSet_singleton _),
      WaveGreenFourier.archimedes e he]
    simp
  rw [measure_mono_null hsub h0, mul_zero]

/-- Auxiliary to the Lean proof route: for `c ≥ 0`, `0 < α < 3` and `x ≠ 0`,
`γ_ε(x) → γ(x)` along `ε_n = 1/(n+1)` (main TeX lines 6178-6186, via
`HigherRieszTwo.approx_identity`). -/
theorem smoothCov_riesz_tendsto {c α : ℝ} (hc : 0 ≤ c) (hα0 : 0 < α) (hα3 : α < 3)
    {x : Rd 3} (hx : x ≠ 0) :
    Tendsto (fun n : ℕ => smoothCov (riesz c α) (1 / ((n : ℝ) + 1)) x) atTop
      (𝓝 (riesz c α x)) := by
  obtain ⟨hint, hlim⟩ := approx_identity (j := 3) hα0 (by exact_mod_cast hα3) hx
  have hval : ∀ ε : ℝ, 0 < ε → smoothCov (riesz c α) ε x =
      ENNReal.ofReal (c * ∫ y : Rd 3, heatK ε (x - y) * ‖y‖ ^ (-α)) := by
    intro ε hε
    rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal]
    · unfold smoothCov riesz
      refine lintegral_congr fun y => ?_
      rw [← ENNReal.ofReal_mul (heatK_pos hε _).le]
      congr 1; ring
    · exact (hint ε hε).const_mul c
    · exact Eventually.of_forall fun y =>
        mul_nonneg hc (mul_nonneg (heatK_pos hε _).le (Real.rpow_nonneg (norm_nonneg _) _))
  have hε : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => by simp only [mem_Ioi]; positivity⟩
  have := ENNReal.tendsto_ofReal ((hlim.comp hε).const_mul c)
  refine this.congr fun n => ?_
  rw [Function.comp_apply, hval _ (by positivity)]

/-- The optimality of `M_3` (main TeX lines 6186-6189): for `c ≥ 0` and
`1 < α < 2`, if Hypothesis `H:spatial-maximum` holds in `d = 3` with
`δ = α - 1` and some `M`, then `M_3 ≤ M`.  Proof: Fatou's lemma at a shift
`|z| = 1`, with `h = 1`, `η = 0` and `ε_n = 1/(n+1) ↓ 0`; the limit of the
smoothed covariances is `γ` off the `G_1^{(3)}`-null point `y = -z`, and
`∫ G_1(dy) γ(y + z) = c F_3(z) = M_3`. -/
theorem higher_riesz_three_optimal {c α : ℝ} (hc : 0 ≤ c) (hα1 : 1 < α) (hα2 : α < 2)
    {M : ℝ} (hS : SpatialMaximum 3 (riesz c α) (α - 1) M) : M3 c α ≤ M := by
  obtain ⟨z, hz⟩ := exists_norm_eq (Rd 3) (zero_le_one : (0 : ℝ) ≤ 1)
  set f : ℕ → Rd 3 → ℝ≥0∞ := fun n y => smoothCov (riesz c α) (1 / ((n : ℝ) + 1)) (y + z)
    with hf_def
  have hfm : ∀ n, Measurable (f n) := fun n =>
    (measurable_smoothCov (measurable_riesz c α) _).comp (measurable_add_const z)
  have hbd : ∀ n, ∫⁻ y, f n y ∂(waveGreen 3 1) ≤ ENNReal.ofReal M := by
    intro n
    have := hS.2 1 one_pos z (1 / ((n : ℝ) + 1)) (by positivity) 0 le_rfl
    simp only [pairing, smoothGreen, ite_true, Real.one_rpow, mul_one] at this
    exact this
  have hae : ∀ᵐ y ∂(waveGreen 3 1), liminf (fun n => f n y) atTop = riesz c α (y + z) := by
    have hnull : waveGreen 3 1 {-z} = 0 := waveGreen_three_point (-z)
    rw [ae_iff]
    refine measure_mono_null (fun y hy => ?_) hnull
    simp only [mem_ofPred_eq] at hy
    simp only [mem_singleton_iff]
    by_contra hne
    have hyz : y + z ≠ 0 := fun h => hne (eq_neg_of_add_eq_zero_left h)
    exact hy (smoothCov_riesz_tendsto hc (by linarith) (by linarith) hyz).liminf_eq
  have hval : ∫⁻ y, riesz c α (y + z) ∂(waveGreen 3 1) = ENNReal.ofReal (M3 c α) := by
    rw [unsmoothed_scaling (Or.inr (Or.inr rfl)) hc α one_pos z, inv_one, one_smul]
    rw [show ∫⁻ y, ENNReal.ofReal (‖y + z‖ ^ (-α)) ∂(waveGreen 3 1) = F3w α z from rfl,
      F3w_unit hα1 hα2 hz, Real.one_rpow, mul_one, ← ENNReal.ofReal_mul hc, M3]
  have hle : ENNReal.ofReal (M3 c α) ≤ ENNReal.ofReal M := by
    calc ENNReal.ofReal (M3 c α)
        = ∫⁻ y, liminf (fun n => f n y) atTop ∂(waveGreen 3 1) := by
          rw [← hval]; exact (lintegral_congr_ae hae).symm
      _ ≤ liminf (fun n => ∫⁻ y, f n y ∂(waveGreen 3 1)) atTop := lintegral_liminf_le hfm
      _ ≤ ENNReal.ofReal M :=
          liminf_le_of_frequently_le' (Eventually.frequently (Eventually.of_forall hbd))
  exact (ENNReal.ofReal_le_ofReal_iff hS.1.le).1 hle

/-- `L:higher-riesz` in dimension three, in full (main TeX lines 6103-6190):
for `c > 0` and `1 < α < 2`, Hypothesis `H:spatial-maximum` holds with
`δ = α - 1` and `M = M_3`, and `M_3` is the optimal uniform constant (every
admissible `M` satisfies `M_3 ≤ M`). -/
theorem higher_riesz_three_full {c α : ℝ} (hc : 0 < c) (hα1 : 1 < α) (hα2 : α < 2) :
    SpatialMaximum 3 (riesz c α) (α - 1) (M3 c α) ∧
      ∀ M : ℝ, SpatialMaximum 3 (riesz c α) (α - 1) M → M3 c α ≤ M :=
  ⟨higher_riesz_three hc hα1 hα2, fun _ hS => higher_riesz_three_optimal hc.le hα1 hα2 hS⟩

/-! ### The paper wrappers -/

/-- Auxiliary to the Lean proof route: under `H:homog`, `α < 2` (from `α₀ > 0`
and `α₀ + α < 2`, the section's `α < 2 - α₀`, main TeX lines 5912-5913). -/
theorem alpha_lt_two {d : ℕ} {α α₀ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d α α₀ Γ μ) : α < 2 := by
  linarith [hH.alpha0_pos, hH.threshold]

/-- `L:higher-riesz`, the dimension-three clause, with the manuscript's
hypotheses (main TeX lines 6103-6112 and the section's standing assumptions,
lines 5912-5917): `H:homog` for `Γ = γ dx` with `d = 3` and exponents `α, α₀`
(`HomogCovariance`; it gives `α < 2 - α₀ < 2`), `c > 0`, `1 < α`.
Conclusion: Hypothesis `H:spatial-maximum` with `δ = α - 1` and `M = M_3`, and
`M_3` is optimal.  `H:homog` is used only for `α < 2`. -/
theorem higher_riesz_three_paper {c α α₀ : ℝ} {μ : Measure (Rd 3)}
    (hH : HomogCovariance 3 α α₀ (volume.withDensity (riesz c α)) μ) (hc : 0 < c)
    (hα1 : 1 < α) :
    SpatialMaximum 3 (riesz c α) (α - 1) (M3 c α) ∧
      ∀ M : ℝ, SpatialMaximum 3 (riesz c α) (α - 1) M → M3 c α ≤ M :=
  higher_riesz_three_full hc hα1 (alpha_lt_two hH)

/-- `L:higher-riesz` in full, with the manuscript's hypotheses (main TeX lines
6103-6190, the section's standing assumptions at lines 5912-5917): for
`d ∈ {2,3}`, `H:homog` for `Γ = γ dx`, `γ(x) = c|x|^{-α}`, `c > 0`, `1 < α`,
and `α < 3/2` when `d = 2`, Hypothesis `H:spatial-maximum` holds with
`δ = α - 1` and `M = M_d`; in `d = 3` the constant `M_3` is optimal.  In
`d = 3` the bound `α < 2` comes from `H:homog`; in `d = 2`, `H:homog` is
carried but unused and of `1 < α` only `0 < α` is used. -/
theorem higher_riesz_paper {d : ℕ} {c α α₀ : ℝ} {μ : Measure (Rd d)}
    (hH : HomogCovariance d α α₀ (volume.withDensity (riesz c α)) μ) (hd : d = 2 ∨ d = 3)
    (hc : 0 < c) (hα1 : 1 < α) (hα2 : d = 2 → α < 3 / 2) :
    SpatialMaximum d (riesz c α) (α - 1) (Md d c α) ∧
      (d = 3 → ∀ M : ℝ, SpatialMaximum d (riesz c α) (α - 1) M → Md d c α ≤ M) := by
  rcases hd with rfl | rfl
  · refine ⟨?_, fun h => absurd h (by norm_num)⟩
    rw [show Md 2 c α = M2 c α by simp [Md]]
    exact higher_riesz_two_paper hH hc hα1 (hα2 rfl)
  · rw [show Md 3 c α = M3 c α by simp [Md]]
    exact ⟨(higher_riesz_three_paper hH hc hα1).1,
      fun _ => (higher_riesz_three_paper hH hc hα1).2⟩

end StratonovichHAMSecondMoment.HigherRieszThree
