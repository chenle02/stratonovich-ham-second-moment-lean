module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Lemma `L:terminal-wick` (The finite terminal-chain Wick formula) of the main TeX
file `notes/notes_stratonovich_ham_second_moment.tex` at revision a284420:
the terminal-chain measure `E:terminal-chain-measure` (lines 3585-3598), the
statement (lines 3600-3645) and the proof (lines 3647-3699).  Built on the
finite Wick foundation `FiniteWick`.

Formalized:
* The masses (lines 3648-3651): `chainMass d n T = ∫ 1_{[0,T]^n_<} ∏ G_{s_{j+1}-s_j}(ℝ^d) ds`
  equals `T^{2n}/(2n)!` for `T ≥ 0`, `d ∈ {1,2,3}` (`chainMass_eq`; recursion at
  the last vertex `chainMassReal_succ`, wave Green masses from
  `WaveGreen.waveGreen_mass`).
* The terms `Y_n = ∫ ∏_j W(s_j, y_j) ν_n(ds, dy)` as `L²(Ω)`-valued Bochner
  integrals (`prodL2`, `chainIntegral`), their existence (`integrable_prodL2`),
  `Y_0 = 1` (`chainIntegral_zero`) and the majorant `E:terminal-term-majorant`
  (`norm_chainIntegral_le`, with `√V^n = V^{n/2}`).
* `E:terminal-wick-formula` with `E:terminal-pairing-integral`
  (`mixed_moment_eq_sum_pairings`, `pairingIntegral`; via `inner_chainIntegral`),
  zero for odd `m + n` (`mixed_moment_odd`), nonnegativity of every pairing
  integral and of every mixed moment when `K ≥ 0` (`pairing_integral_nonneg`,
  `mixed_moment_nonneg`), entrywise monotonicity for `0 ≤ K₁ ≤ K₂`
  (`mixed_moment_mono`), absolute convergence of `Σ r^n Y_n` in `L²` for every
  real `r` (`summable_norm_smul_chainIntegral`).
* Discharge of both fields of `UniformSeriesTail.TerminalWickInput` for every
  real `r` when `K ≥ 0` (`terminalWickInput_of_nonneg`; in the wrapper's last
  conjunct).
* Wrappers `terminal_wick_paper` and `terminal_wick_mono_paper`. Both use the
  TeX's hypotheses and the supplied inputs below; only `terminal_wick_paper`
  additionally requires the added restriction `hK`, and
  `terminal_wick_mono_paper` does not.

The general theorems are stated for an arbitrary measurable point set `X`, a
centered real Gaussian field (`FiniteWick.CenteredGaussianField`), a variance
bound `K(x,x) ≤ V` and arbitrary finite measures `ν n` on `n`-tuples of points.
The wrappers take `X = [0,T] × ℝ^d` (`Pt d T`), `V = sup_p K(p,p)` with
`BddAbove` (the TeX's `V < ∞`, so `⨆` is a genuine supremum), and the chain
measures `ν n` with total mass `chainMass d n T`.

Supplied inputs (named hypotheses; no conclusion is assumed):
* `hmeas` (TeX lines 3657-3659, "the product is strongly measurable in `L²` on
  the stated pieces"): `z ↦ prodL2 hW z` is a.e. strongly measurable for
  `ν n`.  In the TeX this follows from the mean-square continuity on cells;
  here it is assumed, a.e. only, so it is no stronger than the TeX claim.
* The chain measures `ν n` are not constructed in Lean.  The wrappers take them
  as finite measures on `n`-tuples of points of `[0,T] × ℝ^d` with
  `hmass : ν n (total) = chainMass d n T`, the total mass that the definition
  `E:terminal-chain-measure` gives by Tonelli (pushforwards preserve mass).
  Only this mass is used; every conclusion therefore holds for any finite
  measures with these masses, in particular for `g_n^{T,x}`.

Added restriction, not in the manuscript: global measurability of `K` on pairs
of points (`hK`, used only to split the integral of the pairing sum into the
separate pairing integrals of the formula).  The TeX's hypotheses (mean-square
continuity on the open cells only) do not imply it: a field that is a
non-Borel function of the space variable at one cut time satisfies them.

Implicit hypotheses made explicit: the covariance matrices of the field are
positive semidefinite (part of `CenteredGaussianField`); `IsFiniteMeasure (ν n)`;
`BddAbove` of the variances; `T > 0`.  Every integral conclusion comes with its
integrability (`integrable_prodL2`, `integrable_pairWeight`).

Hypotheses carried but unused: `MeanSquareCellContinuous` (it stands behind the
supplied `hmeas`), `IsProbabilityMeasure P` (the field's laws already force
it), and in `terminal_wick_mono_paper` also `d ∈ {1,2,3}` and `hmass` (the
comparison needs neither).

Differences from the TeX:
* Moment bound: Wick formula plus the count `(2n-1)!!` of pairings
  (`FiniteWick.CenteredGaussianField.sq_moment_le`) instead of Hölder's
  inequality; same bound.
* Absolute convergence: comparison with `Σ c^n/n!` through
  `√((2n-1)!!)/(2n)! ≤ 1/n!` instead of the ratio test.
* Narrower: `r` is real.  The TeX also states complex `r`; the real `L²` space
  is used here (for complex `r` the scalar series `Σ |r|^n ‖Y_n‖₂`, which is
  what absolute convergence means, is the case `r := |r|` of the real statement,
  but a complexified `L²` is not set up).
* Not formalized: the symmetrization paragraph (lines 3677-3683, identification
  with the symmetrized convention of `E:expansion`) and the `d = 3`
  Green-regularization paragraph (lines 3685-3691, agreement with the source's
  fixed-noise convention).  Neither is used by any conclusion here; the chain
  measures enter only through their masses, and `G` in `d = 3` is
  `WaveGreen.waveGreen 3`, whose definition is a documented choice of that
  module.
Lemmas marked "Auxiliary" serve only the Lean proof route.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.FiniteWick
public import StratonovichHAMSecondMoment.WaveGreen
public import StratonovichHAMSecondMoment.UniformSeriesTail

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace StratonovichHAMSecondMoment.TerminalWick

open WaveGreen

/-- The integrand of the total mass of the terminal-chain measure
`g_n^{T,x}` (`E:terminal-chain-measure`, main TeX lines 3585-3598), written by
recursion on the last vertex: `chainWeight d 0 T () = 1` and
`chainWeight d (n+1) T s = 1_{0 < s_{n+1} < T} G_{T - s_{n+1}}(ℝ^d) ·
chainWeight d n s_{n+1} (s_1, …, s_n)`, i.e. `1_{[0,T]^n_<}(s) ∏_j G_{s_{j+1}-s_j}(ℝ^d)`
with `s_{n+1} = T` and the open ordered simplex `0 < s_1 < ⋯ < s_n < T`
(boundary null).  The spatial pushforward under `y_j = x - Σ_{l ≥ j} w_l`
preserves mass, so `∫ chainWeight d n T = g_n^{T,x}(total)` for every `x`
(Tonelli); the measure `g_n^{T,x}` itself is not constructed in Lean. -/
def chainWeight (d : ℕ) : (n : ℕ) → ℝ → (Fin n → ℝ) → ℝ≥0∞
  | 0, _, _ => 1
  | n + 1, T, s =>
    (if 0 < s (Fin.last n) ∧ s (Fin.last n) < T then waveGreen d (T - s (Fin.last n)) univ else 0) *
      chainWeight d n (s (Fin.last n)) (Fin.init s)

/-- Auxiliary (Lean proof route): `chainWeight` with `G_h(ℝ^d)` replaced by `h`. -/
def chainWeightReal : (n : ℕ) → ℝ → (Fin n → ℝ) → ℝ≥0∞
  | 0, _, _ => 1
  | n + 1, T, s =>
    (if 0 < s (Fin.last n) ∧ s (Fin.last n) < T then ENNReal.ofReal (T - s (Fin.last n)) else 0) *
      chainWeightReal n (s (Fin.last n)) (Fin.init s)

/-- Auxiliary: `G_h(ℝ^d) = h` for `h > 0` (`WaveGreen.waveGreen_mass`) identifies the two weights. -/
theorem chainWeight_eq (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) :
    ∀ (n : ℕ) (T : ℝ) (s : Fin n → ℝ), chainWeight d n T s = chainWeightReal n T s := by
  intro n
  induction n with
  | zero => intro T s; rfl
  | succ n ih =>
    intro T s
    simp only [chainWeight, chainWeightReal, ih]
    congr 1
    split_ifs with h
    · exact waveGreen_mass d hd _ (by linarith [h.2])
    · rfl

/-- Auxiliary: joint measurability of `(T, s) ↦ chainWeightReal n T s`. -/
theorem measurable_chainWeightReal (n : ℕ) :
    Measurable fun p : ℝ × (Fin n → ℝ) => chainWeightReal n p.1 p.2 := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    simp only [chainWeightReal]
    have hlast : Measurable fun p : ℝ × (Fin (n + 1) → ℝ) => p.2 (Fin.last n) :=
      (measurable_pi_apply _).comp measurable_snd
    have hinit : Measurable fun p : ℝ × (Fin (n + 1) → ℝ) => Fin.init p.2 :=
      measurable_pi_iff.mpr fun i => (measurable_pi_apply _).comp measurable_snd
    refine Measurable.mul ?_ (ih.comp (hlast.prodMk hinit))
    refine Measurable.ite ?_ (ENNReal.measurable_ofReal.comp (measurable_fst.sub hlast))
      measurable_const
    exact (measurableSet_lt measurable_const hlast).inter (measurableSet_lt hlast measurable_fst)

/-- Auxiliary (Lean proof route): `∫ chainWeightReal n T`. -/
def chainMassReal (n : ℕ) (T : ℝ) : ℝ≥0∞ := ∫⁻ s, chainWeightReal n T s

/-- Integration at the last vertex (TeX lines 3648-3650):
`M_{n+1}(T) = ∫_0^T (T - s) M_n(s) ds`. -/
theorem chainMassReal_succ (n : ℕ) (T : ℝ) :
    chainMassReal (n + 1) T = ∫⁻ t in Ioo 0 T, ENNReal.ofReal (T - t) * chainMassReal n t := by
  unfold chainMassReal
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure ℝ))
    (Fin.last n)
  have hvol : (Measure.pi fun _ : Fin (n + 1) => (volume : Measure ℝ)) = volume := rfl
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)
  set F : ℝ × (Fin n → ℝ) → ℝ≥0∞ := fun p =>
    (if 0 < p.1 ∧ p.1 < T then ENNReal.ofReal (T - p.1) else 0) * chainWeightReal n p.1 p.2 with hF
  have hf : ∀ s : Fin (n + 1) → ℝ, chainWeightReal (n + 1) T s = F (e s) := by
    intro s
    simp [chainWeightReal, hF, e, MeasurableEquiv.piFinSuccAbove_apply]
  calc ∫⁻ s, chainWeightReal (n + 1) T s = ∫⁻ s, F (e s) ∂(Measure.pi fun _ => volume) :=
        lintegral_congr hf
    _ = ∫⁻ p, F p ∂((volume : Measure ℝ).prod (Measure.pi fun _ : Fin n => (volume : Measure ℝ))) :=
        hmp.lintegral_comp_emb e.measurableEmbedding F
    _ = _ := ?_
  rw [show (Measure.pi fun _ : Fin n => (volume : Measure ℝ)) = volume from rfl]
  rw [lintegral_prod _ ?_]
  · rw [← lintegral_indicator measurableSet_Ioo]
    refine lintegral_congr fun t => ?_
    by_cases ht : t ∈ Ioo 0 T
    · rw [indicator_of_mem ht]
      simp only [hF, ite_eq_left (show 0 < t ∧ t < T from ht)]
      exact lintegral_const_mul _ ((measurable_chainWeightReal n).comp measurable_prodMk_left)
    · rw [indicator_of_notMem ht]
      simp only [hF, ite_eq_right (show ¬ (0 < t ∧ t < T) from ht), zero_mul, lintegral_const]
  · refine Measurable.aemeasurable (Measurable.mul ?_ (measurable_chainWeightReal n))
    refine Measurable.ite ?_ (ENNReal.measurable_ofReal.comp (measurable_const.sub measurable_fst))
      measurable_const
    exact (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst measurable_const)

/-- `M_n(T) = T^{2n}/(2n)!` for `T ≥ 0` (TeX lines 3650-3651), by induction. -/
theorem chainMassReal_eq (n : ℕ) : ∀ T : ℝ, 0 ≤ T →
    chainMassReal n T = ENNReal.ofReal (T ^ (2 * n) / (2 * n).factorial) := by
  induction n with
  | zero => intro T _; simp [chainMassReal, chainWeightReal, MeasureTheory.volume_pi]
  | succ n ih =>
    intro T hT
    rw [chainMassReal_succ]
    rw [setLIntegral_congr_fun measurableSet_Ioo (g := fun t => ENNReal.ofReal
      ((T - t) * (t ^ (2 * n) / (2 * n).factorial))) (fun t ht => by
        rw [ih t ht.1.le, ← ENNReal.ofReal_mul (by linarith [ht.2])])]
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · congr 1
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hT]
      have : ∀ t : ℝ, (T - t) * (t ^ (2 * n) / (2 * n).factorial) =
          (T * t ^ (2 * n) - t ^ (2 * n + 1)) / (2 * n).factorial := by
        intro t; ring
      simp_rw [this]
      rw [intervalIntegral.integral_div, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
        integral_pow, integral_pow]
      · rw [show 2 * (n + 1) = 2 * n + 2 by ring, Nat.factorial_succ, Nat.factorial_succ]
        push_cast
        field_simp
        ring
      · exact (continuous_const.mul (continuous_pow _)).intervalIntegrable _ _
      · exact (continuous_pow _).intervalIntegrable _ _
    · exact (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ioo_subset_Icc_self
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact mul_nonneg (by linarith [ht.2]) (div_nonneg (pow_nonneg ht.1.le _) (by positivity))


section Assembly
open FiniteWick Finset
variable {X Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : X → Ω → ℝ} {K : X → X → ℝ}

/-- Auxiliary: `ω ↦ ∏_a W(z_a, ω)` is a.e. strongly measurable (from the law of the vector). -/
theorem aestronglyMeasurable_prod (hW : CenteredGaussianField W K P) {n : ℕ} (z : Fin n → X) :
    AEStronglyMeasurable (fun ω => ∏ a, W (z a) ω) P := by
  have hm := (hW.law n z).aemeasurable
  have hc : Continuous fun x : EuclideanSpace ℝ (Fin n) => ∏ a, x a := by fun_prop
  simpa [Function.comp_def] using hc.comp_aestronglyMeasurable hm.aestronglyMeasurable

/-- `∏_a W(z_a)` is in `L²(Ω)` (its square is integrable by the Wick formula). -/
theorem memLp_prod (hW : CenteredGaussianField W K P) {n : ℕ} (z : Fin n → X) :
    MemLp (fun ω => ∏ a, W (z a) ω) 2 P := by
  rw [memLp_two_iff_integrable_sq (aestronglyMeasurable_prod hW z)]
  simpa [sq] using (hW.wick_append z z).1

/-- The `L²(Ω)` class of `∏_{j} W(z_j)` for a tuple of points `z : Fin n → X`
(the integrand of `Y_n`, TeX line 3607). -/
def prodL2 (hW : CenteredGaussianField W K P) {n : ℕ} (z : Fin n → X) : Lp ℝ 2 P :=
  (memLp_prod hW z).toLp _

/-- `prodL2 hW z = ∏_a W(z_a)` almost surely. -/
theorem coeFn_prodL2 (hW : CenteredGaussianField W K P) {n : ℕ} (z : Fin n → X) :
    prodL2 hW z =ᵐ[P] fun ω => ∏ a, W (z a) ω :=
  MemLp.coeFn_toLp _

/-- `E[∏_a W(z_a) ∏_b W(z'_b)] = Σ_{D ∈ Π(m+n)} ∏_{{a,b} ∈ D} K(τ_a, τ_b)`,
`τ = Fin.append z z'` (TeX lines 3662-3673, pointwise in the chain variables). -/
theorem inner_prodL2 (hW : CenteredGaussianField W K P) {m n : ℕ} (z : Fin m → X)
    (z' : Fin n → X) :
    inner ℝ (prodL2 hW z) (prodL2 hW z') =
      wickSum (fun a b => K (Fin.append z z' a) (Fin.append z z' b)) univ := by
  rw [← UniformSeriesTail.integral_mul_eq_inner, ← (hW.wick_append z z').2]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_prodL2 hW z, coeFn_prodL2 hW z'] with ω h1 h2
  rw [h1, h2]

/-- `‖∏_j W(z_j)‖₂ ≤ √((2n-1)!!) (√V)^n` when `K(x,x) ≤ V` for all `x` (TeX
lines 3651-3656; Lean route via `FiniteWick.wickSum_abs_le`, not Hölder). -/
theorem norm_prodL2_le (hW : CenteredGaussianField W K P) (V : ℝ) (hV0 : 0 ≤ V)
    (hV : ∀ x, K x x ≤ V) {n : ℕ} (z : Fin n → X) :
    ‖prodL2 hW z‖ ≤ Real.sqrt ((2 * n - 1).doubleFactorial) * Real.sqrt V ^ n := by
  have hsq : ‖prodL2 hW z‖ ^ 2 ≤ ((2 * n - 1).doubleFactorial : ℝ) * V ^ n := by
    rw [← real_inner_self_eq_norm_sq, inner_prodL2]
    refine (le_abs_self _).trans ?_
    exact wickSum_abs_le _ V (fun a b => hW.abs_le V hV _ _) n _ (by simp; ring)
  have hB : 0 ≤ Real.sqrt ((2 * n - 1).doubleFactorial) * Real.sqrt V ^ n := by positivity
  have hB2 : (Real.sqrt ((2 * n - 1).doubleFactorial) * Real.sqrt V ^ n) ^ 2 =
      ((2 * n - 1).doubleFactorial : ℝ) * V ^ n := by
    rw [mul_pow, Real.sq_sqrt (by positivity), ← pow_mul, mul_comm n 2, pow_mul,
      Real.sq_sqrt hV0]
  rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq hB]
  exact Real.sqrt_le_sqrt (hsq.trans hB2.ge)

variable [MeasurableSpace X] (ν : ∀ n : ℕ, Measure (Fin n → X)) [∀ n, IsFiniteMeasure (ν n)]

/-- `Y_n = ∫ ∏_j W(s_j, y_j) g_n(ds, dy)` as an `L²(Ω)`-valued Bochner integral
(TeX lines 3605-3608) against a measure `ν n` on `n`-tuples of points.  It is a
genuine integral (not the junk value `0`) exactly when `prodL2 hW` is
`ν n`-integrable, which `integrable_prodL2` proves from the supplied strong
measurability. -/
def chainIntegral (hW : CenteredGaussianField W K P) (n : ℕ) : Lp ℝ 2 P :=
  ∫ z, prodL2 hW z ∂ν n

/-- The Bochner integrals `Y_n` exist (TeX lines 3610, 3657-3660): from the
supplied a.e. strong measurability `hmeas` (the input standing for "the product
is strongly measurable in `L²`", lines 3657-3659), the bound `norm_prodL2_le`
and finiteness of `ν n`. -/
theorem integrable_prodL2 (hW : CenteredGaussianField W K P) (V : ℝ) (hV0 : 0 ≤ V)
    (hV : ∀ x, K x x ≤ V)
    (hmeas : ∀ n, AEStronglyMeasurable (fun z : Fin n → X => prodL2 hW z) (ν n)) (n : ℕ) :
    Integrable (fun z : Fin n → X => prodL2 hW z) (ν n) :=
  Integrable.of_bound (hmeas n) _ (ae_of_all _ fun z => norm_prodL2_le hW V hV0 hV z)

/-- The majorant: `‖Y_n‖₂ ≤ √((2n-1)!!) (√V)^n ν_n(total)` (with the mass
`T^{2n}/(2n)!` this is `E:terminal-term-majorant`, TeX lines 3611-3615).  No
integrability hypothesis is needed for the inequality itself. -/
theorem norm_chainIntegral_le (hW : CenteredGaussianField W K P) (V : ℝ) (hV0 : 0 ≤ V)
    (hV : ∀ x, K x x ≤ V) (n : ℕ) :
    ‖chainIntegral ν hW n‖ ≤
      Real.sqrt ((2 * n - 1).doubleFactorial) * Real.sqrt V ^ n * (ν n).real univ :=
  norm_integral_le_of_norm_le_const (ae_of_all _ fun z => norm_prodL2_le hW V hV0 hV z)

/-- Auxiliary: `(s, r) ↦ ⟪prodL2 s, prodL2 r⟫` is integrable for `ν_m ⊗ ν_n`. -/
theorem integrable_inner_prod (hW : CenteredGaussianField W K P) (V : ℝ) (hV0 : 0 ≤ V)
    (hV : ∀ x, K x x ≤ V)
    (hmeas : ∀ n, AEStronglyMeasurable (fun z : Fin n → X => prodL2 hW z) (ν n)) (m n : ℕ) :
    Integrable (fun q : (Fin m → X) × (Fin n → X) => inner ℝ (prodL2 hW q.1) (prodL2 hW q.2))
      ((ν m).prod (ν n)) := by
  refine Integrable.of_bound ((hmeas m).comp_fst.inner (hmeas n).comp_snd)
    ((Real.sqrt ((2 * m - 1).doubleFactorial) * Real.sqrt V ^ m) *
      (Real.sqrt ((2 * n - 1).doubleFactorial) * Real.sqrt V ^ n)) (ae_of_all _ fun q => ?_)
  refine (norm_inner_le_norm _ _).trans ?_
  exact mul_le_mul (norm_prodL2_le hW V hV0 hV _) (norm_prodL2_le hW V hV0 hV _)
    (norm_nonneg _) (by positivity)

/-- Fubini through the two chain measures (TeX lines 3662-3675):
`⟪Y_m, Y_n⟫ = ∫∫ Σ_{D ∈ Π(m+n)} ∏_{{a,b} ∈ D} K(τ_a, τ_b) d(ν_m ⊗ ν_n)`, via
`integral_inner` twice and `integral_prod_symm`. -/
theorem inner_chainIntegral (hW : CenteredGaussianField W K P) (V : ℝ) (hV0 : 0 ≤ V)
    (hV : ∀ x, K x x ≤ V)
    (hmeas : ∀ n, AEStronglyMeasurable (fun z : Fin n → X => prodL2 hW z) (ν n)) (m n : ℕ) :
    inner ℝ (chainIntegral ν hW m) (chainIntegral ν hW n) =
      ∫ q, wickSum (fun a b => K (Fin.append q.1 q.2 a) (Fin.append q.1 q.2 b)) univ
        ∂((ν m).prod (ν n)) := by
  have hm := integrable_prodL2 ν hW V hV0 hV hmeas m
  have hn := integrable_prodL2 ν hW V hV0 hV hmeas n
  calc inner ℝ (chainIntegral ν hW m) (chainIntegral ν hW n)
      = ∫ r, inner ℝ (chainIntegral ν hW m) (prodL2 hW r) ∂ν n :=
        (integral_inner hn _).symm
    _ = ∫ r, ∫ s, inner ℝ (prodL2 hW s) (prodL2 hW r) ∂ν m ∂ν n := by
        refine integral_congr_ae (ae_of_all _ fun r => ?_)
        simp only
        rw [real_inner_comm, chainIntegral, ← integral_inner hm]
        exact integral_congr_ae (ae_of_all _ fun s => real_inner_comm _ _)
    _ = ∫ q, inner ℝ (prodL2 hW q.1) (prodL2 hW q.2) ∂((ν m).prod (ν n)) :=
        (integral_prod_symm _ (integrable_inner_prod ν hW V hV0 hV hmeas m n)).symm
    _ = _ := integral_congr_ae (ae_of_all _ fun q => inner_prodL2 hW q.1 q.2)


/-- Auxiliary: concatenation of tuples is measurable. -/
theorem measurable_append {m n : ℕ} :
    Measurable fun q : (Fin m → X) × (Fin n → X) => Fin.append q.1 q.2 := by
  refine measurable_pi_iff.mpr fun a => ?_
  refine Fin.addCases (fun i => ?_) (fun i => ?_) a
  · simp only [Fin.append_left]; exact (measurable_pi_apply i).comp measurable_fst
  · simp only [Fin.append_right]; exact (measurable_pi_apply i).comp measurable_snd

/-- Each pairing integrand `q ↦ ∏_{{a,b} ∈ D} K(τ_a, τ_b)` is integrable for
`ν_m ⊗ ν_n`, given measurability of `K` and `|K| ≤ V` (bound `max(V,1)^{m+n}`). -/
theorem integrable_pairWeight (hK : Measurable fun q : X × X => K q.1 q.2) (V : ℝ)
    (hKV : ∀ x y, |K x y| ≤ V) (m n : ℕ) (D : Fin (m + n) → Fin (m + n)) :
    Integrable (fun q : (Fin m → X) × (Fin n → X) =>
      pairWeight (fun a b => K (Fin.append q.1 q.2 a) (Fin.append q.1 q.2 b)) univ D)
      ((ν m).prod (ν n)) := by
  have hmeasf : Measurable fun q : (Fin m → X) × (Fin n → X) =>
      pairWeight (fun a b => K (Fin.append q.1 q.2 a) (Fin.append q.1 q.2 b)) univ D := by
    unfold pairWeight
    refine Finset.measurable_prod _ fun x _ => ?_
    exact hK.comp (((measurable_pi_apply x).comp measurable_append).prodMk
      ((measurable_pi_apply (D x)).comp measurable_append))
  refine Integrable.of_bound hmeasf.aestronglyMeasurable (max V 1 ^ (m + n))
    (ae_of_all _ fun q => ?_)
  unfold pairWeight
  rw [Real.norm_eq_abs, Finset.abs_prod]
  have h1 : ∏ x ∈ univ with x < D x, |K (Fin.append q.1 q.2 x) (Fin.append q.1 q.2 (D x))| ≤
      ∏ x ∈ univ with x < D x, (fun _ => max V 1) x :=
    Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun x _ => (hKV _ _).trans (le_max_left _ _)
  refine h1.trans ?_
  rw [Finset.prod_const]
  refine pow_le_pow_right₀ (le_max_right _ _) ?_
  exact (Finset.card_le_univ _).trans (by simp)

omit [∀ n, IsFiniteMeasure (ν n)] in
/-- Auxiliary: `E[Y_m Y_n] = ⟪Y_m, Y_n⟫` in `L²`. -/
theorem mixed_moment_eq_inner (hW : CenteredGaussianField W K P) (m n : ℕ) :
    ∫ ω, chainIntegral ν hW m ω * chainIntegral ν hW n ω ∂P =
      inner ℝ (chainIntegral ν hW m) (chainIntegral ν hW n) :=
  UniformSeriesTail.integral_mul_eq_inner _ _

/-- `E:terminal-wick-formula` (TeX lines 3616-3637) in general form:
`E[Y_m Y_n] = Σ_{D ∈ Π(m+n)} ∫ ∏_{{a,b} ∈ D} K(τ_a, τ_b) d(ν_m ⊗ ν_n)`, one
term per pairing with coefficient one.  `hK` (measurability of `K`) is used
only to split the integral of the pairing sum into the individual pairing
integrals. -/
theorem mixed_moment_eq_sum_pairings (hW : CenteredGaussianField W K P) (V : ℝ) (hV0 : 0 ≤ V)
    (hV : ∀ x, K x x ≤ V)
    (hmeas : ∀ n, AEStronglyMeasurable (fun z : Fin n → X => prodL2 hW z) (ν n))
    (hK : Measurable fun q : X × X => K q.1 q.2) (m n : ℕ) :
    ∫ ω, chainIntegral ν hW m ω * chainIntegral ν hW n ω ∂P =
      ∑ D ∈ pairings (univ : Finset (Fin (m + n))),
        ∫ q, pairWeight (fun a b => K (Fin.append q.1 q.2 a) (Fin.append q.1 q.2 b)) univ D
          ∂((ν m).prod (ν n)) := by
  rw [mixed_moment_eq_inner, inner_chainIntegral ν hW V hV0 hV hmeas]
  unfold wickSum
  exact integral_finsetSum _ fun D _ =>
    integrable_pairWeight ν hK V (fun x y => hW.abs_le V hV x y) m n D

/-- If `m + n` is odd, `E[Y_m Y_n] = 0` (TeX line 3638). -/
theorem mixed_moment_odd (hW : CenteredGaussianField W K P) (V : ℝ) (hV0 : 0 ≤ V)
    (hV : ∀ x, K x x ≤ V)
    (hmeas : ∀ n, AEStronglyMeasurable (fun z : Fin n → X => prodL2 hW z) (ν n)) (m n : ℕ)
    (hodd : Odd (m + n)) :
    ∫ ω, chainIntegral ν hW m ω * chainIntegral ν hW n ω ∂P = 0 := by
  obtain ⟨k, hk⟩ := hodd
  rw [mixed_moment_eq_inner, inner_chainIntegral ν hW V hV0 hV hmeas]
  refine (integral_congr_ae (ae_of_all _ fun q => ?_)).trans (integral_zero _ _)
  exact wickSum_odd _ k _ (by simp [hk])

/-- Auxiliary: the pairing-sum integrand is `ν_m ⊗ ν_n`-integrable. -/
theorem integrable_wickSum_append (hW : CenteredGaussianField W K P) (V : ℝ) (hV0 : 0 ≤ V)
    (hV : ∀ x, K x x ≤ V)
    (hmeas : ∀ n, AEStronglyMeasurable (fun z : Fin n → X => prodL2 hW z) (ν n)) (m n : ℕ) :
    Integrable (fun q : (Fin m → X) × (Fin n → X) =>
      wickSum (fun a b => K (Fin.append q.1 q.2 a) (Fin.append q.1 q.2 b)) univ)
      ((ν m).prod (ν n)) :=
  (integrable_inner_prod ν hW V hV0 hV hmeas m n).congr
    (ae_of_all _ fun q => inner_prodL2 hW q.1 q.2)

/-- If `K ≥ 0` then `E[Y_m Y_n] ≥ 0` (TeX lines 3639-3640, 3693-3694). -/
theorem mixed_moment_nonneg (hW : CenteredGaussianField W K P) (V : ℝ) (hV0 : 0 ≤ V)
    (hV : ∀ x, K x x ≤ V)
    (hmeas : ∀ n, AEStronglyMeasurable (fun z : Fin n → X => prodL2 hW z) (ν n))
    (hKpos : ∀ x y, 0 ≤ K x y) (m n : ℕ) :
    0 ≤ ∫ ω, chainIntegral ν hW m ω * chainIntegral ν hW n ω ∂P := by
  rw [mixed_moment_eq_inner, inner_chainIntegral ν hW V hV0 hV hmeas]
  exact integral_nonneg fun q => wickSum_nonneg _ (fun a b => hKpos _ _) _

omit [∀ n, IsFiniteMeasure (ν n)] in
/-- If `K ≥ 0`, every pairing integral is nonnegative (TeX lines 3639-3640). -/
theorem pairing_integral_nonneg (hKpos : ∀ x y, 0 ≤ K x y) (m n : ℕ)
    (D : Fin (m + n) → Fin (m + n)) :
    0 ≤ ∫ q, pairWeight (fun a b => K (Fin.append q.1 q.2 a) (Fin.append q.1 q.2 b)) univ D
      ∂((ν m).prod (ν n)) :=
  integral_nonneg fun _ => Finset.prod_nonneg fun _ _ => hKpos _ _

/-- Auxiliary (Lean proof route): `√((2n-1)!!)/(2n)! ≤ 1/n!`, from
`(2n-1)!! ≤ (2n)!` and `(n!)² ≤ (2n)!`. -/
theorem sqrt_doubleFactorial_div_le (n : ℕ) :
    Real.sqrt ((2 * n - 1).doubleFactorial) / (2 * n).factorial ≤ 1 / n.factorial := by
  have h1 : (2 * n - 1).doubleFactorial ≤ (2 * n).factorial :=
    (Nat.doubleFactorial_le_factorial _).trans (Nat.factorial_le (by omega))
  have h2 : n.factorial * n.factorial ≤ (2 * n).factorial := by
    have := Nat.factorial_mul_factorial_dvd_factorial_add n n
    rw [show n + n = 2 * n by ring] at this
    exact Nat.le_of_dvd (Nat.factorial_pos _) this
  have hb : (0 : ℝ) < (2 * n).factorial := by exact_mod_cast Nat.factorial_pos _
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos _
  have h1' : ((2 * n - 1).doubleFactorial : ℝ) ≤ (2 * n).factorial := by exact_mod_cast h1
  have h2' : (n.factorial : ℝ) ^ 2 ≤ (2 * n).factorial := by rw [sq]; exact_mod_cast h2
  have hs1 : Real.sqrt ((2 * n - 1).doubleFactorial) ≤ Real.sqrt ((2 * n).factorial) :=
    Real.sqrt_le_sqrt h1'
  have hs2 : (n.factorial : ℝ) ≤ Real.sqrt ((2 * n).factorial) :=
    Real.le_sqrt_of_sq_le h2'
  rw [div_le_div_iff₀ hb hf, one_mul]
  calc Real.sqrt ((2 * n - 1).doubleFactorial) * n.factorial
      ≤ Real.sqrt ((2 * n).factorial) * Real.sqrt ((2 * n).factorial) :=
        mul_le_mul hs1 hs2 hf.le (Real.sqrt_nonneg _)
    _ = (2 * n).factorial := Real.mul_self_sqrt hb.le

/-- Auxiliary: `Σ_n c^n √((2n-1)!!)/(2n)!` converges for `c ≥ 0` (comparison
with `Σ c^n/n!`; the TeX uses the ratio test, lines 3695-3697). -/
theorem summable_majorant (c : ℝ) (hc : 0 ≤ c) :
    Summable fun n : ℕ => c ^ n * (Real.sqrt ((2 * n - 1).doubleFactorial) / (2 * n).factorial) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (Real.summable_pow_div_factorial c)
  rw [div_eq_mul_one_div (c ^ n)]
  exact mul_le_mul_of_nonneg_left (sqrt_doubleFactorial_div_le n) (pow_nonneg hc n)

/-- Absolute convergence of `Σ_n r^n Y_n` in `L²` for every real `r` (TeX lines
3642-3644, 3695-3698), given the masses `ν_n(total) = T^{2n}/(2n)!`; the
zero-variance case `V = 0` is included. -/
theorem summable_norm_smul_chainIntegral (hW : CenteredGaussianField W K P) (V : ℝ)
    (hV0 : 0 ≤ V) (hV : ∀ x, K x x ≤ V) (T : ℝ)
    (hmass : ∀ n, (ν n).real univ = T ^ (2 * n) / (2 * n).factorial) (r : ℝ) :
    Summable fun n => ‖r ^ n • chainIntegral ν hW n‖ := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (summable_majorant (|r| * Real.sqrt V * T ^ 2) (by positivity))
  rw [norm_smul, norm_pow, Real.norm_eq_abs]
  have h := norm_chainIntegral_le ν hW V hV0 hV n
  rw [hmass n] at h
  calc |r| ^ n * ‖chainIntegral ν hW n‖
      ≤ |r| ^ n * (Real.sqrt ((2 * n - 1).doubleFactorial) * Real.sqrt V ^ n *
          (T ^ (2 * n) / (2 * n).factorial)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = (|r| * Real.sqrt V * T ^ 2) ^ n *
          (Real.sqrt ((2 * n - 1).doubleFactorial) / (2 * n).factorial) := by
        rw [mul_pow, mul_pow, ← pow_mul, mul_comm 2 n]
        ring

/-- Discharge of `UniformSeriesTail.TerminalWickInput` (both fields) for the
family `Y_n` and every real `r`, when `K ≥ 0`. -/
theorem terminalWickInput_of_nonneg (hW : CenteredGaussianField W K P) (V : ℝ)
    (hV0 : 0 ≤ V) (hV : ∀ x, K x x ≤ V)
    (hmeas : ∀ n, AEStronglyMeasurable (fun z : Fin n → X => prodL2 hW z) (ν n)) (T : ℝ)
    (hmass : ∀ n, (ν n).real univ = T ^ (2 * n) / (2 * n).factorial)
    (hKpos : ∀ x y, 0 ≤ K x y) (r : ℝ) :
    UniformSeriesTail.TerminalWickInput P (fun n => chainIntegral ν hW n) r :=
  ⟨summable_norm_smul_chainIntegral ν hW V hV0 hV T hmass r,
    fun m n => mixed_moment_nonneg ν hW V hV0 hV hmeas hKpos m n⟩

end Assembly

section Mono
open FiniteWick Finset
variable {X Ω₁ Ω₂ : Type*} [MeasurableSpace X] [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
  {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} {W₁ : X → Ω₁ → ℝ} {W₂ : X → Ω₂ → ℝ} {K₁ K₂ : X → X → ℝ}
  (ν : ∀ n : ℕ, Measure (Fin n → X)) [∀ n, IsFiniteMeasure (ν n)]

/-- Entrywise comparison (TeX lines 3640-3642, 3694-3695): for two centered
Gaussian fields with `0 ≤ K₁ ≤ K₂` and the same chain measures,
`E[Y¹_m Y¹_n] ≤ E[Y²_m Y²_n]`. -/
theorem mixed_moment_mono (hW₁ : CenteredGaussianField W₁ K₁ P₁)
    (hW₂ : CenteredGaussianField W₂ K₂ P₂) (V₁ V₂ : ℝ) (hV₁0 : 0 ≤ V₁) (hV₂0 : 0 ≤ V₂)
    (hV₁ : ∀ x, K₁ x x ≤ V₁) (hV₂ : ∀ x, K₂ x x ≤ V₂)
    (hmeas₁ : ∀ n, AEStronglyMeasurable (fun z : Fin n → X => prodL2 hW₁ z) (ν n))
    (hmeas₂ : ∀ n, AEStronglyMeasurable (fun z : Fin n → X => prodL2 hW₂ z) (ν n))
    (h0 : ∀ x y, 0 ≤ K₁ x y) (h12 : ∀ x y, K₁ x y ≤ K₂ x y) (m n : ℕ) :
    ∫ ω, chainIntegral ν hW₁ m ω * chainIntegral ν hW₁ n ω ∂P₁ ≤
      ∫ ω, chainIntegral ν hW₂ m ω * chainIntegral ν hW₂ n ω ∂P₂ := by
  rw [mixed_moment_eq_inner, inner_chainIntegral ν hW₁ V₁ hV₁0 hV₁ hmeas₁,
    mixed_moment_eq_inner, inner_chainIntegral ν hW₂ V₂ hV₂0 hV₂ hmeas₂]
  exact integral_mono (integrable_wickSum_append ν hW₁ V₁ hV₁0 hV₁ hmeas₁ m n)
    (integrable_wickSum_append ν hW₂ V₂ hV₂0 hV₂ hmeas₂ m n)
    fun q => wickSum_mono _ _ (fun a b => h0 _ _) (fun a b => h12 _ _) _

end Mono
section Paper
open FiniteWick Finset Filter Topology HomogHypothesis

/-- The point set `[0,T] × ℝ^d` of the field in `L:terminal-wick` (TeX line 3601). -/
abbrev Pt (d : ℕ) (T : ℝ) := ↥(Set.Icc (0 : ℝ) T) × Rd d

/-- `M_n(T)`, the total mass of `g_n^{T,x}` (TeX lines 3648-3651), as the integral
of `chainWeight` (product of the wave Green masses over the ordered simplex). -/
def chainMass (d n : ℕ) (T : ℝ) : ℝ≥0∞ := ∫⁻ s, chainWeight d n T s

/-- `M_n(T) = T^{2n}/(2n)!` for `T ≥ 0`, `d ∈ {1,2,3}` (TeX lines 3648-3651),
from `G_h(ℝ^d) = h` (`WaveGreen.waveGreen_mass`). -/
theorem chainMass_eq (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) (n : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    chainMass d n T = ENNReal.ofReal (T ^ (2 * n) / (2 * n).factorial) := by
  unfold chainMass
  simp_rw [chainWeight_eq d hd]
  exact chainMassReal_eq n T hT

/-- Joint mean-square continuity on each open cell of a finite partition of
`[0,T]`, times `ℝ^d` (TeX lines 3603-3605): there is a finite set `Z` of cut
times such that at every point `p` whose time is not in `Z`,
`E|W(q) - W(p)|² = K(q,q) - 2K(p,q) + K(p,p) → 0` as `q → p` (the open cells
are open, so continuity on them is continuity at their points; `Z` contains the
cut points, which may include `0` and `T`). -/
def MeanSquareCellContinuous {d : ℕ} {T : ℝ} (K : Pt d T → Pt d T → ℝ) : Prop :=
  ∃ Z : Finset ℝ, ∀ p : Pt d T, (p.1 : ℝ) ∉ Z →
    Tendsto (fun q => K q q - 2 * K p q + K p p) (𝓝 p) (𝓝 0)

/-- The pairing integral `T^K_{m,n,D}` of `E:terminal-pairing-integral` (TeX
lines 3624-3637): the integral against `ν_m ⊗ ν_n` (the two chain measures)
of `∏_{{a,b} ∈ D} K(τ_a, τ_b)`, `τ = Fin.append` of the two tuples. -/
def pairingIntegral {X : Type*} [MeasurableSpace X] (ν : ∀ n : ℕ, Measure (Fin n → X))
    (K : X → X → ℝ) (m n : ℕ) (D : Fin (m + n) → Fin (m + n)) : ℝ :=
  ∫ q, pairWeight (fun a b => K (Fin.append q.1 q.2 a) (Fin.append q.1 q.2 b)) univ D
    ∂((ν m).prod (ν n))

/-- `Y_0 = 1` (TeX lines 3597-3598, 3605): if `ν 0` has mass one (the unit mass on
the empty tuple), then `Y_0 = 1` almost surely. -/
theorem chainIntegral_zero {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    {P : Measure Ω} {W : X → Ω → ℝ} {K : X → X → ℝ} (hW : CenteredGaussianField W K P)
    (ν : ∀ n : ℕ, Measure (Fin n → X)) (h0 : ν 0 univ = 1) :
    (chainIntegral ν hW 0 : Ω → ℝ) =ᵐ[P] fun _ => 1 := by
  unfold chainIntegral
  rw [integral_unique, measureReal_def, h0, ENNReal.toReal_one, one_smul]
  filter_upwards [coeFn_prodL2 hW (default : Fin 0 → X)] with ω h
  rw [h]
  simp

/-- Auxiliary: `(√V)^n = V^{n/2}` for `V ≥ 0`. -/
theorem sqrt_pow_eq_rpow (V : ℝ) (hV : 0 ≤ V) (n : ℕ) :
    Real.sqrt V ^ n = V ^ ((n : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hV]
  congr 1
  ring

/-- Auxiliary: `V = sup_p K(p,p) ≥ 0` (variances are nonnegative; `[0,T] × ℝ^d` is nonempty). -/
theorem supVar_nonneg {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ} {T : ℝ}
    {W : Pt d T → Ω → ℝ} {K : Pt d T → Pt d T → ℝ} (hW : CenteredGaussianField W K P)
    (hT : 0 ≤ T) (hVfin : BddAbove (Set.range fun p => K p p)) : 0 ≤ ⨆ p, K p p := by
  have h1 := (hW.psd 1 ![(⟨0, ⟨le_rfl, hT⟩⟩, 0)]).diag_nonneg (i := 0)
  simp at h1
  exact h1.trans (le_ciSup hVfin _)

/-- `L:terminal-wick` (main TeX lines 3600-3645, proof 3647-3699 at a284420),
wrapper.  Hypotheses: `d ∈ {1,2,3}`, `T > 0`; a centered real
Gaussian field `W` on `[0,T] × ℝ^d` with covariance `K`; `V = sup_p K(p,p) < ∞`
(`BddAbove`); mean-square continuity on the open cells of a finite partition
(carried, unused: it stands behind `hmeas`); the chain measures `ν n`
(finite, total mass `chainMass d n T`; see the module doc); the supplied
strong measurability `hmeas`; global measurability of `K` (`hK`, an added
restriction not in the manuscript, used only for the pairing-by-pairing
split).  Conclusions: the Bochner integrals `Y_n` exist in
`L²`; `Y_0 = 1`; `‖Y_n‖₂ ≤ √((2n-1)!!) V^{n/2} T^{2n}/(2n)!`
(`E:terminal-term-majorant`, all `n`, including `n = 0`); `E[Y_m Y_n] =
Σ_{D ∈ Π(m+n)} T^K_{m,n,D}` (`E:terminal-wick-formula`; `Π(m+n)` is empty when
`m + n` is odd), each pairing integrand being integrable; `E[Y_m Y_n] = 0` for odd `m + n`; if `K ≥ 0`, every
`T^K_{m,n,D} ≥ 0` and every `E[Y_m Y_n] ≥ 0`; `Σ r^n Y_n` converges absolutely
in `L²` for every REAL `r` (narrower: complex `r` not stated); and, if `K ≥ 0`,
`UniformSeriesTail.TerminalWickInput P Y r` for every real `r`.  The
comparison `0 ≤ K₁ ≤ K₂` is `terminal_wick_mono_paper`. -/
theorem terminal_wick_paper {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) (T : ℝ) (hT : 0 < T)
    (W : Pt d T → Ω → ℝ) (K : Pt d T → Pt d T → ℝ) (hW : CenteredGaussianField W K P)
    (hVfin : BddAbove (Set.range fun p => K p p))
    (_hcell : MeanSquareCellContinuous K)
    (ν : ∀ n : ℕ, Measure (Fin n → Pt d T)) [∀ n, IsFiniteMeasure (ν n)]
    (hmass : ∀ n, ν n univ = chainMass d n T)
    (hmeas : ∀ n, AEStronglyMeasurable (fun z : Fin n → Pt d T => prodL2 hW z) (ν n))
    (hK : Measurable fun q : Pt d T × Pt d T => K q.1 q.2) :
    (∀ n, Integrable (fun z : Fin n → Pt d T => prodL2 hW z) (ν n)) ∧
      ((chainIntegral ν hW 0 : Ω → ℝ) =ᵐ[P] fun _ => 1) ∧
      (∀ n, ‖chainIntegral ν hW n‖ ≤ Real.sqrt ((2 * n - 1).doubleFactorial) *
        (⨆ p, K p p) ^ ((n : ℝ) / 2) * (T ^ (2 * n) / (2 * n).factorial)) ∧
      (∀ m n, ∫ ω, chainIntegral ν hW m ω * chainIntegral ν hW n ω ∂P =
        ∑ D ∈ pairings (univ : Finset (Fin (m + n))), pairingIntegral ν K m n D) ∧
      (∀ m n (D : Fin (m + n) → Fin (m + n)), Integrable (fun q : (Fin m → Pt d T) × (Fin n → Pt d T) =>
        pairWeight (fun a b => K (Fin.append q.1 q.2 a) (Fin.append q.1 q.2 b)) univ D)
        ((ν m).prod (ν n))) ∧
      (∀ m n, Odd (m + n) → ∫ ω, chainIntegral ν hW m ω * chainIntegral ν hW n ω ∂P = 0) ∧
      ((∀ p q, 0 ≤ K p q) →
        (∀ m n (D : Fin (m + n) → Fin (m + n)), 0 ≤ pairingIntegral ν K m n D) ∧
        ∀ m n, 0 ≤ ∫ ω, chainIntegral ν hW m ω * chainIntegral ν hW n ω ∂P) ∧
      (∀ r : ℝ, Summable fun n => ‖r ^ n • chainIntegral ν hW n‖) ∧
      ((∀ p q, 0 ≤ K p q) → ∀ r : ℝ,
        UniformSeriesTail.TerminalWickInput P (fun n => chainIntegral ν hW n) r) := by
  set V := ⨆ p, K p p with hVdef
  have hV : ∀ p, K p p ≤ V := fun p => le_ciSup hVfin p
  have hV0 : 0 ≤ V := supVar_nonneg hW hT.le hVfin
  have hmassR : ∀ n, (ν n).real univ = T ^ (2 * n) / (2 * n).factorial := by
    intro n
    rw [measureReal_def, hmass n, chainMass_eq d hd n T hT.le, ENNReal.toReal_ofReal]
    positivity
  refine ⟨integrable_prodL2 ν hW V hV0 hV hmeas, ?_, fun n => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine chainIntegral_zero hW ν ?_
    rw [hmass 0, chainMass_eq d hd 0 T hT.le]; simp
  · have h := norm_chainIntegral_le ν hW V hV0 hV n
    rwa [hmassR n, sqrt_pow_eq_rpow V hV0] at h
  · exact fun m n => mixed_moment_eq_sum_pairings ν hW V hV0 hV hmeas hK m n
  · exact fun m n D => integrable_pairWeight ν hK V (fun x y => hW.abs_le V hV x y) m n D
  · exact fun m n h => mixed_moment_odd ν hW V hV0 hV hmeas m n h
  · exact fun hpos => ⟨fun m n D => pairing_integral_nonneg ν hpos m n D,
      fun m n => mixed_moment_nonneg ν hW V hV0 hV hmeas hpos m n⟩
  · exact summable_norm_smul_chainIntegral ν hW V hV0 hV T hmassR
  · exact fun hpos r => terminalWickInput_of_nonneg ν hW V hV0 hV hmeas T hmassR hpos r

/-- The comparison sentence of `L:terminal-wick` (main TeX lines 3640-3642,
proof 3693-3695 at a284420), exact-hypothesis wrapper: two centered real
Gaussian fields on `[0,T] × ℝ^d` with covariances `0 ≤ K₁ ≤ K₂` (entrywise),
each under the hypotheses of `terminal_wick_paper`, and the same chain measures;
then `E[Y¹_m Y¹_n] ≤ E[Y²_m Y²_n]` for all `m, n`.  Carried, unused: `d ∈ {1,2,3}`,
the masses `hmass`, the cell continuity and `IsProbabilityMeasure`. -/
theorem terminal_wick_mono_paper {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (P₁ : Measure Ω₁) (P₂ : Measure Ω₂) [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (d : ℕ) (_hd : d = 1 ∨ d = 2 ∨ d = 3) (T : ℝ) (hT : 0 < T)
    (W₁ : Pt d T → Ω₁ → ℝ) (K₁ : Pt d T → Pt d T → ℝ) (hW₁ : CenteredGaussianField W₁ K₁ P₁)
    (W₂ : Pt d T → Ω₂ → ℝ) (K₂ : Pt d T → Pt d T → ℝ) (hW₂ : CenteredGaussianField W₂ K₂ P₂)
    (hV₁fin : BddAbove (Set.range fun p => K₁ p p))
    (hV₂fin : BddAbove (Set.range fun p => K₂ p p))
    (_hcell₁ : MeanSquareCellContinuous K₁) (_hcell₂ : MeanSquareCellContinuous K₂)
    (ν : ∀ n : ℕ, Measure (Fin n → Pt d T)) [∀ n, IsFiniteMeasure (ν n)]
    (_hmass : ∀ n, ν n univ = chainMass d n T)
    (hmeas₁ : ∀ n, AEStronglyMeasurable (fun z : Fin n → Pt d T => prodL2 hW₁ z) (ν n))
    (hmeas₂ : ∀ n, AEStronglyMeasurable (fun z : Fin n → Pt d T => prodL2 hW₂ z) (ν n))
    (h0 : ∀ p q, 0 ≤ K₁ p q) (h12 : ∀ p q, K₁ p q ≤ K₂ p q) (m n : ℕ) :
    ∫ ω, chainIntegral ν hW₁ m ω * chainIntegral ν hW₁ n ω ∂P₁ ≤
      ∫ ω, chainIntegral ν hW₂ m ω * chainIntegral ν hW₂ n ω ∂P₂ :=
  mixed_moment_mono ν hW₁ hW₂ _ _ (supVar_nonneg hW₁ hT.le hV₁fin) (supVar_nonneg hW₂ hT.le hV₂fin)
    (fun p => le_ciSup hV₁fin p) (fun p => le_ciSup hV₂fin p) hmeas₁ hmeas₂ h0 h12 m n

end Paper
end StratonovichHAMSecondMoment.TerminalWick
