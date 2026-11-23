module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

`P:low-alpha-upper` (Upper bound for `α ≤ 1`) and `C:d1-first-calibration`
(First-moment calibration) of the main TeX file
`notes/notes_stratonovich_ham_second_moment.tex` at revision edf7085f (wave L13
item D3): `P:low-alpha-upper` statement at main TeX lines 5711-5733 (constants
`E:low-alpha-constants`, lines 5714-5725; displays `E:low-alpha-coefficient`,
lines 5727-5732), proof at lines 5736-5807; `C:d1-first-calibration` statement
at lines 5830-5842 (`E:d1-first-calibration`, lines 5834-5838), proof at lines
5844-5864.  Standing assumptions of the subsection: lines 5552-5563 (`H:homog`,
`d ∈ {1,2,3}`, `0 < α ≤ 1`, `μ` the spectral measure, `V = μ{|ξ| ≤ 1}`); the
parameters `b = 2-α`, `q = 3-α`, `β = 4-α-α₀`, `Z`, `K_sp` of `E:d1-constants`
(lines 5324-5332) and `0 < α₀ < 1` (line 5315).

How the TeX's objects map to the model (`DiagramModel`, a registered model
choice):
* `A_k(t)` is `DiagramModel.coeffALim d Γ α₀ k t`, the sum over splits and
  pairings of the diagram limits as the noise width `ε ↓ 0`; at a fixed width it
  is `coeffA (waveGreen d) (covEps Γ ε) α₀ k t` (the TeX's "regularized moments",
  line 5779).  Through `MixedMoment.coeffA_eq` it is the TeX's definition
  `Σ_{m=0}^{2k} E[X_m X_{2k-m}]`;
* the Green kernels are the model's unsmoothed wave Green measures
  `waveGreen d h` in every dimension (the `d = 3` sphere measure being the
  recorded `toSphere` choice); the TeX's auxiliary Green smoothing `G_{h,η}`,
  `η > 0`, in `d = 3` and its limit `η ↓ 0` (lines 5746-5747, 5785-5802) are
  therefore not needed: the convolution lemmas are applied at `η = 0`, where
  `G_{h,0} = G_h` (`LowAlphaConvolution.smoothedGreen_zero`);
* `K_sp^gen` is `Kgen α V` with `V = (specV μ).toReal`; `C_dir^gen` is
  `C2 α α₀ K`, `κ` is `kappa α α₀`, `C_{1,*}` is `C1 α α₀ K`, `Z` is
  `TwoSimplexTime.Zc α₀`.

Formalized (all proved):
* the spatial step in `d = 1, 2, 3` (lines 5747-5769): `closing_le` (the
  convolution bounds `L:low-alpha-convolution`, `L:alpha-one-convolution`
  turned into the lower-integral closing bound of `D1Spatial.spatialPair_le`,
  using the evenness of `Γ`), `spatial_le_closing` (the descending-label
  integration, by `D1Spatial.spatialPair_le`), the weighted and ordinary
  arithmetic-geometric means (`D1Spatial.amgm_riesz`, `amgm_white`), giving
  `spatialMax_gen`: the model's spatial part is at most
  `(K_sp^gen)^k T^{bk}/k^{bk}` whenever `Σ h_l ≤ 2T`, uniformly in the noise
  width (predicate `SpatialMax`);  `spatialMax_riesz`, `spatialMax_white`: the
  same in `d = 1` under `E:d1-covariances` from `D1Spatial` (`K_* = K_sp`);
* the temporal step (lines 5774-5779, by reference to the proof of
  `P:d1-upper`): `TwoSimplexTime.coeffA_le`, `TwoSimplexTime.oneChain_le`;
* the regularized coefficient bound `coeffA_eps_le` (first display of
  `E:low-alpha-coefficient` at every width `ε > 0`), its limit `coeffALim_le`,
  the factorial step `coeff_factorial_le` (second display), the moment display
  `secondMoment_le` (series argument, `TwoSimplexTime.sum_div_factorial_rpow_le`);
* the one-chain bound `oneChainLim_le`, the first-moment display `firstMoment_le`,
  the constants `C1_eq` (`C_{1,*} = C_{2,*}/2^{(4-α)/(3-α)}`), `two_C1_lt_C2`,
  and the conditional rate statement `lower_rate_le`.

Supplied inputs (named; both TRUE):
* `DiagramModel.MixedMoment d α₀ Γ P X u t` (`P:mixed`; existing; blocker D5 when this module
  was written, discharged in wave L19 for the source-field chaos terms by
  `SourceFinal.mixed_terms_l19`):
  used for the diagram limits (`A_k(t)` as a limit of the regularized
  coefficients, the TeX's limit paragraph lines 5785-5802 and `L:joint-fixed-order`)
  and for `E u² = Σ_k A_k(t)`;
* `FirstMomentSeries P X u` (new): `X_0 = 1`, `u` integrable and
  `E u = Σ_n E X_n` (main TeX lines 796 and 5856-5857, "the `L²` expansion
  permits taking expectations of partial sums").  TRUE for the solution and its
  chaos terms (`L²` convergence of the chaos series implies `L¹` convergence);
  not proved here (blocker D5 when this module was written); discharged in wave L19 for the
  chaos terms `srcX` and their series `srcU` on every source field by
  `SourceFinal.first_moment_series_l19`.

Wrappers with the manuscript's hypotheses: `low_alpha_upper_paper`,
`low_alpha_upper_moment_paper` (`P:low-alpha-upper`), `first_calibration_paper`,
`first_calibration_riesz_paper`, `first_calibration_white_paper`
(`C:d1-first-calibration`, the three cases of `K_*`).  Fields of `H:homog` used:
`dim`, `μ_radon`, `μ_tempered`, `Γ_tempered`, `spectral`, `scaling` (through the
convolution lemmas), `Γ_even` (orientation of the pair covariance),
`alpha_range` (for `0 < α` in the convolution lemma), `alpha0_lt_one`.  Carried, unused: `V > 0`
in `P:low-alpha-upper` (the bounds hold for `V ≥ 0`; `V > 0` is used only for
`2C_1 < C_2` in the corollary), `alpha0_pos`, `Γ_radon`, `Γ_posdef`, `μ_even`,
`threshold`; `t > 0` is used only as `t ≥ 0`.

Differences from the TeX (statements):
* `E:low-alpha-coefficient` is proved (i) for the regularized coefficients at
  every noise width, unconditionally, and (ii) for `A_k(t)` given the existence
  of the diagram limits (part of `MixedMoment`); the TeX proves the limits by
  `L:joint-fixed-order` and the `η`-limit paragraph, which are not formalized.
* The conditional clause of `C:d1-first-calibration` ("first-moment lower rate
  at least `L_*`") is formalized as: for every `L' < L_*`, eventually
  `E u(t) ≥ exp(L' t^κ)`.  The comparison with `P:Jensen` is commentary and not
  stated.

Category: narrower result for both labels.  Missing here: the solution `u` and
its chaos terms (blocker D5 when this module was written; moment displays rest on
`MixedMoment` and, for the first moment, `FirstMomentSeries`, split
modelled-object rule; both discharged in wave L19 for the chaos terms `srcX` and
their series `srcU` on every source field, `SourceFinal.mixed_terms_l19` and
`SourceFinal.first_moment_series_l19`); the
existence of the diagram limits for `A_k(t)` is part of `MixedMoment`.  Whole on
the model: the regularized coefficient bounds, the factorial step, the
calibration constants (`C1_eq`, `two_C1_lt_C2`) and the conditional rate
comparison.

Lemmas marked "Auxiliary" serve only the Lean route.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.TwoSimplexTime
public import StratonovichHAMSecondMoment.L9Completed
public import StratonovichHAMSecondMoment.L10Completed

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Filter Topology Set
open scoped ENNReal Nat

namespace StratonovichHAMSecondMoment.LowAlphaUpper

open HomogHypothesis (Rd HomogCovariance IsEven)
open WaveGreen (waveGreen waveGreen_mass)
open DiagramModel
open FiniteWick (pairings mem_pairings)
open D1Spatial (closers spatialPair spatialPair_le pairing_inv card_closers Ksp)
open LowAlphaConvolution (heatDens gammaEps specV heatDens_nonneg gammaEps_nonneg
  smoothedGreen_zero)
open TwoSimplexTime (Zc Zc_pos)

/-! ### Constants -/

/-- `K_sp^gen` of `E:low-alpha-constants` (main TeX lines 5715-5722):
`V 2^{2-α}(1-α)^{-α}/(2-α)^{2-α}` for `α < 1` (`D1Spatial.Ksp V α`), `πV` at
`α = 1`. -/
def Kgen (α V : ℝ) : ℝ := if α < 1 then Ksp V α else Real.pi * V

/-- `C_dir = q (2ZK)^{1/q}` with `q = 3 - α` (`C_dir^gen` of `E:low-alpha-constants`, line 5724;
`E:d1-upper`, line 5464). -/
def C2 (α α₀ K : ℝ) : ℝ := (3 - α) * (2 * Zc α₀ * K) ^ (1 / (3 - α))

/-- `C_{1,*} = q (ZK/2^{3-α})^{1/q}` (`E:d1-first-calibration`, line 5836). -/
def C1 (α α₀ K : ℝ) : ℝ := (3 - α) * (Zc α₀ * K / 2 ^ (3 - α)) ^ (1 / (3 - α))

/-- `κ = β/q = (4-α-α₀)/(3-α)` (line 5464). -/
def kappa (α α₀ : ℝ) : ℝ := (4 - α - α₀) / (3 - α)

/-- `K_sp^gen = K_sp(V)` for `α < 1`. -/
theorem Kgen_of_lt {α V : ℝ} (h : α < 1) : Kgen α V = Ksp V α := by simp [Kgen, h]

/-- `K_sp^gen = πV` at `α = 1`. -/
theorem Kgen_one (V : ℝ) : Kgen 1 V = Real.pi * V := by simp [Kgen]

/-- `K_sp^gen ≥ 0` for `V ≥ 0`. -/
theorem Kgen_nonneg {α V : ℝ} (hV : 0 ≤ V) : 0 ≤ Kgen α V := by
  unfold Kgen Ksp
  split_ifs with h
  · have h1 : 0 < 1 - α := by linarith
    have h2 : 0 < 2 - α := by linarith
    have := Real.rpow_pos_of_pos h1 (-α)
    have := Real.rpow_pos_of_pos h2 (2 - α)
    have := Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num) (2 - α)
    positivity
  · positivity

/-- `K_sp^gen > 0` for `V > 0`. -/
theorem Kgen_pos {α V : ℝ} (hV : 0 < V) : 0 < Kgen α V := by
  unfold Kgen Ksp
  split_ifs with h
  · have h1 : 0 < 1 - α := by linarith
    have h2 : 0 < 2 - α := by linarith
    have := Real.rpow_pos_of_pos h1 (-α)
    have := Real.rpow_pos_of_pos h2 (2 - α)
    have := Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num) (2 - α)
    positivity
  · positivity

/-! ### The closing convolution bound -/

/-- Auxiliary to the Lean proof route: `p_ε` is continuous. -/
theorem continuous_heatDens {d : ℕ} (ε : ℝ) : Continuous (heatDens (d := d) ε) := by
  unfold heatDens; fun_prop

/-- Auxiliary to the Lean proof route: the model's `covEps Γ ε` is
`ofReal (γ_ε)` when `p_ε(x - ·)` is `Γ`-integrable. -/
theorem covEps_eq_ofReal {d : ℕ} {Γ : Measure (Rd d)} {ε : ℝ} (hε : 0 ≤ ε)
    (hint : ∀ x, Integrable (fun y => heatDens ε (x - y)) Γ) (x : Rd d) :
    covEps Γ ε x = ENNReal.ofReal (gammaEps Γ ε x) := by
  unfold covEps gammaEps
  rw [ofReal_integral_eq_lintegral_ofReal (hint x)
    (Eventually.of_forall fun y => heatDens_nonneg hε _)]

/-- `γ_ε` is even when `Γ` is (`H:homog`, field `Γ_even`). -/
theorem gammaEps_neg {d : ℕ} {Γ : Measure (Rd d)} (hΓe : IsEven Γ) (ε : ℝ) (x : Rd d) :
    gammaEps Γ ε (-x) = gammaEps Γ ε x := by
  unfold gammaEps
  have hc : Continuous fun y : Rd d => heatDens ε (-x - y) :=
    (continuous_heatDens ε).comp (continuous_const.sub continuous_id)
  conv_lhs => rw [← hΓe]
  rw [integral_map (show AEMeasurable (fun y : Rd d => -y) Γ from
    (by fun_prop : Measurable fun y : Rd d => -y).aemeasurable) hc.aestronglyMeasurable]
  congr 1
  funext y
  rw [show -x - -y = -(x - y) by abel, D1Spatial.heatDens_neg]

/-- **The closing bound** (main TeX lines 5754-5757), in the form consumed by
`D1Spatial.spatialPair_le`: a bound `∫ G_h(dy) γ_ε(y + z) ≤ c` for every shift
(the form of `L:low-alpha-convolution` and `L:alpha-one-convolution` at `η = 0`)
gives `∫ γ_ε(z - v) G_h(dv) ≤ c` in lower integrals for every `z`. -/
theorem closing_le {d : ℕ} {Γ : Measure (Rd d)} (hΓe : IsEven Γ) {ε : ℝ} (hε : 0 < ε)
    (hint : ∀ x, Integrable (fun y => heatDens ε (x - y)) Γ) {h c : ℝ}
    (hI : ∀ z, Integrable (fun y => gammaEps Γ ε (y + z)) (waveGreen d h))
    (hB : ∀ z, ∫ y, gammaEps Γ ε (y + z) ∂(waveGreen d h) ≤ c) (z : Rd d) :
    ∫⁻ v, covEps Γ ε (z - v) ∂(waveGreen d h) ≤ ENNReal.ofReal c := by
  have e : ∀ v, covEps Γ ε (z - v) = ENNReal.ofReal (gammaEps Γ ε (v + -z)) := by
    intro v
    rw [covEps_eq_ofReal hε.le hint, show z - v = -(v + -z) by abel, gammaEps_neg hΓe]
  simp_rw [e]
  rw [← ofReal_integral_eq_lintegral_ofReal (hI (-z))
    (Eventually.of_forall fun y => gammaEps_nonneg Γ hε.le _)]
  exact ENNReal.ofReal_le_ofReal (hB (-z))

/-- **The descending-label integration in `d = 1, 2, 3`** (main TeX lines
5747-5758, by `D1Spatial.spatialPair_le`): if every closing increment of length
`h` has the closing bound `c(h)`, the model's spatial part is at most
`∏_{C_D} c(h_l) ∏_{O_D} h_i` (each opening gives the mass `h_i`). -/
theorem spatial_le_closing {d : ℕ} (hd : d = 1 ∨ d = 2 ∨ d = 3) {Γ : Measure (Rd d)}
    {ε : ℝ} (hγm : Measurable (covEps Γ ε)) (c : ℝ → ℝ)
    (hc : ∀ h : ℝ, 0 < h → ∀ z, ∫⁻ v, covEps Γ ε (z - v) ∂(waveGreen d h) ≤ ENNReal.ofReal (c h))
    (m : ℕ) {N : ℕ} {D : Fin N → Fin N} (hD : D ∈ pairings (Finset.univ : Finset (Fin N)))
    {h : Fin N → ℝ} (hh : ∀ i, 0 < h i) :
    spatial (waveGreen d) (covEps Γ ε) m D h ≤
      (∏ l ∈ closers D, ENNReal.ofReal (c (h l))) * ∏ i ∈ openers D, ENNReal.ofReal (h i) := by
  rw [← D1Spatial.spatialPair_const]
  refine (spatialPair_le (waveGreen d) (fun _ => covEps Γ ε) (fun _ => hγm) m D (pairing_inv hD)
    h (fun l => ENNReal.ofReal (c (h l))) (fun l _ z => hc _ (hh l) z)).trans (le_of_eq ?_)
  congr 1
  exact Finset.prod_congr rfl fun i _ => waveGreen_mass d hd _ (hh i).le

/-! ### The spatial maximum -/

/-- Auxiliary predicate (proved in each case below, never assumed): the model's
spatial part with noise width `ε > 0` is at most `K^k T^{bk}/k^{bk}` for every
`k ≥ 1`, split, pairing and positive increments with `Σ_l h_l ≤ 2T`
(`E:d1-spatial-max` and its general-`d` analogue, main TeX lines 5759-5769). -/
def SpatialMax (d : ℕ) (Γ : Measure (Rd d)) (K b : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ k : ℕ, 1 ≤ k → ∀ m n : ℕ, m + n = 2 * k → ∀ D ∈ Pi2 m n,
    ∀ h : Fin (m + n) → ℝ, (∀ i, 0 < h i) → ∀ T : ℝ, ∑ i, h i ≤ 2 * T →
      spatial (waveGreen d) (covEps Γ ε) m D h ≤
        ENNReal.ofReal (K ^ k * T ^ (b * k) / (k : ℝ) ^ (b * k))

/-- Auxiliary to the Lean proof route: measurability of `covEps Γ ε` under
`H:homog`. -/
theorem measurable_covEps {d : ℕ} {α α₀ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d α α₀ Γ μ) {ε : ℝ} (hε : 0 < ε) : Measurable (covEps Γ ε) := by
  have := hH.μ_radon
  have hcont := (LowAlphaConvolution.gammaEps_continuous_bounded hH.μ_tempered hH.spectral hε).1
  have e : covEps Γ ε = fun x => ENNReal.ofReal (gammaEps Γ ε x) :=
    funext (covEps_eq_ofReal hε.le (LowAlphaConvolution.integrable_heatDens hH.Γ_tempered hε))
  rw [e]
  exact ENNReal.measurable_ofReal.comp hcont.measurable

/-- **The spatial maximum for `0 < α < 1`, `d ∈ {1,2,3}`** (main TeX lines
5754-5764): with `M = V/(1-α)` and the weighted arithmetic-geometric mean,
`spatial ≤ (K_sp^gen)^k T^{(2-α)k}/k^{(2-α)k}`. -/
theorem spatialMax_low {d : ℕ} {α α₀ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d α α₀ Γ μ) (hα1 : α < 1) :
    SpatialMax d Γ (Kgen α (specV μ).toReal) (2 - α) := by
  obtain ⟨hα0, -, -, -, -, hconv⟩ := L9Completed.low_alpha_convolution_paper_completed hH hα1
  set V := (specV μ).toReal
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hb : 0 < 1 - α := by linarith
  intro ε hε k hk m n hmn D hD h hh T hsum
  have hint := LowAlphaConvolution.integrable_heatDens hH.Γ_tempered hε
  have hc : ∀ x : ℝ, 0 < x → ∀ z, ∫⁻ v, covEps Γ ε (z - v) ∂(waveGreen d x) ≤
      ENNReal.ofReal (V / (1 - α) * x ^ (1 - α)) := by
    intro x hx z
    refine closing_le hH.Γ_even hε hint (fun z => ?_) (fun z => ?_) z
    · have := (hconv x hx ε hε 0 le_rfl z).1
      rwa [smoothedGreen_zero] at this
    · have := (hconv x hx ε hε 0 le_rfl z).2.2
      rwa [smoothedGreen_zero] at this
  have hnn : ∀ j, 0 ≤ V / (1 - α) * h j ^ (1 - α) := fun j =>
    mul_nonneg (div_nonneg hV hb.le) (Real.rpow_nonneg (hh j).le _)
  refine (spatial_le_closing hH.dim (measurable_covEps hH hε) _ hc m hD hh).trans ?_
  rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => hnn i,
    ← ENNReal.ofReal_prod_of_nonneg fun i _ => (hh i).le,
    ← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => hnn i)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hT : 0 ≤ T := by
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => (hh i).le
    linarith
  rw [Finset.prod_mul_distrib, Finset.prod_const, card_closers hD hmn, Kgen_of_lt hα1,
    ← D1Spatial.riesz_constant_eq hα0 hα1 hk hT]
  calc (V / (1 - α)) ^ k * (∏ j ∈ closers D, h j ^ (1 - α)) * ∏ i ∈ openers D, h i
      = (V / (1 - α)) ^ k * ((∏ i ∈ openers D, h i) * ∏ j ∈ closers D, h j ^ (1 - α)) := by
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
        (D1Spatial.amgm_riesz hα0 hα1 hk hmn hD (fun i => (hh i).le) hsum)
        (pow_nonneg (div_nonneg hV hb.le) _)

/-- **The spatial maximum at `α = 1`, `d ∈ {1,2,3}`** (main TeX lines 5756-5758,
5765-5768): with the constant closing bound `M = πV/2` and the ordinary
arithmetic-geometric mean, `spatial ≤ (πV)^k T^k/k^k` (`b = 1`). -/
theorem spatialMax_one {d : ℕ} {α₀ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d 1 α₀ Γ μ) :
    SpatialMax d Γ (Kgen 1 (specV μ).toReal) (2 - 1) := by
  obtain ⟨-, hconv⟩ := L10Completed.alpha_one_convolution_paper_completed hH
  set V := (specV μ).toReal
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  intro ε hε k hk m n hmn D hD h hh T hsum
  have hint := LowAlphaConvolution.integrable_heatDens hH.Γ_tempered hε
  have hc : ∀ x : ℝ, 0 < x → ∀ z, ∫⁻ v, covEps Γ ε (z - v) ∂(waveGreen d x) ≤
      ENNReal.ofReal ((fun _ : ℝ => Real.pi * V / 2) x) := by
    intro x hx z
    refine closing_le hH.Γ_even hε hint (fun z => ?_) (fun z => ?_) z
    · have := (hconv x hx ε hε 0 le_rfl z).1
      rwa [smoothedGreen_zero] at this
    · have := (hconv x hx ε hε 0 le_rfl z).2.2.2.2.2
      rwa [smoothedGreen_zero] at this
  refine (spatial_le_closing hH.dim (measurable_covEps hH hε) _ hc m hD hh).trans ?_
  have hK : (0 : ℝ) < k := by exact_mod_cast hk
  rw [Finset.prod_const, card_closers hD hmn,
    ← ENNReal.ofReal_prod_of_nonneg fun i _ => (hh i).le,
    ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hcast : (2 - 1 : ℝ) * k = ((k : ℕ) : ℝ) := by ring
  rw [hcast, Real.rpow_natCast, Real.rpow_natCast, Kgen_one]
  calc (Real.pi * V / 2) ^ k * ∏ i ∈ openers D, h i
      ≤ (Real.pi * V / 2) ^ k * (2 * T / k) ^ k :=
        mul_le_mul_of_nonneg_left (D1Spatial.amgm_white hk hmn hD (fun i => (hh i).le) hsum)
          (by positivity)
    _ = (Real.pi * V) ^ k * T ^ k / (k : ℝ) ^ k := by
        rw [← mul_pow, ← mul_pow, ← div_pow]
        congr 1
        field_simp

/-- **The spatial maximum for `0 < α ≤ 1`** (both cases of
`E:low-alpha-constants`), `b = 2 - α`. -/
theorem spatialMax_gen {d : ℕ} {α α₀ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d α α₀ Γ μ) (hα1 : α ≤ 1) :
    SpatialMax d Γ (Kgen α (specV μ).toReal) (2 - α) := by
  rcases hα1.lt_or_eq with h | rfl
  · exact spatialMax_low hH h
  · exact spatialMax_one hH

/-- The spatial maximum in `d = 1` for the Riesz case of `E:d1-covariances`
(`K_* = K_sp`), from `D1Spatial.spatial_riesz_le`. -/
theorem spatialMax_riesz {c α : ℝ} (hc : 0 ≤ c) (hα0 : 0 < α) (hα1 : α < 1) :
    SpatialMax 1 (volume.withDensity (HigherRieszTwo.riesz c α)) (Ksp c α) (2 - α) :=
  fun _ hε _ hk _ _ hmn _ hD _ hh T hsum =>
    (D1Spatial.spatial_riesz_le hc hα0 hα1 hmn hD hε fun i => (hh i).le).2 hk T hsum

/-- The spatial maximum in `d = 1` for the white case of `E:d1-covariances`
(`K_* = K_sp = c_δ`, `b = 1`), from `D1Spatial.spatial_white_le`. -/
theorem spatialMax_white {c : ℝ} (hc : 0 ≤ c) :
    SpatialMax 1 (WhiteModel.whiteCov c) c (2 - 1) := by
  intro _ hε k hk _ _ hmn _ hD _ hh T hsum
  have hcast : (2 - 1 : ℝ) * k = ((k : ℕ) : ℝ) := by ring
  rw [hcast, Real.rpow_natCast, Real.rpow_natCast]
  exact (D1Spatial.spatial_white_le hc hmn hD hε fun i => (hh i).le).2 hk T hsum

/-! ### The coefficient bounds -/

/-- Auxiliary to the Lean proof route: `t^{(b+2-α₀)k} = t^{bk} (t^{2-α₀})^k`. -/
theorem rpow_split {t b α₀ : ℝ} (ht : 0 ≤ t) (hb : 0 ≤ b) (hα1 : α₀ < 1) (k : ℕ)
    (hk : 1 ≤ k) : t ^ ((b + 2 - α₀) * k) = t ^ (b * k) * (t ^ (2 - α₀)) ^ k := by
  have hK : (0 : ℝ) < k := by exact_mod_cast hk
  rw [← Real.rpow_natCast (t ^ (2 - α₀)), ← Real.rpow_mul ht, ← Real.rpow_add' ht]
  · congr 1; ring
  · have : 0 < (b + 2 - α₀) * k := by
      have : 0 < b + 2 - α₀ := by linarith
      positivity
    linarith

/-- **First display of `E:low-alpha-coefficient` for the regularized moments**
(main TeX lines 5774-5779; the multiplication of counts of `P:d1-upper`, lines
5518-5526): at every noise width `ε > 0`, for `k ≥ 1`, `t ≥ 0`,
`A_k^ε(t) ≤ (2ZK)^k t^{(b+2-α₀)k}/(k! k^{bk})`. -/
theorem coeffA_eps_le {d : ℕ} {Γ : Measure (Rd d)} {K b α₀ : ℝ} (hS : SpatialMax d Γ K b)
    (hK : 0 ≤ K) (hb : 0 ≤ b) (hα1 : α₀ < 1) {ε : ℝ} (hε : 0 < ε) {k : ℕ} (hk : 1 ≤ k)
    {t : ℝ} (ht : 0 ≤ t) :
    coeffA (waveGreen d) (covEps Γ ε) α₀ k t ≤
      ENNReal.ofReal ((2 * Zc α₀ * K) ^ k * t ^ ((b + 2 - α₀) * k) /
        ((k ! : ℝ) * (k : ℝ) ^ (b * k))) := by
  have hK' : (0 : ℝ) < k := by exact_mod_cast hk
  have hZ := (Zc_pos hα1).le
  refine (TwoSimplexTime.coeffA_le (waveGreen d) (covEps Γ ε) hα1 k ht
    (ENNReal.ofReal (K ^ k * t ^ (b * k) / (k : ℝ) ^ (b * k)))
    fun m n hmn D hD h hh hsum => hS ε hε k hk m n hmn D hD h hh t hsum).trans (le_of_eq ?_)
  have h1 : 0 ≤ K ^ k * t ^ (b * k) / (k : ℝ) ^ (b * k) := by
    have := Real.rpow_nonneg ht (b * k); positivity
  rw [← ENNReal.ofReal_mul h1, rpow_split ht hb hα1 k hk]
  congr 1
  have h3 : (0 : ℝ) < (k : ℝ) ^ (b * k) := Real.rpow_pos_of_pos hK' _
  have h4 : (0 : ℝ) < (k ! : ℝ) := by positivity
  field_simp
  ring

/-- **First display of `E:low-alpha-coefficient` for `A_k(t)`** (main TeX lines
5727-5729, 5803): given the diagram limits (part 1 of `MixedMoment`), the bound
of `coeffA_eps_le` passes to `coeffALim`. -/
theorem coeffALim_le {d : ℕ} {Γ : Measure (Rd d)} {K b α₀ : ℝ} (hS : SpatialMax d Γ K b)
    (hK : 0 ≤ K) (hb : 0 ≤ b) (hα1 : α₀ < 1) {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht : 0 ≤ t)
    (hlim : ∀ (m n : ℕ) (D : Fin (m + n) → Fin (m + n)), D ∈ Pi2 m n →
      Tendsto (fun ε => diagram (waveGreen d) (covEps Γ ε) α₀ m n D t) (𝓝[>] 0)
        (𝓝 (diagramLim d Γ α₀ m n D t))) :
    coeffALim d Γ α₀ k t ≤
      ENNReal.ofReal ((2 * Zc α₀ * K) ^ k * t ^ ((b + 2 - α₀) * k) /
        ((k ! : ℝ) * (k : ℝ) ^ (b * k))) := by
  have hT : Tendsto (fun ε => coeffA (waveGreen d) (covEps Γ ε) α₀ k t) (𝓝[>] 0)
      (𝓝 (coeffALim d Γ α₀ k t)) := by
    unfold coeffA coeffALim
    exact tendsto_finsetSum _ fun m _ => tendsto_finsetSum _ fun D hD => hlim m _ D hD
  exact le_of_tendsto hT (eventually_nhdsWithin_of_forall fun ε hε =>
    coeffA_eps_le hS hK hb hα1 hε hk ht)

/-- **Second display of `E:low-alpha-coefficient`** (main TeX lines 5537-5538,
5729-5730): `k! ≤ k^k` and `b ≥ 0` give `k! k^{bk} ≥ (k!)^{b+1}`, so
`x/(k! k^{bk}) ≤ x/(k!)^{b+1}` for `x ≥ 0`. -/
theorem coeff_factorial_le {x b : ℝ} (hx : 0 ≤ x) (hb : 0 ≤ b) (k : ℕ) :
    x / ((k ! : ℝ) * (k : ℝ) ^ (b * k)) ≤ x / (k ! : ℝ) ^ (b + 1) := by
  have hf : (0 : ℝ) < (k ! : ℝ) := by positivity
  have hle : (k ! : ℝ) ^ b ≤ (k : ℝ) ^ (b * k) := by
    have h1 : (k ! : ℝ) ≤ (k : ℝ) ^ k := by exact_mod_cast Nat.factorial_le_pow k
    calc (k ! : ℝ) ^ b ≤ ((k : ℝ) ^ k) ^ b := Real.rpow_le_rpow hf.le h1 hb
      _ = (k : ℝ) ^ (b * k) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), mul_comm]
  refine div_le_div_of_nonneg_left hx (Real.rpow_pos_of_pos hf _) ?_
  rw [Real.rpow_add hf, Real.rpow_one, mul_comm]
  exact mul_le_mul_of_nonneg_left hle hf.le

/-- **`E u² ≤ exp(C_dir t^κ)`** (`E:low-alpha-coefficient` third display, main TeX
lines 5731, 5803-5806; the series argument of lines 5540-5545), for a spatial
maximum with `b ≥ 0`, under the supplied input `MixedMoment`; here
`q = b + 1`, `β = b + 2 - α₀`. -/
theorem secondMoment_le {d : ℕ} {Γ : Measure (Rd d)} {K b α₀ : ℝ} (hS : SpatialMax d Γ K b)
    (hK : 0 ≤ K) (hb : 0 ≤ b) (hα1 : α₀ < 1) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℝ} {u : Ω → ℝ} {t : ℝ} (ht : 0 ≤ t) (hM : MixedMoment d α₀ Γ P X u t) :
    ∫ ω, u ω ^ 2 ∂P ≤
      Real.exp ((b + 1) * (2 * Zc α₀ * K) ^ (1 / (b + 1)) * t ^ ((b + 2 - α₀) / (b + 1))) := by
  have hZK : 0 ≤ 2 * Zc α₀ * K := by have := (Zc_pos hα1).le; positivity
  set z := 2 * Zc α₀ * K * t ^ (b + 2 - α₀)
  have hz : 0 ≤ z := mul_nonneg hZK (Real.rpow_nonneg ht _)
  have hak : ∀ k, (coeffALim d Γ α₀ k t).toReal ≤ z ^ k / (k ! : ℝ) ^ (b + 1) := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [coeffALim_zero]
    · have h1 := coeffALim_le hS hK hb hα1 hk ht fun m n D hD => (hM.1 m n D hD).1
      have h2 := ENNReal.toReal_le_of_le_ofReal (by
        have := Real.rpow_nonneg ht ((b + 2 - α₀) * k)
        have := Real.rpow_nonneg (Nat.cast_nonneg k) (b * k)
        positivity) h1
      refine h2.trans ((coeff_factorial_le (by
        have := Real.rpow_nonneg ht ((b + 2 - α₀) * k); positivity) hb k).trans
        (le_of_eq ?_))
      simp only [z]
      rw [mul_pow (2 * Zc α₀ * K) (t ^ (b + 2 - α₀)) k, ← Real.rpow_natCast (t ^ (b + 2 - α₀)),
        ← Real.rpow_mul ht]
  rw [hM.secondMoment_eq]
  refine Real.tsum_le_of_sum_range_le (fun k => ENNReal.toReal_nonneg) fun n =>
    (Finset.sum_le_sum fun k _ => hak k).trans ?_
  refine (TwoSimplexTime.sum_div_factorial_rpow_le (by linarith) hz n).trans (le_of_eq ?_)
  congr 1
  simp only [z]
  rw [Real.mul_rpow hZK (Real.rpow_nonneg ht _), ← Real.rpow_mul ht]
  ring_nf

/-! ### The first moment -/

/-- **Supplied input `FirstMomentSeries P X u`** (main TeX line 796, `X_0 = 1`;
lines 5856-5857, "the `L²` expansion permits taking expectations of partial
sums"): `X_0 = 1`, `u` is integrable and `E u = Σ_n E X_n`.  TRUE for the
solution `u(t,x)` and its chaos terms `X_n(t,x)` (`L²` convergence of the chaos
series implies convergence of the expectations); assumed here (blocker D5 when
this module was written).  Discharged in wave L19 for the chaos terms `srcX` and
their series `srcU` on every source field under `H:homog`, for `t > 0` and every `x`:
`SourceFinal.first_moment_series_l19`
(`SourceFinal.firstMomentSeries_m9_l19` at the constructed `m9`). -/
def FirstMomentSeries {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (u : Ω → ℝ) : Prop :=
  (∀ ω, X 0 ω = 1) ∧ Integrable u P ∧ HasSum (fun n => ∫ ω, X n ω ∂P) (∫ ω, u ω ∂P)

/-- **One chain at a fixed width** (proof of `C:d1-first-calibration`, main TeX
lines 5845-5853): `Σ_D J^ε_{2k,0,D}(t) ≤ (ZK/2^{b+1})^k t^{(b+2-α₀)k}/(k! k^{bk})`. -/
theorem oneChain_eps_le {d : ℕ} {Γ : Measure (Rd d)} {K b α₀ : ℝ} (hS : SpatialMax d Γ K b)
    (hK : 0 ≤ K) (hb : 0 ≤ b) (hα1 : α₀ < 1) {ε : ℝ} (hε : 0 < ε) {k : ℕ} (hk : 1 ≤ k)
    {t : ℝ} (ht : 0 ≤ t) :
    ∑ D ∈ Pi2 (2 * k) 0, diagram (waveGreen d) (covEps Γ ε) α₀ (2 * k) 0 D t ≤
      ENNReal.ofReal ((Zc α₀ * K / 2 ^ (b + 1)) ^ k * t ^ ((b + 2 - α₀) * k) /
        ((k ! : ℝ) * (k : ℝ) ^ (b * k))) := by
  have hK' : (0 : ℝ) < k := by exact_mod_cast hk
  have hZ := (Zc_pos hα1).le
  have ht2 : 0 ≤ t / 2 := by linarith
  refine (TwoSimplexTime.oneChain_le (waveGreen d) (covEps Γ ε) hα1 k ht
    (ENNReal.ofReal (K ^ k * (t / 2) ^ (b * k) / (k : ℝ) ^ (b * k)))
    fun D hD h hh hsum => hS ε hε k hk (2 * k) 0 (by omega) D hD h hh (t / 2)
      (by linarith)).trans (le_of_eq ?_)
  have h1 : 0 ≤ K ^ k * (t / 2) ^ (b * k) / (k : ℝ) ^ (b * k) := by
    have := Real.rpow_nonneg ht2 (b * k); positivity
  rw [← ENNReal.ofReal_mul h1, rpow_split ht hb hα1 k hk]
  congr 1
  have h3 : (0 : ℝ) < (k : ℝ) ^ (b * k) := Real.rpow_pos_of_pos hK' _
  have h4 : (0 : ℝ) < (k ! : ℝ) := by positivity
  have h5 : (0 : ℝ) < (2 : ℝ) ^ (b * k) := Real.rpow_pos_of_pos (by norm_num) _
  have e1 : (t / 2) ^ (b * k) = t ^ (b * k) / 2 ^ (b * k) := Real.div_rpow ht (by norm_num) _
  have e2 : ((2 : ℝ) ^ (b + 1)) ^ k = 2 ^ (b * k) * 2 ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast (2 : ℝ) k,
      ← Real.rpow_add (by norm_num)]
    congr 1; ring
  rw [e1, div_pow, e2]
  field_simp
  ring

/-- **The first-moment display** (`E:d1-first-calibration`, main TeX lines
5834-5838, proof 5845-5859): under `MixedMoment` and `FirstMomentSeries`, for a
spatial maximum with `b ≥ 0` and `q = b + 1`, `E X_{2k} ≤ (ZK/2^q)^k t^{βk}/(k!)^q`
for `k ≥ 1` and `E u ≤ exp(q (ZK/2^q)^{1/q} t^{β/q})`, `β = b + 2 - α₀`. -/
theorem firstMoment_le {d : ℕ} {Γ : Measure (Rd d)} {K b α₀ : ℝ} (hS : SpatialMax d Γ K b)
    (hK : 0 ≤ K) (hb : 0 ≤ b) (hα1 : α₀ < 1) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℝ} {u : Ω → ℝ} {t : ℝ} (ht : 0 ≤ t) (hM : MixedMoment d α₀ Γ P X u t)
    (hF : FirstMomentSeries P X u) :
    (∀ k : ℕ, 1 ≤ k → ∫ ω, X (2 * k) ω ∂P ≤
      (Zc α₀ * K / 2 ^ (b + 1)) ^ k * t ^ ((b + 2 - α₀) * k) /
        ((k ! : ℝ) * (k : ℝ) ^ (b * k))) ∧
    ∫ ω, u ω ∂P ≤ Real.exp ((b + 1) * (Zc α₀ * K / 2 ^ (b + 1)) ^ (1 / (b + 1)) *
      t ^ ((b + 2 - α₀) / (b + 1))) := by
  have hZK : 0 ≤ Zc α₀ * K / 2 ^ (b + 1) := by
    have := (Zc_pos hα1).le; have := Real.rpow_pos_of_pos (show (0:ℝ) < 2 by norm_num) (b + 1)
    positivity
  set w := Zc α₀ * K / 2 ^ (b + 1) * t ^ (b + 2 - α₀)
  have hw : 0 ≤ w := mul_nonneg hZK (Real.rpow_nonneg ht _)
  -- the expectation of `X n`
  have hEX : ∀ n, ∫ ω, X n ω ∂P = ∑ D ∈ Pi2 n 0, (diagramLim d Γ α₀ n 0 D t).toReal := by
    intro n
    rw [← (hM.2.1 n 0).2]
    simp [hF.1]
  have hEXnn : ∀ n, 0 ≤ ∫ ω, X n ω ∂P := fun n => by
    rw [hEX]; exact Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  -- the one-chain limit
  have hlimk : ∀ k, 1 ≤ k → ∫ ω, X (2 * k) ω ∂P ≤
      (Zc α₀ * K / 2 ^ (b + 1)) ^ k * t ^ ((b + 2 - α₀) * k) /
        ((k ! : ℝ) * (k : ℝ) ^ (b * k)) := by
    intro k hk
    have hT : Tendsto (fun ε => ∑ D ∈ Pi2 (2 * k) 0,
        diagram (waveGreen d) (covEps Γ ε) α₀ (2 * k) 0 D t) (𝓝[>] 0)
        (𝓝 (∑ D ∈ Pi2 (2 * k) 0, diagramLim d Γ α₀ (2 * k) 0 D t)) :=
      tendsto_finsetSum _ fun D hD => (hM.1 _ 0 D hD).1
    have h1 := le_of_tendsto hT (eventually_nhdsWithin_of_forall fun ε hε =>
      oneChain_eps_le hS hK hb hα1 hε hk ht)
    rw [hEX, ← ENNReal.toReal_sum fun D hD => (hM.1 _ 0 D hD).2]
    exact ENNReal.toReal_le_of_le_ofReal (by
      have := Real.rpow_nonneg ht ((b + 2 - α₀) * k)
      have := Real.rpow_nonneg (Nat.cast_nonneg k) (b * k)
      positivity) h1
  -- the bound on every term, in the series form `w^k/(k!)^q`
  let c : ℕ → ℝ := fun k => w ^ k / (k ! : ℝ) ^ (b + 1)
  have hc0 : ∀ k, 0 ≤ c k := fun k => by simp only [c]; positivity
  have hce : ∀ k, ∫ ω, X (2 * k) ω ∂P ≤ c k := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [hEX]; simp [c, Pi2_zero_zero, diagramLim_zero_zero]
    · refine (hlimk k hk).trans ((coeff_factorial_le (by
        have := Real.rpow_nonneg ht ((b + 2 - α₀) * k); positivity) hb k).trans
        (le_of_eq ?_))
      simp only [c, w]
      rw [mul_pow (Zc α₀ * K / 2 ^ (b + 1)) (t ^ (b + 2 - α₀)) k,
        ← Real.rpow_natCast (t ^ (b + 2 - α₀)), ← Real.rpow_mul ht]
  have hco : ∀ k, ∫ ω, X (2 * k + 1) ω ∂P = 0 := by
    intro k
    rw [hEX, Pi2_odd (by rw [Nat.add_zero]; exact odd_two_mul_add_one k), Finset.sum_empty]
  have hpair : ∀ N, ∑ n ∈ Finset.range (2 * N), ∫ ω, X n ω ∂P =
      ∑ k ∈ Finset.range N, (∫ ω, X (2 * k) ω ∂P + ∫ ω, X (2 * k + 1) ω ∂P) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ,
        Finset.sum_range_succ, ih, Finset.sum_range_succ]
      ring
  refine ⟨hlimk, ?_⟩
  rw [← hF.2.2.tsum_eq]
  refine Real.tsum_le_of_sum_range_le hEXnn fun N => ?_
  calc ∑ n ∈ Finset.range N, ∫ ω, X n ω ∂P
      ≤ ∑ n ∈ Finset.range (2 * N), ∫ ω, X n ω ∂P :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
          fun n _ _ => hEXnn n
    _ ≤ ∑ k ∈ Finset.range N, c k := by
        rw [hpair]
        exact Finset.sum_le_sum fun k _ => by rw [hco, add_zero]; exact hce k
    _ ≤ _ := by
        refine (TwoSimplexTime.sum_div_factorial_rpow_le (by linarith) hw N).trans
          (le_of_eq ?_)
        congr 1
        simp only [w]
        rw [Real.mul_rpow hZK (Real.rpow_nonneg ht _), ← Real.rpow_mul ht]
        ring_nf

/-! ### The calibration constants -/

/-- **`C_{1,*} = C_{2,*}/2^{(4-α)/(3-α)}`** (`E:d1-first-calibration`, main TeX
lines 5836-5837), for `α < 3` and `ZK ≥ 0`. -/
theorem C1_eq {α α₀ K : ℝ} (hα : α < 3) (hα1 : α₀ < 1) (hK : 0 ≤ K) :
    C1 α α₀ K = C2 α α₀ K / 2 ^ ((4 - α) / (3 - α)) := by
  have hq : 0 < 3 - α := by linarith
  have hZK : 0 ≤ 2 * Zc α₀ * K := by have := (Zc_pos hα1).le; positivity
  unfold C1 C2
  have e1 : Zc α₀ * K / 2 ^ (3 - α) = 2 * Zc α₀ * K / 2 ^ (4 - α) := by
    rw [show (4 : ℝ) - α = (3 - α) + 1 by ring, Real.rpow_add_one (by norm_num)]
    field_simp
  have e2 : ((2 : ℝ) ^ (4 - α)) ^ (1 / (3 - α)) = 2 ^ ((4 - α) / (3 - α)) := by
    rw [← Real.rpow_mul (by norm_num)]; congr 1; ring
  rw [e1, Real.div_rpow hZK (Real.rpow_nonneg (by norm_num) _), e2]
  ring

/-- **`2C_{1,*} < C_{2,*}`** (main TeX lines 5839, 5861-5863): for `α < 3` and
`K > 0`, since `(4-α)/(3-α) > 1`. -/
theorem two_C1_lt_C2 {α α₀ K : ℝ} (hα : α < 3) (hα1 : α₀ < 1) (hK : 0 < K) :
    2 * C1 α α₀ K < C2 α α₀ K := by
  have hq : 0 < 3 - α := by linarith
  have hC2 : 0 < C2 α α₀ K := by
    unfold C2
    have := Zc_pos hα1
    exact mul_pos hq (Real.rpow_pos_of_pos (by positivity) _)
  have he : 1 < (4 - α) / (3 - α) := by rw [lt_div_iff₀ hq]; linarith
  have h2 : (2 : ℝ) < 2 ^ ((4 - α) / (3 - α)) := by
    have := Real.rpow_lt_rpow_of_exponent_lt (show (1 : ℝ) < 2 by norm_num) he
    rwa [Real.rpow_one] at this
  rw [C1_eq hα hα1 hK.le, mul_div_assoc', div_lt_iff₀ (by linarith)]
  nlinarith

/-- **The conditional rate comparison** (main TeX lines 5839-5841, 5859-5860): if
`E u(t) ≤ exp(C_1 t^κ)` for every `t > 0` and the first-moment lower rate is at
least `L` (for every `L' < L`, eventually `E u(t) ≥ exp(L' t^κ)`), then
`L ≤ C_1`. -/
theorem lower_rate_le {κ C L : ℝ} (Eu : ℝ → ℝ) (hup : ∀ t : ℝ, 0 < t → Eu t ≤ Real.exp (C * t ^ κ))
    (hlow : ∀ L' < L, ∀ᶠ t in atTop, Real.exp (L' * t ^ κ) ≤ Eu t) : L ≤ C := by
  by_contra hcon
  push Not at hcon
  obtain ⟨t, h1, h2⟩ := ((hlow ((C + L) / 2) (by linarith)).and (eventually_gt_atTop 0)).exists
  have h3 := Real.exp_le_exp.1 (h1.trans (hup t h2))
  have h4 : 0 < t ^ κ := Real.rpow_pos_of_pos h2 _
  have : (C + L) / 2 ≤ C := le_of_mul_le_mul_right h3 h4
  linarith

/-! ### Wrappers with the manuscript's hypotheses -/

/-- **`P:low-alpha-upper`, coefficient displays at every noise width** (main TeX
lines 5711-5730, 5774-5779) under the manuscript's hypotheses: `H:homog`
(`HomogCovariance d α α₀ Γ μ`, `d ∈ {1,2,3}`), `α ≤ 1`, `V > 0`, `k ≥ 1`,
`t > 0`.  For every `ε > 0` the regularized `A_k` is at most
`(2ZK)^k t^{βk}/(k! k^{bk})`, and that is at most `(2ZK)^k t^{βk}/(k!)^q`
(`b = 2-α`, `q = 3-α`, `β = 4-α-α₀`, `K = K_sp^gen`).  Nothing supplied.
Carried, unused: `V > 0`; `t > 0` used as `t ≥ 0`. -/
theorem low_alpha_upper_paper {d : ℕ} {α α₀ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d α α₀ Γ μ) (hα1 : α ≤ 1) (_hV : 0 < (specV μ).toReal) {k : ℕ}
    (hk : 1 ≤ k) {t : ℝ} (ht : 0 < t) :
    (∀ ε : ℝ, 0 < ε → coeffA (waveGreen d) (covEps Γ ε) α₀ k t ≤
      ENNReal.ofReal ((2 * Zc α₀ * Kgen α (specV μ).toReal) ^ k * t ^ ((4 - α - α₀) * k) /
        ((k ! : ℝ) * (k : ℝ) ^ ((2 - α) * k)))) ∧
    (2 * Zc α₀ * Kgen α (specV μ).toReal) ^ k * t ^ ((4 - α - α₀) * k) /
        ((k ! : ℝ) * (k : ℝ) ^ ((2 - α) * k)) ≤
      (2 * Zc α₀ * Kgen α (specV μ).toReal) ^ k * t ^ ((4 - α - α₀) * k) /
        (k ! : ℝ) ^ (3 - α) := by
  have hK := Kgen_nonneg (α := α) (ENNReal.toReal_nonneg : 0 ≤ (specV μ).toReal)
  have hb : 0 ≤ 2 - α := by linarith
  have hα0 := hH.alpha0_lt_one
  have e : (4 - α - α₀) = (2 - α) + 2 - α₀ := by ring
  have e' : (3 - α) = (2 - α) + 1 := by ring
  refine ⟨fun ε hε => ?_, ?_⟩
  · rw [e]; exact coeffA_eps_le (spatialMax_gen hH hα1) hK hb hα0 hε hk ht.le
  · rw [e']
    have := (Zc_pos hα0).le
    exact coeff_factorial_le (by have := Real.rpow_nonneg ht.le ((4 - α - α₀) * k); positivity)
      hb k

/-- **`P:low-alpha-upper`, the displays for `A_k(t)` and `E u²`** (main TeX lines
5727-5732, 5803-5806) under the manuscript's hypotheses (`H:homog`, `α ≤ 1`,
`V > 0`, `t > 0`) and the supplied input `MixedMoment` at time `t` (`u`, `X_n`
unconstructed): for `k ≥ 1`, `A_k(t) = Σ_{m=0}^{2k} E[X_m X_{2k-m}] ≤
(2ZK)^k t^{βk}/(k! k^{bk})`, and `E u² ≤ exp(C_dir^gen t^κ)`.  Carried, unused:
`V > 0`; `t > 0` used as `t ≥ 0`. -/
theorem low_alpha_upper_moment_paper {d : ℕ} {α α₀ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d α α₀ Γ μ) (hα1 : α ≤ 1) (_hV : 0 < (specV μ).toReal)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ} {u : Ω → ℝ} {t : ℝ}
    (ht : 0 < t) (hM : MixedMoment d α₀ Γ P X u t) :
    (∀ k : ℕ, 1 ≤ k →
      ∑ m ∈ Finset.range (2 * k + 1), ∫ ω, X m ω * X (2 * k - m) ω ∂P ≤
        (2 * Zc α₀ * Kgen α (specV μ).toReal) ^ k * t ^ ((4 - α - α₀) * k) /
          ((k ! : ℝ) * (k : ℝ) ^ ((2 - α) * k))) ∧
    ∫ ω, u ω ^ 2 ∂P ≤ Real.exp (C2 α α₀ (Kgen α (specV μ).toReal) * t ^ kappa α α₀) := by
  have hK := Kgen_nonneg (α := α) (ENNReal.toReal_nonneg : 0 ≤ (specV μ).toReal)
  have hb : 0 ≤ 2 - α := by linarith
  have hα0 := hH.alpha0_lt_one
  have e : (4 - α - α₀) = (2 - α) + 2 - α₀ := by ring
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [← hM.coeffA_eq k, e]
    refine ENNReal.toReal_le_of_le_ofReal (by
      have := (Zc_pos hα0).le
      have := Real.rpow_nonneg ht.le (((2 - α) + 2 - α₀) * k)
      have := Real.rpow_nonneg (Nat.cast_nonneg k) ((2 - α) * k)
      positivity) ?_
    exact coeffALim_le (spatialMax_gen hH hα1) hK hb hα0 hk ht.le
      fun m n D hD => (hM.1 m n D hD).1
  · have h := secondMoment_le (spatialMax_gen hH hα1) hK hb hα0 ht.le hM
    refine h.trans (le_of_eq ?_)
    unfold C2 kappa
    congr 1
    rw [show (2 - α) + 1 = 3 - α by ring, show (2 - α) + 2 - α₀ = 4 - α - α₀ by ring]

/-- Auxiliary to the Lean proof route: the common form of
`C:d1-first-calibration` for any spatial maximum with `b = 2 - α`. -/
theorem first_calibration_of_spatialMax {d : ℕ} {α α₀ K : ℝ} {Γ : Measure (Rd d)}
    (hS : SpatialMax d Γ K (2 - α)) (hα1 : α ≤ 1) (hα0 : α₀ < 1) (hK : 0 < K)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ} {u : Ω → ℝ} {t : ℝ}
    (ht : 0 < t) (hM : MixedMoment d α₀ Γ P X u t) (hF : FirstMomentSeries P X u) :
    (∀ k : ℕ, 1 ≤ k → ∫ ω, X (2 * k) ω ∂P ≤
      (Zc α₀ * K / 2 ^ (3 - α)) ^ k * t ^ ((4 - α - α₀) * k) /
        ((k ! : ℝ) * (k : ℝ) ^ ((2 - α) * k)) ∧
      (Zc α₀ * K / 2 ^ (3 - α)) ^ k * t ^ ((4 - α - α₀) * k) /
          ((k ! : ℝ) * (k : ℝ) ^ ((2 - α) * k)) ≤
        (Zc α₀ * K / 2 ^ (3 - α)) ^ k * t ^ ((4 - α - α₀) * k) / (k ! : ℝ) ^ (3 - α)) ∧
    ∫ ω, u ω ∂P ≤ Real.exp (C1 α α₀ K * t ^ kappa α α₀) ∧
    C1 α α₀ K = C2 α α₀ K / 2 ^ ((4 - α) / (3 - α)) ∧
    2 * C1 α α₀ K < C2 α α₀ K := by
  have hb : 0 ≤ 2 - α := by linarith
  obtain ⟨h1, h2⟩ := firstMoment_le hS hK.le hb hα0 ht.le hM hF
  have e1 : (2 - α) + 1 = 3 - α := by ring
  have e2 : (2 - α) + 2 - α₀ = 4 - α - α₀ := by ring
  rw [e1, e2] at h1 h2
  refine ⟨fun k hk => ⟨h1 k hk, ?_⟩, h2.trans (le_of_eq ?_), C1_eq (by linarith) hα0 hK.le,
    two_C1_lt_C2 (by linarith) hα0 hK⟩
  · have := (Zc_pos hα0).le
    have := Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num) (3 - α)
    rw [show (3 : ℝ) - α = (2 - α) + 1 by ring]
    exact coeff_factorial_le (by
      have := Real.rpow_nonneg ht.le ((4 - α - α₀) * k); positivity) hb k
  · unfold C1 kappa; ring_nf

/-- **`C:d1-first-calibration`, `K_* = K_sp^gen`** (main TeX lines 5830-5864)
under the hypotheses of `P:low-alpha-upper` (`H:homog`, `α ≤ 1`, `V > 0`) and
`t > 0`, with the supplied inputs `MixedMoment` and `FirstMomentSeries` at time
`t`: for `k ≥ 1`, `E X_{2k} ≤ (ZK/2^{b+1})^k t^{βk}/(k! k^{bk}) ≤
(ZK/2^{3-α})^k t^{βk}/(k!)^q` (`b + 1 = 3 - α`); `E u ≤ exp(C_1 t^κ)`;
`C_1 = C_2/2^{(4-α)/(3-α)}` and `2C_1 < C_2`. -/
theorem first_calibration_paper {d : ℕ} {α α₀ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d α α₀ Γ μ) (hα1 : α ≤ 1) (hV : 0 < (specV μ).toReal)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ} {u : Ω → ℝ} {t : ℝ}
    (ht : 0 < t) (hM : MixedMoment d α₀ Γ P X u t) (hF : FirstMomentSeries P X u) :
    (∀ k : ℕ, 1 ≤ k → ∫ ω, X (2 * k) ω ∂P ≤
      (Zc α₀ * Kgen α (specV μ).toReal / 2 ^ (3 - α)) ^ k * t ^ ((4 - α - α₀) * k) /
        ((k ! : ℝ) * (k : ℝ) ^ ((2 - α) * k)) ∧
      (Zc α₀ * Kgen α (specV μ).toReal / 2 ^ (3 - α)) ^ k * t ^ ((4 - α - α₀) * k) /
          ((k ! : ℝ) * (k : ℝ) ^ ((2 - α) * k)) ≤
        (Zc α₀ * Kgen α (specV μ).toReal / 2 ^ (3 - α)) ^ k * t ^ ((4 - α - α₀) * k) /
          (k ! : ℝ) ^ (3 - α)) ∧
    ∫ ω, u ω ∂P ≤ Real.exp (C1 α α₀ (Kgen α (specV μ).toReal) * t ^ kappa α α₀) ∧
    C1 α α₀ (Kgen α (specV μ).toReal) =
      C2 α α₀ (Kgen α (specV μ).toReal) / 2 ^ ((4 - α) / (3 - α)) ∧
    2 * C1 α α₀ (Kgen α (specV μ).toReal) < C2 α α₀ (Kgen α (specV μ).toReal) :=
  first_calibration_of_spatialMax (spatialMax_gen hH hα1) hα1 hH.alpha0_lt_one
    (Kgen_pos hV) ht hM hF

/-- **`C:d1-first-calibration`, `K_* = K_sp`, Riesz case of `E:d1-covariances`**
(`d = 1`, `γ = c|y|^{-α}`, `0 < α < 1`, `c > 0`, `0 < α₀ < 1`, `t > 0`), with the
supplied inputs `MixedMoment` and `FirstMomentSeries`.  Conclusions as in
`first_calibration_paper` with `K = K_sp = Ksp c α`.  Carried, unused:
`0 < α₀`. -/
theorem first_calibration_riesz_paper {c α α₀ : ℝ} (hc : 0 < c) (hα0 : 0 < α) (hα1 : α < 1)
    (_hα₀0 : 0 < α₀) (hα₀1 : α₀ < 1) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℝ} {u : Ω → ℝ} {t : ℝ} (ht : 0 < t)
    (hM : MixedMoment 1 α₀ (volume.withDensity (HigherRieszTwo.riesz c α)) P X u t)
    (hF : FirstMomentSeries P X u) :
    (∀ k : ℕ, 1 ≤ k → ∫ ω, X (2 * k) ω ∂P ≤
      (Zc α₀ * Ksp c α / 2 ^ (3 - α)) ^ k * t ^ ((4 - α - α₀) * k) /
        ((k ! : ℝ) * (k : ℝ) ^ ((2 - α) * k)) ∧
      (Zc α₀ * Ksp c α / 2 ^ (3 - α)) ^ k * t ^ ((4 - α - α₀) * k) /
          ((k ! : ℝ) * (k : ℝ) ^ ((2 - α) * k)) ≤
        (Zc α₀ * Ksp c α / 2 ^ (3 - α)) ^ k * t ^ ((4 - α - α₀) * k) / (k ! : ℝ) ^ (3 - α)) ∧
    ∫ ω, u ω ∂P ≤ Real.exp (C1 α α₀ (Ksp c α) * t ^ kappa α α₀) ∧
    C1 α α₀ (Ksp c α) = C2 α α₀ (Ksp c α) / 2 ^ ((4 - α) / (3 - α)) ∧
    2 * C1 α α₀ (Ksp c α) < C2 α α₀ (Ksp c α) := by
  have hK : 0 < Ksp c α := by
    have := Kgen_pos (α := α) hc
    rwa [Kgen_of_lt hα1] at this
  exact first_calibration_of_spatialMax (spatialMax_riesz hc.le hα0 hα1) hα1.le hα₀1 hK ht hM hF

/-- **`C:d1-first-calibration`, `K_* = K_sp = c_δ`, white case of
`E:d1-covariances`** (`d = 1`, `γ = c_δ δ₀`, `α = 1`, `c_δ > 0`, `0 < α₀ < 1`,
`t > 0`), with the supplied inputs `MixedMoment` and `FirstMomentSeries`.
Conclusions as in `first_calibration_paper` with `α = 1`, `K = c_δ`.  Carried,
unused: `0 < α₀`. -/
theorem first_calibration_white_paper {c α₀ : ℝ} (hc : 0 < c) (_hα₀0 : 0 < α₀)
    (hα₀1 : α₀ < 1) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ}
    {u : Ω → ℝ} {t : ℝ} (ht : 0 < t) (hM : MixedMoment 1 α₀ (WhiteModel.whiteCov c) P X u t)
    (hF : FirstMomentSeries P X u) :
    (∀ k : ℕ, 1 ≤ k → ∫ ω, X (2 * k) ω ∂P ≤
      (Zc α₀ * c / 2 ^ (3 - 1 : ℝ)) ^ k * t ^ ((4 - 1 - α₀) * k) /
        ((k ! : ℝ) * (k : ℝ) ^ ((2 - 1 : ℝ) * k)) ∧
      (Zc α₀ * c / 2 ^ (3 - 1 : ℝ)) ^ k * t ^ ((4 - 1 - α₀) * k) /
          ((k ! : ℝ) * (k : ℝ) ^ ((2 - 1 : ℝ) * k)) ≤
        (Zc α₀ * c / 2 ^ (3 - 1 : ℝ)) ^ k * t ^ ((4 - 1 - α₀) * k) / (k ! : ℝ) ^ (3 - 1 : ℝ)) ∧
    ∫ ω, u ω ∂P ≤ Real.exp (C1 1 α₀ c * t ^ kappa 1 α₀) ∧
    C1 1 α₀ c = C2 1 α₀ c / 2 ^ ((4 - 1 : ℝ) / (3 - 1)) ∧
    2 * C1 1 α₀ c < C2 1 α₀ c :=
  first_calibration_of_spatialMax (spatialMax_white hc.le) le_rfl hα₀1 hc ht hM hF

end StratonovichHAMSecondMoment.LowAlphaUpper
