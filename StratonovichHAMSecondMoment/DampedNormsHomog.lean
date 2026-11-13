module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

The remaining parts of `L:damped-homogeneous-norms` (Homogeneous damped norms
and temporal tails) of the main TeX file
`notes/notes_stratonovich_ham_second_moment.tex` (revision a284420): the
definitions `E:damped-norm-definitions` (lines 782-792), the lemma (lines
803-848, tails `E:damped-tail-norms` at lines 822-825, multiplier comparison
`E:damped-multiplier-comparison` with its definitions at lines 826-847, display
at 836-841) and its proof (lines 849-919, the comparison at 894-917).  The finiteness part and
`N₂(θ)² ≥ 0` are already in `ClockCopyHomog`; this module adds the rest and
bundles everything into `damped_homogeneous_norms_paper`.

Formalized, under `H:homog` (`HomogHypothesis.HomogCovariance`, temporal
exponent `a = α₀`; no `Γ ≠ 0`, as in the TeX):
* scaling (lines 809-812): `N₁(θ) = θ^{α+α₀-2} N₁(1)` (`N1_scaling`, from the
  spectral homogeneity alone, any `a`) and `N₂(θ)² = θ^{-β} N₂(1)²`,
  `β = 4-α-α₀` (`N2sq_scaling`);
* `N₀(θ) = θ^{-2}` with its integrand integrable on `(0,∞)` (`N0_eq`), from the
  one supplied input `GreenMass G` (see below);
* the tails `E:damped-tail-norms`: `N₁^{(M)}(1) → 0` (`N1tail_tendsto`),
  `N₂^{(M)}(1)² → 0` and `N₂^{(M)}(1) → 0` (`N2tail_tendsto`); for each `M` the
  tail integrands are integrable and `N₂^{(M)}(1)² ≥ 0`, the "tail form ≥ 0"
  of lines 891-892 (`N2tail_props`); also `0 ≤ K_M ≤ |r|^{-a}` and `K_M(r) → 0` for
  `r ≠ 0` (`KS_nonneg`, `KS_le`, `KM_tendsto`, lines 888-889);
* the multiplier comparison `E:damped-multiplier-comparison` (lines 826-847,
  display 836-841), in the manuscript's own terms: a measurable multiplier
  `m : ℝ^d → [0,1]` (`g` here; `μ` is replaced by `g(ξ)μ(dξ)`, `smoothed`) and
  measurable Laplace domains `S ⊆ S' ⊆ (0,∞)` (`N1on`, `KS`, `N2onSq`; Lean
  allows any measurable `S ⊆ S'` in `ℝ` and integrates `λ` over `S ∩ (0,∞)`,
  which contains the TeX's case): for every `θ > 0`,
  `N_{1,m,S}(θ) ≤ N_{1,1,S'}(θ)` and `N_{2,m,S}(θ)² ≤ N_{2,1,S'}(θ)²`, with the
  integrands integrable (`N1on_smoothed_mono`, `N2onSq_smoothed_mono`);
  `S' = (0,∞)` gives the full norms (`N1on_univ`, `N2onSq_univ`), `S' = (M,∞)`
  and `θ = 1` the tails, as the TeX notes at line 914.  Not stated as Lean
  conclusions: the lower bounds `0 ≤ N_{1,m,S}(θ)` and `0 ≤ N_{2,m,S}(θ)²` of
  the display for a general `m` and `S` (for `m = 1` they are stated with the
  full domain, `N₂(θ)² ≥ 0`, and the tail domains, `N2tail_props`; in general
  `N_{2,m,S}(θ)² = ∫_S w_θ^{mμ} ≥ 0` follows from `N2onSq_eq` and
  `weight_nonneg` but is not a stated theorem); and the closing remarks that
  Gaussian spatial and Green smoothing give multipliers in this class and
  leave the `N₀` mass identity unchanged (this module defines no smoothed
  Green kernels; Green smoothing `p_η * G_s` multiplies `Ĝ_s(ξ)Ĝ_t(ξ)` by
  `e^{-η|ξ|²}`, a function of `ξ` with values in `(0,1]`).  As the lemma says,
  the scaling identities are asserted only for the original covariance.  The
  TeX applies the comparison at lines 1145-1155 (the Laplace domains `A_e`,
  Green smoothing) and 1664-1673 (the Gaussian multipliers "can be removed in
  the upper bounds").
The wrapper `damped_homogeneous_norms_paper` bundles these with the finiteness
part (`ClockCopyHomog.damped_norms_finite_paper`) and
`ClockCopyHomog.damped_N2_nonneg_paper`.

Supplied input (one, for `N₀` only): `GreenMass G`, the mass identity
`G_s(ℝ^d) = s` for `s > 0` that the proof uses at line 881 (imported in the
TeX from the source, Chen (2.5)).  The wave Green measures are not defined in
this module, so `N₀` is defined for an arbitrary family `G` of measures and
the input is exactly the identity the TeX uses, no stronger.  The other
conclusions do not use it.  The module `WaveGreen` defines the wave Green
measures and discharges the input (`WaveGreen.waveGreen_greenMass`, for
`d ∈ {1,2,3}`).

Conventions and junk values made explicit:
* `N1tail a M μ` and `K_M` integrate `λ` over `(M,∞) ∩ (0,∞)`; for `M ≥ 0`
  this is the TeX's `∫_M^∞`, and only `M → ∞` is asserted.
* `K_S(0)` is the integral of `λ^{a-1}` over `S ∩ (0,∞)`, which diverges for
  `S = (M,∞)`; Lean's value there is the junk value `0`.  It occurs only on the
  diagonal `s = t`, a `P2`-null set, so no statement depends on it
  (`integral_FKS_eq` holds at every `(s,t)` because both sides use the same
  totalized integral).
* `N₂^{(M)}(1)` is `Real.sqrt` of `N2tailSq`; `N2tailSq ≥ 0` is proved, so the
  square root is not a junk value.  `N₀` uses `(G s univ).toReal`, which equals
  `s` under `GreenMass` (no `∞` junk).
* Every integral the lemma asserts finite comes with an integrability
  conclusion.

Hypotheses of `H:homog` used: `alpha0_pos`, `alpha0_lt_one`, `threshold`,
`alpha_range` (for `α > 0`), `μ_radon`, and `μ_tempered`, `spectral`,
`scaling` through `MaskedSpectralGrowth.spectralHomogeneous_of_homog`;
the other fields (including `Γ_tempered`) are carried, unused.

Proof route (differs from the TeX, same statements):
* `N₂` scaling: instead of changing `(s,t,ξ)` in the spectral formula, both
  sides are written as `∫_0^∞ w_θ` (`ClockCopy.K_eq_integral_weight`) and the
  one-dimensional substitution `λ = θu` is combined with
  `w_θ(θu) = θ^{a+α-5} w_1(u)` (`weight_scaling`, auxiliary).  `N₁` scaling uses
  the same substitution and `R_Γ(q) = q^{α-2} R_Γ(1)`.
* Tails and truncation: instead of dominated convergence in `(s,t,ξ)`, the
  subordinated integrand of `DampedNorms` is restricted to `λ ∈ S` (`FKS`,
  auxiliary) and Fubini gives `N_S(θ)² = ∫_{S ∩ (0,∞)} w_θ` (`N2onSq_eq`);
  the tail limit is then the tail of the integrable `w_1`, and nonnegativity
  is `w_θ ≥ 0` (the TeX argues by positive definiteness of the tail kernel).
* Multiplier comparison: the same order as the TeX (lines 894-913): at each
  `λ` the time integral is taken first and is nonnegative for every `ξ`, then
  `N_{2,m,S}(θ)² = ∫_S w_θ^{mμ}` and `w_θ^{gμ}(λ) ≤ w_θ^{μ}(λ)`
  (`weight_smoothed_le`).  The TeX gets `B_θ(λ,ξ) ≥ 0` from positive
  definiteness of `e^{-λ|s-t|}`; here the time integral is evaluated in
  closed form, so `w_θ(λ)` is a `μ`-integral of an explicit nonnegative
  function of `ξ`.  For `N₁`, `R_{gμ} ≤ R_μ` (`resolvent_smoothed_le`), as
  at lines 912-913.
Lemmas marked "Auxiliary to the Lean proof route" have no manuscript label.
General lemmas state their hypotheses (s-finiteness, `∫(1+|ξ|²)⁻¹ dμ < ∞`,
`μ{0} = 0`, measurability of `g` and `S`) in their signatures and doc comments.
-/

public import Mathlib
public import StratonovichHAMSecondMoment.HomogHypothesis
public import StratonovichHAMSecondMoment.TimeFractional
public import StratonovichHAMSecondMoment.SpectralHomog
public import StratonovichHAMSecondMoment.WaveKernel
public import StratonovichHAMSecondMoment.DampedNorms
public import StratonovichHAMSecondMoment.ClockCopy
public import StratonovichHAMSecondMoment.ClockCopyHomog
public import StratonovichHAMSecondMoment.MaskedSpectralGrowth

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Real Filter
open scoped ENNReal NNReal Topology

namespace StratonovichHAMSecondMoment.DampedNormsHomog

open HomogHypothesis TimeFractional SpectralHomog WaveKernel DampedNorms ClockCopy
  MaskedSpectralGrowth

variable {d : ℕ}

/-! ### Definitions -/

/-- The supplied input for `N₀`: the mass identity `G_s(ℝ^d) = s` for `s > 0`
(proof of `L:damped-homogeneous-norms`, line 881), stated for a family `G` of
measures on `ℝ^d` standing for the wave Green measures, which are not defined
in this module; `WaveGreen` defines them and `WaveGreen.waveGreen_greenMass`
discharges this input for `d ∈ {1,2,3}`. -/
structure GreenMass (G : ℝ → Measure (Rd d)) : Prop where
  mass : ∀ s : ℝ, 0 < s → G s univ = ENNReal.ofReal s

/-- `N₀(θ) = ∫_0^∞ e^{-θs} G_s(ℝ^d) ds` (`E:damped-norm-definitions`, line 784),
for a family `G` of measures on `ℝ^d`. -/
def N0 (G : ℝ → Measure (Rd d)) (θ : ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), Real.exp (-(θ * s)) * (G s univ).toReal

/-- The first norm with the Laplace variable restricted to `S`:
`Γ(a)⁻¹ ∫_{S ∩ (0,∞)} λ^{a-1} R_Γ(θ+λ) dλ`. -/
def N1on (a θ : ℝ) (S : Set ℝ) (μ : Measure (Rd d)) : ℝ :=
  (Real.Gamma a)⁻¹ * ∫ l in S, l ^ (a - 1) * resolvent μ (θ + l) ∂L0

/-- `N₁^{(M)}(1)`, the first norm at `θ = 1` with `λ > M` (lines 819-821). -/
def N1tail (a M : ℝ) (μ : Measure (Rd d)) : ℝ := N1on a 1 (Ioi M) μ

/-- The temporal kernel with the Laplace variable restricted to `S`:
`K_S(r) = Γ(a)⁻¹ ∫_{S ∩ (0,∞)} e^{-λ|r|} λ^{a-1} dλ`.  At `r = 0` with
`S ∩ (0,∞)` of infinite `λ^{a-1} dλ`-mass the integral diverges and the Lean
value is the junk value `0`; this happens only on the diagonal `s = t`, a
`P2`-null set. -/
def KS (a : ℝ) (S : Set ℝ) (r : ℝ) : ℝ :=
  (Real.Gamma a)⁻¹ * ∫ l in S, subKernel a |r| l ∂L0

/-- `K_M(r) = Γ(a)⁻¹ ∫_M^∞ e^{-λ|r|} λ^{a-1} dλ` (lines 815-818), the
`λ`-integral taken over `(M,∞) ∩ (0,∞)`. -/
def KM (a M r : ℝ) : ℝ := KS a (Ioi M) r

/-- The outer integrand of the second norm with kernel `K_S`. -/
def N2onOuter (a θ : ℝ) (S : Set ℝ) (μ : Measure (Rd d)) (p : ℝ × ℝ) : ℝ :=
  Real.exp (-(θ * (p.1 + p.2))) * KS a S (p.1 - p.2) *
    ∫ ξ, waveHat p.1 ξ * waveHat p.2 ξ ∂μ

/-- The integrand on `(0,∞)² × ℝ^d` of the second norm with kernel `K_S`. -/
def N2onIntegrand (a θ : ℝ) (S : Set ℝ) (z : (ℝ × ℝ) × Rd d) : ℝ :=
  Real.exp (-(θ * (z.1.1 + z.1.2))) * KS a S (z.1.1 - z.1.2) *
    (waveHat z.1.1 z.2 * waveHat z.1.2 z.2)

/-- The squared second norm with `K_S(s-t)` in place of `|s-t|^{-a}`. -/
def N2onSq (a θ : ℝ) (S : Set ℝ) (μ : Measure (Rd d)) : ℝ :=
  ∫ p, N2onOuter a θ S μ p ∂P2

/-- `N₂^{(M)}(1)²`: the squared second norm at `θ = 1` with `K_M(s-t)` in place
of `|s-t|^{-a}` (lines 820-821). -/
def N2tailSq (a M : ℝ) (μ : Measure (Rd d)) : ℝ := N2onSq a 1 (Ioi M) μ

/-- `N₂^{(M)}(1) = (N₂^{(M)}(1)²)^{1/2}` (the printed form of `E:damped-tail-norms`). -/
def N2tail (a M : ℝ) (μ : Measure (Rd d)) : ℝ := Real.sqrt (N2tailSq a M μ)

/-- The spectral measure multiplied by `g`, `g(ξ) μ(dξ)`: the measure `mμ` of
`E:damped-multiplier-comparison` (TeX lines 826-829; that `g` is measurable
with values in `[0,1]` is imposed separately). -/
def smoothed (μ : Measure (Rd d)) (g : Rd d → ℝ≥0) : Measure (Rd d) :=
  μ.withDensity fun ξ => (g ξ : ℝ≥0∞)

/-- The subordinated integrand `FK` restricted to `λ ∈ S` (auxiliary to the Lean
proof route). -/
def FKS (a θ : ℝ) (S : Set ℝ) : ℝ × (Rd d × (ℝ × ℝ)) → ℝ :=
  (Prod.fst ⁻¹' S).indicator (FK a θ)

/-! ### Elementary facts -/

/-- Auxiliary to the Lean proof route. `α > 0` under `H:homog`. -/
theorem alpha_pos {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (h : HomogCovariance d alpha alpha0 Γ μ) : 0 < alpha := by
  rcases h.alpha_range with h1 | h1
  · exact h1.1
  · rw [h1.1, h1.2]; norm_num

/-- `0 ≤ K_S(r)` (line 888 for `S = (M,∞)`). -/
theorem KS_nonneg (a : ℝ) (S : Set ℝ) (r : ℝ) (ha : 0 < a) : 0 ≤ KS a S r := by
  have := Real.Gamma_pos_of_pos ha
  refine mul_nonneg (by positivity) (integral_nonneg_of_ae ?_)
  filter_upwards [ae_restrict_of_ae ae_L0_pos] with l hl
  exact subKernel_nonneg a |r| l hl.le

/-- `K_S(r) ≤ |r|^{-a}` for `r ≠ 0` (lines 888-889 for `S = (M,∞)`), with the
`λ`-integral integrable. -/
theorem KS_le (a : ℝ) (S : Set ℝ) (r : ℝ) (ha : 0 < a) (hr : r ≠ 0) :
    IntegrableOn (subKernel a |r|) S L0 ∧ KS a S r ≤ |r| ^ (-a) := by
  have hr' : 0 < |r| := abs_pos.2 hr
  have hI := subKernel_integrable a |r| ha hr'
  refine ⟨hI.integrableOn, ?_⟩
  rw [rpow_neg_eq_subordination a |r| ha hr', KS]
  have := Real.Gamma_pos_of_pos ha
  refine mul_le_mul_of_nonneg_left (setIntegral_le_integral hI ?_) (by positivity)
  filter_upwards [ae_L0_pos] with l hl
  exact subKernel_nonneg a |r| l hl.le

/-- `K_{(0,∞)}(r) = |r|^{-a}` for `r ≠ 0`. -/
theorem KS_univ (a r : ℝ) (ha : 0 < a) (hr : r ≠ 0) : KS a univ r = |r| ^ (-a) := by
  rw [rpow_neg_eq_subordination a |r| ha (abs_pos.2 hr), KS, Measure.restrict_univ]

/-- Auxiliary to the Lean proof route. Tails of an integrable function on `(0,∞)`
tend to `0`. -/
theorem tail_tendsto_zero {f : ℝ → ℝ} (hf : Integrable f L0) :
    Tendsto (fun M : ℝ => ∫ l in Ioi M, f l ∂L0) atTop (𝓝 0) := by
  have h := tendsto_setIntegral_of_antitone (μ := L0) (f := f) (s := fun M : ℝ => Ioi M)
    (fun _ => measurableSet_Ioi) (fun _ _ hMN => Ioi_subset_Ioi hMN) ⟨0, hf.integrableOn⟩
  have he : (⋂ M : ℝ, Ioi M) = ∅ := by
    ext x
    simp only [mem_iInter, mem_Ioi, mem_empty_iff_false, iff_false, not_forall, not_lt]
    exact ⟨x, le_rfl⟩
  rwa [he, Measure.restrict_empty, integral_zero_measure] at h

/-- `K_M(r) → 0` as `M → ∞` for `r ≠ 0` (line 889). -/
theorem KM_tendsto (a r : ℝ) (ha : 0 < a) (hr : r ≠ 0) :
    Tendsto (fun M => KM a M r) atTop (𝓝 0) := by
  have hI := subKernel_integrable a |r| ha (abs_pos.2 hr)
  simpa [KM, KS] using (tail_tendsto_zero hI).const_mul (Real.Gamma a)⁻¹

/-! ### Scaling and `N₀` -/

/-- Auxiliary to the Lean proof route. Scaling of the weight `w_θ` of
`ClockCopy`: `w_θ(θu) = θ^{a+α-5} w_1(u)` for `θ, u > 0`, given the spectral
homogeneity `μ(cA) = c^α μ(A)`. -/
theorem weight_scaling {μ : Measure (Rd d)} {alpha : ℝ} (hI : SpectralHomogeneous μ alpha)
    (a θ u : ℝ) (hθ : 0 < θ) (hu : 0 < u) :
    weight a θ μ (θ * u) = θ ^ (a + alpha - 5) * weight a 1 μ u := by
  unfold weight
  rw [show θ + θ * u = θ * (1 + u) by ring]
  rw [resolvent_homog hI θ hθ, resolvent_homog hI (θ * (1 + u)) (by positivity),
    resolvent_homog hI (1 + u) (by positivity), resolvent_homog hI 1 one_pos, Real.one_rpow,
    one_mul, Real.mul_rpow hθ.le (show (0 : ℝ) ≤ 1 + u by positivity),
    Real.mul_rpow hθ.le hu.le]
  have e : θ ^ (a + alpha - 5) = θ ^ (a - 2) * θ ^ (alpha - 2) * θ⁻¹ := by
    rw [← Real.rpow_add hθ, ← Real.rpow_neg_one, ← Real.rpow_add hθ]; ring_nf
  rw [e]
  field_simp

/-- `N₂(θ)² = θ^{-β} N₂(1)²` with `β = 4 - α - α₀`, for `θ > 0`, under
`H:homog` (lines 809-812; the change of variables of lines 881-885). -/
theorem N2sq_scaling {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (h : HomogCovariance d alpha alpha0 Γ μ) (θ : ℝ) (hθ : 0 < θ) :
    N2sq alpha0 θ μ = θ ^ (-(4 - alpha - alpha0)) * N2sq alpha0 1 μ := by
  have hI := spectralHomogeneous_of_homog h
  have := h.μ_radon
  have hR := integrable_inv_one_add_sq hI (by linarith [h.threshold, h.alpha0_pos])
  have h0 := measure_zero hI (alpha_pos h)
  rw [K_eq_integral_weight μ hR h0 alpha0 θ h.alpha0_pos h.alpha0_lt_one hθ,
    K_eq_integral_weight μ hR h0 alpha0 1 h.alpha0_pos h.alpha0_lt_one one_pos]
  have hc := integral_comp_mul_left_Ioi (weight alpha0 θ μ) 0 hθ
  rw [mul_zero, smul_eq_mul] at hc
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun u hu => weight_scaling hI alpha0 θ u hθ hu), integral_const_mul] at hc
  have e : θ ^ (-(4 - alpha - alpha0)) = θ * θ ^ (alpha0 + alpha - 5) := by
    rw [show -(4 - alpha - alpha0) = 1 + (alpha0 + alpha - 5) by ring,
      Real.rpow_add hθ, Real.rpow_one]
  rw [e, mul_assoc, hc]
  field_simp

/-- `N₁(θ) = θ^{α+a-2} N₁(1)` for `θ > 0`, given the spectral homogeneity
`μ(cA) = c^α μ(A)` (any `a`; lines 809-812 and 881-882 with `a = α₀`). -/
theorem N1_scaling {alpha : ℝ} {μ : Measure (Rd d)} (hI : SpectralHomogeneous μ alpha)
    (a θ : ℝ) (hθ : 0 < θ) :
    N1 a θ μ = θ ^ (alpha + a - 2) * N1 a 1 μ := by
  unfold N1
  have hc := integral_comp_mul_left_Ioi (fun l => l ^ (a - 1) * resolvent μ (θ + l)) 0 hθ
  rw [mul_zero, smul_eq_mul] at hc
  have hpt : ∀ u ∈ Ioi (0 : ℝ), (θ * u) ^ (a - 1) * resolvent μ (θ + θ * u) =
      θ ^ (alpha + a - 3) * (u ^ (a - 1) * resolvent μ (1 + u)) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    rw [show θ + θ * u = θ * (1 + u) by ring, resolvent_homog hI _ (by positivity),
      resolvent_homog hI (1 + u) (by positivity),
      Real.mul_rpow hθ.le (show (0 : ℝ) ≤ 1 + u by positivity), Real.mul_rpow hθ.le hu0.le]
    have e : θ ^ (alpha + a - 3) = θ ^ (a - 1) * θ ^ (alpha - 2) := by
      rw [← Real.rpow_add hθ]; ring_nf
    rw [e]; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul] at hc
  have e : θ ^ (alpha + a - 2) = θ * θ ^ (alpha + a - 3) := by
    rw [show alpha + a - 2 = 1 + (alpha + a - 3) by ring, Real.rpow_add hθ, Real.rpow_one]
  rw [e]
  have : ∫ l in Ioi (0 : ℝ), l ^ (a - 1) * resolvent μ (θ + l) =
      θ * θ ^ (alpha + a - 3) * ∫ u in Ioi (0 : ℝ), u ^ (a - 1) * resolvent μ (1 + u) := by
    rw [mul_assoc, hc]; field_simp
  rw [this]; simp only [add_comm (1 : ℝ)]; ring

/-- `N₀(θ) = θ^{-2}` for `θ > 0` (lines 809-810), given the supplied mass identity
`G_s(ℝ^d) = s` (line 881), with the integrand integrable on `(0,∞)`. -/
theorem N0_eq (G : ℝ → Measure (Rd d)) (hG : GreenMass G) (θ : ℝ) (hθ : 0 < θ) :
    IntegrableOn (fun s => Real.exp (-(θ * s)) * (G s univ).toReal) (Ioi 0) ∧
      N0 G θ = θ ^ (-(2 : ℝ)) := by
  have hpt : ∀ s ∈ Ioi (0 : ℝ), Real.exp (-(θ * s)) * (G s univ).toReal =
      s ^ (1 : ℝ) * Real.exp (-θ * s ^ (1 : ℝ)) := by
    intro s hs
    rw [hG.mass s hs, ENNReal.toReal_ofReal (le_of_lt hs), Real.rpow_one, neg_mul]
    ring
  have hI := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := θ) (by norm_num)
    one_pos hθ
  refine ⟨hI.congr_fun (fun s hs => (hpt s hs).symm) measurableSet_Ioi, ?_⟩
  have h2 := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := θ) two_pos hθ
  norm_num at h2
  rw [N0, setIntegral_congr_fun measurableSet_Ioi (g := fun t => t * Real.exp (-(θ * t)))
    (fun t ht => by rw [hpt t ht]; simp only [Real.rpow_one, neg_mul]), h2,
    Real.rpow_neg hθ.le, Real.rpow_two]

/-! ### The second norm with a restricted Laplace domain -/

/-- Auxiliary to the Lean proof route. -/
theorem FKS_integrable (μ : Measure (Rd d)) [SFinite μ]
    (hR : Integrable (fun ξ : Rd d => 1 / (1 + ‖ξ‖ ^ 2)) μ)
    (a θ : ℝ) (S : Set ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hθ : 0 < θ) (hS : MeasurableSet S) :
    Integrable (FKS (d := d) a θ S) (L0.prod (μ.prod P2)) :=
  (FK_integrable μ hR a θ ha0 ha1 hθ).indicator (measurable_fst hS)

/-- Auxiliary to the Lean proof route. -/
theorem FKS_apply (a θ : ℝ) (S : Set ℝ) (l : ℝ) (y : Rd d × (ℝ × ℝ)) :
    FKS a θ S (l, y) = S.indicator (fun l => FK a θ (l, y)) l := by
  unfold FKS
  by_cases h : l ∈ S <;> simp [h]

/-- Auxiliary to the Lean proof route. The `λ`-integral of the restricted
subordinated integrand is the integrand with kernel `K_S` (every `s, t`). -/
theorem integral_FKS_eq (a θ : ℝ) (S : Set ℝ) (hS : MeasurableSet S) (ξ : Rd d)
    (p : ℝ × ℝ) :
    ∫ l, FKS a θ S (l, (ξ, p)) ∂L0 = N2onIntegrand a θ S (p, ξ) := by
  have e : (fun l => FKS a θ S (l, (ξ, p))) = S.indicator (fun l => FK a θ (l, (ξ, p))) := by
    funext l
    exact FKS_apply a θ S l (ξ, p)
  rw [e, integral_indicator hS]
  have h2 : ∫ l in S, FK a θ (l, (ξ, p)) ∂L0 = ∫ l in S,
      (Real.exp (-(θ * (p.1 + p.2))) * (waveHat p.1 ξ * waveHat p.2 ξ) * (Real.Gamma a)⁻¹) *
        subKernel a |p.1 - p.2| l ∂L0 := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae ae_L0_pos] with l hl
    simp only [FK, twoTimeR, subKernel, abs_of_pos hl]
    rw [show -(θ * (p.1 + p.2)) - l * |p.1 - p.2| = -(θ * (p.1 + p.2)) + -(|p.1 - p.2| * l)
      by ring, Real.exp_add]
    ring
  rw [h2, integral_const_mul, N2onIntegrand, KS]
  ring

/-- Auxiliary to the Lean proof route. For `λ > 0`, the `(ξ, (s,t))`-integral
of the restricted subordinated integrand is `1_S(λ) w_θ(λ)`. -/
theorem inner_FKS_eq (μ : Measure (Rd d)) [SFinite μ]
    (hR : Integrable (fun ξ : Rd d => 1 / (1 + ‖ξ‖ ^ 2)) μ) (hμ0 : μ {0} = 0)
    (a θ : ℝ) (S : Set ℝ) (hθ : 0 < θ) (l : ℝ) (hl : 0 < l) :
    ∫ ξ, ∫ p, FKS a θ S (l, (ξ, p)) ∂P2 ∂μ = S.indicator (weight a θ μ) l := by
  by_cases hlS : l ∈ S
  · rw [Set.indicator_of_mem hlS]
    have hF : ∀ (ξ : Rd d) (p : ℝ × ℝ), FKS a θ S (l, (ξ, p)) = FK a θ (l, (ξ, p)) := fun ξ p => by
      rw [FKS_apply, Set.indicator_of_mem hlS]
    simp_rw [hF]
    have hξ0 : ∀ᵐ ξ ∂μ, ξ ≠ 0 := by
      have := measure_eq_zero_iff_ae_notMem.1 hμ0
      filter_upwards [this] with ξ hξ
      simpa using hξ
    rw [← xi_integral_K μ hR a θ l hθ hl]
    refine integral_congr_ae ?_
    filter_upwards [hξ0] with ξ hξ
    have e : (fun p : ℝ × ℝ => FK a θ (l, (ξ, p))) = fun p =>
        ((Real.Gamma a)⁻¹ * l ^ (a - 1)) *
          (twoTimeR θ l p * (waveHat p.1 ξ * waveHat p.2 ξ)) := by
      funext p
      simp only [FK, abs_of_pos hl]
      ring
    rw [e, integral_const_mul, (cross_transform θ l hθ hl.le ξ hξ).2]
  · rw [Set.indicator_of_notMem hlS]
    have hF : ∀ (ξ : Rd d) (p : ℝ × ℝ), FKS a θ S (l, (ξ, p)) = 0 := fun ξ p => by
      rw [FKS_apply, Set.indicator_of_notMem hlS]
    simp_rw [hF, integral_zero]

/-- The second norm with kernel `K_S` (`S` measurable), for a measure with
`∫(1+|ξ|²)⁻¹ dμ < ∞` and `μ{0} = 0`, `0 < a < 1`, `θ > 0`: its integrand is
absolutely integrable on `(0,∞)² × ℝ^d`, its outer integrand is integrable on
`(0,∞)²`, and `N_S(θ)² = ∫_{S ∩ (0,∞)} w_θ(λ) dλ`. -/
theorem N2onSq_eq (μ : Measure (Rd d)) [SFinite μ]
    (hR : Integrable (fun ξ : Rd d => 1 / (1 + ‖ξ‖ ^ 2)) μ) (hμ0 : μ {0} = 0)
    (a θ : ℝ) (S : Set ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hθ : 0 < θ) (hS : MeasurableSet S) :
    Integrable (N2onIntegrand (d := d) a θ S) (P2.prod μ) ∧
      Integrable (N2onOuter a θ S μ) P2 ∧
      N2onSq a θ S μ = ∫ l in S, weight a θ μ l ∂L0 := by
  have hF := FKS_integrable μ hR a θ S ha0 ha1 hθ hS
  have hI : Integrable (N2onIntegrand (d := d) a θ S) (P2.prod μ) := by
    have hG := hF.integral_prod_right
    have hae : (fun yz : Rd d × (ℝ × ℝ) => ∫ l, FKS a θ S (l, yz) ∂L0) =
        fun yz => N2onIntegrand a θ S (yz.2, yz.1) := by
      funext yz
      exact integral_FKS_eq a θ S hS yz.1 yz.2
    rw [hae] at hG
    exact hG.swap
  refine ⟨hI, ?_, ?_⟩
  · refine hI.integral_prod_left.congr (Eventually.of_forall fun p => ?_)
    simp only [N2onIntegrand, N2onOuter]
    rw [integral_const_mul]
  · have hswap := iterated_integral_swap (μX := L0) (μY := μ) (μZ := P2) (FKS a θ S) hF
    have hL : N2onSq a θ S μ = ∫ p, ∫ ξ, ∫ l, FKS a θ S (l, (ξ, p)) ∂L0 ∂μ ∂P2 := by
      unfold N2onSq
      refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      simp_rw [integral_FKS_eq a θ S hS, N2onIntegrand, N2onOuter]
      rw [integral_const_mul]
    rw [hL, hswap, ← integral_indicator hS]
    refine integral_congr_ae ?_
    filter_upwards [ae_L0_pos] with l hl
    exact inner_FKS_eq μ hR hμ0 a θ S hθ l hl

/-- With `S = (0,∞)` the restricted second norm is `N₂(θ)²` (any `a > 0`, any
`μ`). -/
theorem N2onSq_univ (a θ : ℝ) (μ : Measure (Rd d)) (ha : 0 < a) :
    N2onSq a θ univ μ = N2sq a θ μ := by
  unfold N2onSq N2sq N2onOuter
  refine integral_congr_ae ?_
  filter_upwards [ae_P2] with p hp
  rw [KS_univ a _ ha (sub_ne_zero.2 hp.2.2)]

/-- With `S = (0,∞)` the restricted first norm is `N₁(θ)`. -/
theorem N1on_univ (a θ : ℝ) (μ : Measure (Rd d)) : N1on a θ univ μ = N1 a θ μ := by
  rw [N1on, Measure.restrict_univ]
  rfl

/-! ### Smoothing and truncation -/

/-- Auxiliary to the Lean proof route. The smoothed measure of an s-finite
measure is s-finite. -/
instance smoothed_sFinite (μ : Measure (Rd d)) [SFinite μ] (g : Rd d → ℝ≥0) :
    SFinite (smoothed μ g) := by
  unfold smoothed; infer_instance

/-- Auxiliary to the Lean proof route. Multiplying a `μ`-integrable function by
a measurable `g` with `0 ≤ g ≤ 1` keeps it integrable. -/
theorem integrable_mul_of_le_one (μ : Measure (Rd d)) (g : Rd d → ℝ≥0) (hg : Measurable g)
    (hg1 : ∀ ξ, g ξ ≤ 1) {f : Rd d → ℝ} (hf : Integrable f μ) :
    Integrable (fun ξ => (g ξ : ℝ) * f ξ) μ := by
  refine hf.norm.mono' (hg.coe_nnreal_real.aestronglyMeasurable.mul hf.aestronglyMeasurable)
    (Eventually.of_forall fun ξ => ?_)
  simp only [norm_mul, Real.norm_eq_abs, NNReal.abs_eq]
  have h1 : (g ξ : ℝ) ≤ 1 := by exact_mod_cast hg1 ξ
  exact mul_le_of_le_one_left (abs_nonneg _) h1

/-- Auxiliary to the Lean proof route. The smoothed measure inherits
`∫(1+|ξ|²)⁻¹ < ∞`. -/
theorem smoothed_hR (μ : Measure (Rd d)) (g : Rd d → ℝ≥0) (hg : Measurable g)
    (hg1 : ∀ ξ, g ξ ≤ 1) (hR : Integrable (fun ξ : Rd d => 1 / (1 + ‖ξ‖ ^ 2)) μ) :
    Integrable (fun ξ : Rd d => 1 / (1 + ‖ξ‖ ^ 2)) (smoothed μ g) := by
  refine (integrable_withDensity_iff_integrable_smul hg).2 ?_
  simpa only [NNReal.smul_def, smul_eq_mul] using integrable_mul_of_le_one μ g hg hg1 hR

/-- Auxiliary to the Lean proof route. The smoothed measure inherits `μ{0} = 0`. -/
theorem smoothed_zero (μ : Measure (Rd d)) (g : Rd d → ℝ≥0) (hμ0 : μ {0} = 0) :
    smoothed μ g {0} = 0 :=
  withDensity_absolutelyContinuous μ _ hμ0

/-- `R_{gμ}(q) ≤ R_μ(q)` for `q ≠ 0`, `g` measurable with values in `[0,1]` and
`∫(1+|ξ|²)⁻¹ dμ < ∞`. -/
theorem resolvent_smoothed_le (μ : Measure (Rd d)) (g : Rd d → ℝ≥0) (hg : Measurable g)
    (hg1 : ∀ ξ, g ξ ≤ 1) (hR : Integrable (fun ξ : Rd d => 1 / (1 + ‖ξ‖ ^ 2)) μ) (q : ℝ)
    (hq : q ≠ 0) : resolvent (smoothed μ g) q ≤ resolvent μ q := by
  unfold SpectralHomog.resolvent smoothed
  rw [integral_withDensity_eq_integral_smul hg]
  refine integral_mono_of_nonneg (Eventually.of_forall fun ξ => by positivity)
    (resolvent_integrable hR q hq) (Eventually.of_forall fun ξ => ?_)
  simp only [NNReal.smul_def, smul_eq_mul]
  have h0 : 0 ≤ 1 / (q ^ 2 + ‖ξ‖ ^ 2) := by positivity
  exact mul_le_of_le_one_left h0 (by exact_mod_cast hg1 ξ)

/-- Per-`λ` comparison of the weights: `w_θ^{gμ}(λ) ≤ w_θ^μ(λ)` for `λ > 0`,
`θ > 0`, `a > 0`, `g` measurable with values in `[0,1]` and
`∫(1+|ξ|²)⁻¹ dμ < ∞`. -/
theorem weight_smoothed_le (μ : Measure (Rd d)) (g : Rd d → ℝ≥0) (hg : Measurable g)
    (hg1 : ∀ ξ, g ξ ≤ 1) (hR : Integrable (fun ξ : Rd d => 1 / (1 + ‖ξ‖ ^ 2)) μ)
    (a θ l : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hl : 0 < l) :
    weight a θ (smoothed μ g) l ≤ weight a θ μ l := by
  have h1 := resolvent_integrable hR θ hθ.ne'
  have h2 := resolvent_integrable hR (θ + l) (by linarith)
  have hd : resolvent (smoothed μ g) θ - resolvent (smoothed μ g) (θ + l) ≤
      resolvent μ θ - resolvent μ (θ + l) := by
    unfold SpectralHomog.resolvent smoothed
    rw [integral_withDensity_eq_integral_smul hg, integral_withDensity_eq_integral_smul hg]
    simp only [NNReal.smul_def, smul_eq_mul]
    rw [← integral_sub (integrable_mul_of_le_one μ g hg hg1 h1)
        (integrable_mul_of_le_one μ g hg hg1 h2), ← integral_sub h1 h2]
    refine integral_mono ((integrable_mul_of_le_one μ g hg hg1 h1).sub
      (integrable_mul_of_le_one μ g hg hg1 h2)) (h1.sub h2) fun ξ => ?_
    have hA : 0 < θ ^ 2 + ‖ξ‖ ^ 2 := by positivity
    have hle : 1 / ((θ + l) ^ 2 + ‖ξ‖ ^ 2) ≤ 1 / (θ ^ 2 + ‖ξ‖ ^ 2) :=
      one_div_le_one_div_of_le hA (by nlinarith)
    rw [← mul_sub]
    exact mul_le_of_le_one_left (by linarith) (by exact_mod_cast hg1 ξ)
  have := Real.Gamma_pos_of_pos ha
  have := Real.rpow_nonneg hl.le (a - 2)
  unfold weight
  exact mul_le_mul_of_nonneg_left hd (by positivity)

/-- The second comparison of `E:damped-multiplier-comparison` (TeX lines
836-841, proof 894-911), its upper bound: for `S ⊆ S'` measurable and `g`
measurable with values in `[0,1]`, `N_{2,g,S}(θ)²` (the second norm of `gμ`
with kernel `K_S`) is at most `N_{2,1,S'}(θ)²`; both outer integrands are
integrable.  Hypotheses:
`∫(1+|ξ|²)⁻¹ dμ < ∞`, `μ{0} = 0`, `0 < a < 1`, `θ > 0`. -/
theorem N2onSq_smoothed_mono (μ : Measure (Rd d)) [SFinite μ]
    (hR : Integrable (fun ξ : Rd d => 1 / (1 + ‖ξ‖ ^ 2)) μ) (hμ0 : μ {0} = 0)
    (a θ : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hθ : 0 < θ) (g : Rd d → ℝ≥0) (hg : Measurable g)
    (hg1 : ∀ ξ, g ξ ≤ 1) (S S' : Set ℝ) (hS : MeasurableSet S) (hS' : MeasurableSet S')
    (hSS : S ⊆ S') :
    Integrable (N2onOuter a θ S (smoothed μ g)) P2 ∧ Integrable (N2onOuter a θ S' μ) P2 ∧
      N2onSq a θ S (smoothed μ g) ≤ N2onSq a θ S' μ := by
  have hRg := smoothed_hR μ g hg hg1 hR
  have h0g := smoothed_zero μ g hμ0
  obtain ⟨-, hIg, hEg⟩ := N2onSq_eq (smoothed μ g) hRg h0g a θ S ha0 ha1 hθ hS
  obtain ⟨-, hI, hE⟩ := N2onSq_eq μ hR hμ0 a θ S' ha0 ha1 hθ hS'
  refine ⟨hIg, hI, ?_⟩
  rw [hEg, hE]
  have hwi := weight_integrable μ hR a θ ha0 ha1 hθ
  have hwgi := weight_integrable (smoothed μ g) hRg a θ ha0 ha1 hθ
  calc ∫ l in S, weight a θ (smoothed μ g) l ∂L0 ≤ ∫ l in S, weight a θ μ l ∂L0 := by
        refine integral_mono_ae hwgi.integrableOn hwi.integrableOn ?_
        filter_upwards [ae_restrict_of_ae ae_L0_pos] with l hl
        exact weight_smoothed_le μ g hg hg1 hR a θ l ha0 hθ hl
    _ ≤ ∫ l in S', weight a θ μ l ∂L0 := by
        refine setIntegral_mono_set hwi.integrableOn ?_ (Eventually.of_forall hSS)
        filter_upwards [ae_restrict_of_ae ae_L0_pos] with l hl
        exact weight_nonneg μ hR a θ l ha0 hθ hl

/-- The first comparison of `E:damped-multiplier-comparison` (TeX lines
836-841, proof 912-913), its upper bound: for `S ⊆ S'` and `g` measurable with
values in `[0,1]`, `N_{1,g,S}(θ) ≤ N_{1,1,S'}(θ)`, and the integrand for `gμ`
is integrable.  Hypotheses:
`∫(1+|ξ|²)⁻¹ dμ < ∞`, `a > 0`, `θ > 0`, and integrability on `(0,∞)` of the
integrand of `N₁(θ)` for `μ`. -/
theorem N1on_smoothed_mono (μ : Measure (Rd d)) [SFinite μ]
    (hR : Integrable (fun ξ : Rd d => 1 / (1 + ‖ξ‖ ^ 2)) μ) (a θ : ℝ) (ha0 : 0 < a)
    (hθ : 0 < θ) (hN : Integrable (fun l : ℝ => l ^ (a - 1) * resolvent μ (θ + l)) L0)
    (g : Rd d → ℝ≥0) (hg : Measurable g) (hg1 : ∀ ξ, g ξ ≤ 1) (S S' : Set ℝ)
    (hSS : S ⊆ S') :
    Integrable (fun l : ℝ => l ^ (a - 1) * resolvent (smoothed μ g) (θ + l)) L0 ∧
      N1on a θ S (smoothed μ g) ≤ N1on a θ S' μ := by
  have hpt : ∀ l : ℝ, 0 < l → 0 ≤ l ^ (a - 1) * resolvent (smoothed μ g) (θ + l) ∧
      l ^ (a - 1) * resolvent (smoothed μ g) (θ + l) ≤ l ^ (a - 1) * resolvent μ (θ + l) :=
    fun l hl => ⟨mul_nonneg (Real.rpow_nonneg hl.le _) (resolvent_nonneg _ _),
      mul_le_mul_of_nonneg_left (resolvent_smoothed_le μ g hg hg1 hR (θ + l) (by linarith))
        (Real.rpow_nonneg hl.le _)⟩
  have hmeas : Measurable fun l : ℝ => l ^ (a - 1) * resolvent (smoothed μ g) (θ + l) :=
    (by fun_prop : Measurable fun l : ℝ => l ^ (a - 1)).mul
      ((resolvent_measurable (smoothed μ g)).comp (by fun_prop))
  have hIg : Integrable (fun l : ℝ => l ^ (a - 1) * resolvent (smoothed μ g) (θ + l)) L0 := by
    refine hN.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_L0_pos] with l hl
    rw [Real.norm_of_nonneg (hpt l hl).1]
    exact (hpt l hl).2
  refine ⟨hIg, ?_⟩
  have := Real.Gamma_pos_of_pos ha0
  unfold N1on
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc ∫ l in S, l ^ (a - 1) * resolvent (smoothed μ g) (θ + l) ∂L0
      ≤ ∫ l in S, l ^ (a - 1) * resolvent μ (θ + l) ∂L0 := by
        refine integral_mono_ae hIg.integrableOn hN.integrableOn ?_
        filter_upwards [ae_restrict_of_ae ae_L0_pos] with l hl
        exact (hpt l hl).2
    _ ≤ ∫ l in S', l ^ (a - 1) * resolvent μ (θ + l) ∂L0 := by
        refine setIntegral_mono_set hN.integrableOn ?_ (Eventually.of_forall hSS)
        filter_upwards [ae_restrict_of_ae ae_L0_pos] with l hl
        exact mul_nonneg (Real.rpow_nonneg hl.le _) (resolvent_nonneg _ _)

/-! ### The temporal tails under `H:homog` -/

/-- Auxiliary to the Lean proof route. Under `H:homog`: `∫(1+|ξ|²)⁻¹ dμ < ∞`
and `μ{0} = 0`. -/
theorem homog_spectral_facts {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (h : HomogCovariance d alpha alpha0 Γ μ) :
    Integrable (fun ξ : Rd d => 1 / (1 + ‖ξ‖ ^ 2)) μ ∧ μ {0} = 0 := by
  have hI := spectralHomogeneous_of_homog h
  have := h.μ_radon
  exact ⟨integrable_inv_one_add_sq hI (by linarith [h.threshold, h.alpha0_pos]),
    measure_zero hI (alpha_pos h)⟩

/-- The second tail norm under `H:homog`, for every `M`: its integrand is
absolutely integrable on `(0,∞)² × ℝ^d`, its outer integrand is integrable on
`(0,∞)²`, `N₂^{(M)}(1)² = ∫_{(M,∞)∩(0,∞)} w_1(λ) dλ` and
`N₂^{(M)}(1)² ≥ 0` (lines 891-892). -/
theorem N2tail_props {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (h : HomogCovariance d alpha alpha0 Γ μ) (M : ℝ) :
    Integrable (N2onIntegrand (d := d) alpha0 1 (Ioi M)) (P2.prod μ) ∧
      Integrable (N2onOuter alpha0 1 (Ioi M) μ) P2 ∧
      N2tailSq alpha0 M μ = ∫ l in Ioi M, weight alpha0 1 μ l ∂L0 ∧
      0 ≤ N2tailSq alpha0 M μ := by
  obtain ⟨hR, h0⟩ := homog_spectral_facts h
  have := h.μ_radon
  obtain ⟨h1, h2, h3⟩ := N2onSq_eq μ hR h0 alpha0 1 (Ioi M) h.alpha0_pos h.alpha0_lt_one
    one_pos measurableSet_Ioi
  refine ⟨h1, h2, h3, ?_⟩
  rw [N2tailSq, h3]
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_restrict_of_ae ae_L0_pos] with l hl
  exact weight_nonneg μ hR alpha0 1 l h.alpha0_pos one_pos hl

/-- `N₁^{(M)}(1) → 0` as `M → ∞` under `H:homog` (first half of
`E:damped-tail-norms`). -/
theorem N1tail_tendsto {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (h : HomogCovariance d alpha alpha0 Γ μ) :
    Tendsto (fun M => N1tail alpha0 M μ) atTop (𝓝 0) := by
  have hI := (ClockCopyHomog.damped_norms_finite_paper h 1 one_pos).2.2
  simpa [N1tail, N1on] using (tail_tendsto_zero hI).const_mul (Real.Gamma alpha0)⁻¹

/-- `N₂^{(M)}(1)² → 0` and `N₂^{(M)}(1) → 0` as `M → ∞` under `H:homog` (second
half of `E:damped-tail-norms`). -/
theorem N2tail_tendsto {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (h : HomogCovariance d alpha alpha0 Γ μ) :
    Tendsto (fun M => N2tailSq alpha0 M μ) atTop (𝓝 0) ∧
      Tendsto (fun M => N2tail alpha0 M μ) atTop (𝓝 0) := by
  obtain ⟨hR, -⟩ := homog_spectral_facts h
  have := h.μ_radon
  have hw := tail_tendsto_zero
    (weight_integrable μ hR alpha0 1 h.alpha0_pos h.alpha0_lt_one one_pos)
  have hsq : Tendsto (fun M => N2tailSq alpha0 M μ) atTop (𝓝 0) :=
    hw.congr fun M => ((N2tail_props h M).2.2.1).symm
  refine ⟨hsq, ?_⟩
  simpa [N2tail] using hsq.sqrt

/-! ### `L:damped-homogeneous-norms` -/

/-- **`L:damped-homogeneous-norms`** (main TeX lines 803-848) under `H:homog`
(`HomogCovariance`, temporal exponent `a = α₀`; no `Γ ≠ 0`) and the supplied
mass identity `GreenMass G` for the `N₀` part only.  Conclusions:
1. for every `θ > 0`: the finiteness part (`ClockCopyHomog.damped_norms_finite_paper`),
   `N₂(θ)² ≥ 0`, the `N₀` integrand integrable on `(0,∞)` and
   `N₀(θ) = θ^{-2}`, `N₁(θ) = θ^{α+α₀-2} N₁(1)`, `N₂(θ)² = θ^{-β} N₂(1)²` with
   `β = 4-α-α₀`;
2. for every `M`: the tail integrands are integrable and `N₂^{(M)}(1)² ≥ 0`;
3. `E:damped-tail-norms`: `N₁^{(M)}(1) → 0`, `N₂^{(M)}(1)² → 0` and
   `N₂^{(M)}(1) → 0` as `M → ∞`;
4. the upper bounds of `E:damped-multiplier-comparison` (lines 826-847, with
   a measurable multiplier `g` on `μ` with values in `[0,1]` and measurable
   Laplace domains): for `θ > 0` and measurable `S ⊆ S'`,
   `N_{1,g,S}(θ) ≤ N_{1,1,S'}(θ)` and `N_{2,g,S}(θ)² ≤ N_{2,1,S'}(θ)²`, with
   the integrands integrable; `S' = (0,∞)` gives the full norms
   (`N1on_univ`, `N2onSq_univ`) and `S' = (M,∞)`, `θ = 1` the tail norms.  The
   display's lower bounds `0 ≤ N_{1,g,S}(θ)`, `0 ≤ N_{2,g,S}(θ)²` are not
   conclusions here for general `g`, `S` (see the module doc). -/
theorem damped_homogeneous_norms_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (h : HomogCovariance d alpha alpha0 Γ μ) (G : ℝ → Measure (Rd d)) (hG : GreenMass G) :
    (∀ θ : ℝ, 0 < θ →
      (Integrable (N2integrand (d := d) alpha0 θ) (P2.prod μ) ∧
        Integrable (fun p : ℝ × ℝ => Real.exp (-(θ * (p.1 + p.2))) * |p.1 - p.2| ^ (-alpha0) *
          ∫ ξ, waveHat p.1 ξ * waveHat p.2 ξ ∂μ) P2 ∧
        Integrable (fun l : ℝ => l ^ (alpha0 - 1) * resolvent μ (θ + l)) L0) ∧
      0 ≤ N2sq alpha0 θ μ ∧
      IntegrableOn (fun s => Real.exp (-(θ * s)) * (G s univ).toReal) (Ioi 0) ∧
      N0 G θ = θ ^ (-(2 : ℝ)) ∧
      N1 alpha0 θ μ = θ ^ (alpha + alpha0 - 2) * N1 alpha0 1 μ ∧
      N2sq alpha0 θ μ = θ ^ (-(4 - alpha - alpha0)) * N2sq alpha0 1 μ) ∧
    (∀ M : ℝ, Integrable (N2onIntegrand (d := d) alpha0 1 (Ioi M)) (P2.prod μ) ∧
      Integrable (N2onOuter alpha0 1 (Ioi M) μ) P2 ∧ 0 ≤ N2tailSq alpha0 M μ) ∧
    Tendsto (fun M => N1tail alpha0 M μ) atTop (𝓝 0) ∧
    Tendsto (fun M => N2tailSq alpha0 M μ) atTop (𝓝 0) ∧
    Tendsto (fun M => N2tail alpha0 M μ) atTop (𝓝 0) ∧
    (∀ θ : ℝ, 0 < θ → ∀ g : Rd d → ℝ≥0, Measurable g → (∀ ξ, g ξ ≤ 1) →
      ∀ S S' : Set ℝ, MeasurableSet S → MeasurableSet S' → S ⊆ S' →
        Integrable (fun l : ℝ => l ^ (alpha0 - 1) * resolvent (smoothed μ g) (θ + l)) L0 ∧
        N1on alpha0 θ S (smoothed μ g) ≤ N1on alpha0 θ S' μ ∧
        Integrable (N2onOuter alpha0 θ S (smoothed μ g)) P2 ∧
        Integrable (N2onOuter alpha0 θ S' μ) P2 ∧
        N2onSq alpha0 θ S (smoothed μ g) ≤ N2onSq alpha0 θ S' μ) := by
  obtain ⟨hR, h0⟩ := homog_spectral_facts h
  have := h.μ_radon
  have hI := spectralHomogeneous_of_homog h
  refine ⟨fun θ hθ => ⟨ClockCopyHomog.damped_norms_finite_paper h θ hθ,
    ClockCopyHomog.damped_N2_nonneg_paper h θ hθ, (N0_eq G hG θ hθ).1, (N0_eq G hG θ hθ).2,
    ?_, N2sq_scaling h θ hθ⟩, fun M => ⟨(N2tail_props h M).1, (N2tail_props h M).2.1,
    (N2tail_props h M).2.2.2⟩, N1tail_tendsto h, (N2tail_tendsto h).1, (N2tail_tendsto h).2,
    fun θ hθ g hg hg1 S S' hS hS' hSS => ?_⟩
  · rw [N1_scaling hI alpha0 θ hθ, add_comm alpha alpha0, add_comm alpha0 alpha]
  · obtain ⟨h1, h2⟩ := N1on_smoothed_mono μ hR alpha0 θ h.alpha0_pos hθ
      (ClockCopyHomog.damped_norms_finite_paper h θ hθ).2.2 g hg hg1 S S' hSS
    obtain ⟨h3, h4, h5⟩ := N2onSq_smoothed_mono μ hR h0 alpha0 θ h.alpha0_pos h.alpha0_lt_one
      hθ g hg hg1 S S' hS hS' hSS
    exact ⟨h1, h2, h3, h4, h5⟩


end StratonovichHAMSecondMoment.DampedNormsHomog
