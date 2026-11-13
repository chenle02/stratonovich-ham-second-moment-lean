module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

The parts of `L:damped-homogeneous-norms` (Homogeneous damped norms and
temporal tails) of the main TeX file
`notes/notes_stratonovich_ham_second_moment.tex` (revision a284420) that
`DampedNormsHomog` left out: the lower bounds of
`E:damped-multiplier-comparison` (display at main TeX lines 836-841, the class
of multipliers and Laplace domains at 826-834) and the smoothing assertions at
the end of the lemma (lines 845-847) and of its proof (lines 915-917).  Read
with the definitions `E:damped-norm-definitions` (lines 782-793) and
`Ĝ_s(ξ) = sin(s|ξ|)/|ξ|` (lines 777-778).  `DampedNormsHomog` and `WaveGreen`
are unchanged; the extended wrappers here are new declarations.

Formalized:
* the lower bounds `0 ≤ N_{1,m,S}(θ)` (`N1on_nonneg`, any measure, `a > 0`) and
  `0 ≤ N_{2,m,S}(θ)²` (`N2onSq_nonneg`, an s-finite measure with
  `∫(1+|ξ|²)⁻¹ dμ < ∞`, `μ{0} = 0`, `0 < a < 1`, `θ > 0`, `S` measurable), and
  the whole display with its integrability statements for a general measure
  (`damped_multiplier_comparison`, upper bounds from `DampedNormsHomog`);
* (i) the class `IsMultiplier` (measurable, values in `[0,1]`), closed under
  products (`IsMultiplier.mul`; multiplying `μ` by `g` and then by `h` is
  multiplying by `gh`, `smoothed_smoothed`), containing the Gaussian
  multipliers `e^{-η|ξ|²}` for `η ≥ 0` (`gaussMult`, `isMultiplier_gaussMult`);
* (ii) convolution with a probability measure preserves the mass identity
  `GreenMass` (`greenMass_conv`), so `N₀` is unchanged (`N0_conv`); instantiated
  with the Gaussian `gaussKernel v` and the wave Green measures
  (`gauss_waveGreen_mass`, `d ∈ {1,2,3}`);
* (iii) Green smoothing as a Fourier multiplier: for finite `G` the transform
  of `p * G` is `e^{-v|ξ|²/2} Ĝ` (`charFun_gaussKernel_conv`, from Mathlib's
  `charFun_conv` and `charFun_stdGaussian`), so `\widehat{p*G_s}
  \overline{\widehat{p*G_t}} = e^{-v|ξ|²} Ĝ_s \overline{Ĝ_t}`
  (`charFun_pair_gaussKernel_conv`); hence the second norm of `p * G`
  (`N2GreenSq`, the TeX's `N₂²` with `K_S` and `Ĝ_s` the characteristic
  function of `G_s`) equals the second norm of `G` with spectral measure
  `e^{-v|ξ|²}μ(dξ)` (`N2GreenSq_gauss`, any `d`, `G_s` finite for `s > 0`).
  Under the Fourier identity `GreenFourier G` (`Ĝ_s = waveHat s`) the second
  norm of `G` is `N2onSq` (`N2GreenSq_eq`) and that of `p * G` is
  `N_{2,m,S}(θ)²` with `m = e^{-v|ξ|²}` (`N2GreenSq_gauss_eq`); in `d = 1` the
  Fourier identity is proved (`greenFourier_one`, from
  `WaveGreen.waveGreen_fourier_one`).

Wrappers:
* `damped_homogeneous_norms_full_paper`: under `H:homog` (`HomogCovariance`,
  `a = α₀`, no `Γ ≠ 0`, as in the TeX) and `GreenMass G` (the supplied input of
  `DampedNormsHomog.damped_homogeneous_norms_paper`, TeX line 881), the
  conclusions of that wrapper with item 4 extended to the whole display
  `E:damped-multiplier-comparison`, plus (i), (ii) and the general form of
  (iii);
* `damped_homogeneous_norms_full_wave`: the same with `G := waveGreen d` and
  `H:homog` only;
* `damped_homogeneous_norms_fourier_paper`: under `H:homog` and
  `GreenFourier G`, the identification of the second norms of `G` and of the
  Gaussian-smoothed `p * G` with `N2onSq`, with integrability and
  `0 ≤ N_{2,m,S}(θ)² ≤ N_{2,1,S'}(θ)²` for `m = e^{-v|ξ|²}`;
* `damped_homogeneous_norms_fourier_one`: the same in `d = 1` with nothing
  supplied.

Named inputs (no new ones for the lemma's own conclusions):
* `GreenMass G` (TeX line 881) as in `DampedNormsHomog`; discharged for the wave
  Green measures by `WaveGreen.waveGreen_greenMass`.
* `GreenFourier G` (only for the identification with `N2onSq`): `G_s` finite and
  `charFun (G s) = waveHat s` for `s > 0`, i.e. that `Ĝ_s = sin(s|ξ|)/|ξ|` of TeX
  lines 777-778 is the Fourier transform of `G_s`, which the TeX uses when it
  pairs `G_θ(s,x)` with `G_θ(t,y)` (lines 794-797).  It is no stronger than
  that identity.  Proved in `d = 1` (`greenFourier_one`); in `d = 2, 3` it is
  not proved in the package (as in `WaveGreen`).

Narrower than the TeX, or not stated:
* "Spatial Gaussian smoothing ... give[s] multipliers in this class" (lines 845-846)
  is formalized as the membership of `e^{-η|ξ|²}` in the class; the spectral
  identity that the spectral measure of `p_ε * Γ` is `e^{-c ε|ξ|²}μ` is not
  stated (it needs Fubini against the locally finite, infinite `Γ`; Le's
  decision 2 for wave L8).
* The Gaussian `p_η` of the source (pp. 13-14) is represented by the centered
  Gaussian `gaussKernel v = N(0, vI)`, the image of Mathlib's `stdGaussian`
  under `x ↦ √v x`; every normalization `p_η = N(0, cηI)` is `gaussKernel (cη)`.
  The TeX does not fix `c` in this lemma.
* Commentary only (no Lean statement): "the scaling identities above are
  asserted for the original covariance only" (lines 843-844) and "It is used
  after time integration, not pointwise" (lines 911-912).

Conventions and junk values:
* `N2GreenSq` is a complex Bochner integral (the TeX's
  `∫ Ĝ_s \overline{Ĝ_t} dμ` is complex valued before integration in time); a
  non-integrable integrand would give the junk value `0`.  The equalities
  `N2GreenSq_gauss` and `N2GreenSq_eq` are between integrals whose integrands
  agree almost everywhere on `(0,∞)²` (`N2GreenOuter_gauss_ae`,
  `N2GreenOuter_ae_eq`), so they hold whether or not the integrands are
  integrable; the wrappers `..._fourier_paper` and `..._fourier_one` state
  the integrability of all four outer integrands.
* `gaussKernel v` with `v < 0` is the Dirac mass at `0` (`√v = 0`); every
  statement about it carries `0 ≤ v` where the value matters.
* `N₀` uses `(G s univ).toReal`, which is `s` under `GreenMass` (no `∞` junk).

Hypotheses of `H:homog` used: through the called lemmas
(`DampedNormsHomog.damped_homogeneous_norms_paper`, `homog_spectral_facts`,
`ClockCopyHomog.damped_norms_finite_paper`) the fields those use; directly,
`alpha0_pos`, `alpha0_lt_one`, `μ_radon` (s-finiteness of `μ`) and, in
`damped_homogeneous_norms_full_wave`, `dim`.  No other field is used directly.

Proof route.  The lower bounds follow the TeX ("nonnegative integrand" for
`N₁`, line 913; for `N₂` the representation `N_{2,m,S}(θ)² = ∫_S w_θ^{mμ}` of
`DampedNormsHomog.N2onSq_eq` with `w_θ ≥ 0`, where the TeX uses
`B_θ(λ,ξ) ≥ 0` by positive definiteness, lines 900-911).  The smoothing
assertions have no written TeX proof beyond lines 915-917; the Lean route is
Mathlib's convolution and characteristic-function calculus (`Measure.conv`,
`charFun_conv`, `charFun_map_smul`, `charFun_stdGaussian`).  Lemmas marked
"Auxiliary to the Lean proof route" have no manuscript label.
-/

public import Mathlib
public import StratonovichHAMSecondMoment.HomogHypothesis
public import StratonovichHAMSecondMoment.TimeFractional
public import StratonovichHAMSecondMoment.SpectralHomog
public import StratonovichHAMSecondMoment.WaveKernel
public import StratonovichHAMSecondMoment.DampedNorms
public import StratonovichHAMSecondMoment.ClockCopy
public import StratonovichHAMSecondMoment.DampedNormsHomog
public import StratonovichHAMSecondMoment.WaveGreen

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Real Filter ProbabilityTheory
open scoped ENNReal NNReal Topology ComplexConjugate

namespace StratonovichHAMSecondMoment.DampedMultiplier

open HomogHypothesis TimeFractional SpectralHomog WaveKernel DampedNorms ClockCopy
  DampedNormsHomog WaveGreen

variable {d : ℕ}

/-! ### Lower bounds of `E:damped-multiplier-comparison` -/

/-- The first lower bound of `E:damped-multiplier-comparison` (main TeX line
838, proof line 913), for any measure (in particular `mμ`): `0 ≤ N_{1,S}(θ)`
for every set `S` and `a > 0`, since the integrand `λ^{a-1} R(θ+λ)` is
nonnegative on `(0,∞)`. -/
theorem N1on_nonneg (a θ : ℝ) (S : Set ℝ) (μ : Measure (Rd d)) (ha : 0 < a) :
    0 ≤ N1on a θ S μ := by
  have := Real.Gamma_pos_of_pos ha
  unfold N1on
  refine mul_nonneg (by positivity) (integral_nonneg_of_ae ?_)
  filter_upwards [ae_restrict_of_ae ae_L0_pos] with l hl
  exact mul_nonneg (Real.rpow_nonneg hl.le _) (resolvent_nonneg _ _)

/-- The second lower bound of `E:damped-multiplier-comparison` (main TeX line
839, proof lines 900-911), for any s-finite measure (in particular `mμ`) with
`∫(1+|ξ|²)⁻¹ dμ < ∞` and `μ{0} = 0`, `0 < a < 1`, `θ > 0`, `S` measurable:
`0 ≤ N_{2,S}(θ)²`, since `N_{2,S}(θ)² = ∫_{S ∩ (0,∞)} w_θ` (`N2onSq_eq`) and
`w_θ ≥ 0`. -/
theorem N2onSq_nonneg (μ : Measure (Rd d)) [SFinite μ]
    (hR : Integrable (fun ξ : Rd d => 1 / (1 + ‖ξ‖ ^ 2)) μ) (hμ0 : μ {0} = 0)
    (a θ : ℝ) (S : Set ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hθ : 0 < θ) (hS : MeasurableSet S) :
    0 ≤ N2onSq a θ S μ := by
  rw [(N2onSq_eq μ hR hμ0 a θ S ha0 ha1 hθ hS).2.2]
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_restrict_of_ae ae_L0_pos] with l hl
  exact weight_nonneg μ hR a θ l ha0 hθ hl

/-- `E:damped-multiplier-comparison` (main TeX lines 836-841, proof 894-913)
in full, both lower and upper bounds, for a general measure: `μ` s-finite with
`∫(1+|ξ|²)⁻¹ dμ < ∞` and `μ{0} = 0`, `0 < a < 1`, `θ > 0`, the integrand of
`N₁(θ)` for `μ` integrable on `(0,∞)`, `g` measurable with values in `[0,1]`,
`S ⊆ S'` measurable.  Conclusions: the integrand of `N_{1,g,S}` is integrable,
`0 ≤ N_{1,g,S}(θ) ≤ N_{1,1,S'}(θ)`; the outer integrands of `N_{2,g,S}` and
`N_{2,1,S'}` are integrable and `0 ≤ N_{2,g,S}(θ)² ≤ N_{2,1,S'}(θ)²`. -/
theorem damped_multiplier_comparison (μ : Measure (Rd d)) [SFinite μ]
    (hR : Integrable (fun ξ : Rd d => 1 / (1 + ‖ξ‖ ^ 2)) μ) (hμ0 : μ {0} = 0)
    (a θ : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hθ : 0 < θ)
    (hN : Integrable (fun l : ℝ => l ^ (a - 1) * resolvent μ (θ + l)) L0)
    (g : Rd d → ℝ≥0) (hg : Measurable g) (hg1 : ∀ ξ, g ξ ≤ 1) (S S' : Set ℝ)
    (hS : MeasurableSet S) (hS' : MeasurableSet S') (hSS : S ⊆ S') :
    Integrable (fun l : ℝ => l ^ (a - 1) * resolvent (smoothed μ g) (θ + l)) L0 ∧
      0 ≤ N1on a θ S (smoothed μ g) ∧ N1on a θ S (smoothed μ g) ≤ N1on a θ S' μ ∧
      Integrable (N2onOuter a θ S (smoothed μ g)) P2 ∧ Integrable (N2onOuter a θ S' μ) P2 ∧
      0 ≤ N2onSq a θ S (smoothed μ g) ∧ N2onSq a θ S (smoothed μ g) ≤ N2onSq a θ S' μ := by
  obtain ⟨h1, h2⟩ := N1on_smoothed_mono μ hR a θ ha0 hθ hN g hg hg1 S S' hSS
  obtain ⟨h3, h4, h5⟩ := N2onSq_smoothed_mono μ hR hμ0 a θ ha0 ha1 hθ g hg hg1 S S' hS hS' hSS
  exact ⟨h1, N1on_nonneg a θ S _ ha0, h2, h3, h4,
    N2onSq_nonneg _ (smoothed_hR μ g hg hg1 hR) (smoothed_zero μ g hμ0) a θ S ha0 ha1 hθ hS,
    h5⟩

/-! ### (i) The multiplier class and Gaussian multipliers -/

/-- The multiplier class of `E:damped-multiplier-comparison` (TeX lines
826-829): `g : ℝ^d → ℝ≥0` measurable with values in `[0,1]`. -/
def IsMultiplier (g : Rd d → ℝ≥0) : Prop := Measurable g ∧ ∀ ξ, g ξ ≤ 1

/-- The class is closed under pointwise products (TeX lines 845-846 and
915-916: "products of multipliers in `[0,1]` depending only on `ξ`"). -/
theorem IsMultiplier.mul {g h : Rd d → ℝ≥0} (hg : IsMultiplier g) (hh : IsMultiplier h) :
    IsMultiplier (g * h) :=
  ⟨hg.1.mul hh.1, fun ξ => by
    simpa using mul_le_one' (hg.2 ξ) (hh.2 ξ)⟩

/-- Auxiliary to the Lean proof route (no manuscript step).  Multiplying the
spectral measure by `g` and then by `h` (both measurable) is multiplying it by
`g h`: `h(gμ) = (gh)μ`. -/
theorem smoothed_smoothed (μ : Measure (Rd d)) {g h : Rd d → ℝ≥0} (hg : Measurable g)
    (hh : Measurable h) : smoothed (smoothed μ g) h = smoothed μ (g * h) := by
  unfold smoothed
  rw [← withDensity_mul μ hg.coe_nnreal_ennreal hh.coe_nnreal_ennreal]
  congr 1

/-- The Gaussian multiplier `ξ ↦ e^{-η|ξ|²}`, as a function with values in
`ℝ≥0`. -/
def gaussMult (η : ℝ) (ξ : Rd d) : ℝ≥0 := ⟨Real.exp (-(η * ‖ξ‖ ^ 2)), (Real.exp_pos _).le⟩

/-- Auxiliary to the Lean proof route.  The real value of `gaussMult`. -/
theorem coe_gaussMult (η : ℝ) (ξ : Rd d) :
    (gaussMult η ξ : ℝ) = Real.exp (-(η * ‖ξ‖ ^ 2)) := rfl

/-- For `η ≥ 0` the Gaussian multiplier `e^{-η|ξ|²}` is in the class: it is
measurable with values in `[0,1]` (TeX lines 845-846, 915-916). -/
theorem isMultiplier_gaussMult (η : ℝ) (hη : 0 ≤ η) : IsMultiplier (gaussMult (d := d) η) := by
  refine ⟨Measurable.subtype_mk (by fun_prop), fun ξ => ?_⟩
  show Real.exp _ ≤ 1
  rw [Real.exp_le_one_iff]
  have := sq_nonneg ‖ξ‖
  nlinarith

/-! ### (ii) Gaussian smoothing of the Green kernel preserves the mass -/

/-- The centered Gaussian law on `ℝ^d` with covariance `v I` (`v ≥ 0`), the
image of Mathlib's standard Gaussian `stdGaussian` under `x ↦ √v x`.  It stands
for the heat kernel `p_η` of the TeX (lines 1674, 4698): `p_η = N(0, cη I)` for
the source's normalization constant `c > 0` is `gaussKernel (c η)`. -/
def gaussKernel (v : ℝ) : Measure (Rd d) :=
  (stdGaussian (Rd d)).map fun x => Real.sqrt v • x

/-- Auxiliary to the Lean proof route.  `gaussKernel v` is a probability
measure. -/
instance isProbabilityMeasure_gaussKernel (v : ℝ) :
    IsProbabilityMeasure (gaussKernel (d := d) v) := by
  unfold gaussKernel
  infer_instance

/-- Auxiliary to the Lean proof route.  Convolution with a probability measure
preserves total mass: `(ρ * ν)(ℝ^d) = ν(ℝ^d)` for `ν` s-finite. -/
theorem conv_univ (ρ : Measure (Rd d)) [IsProbabilityMeasure ρ] (ν : Measure (Rd d))
    [SFinite ν] : (ρ ∗ ν) univ = ν univ := by
  rw [Measure.conv, Measure.map_apply measurable_add MeasurableSet.univ, preimage_univ,
    ← univ_prod_univ, Measure.prod_prod, measure_univ, one_mul]

/-- Auxiliary to the Lean proof route.  Under `GreenMass G`, every `G_s` with
`s > 0` is a finite measure. -/
theorem isFiniteMeasure_of_greenMass {G : ℝ → Measure (Rd d)} (hG : GreenMass G) (s : ℝ)
    (hs : 0 < s) : IsFiniteMeasure (G s) :=
  ⟨by rw [hG.mass s hs]; exact ENNReal.ofReal_lt_top⟩

/-- `GreenMass` is preserved by convolution with a probability measure `ρ`:
`(ρ * G_s)(ℝ^d) = G_s(ℝ^d) = s` for `s > 0` (for `ρ` the Gaussian `p_η`: TeX
lines 846-847, 916-917). -/
theorem greenMass_conv (ρ : Measure (Rd d)) [IsProbabilityMeasure ρ]
    {G : ℝ → Measure (Rd d)} (hG : GreenMass G) : GreenMass (fun s => ρ ∗ G s) := by
  refine ⟨fun s hs => ?_⟩
  have := isFiniteMeasure_of_greenMass hG s hs
  rw [conv_univ, hG.mass s hs]

/-- The separate mass assertion for `N₀` (TeX lines 846-847, proof 916-917):
smoothing the Green family by a probability measure `ρ` leaves `N₀` unchanged,
`N₀^{ρ*G}(θ) = N₀^{G}(θ) = θ^{-2}` for `θ > 0`, with the integrand of `N₀^{ρ*G}`
integrable on `(0,∞)`; hypothesis `GreenMass G`. -/
theorem N0_conv (ρ : Measure (Rd d)) [IsProbabilityMeasure ρ]
    {G : ℝ → Measure (Rd d)} (hG : GreenMass G) (θ : ℝ) (hθ : 0 < θ) :
    IntegrableOn (fun s => Real.exp (-(θ * s)) * ((ρ ∗ G s) univ).toReal) (Ioi 0) ∧
      N0 (fun s => ρ ∗ G s) θ = N0 G θ ∧ N0 (fun s => ρ ∗ G s) θ = θ ^ (-(2 : ℝ)) := by
  obtain ⟨h1, h2⟩ := N0_eq _ (greenMass_conv ρ hG) θ hθ
  exact ⟨h1, h2.trans (N0_eq G hG θ hθ).2.symm, h2⟩

/-- The Gaussian-smoothed wave Green measures `p * G_s` (`p = gaussKernel v`,
`v ≥ 0` not needed) have mass `s` for `s > 0`, `d ∈ {1,2,3}`, and
`N₀(θ) = θ^{-2}`, the value for the unsmoothed `G_s` (`WaveGreen.N0_waveGreen`). -/
theorem gauss_waveGreen_mass (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) (v θ : ℝ) (hθ : 0 < θ) :
    GreenMass (fun s => gaussKernel v ∗ waveGreen d s) ∧
      IntegrableOn (fun s => Real.exp (-(θ * s)) *
        ((gaussKernel v ∗ waveGreen d s) univ).toReal) (Ioi 0) ∧
      N0 (fun s => gaussKernel v ∗ waveGreen d s) θ = N0 (waveGreen d) θ ∧
      N0 (fun s => gaussKernel v ∗ waveGreen d s) θ = θ ^ (-(2 : ℝ)) :=
  ⟨greenMass_conv _ (waveGreen_greenMass d hd),
    N0_conv (gaussKernel v) (waveGreen_greenMass d hd) θ hθ⟩

/-! ### (iii) Green smoothing as a Fourier multiplier -/

/-- Auxiliary to the Lean proof route.  The characteristic function of
`gaussKernel v` (`v ≥ 0`):
`∫ e^{i⟨x,ξ⟩} p(dx) = e^{-v|ξ|²/2}`. -/
theorem charFun_gaussKernel (v : ℝ) (hv : 0 ≤ v) (ξ : Rd d) :
    charFun (gaussKernel v) ξ = Complex.exp (-(v * ‖ξ‖ ^ 2) / 2) := by
  unfold gaussKernel
  rw [charFun_map_smul, charFun_stdGaussian, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg v)]
  congr 1
  have h2 : (√v * ‖ξ‖) ^ 2 = v * ‖ξ‖ ^ 2 := by rw [mul_pow, Real.sq_sqrt hv]
  rw [← Complex.ofReal_pow, h2]
  push_cast
  ring

/-- Gaussian smoothing of a finite measure `G` multiplies its characteristic
function by `e^{-v|ξ|²/2}` (`v ≥ 0`): `\widehat{p*G}(ξ) = e^{-v|ξ|²/2} Ĝ(ξ)`. -/
theorem charFun_gaussKernel_conv (v : ℝ) (hv : 0 ≤ v) (G : Measure (Rd d)) [IsFiniteMeasure G]
    (ξ : Rd d) :
    charFun (gaussKernel v ∗ G) ξ = Complex.exp (-(v * ‖ξ‖ ^ 2) / 2) * charFun G ξ := by
  rw [charFun_conv, charFun_gaussKernel v hv]

/-- For finite `G`, `H` and `v ≥ 0`, the product of the transforms of the
smoothed measures is the multiplier `e^{-v|ξ|²}` (`gaussMult v`) times the
product of the transforms:
`\widehat{p*G}(ξ) \overline{\widehat{p*H}(ξ)} = e^{-v|ξ|²} Ĝ(ξ) \overline{Ĥ(ξ)}`. -/
theorem charFun_pair_gaussKernel_conv (v : ℝ) (hv : 0 ≤ v) (G H : Measure (Rd d))
    [IsFiniteMeasure G] [IsFiniteMeasure H] (ξ : Rd d) :
    charFun (gaussKernel v ∗ G) ξ * conj (charFun (gaussKernel v ∗ H) ξ) =
      (gaussMult v ξ : ℝ) * (charFun G ξ * conj (charFun H ξ)) := by
  rw [charFun_gaussKernel_conv v hv G, charFun_gaussKernel_conv v hv H, coe_gaussMult, map_mul,
    ← Complex.ofReal_ofNat, ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_neg,
    ← Complex.ofReal_div, ← Complex.ofReal_exp, Complex.conj_ofReal, Complex.ofReal_exp]
  have : Real.exp (-(v * ‖ξ‖ ^ 2) / 2) * Real.exp (-(v * ‖ξ‖ ^ 2) / 2) =
      Real.exp (-(v * ‖ξ‖ ^ 2)) := by rw [← Real.exp_add]; ring_nf
  rw [← this]
  push_cast
  ring

/-- The outer integrand of the second norm of a Green family `G` (TeX
`E:damped-norm-definitions`, lines 788-791, with kernel `K_S`, `μ` the spectral
measure), with `Ĝ_s` the characteristic function of `G_s`:
`e^{-θ(s+t)} K_S(s-t) ∫ Ĝ_s(ξ) \overline{Ĝ_t(ξ)} μ(dξ)` (complex valued). -/
def N2GreenOuter (a θ : ℝ) (S : Set ℝ) (μ : Measure (Rd d)) (G : ℝ → Measure (Rd d))
    (p : ℝ × ℝ) : ℂ :=
  ((Real.exp (-(θ * (p.1 + p.2))) * KS a S (p.1 - p.2) : ℝ) : ℂ) *
    ∫ ξ, charFun (G p.1) ξ * conj (charFun (G p.2) ξ) ∂μ

/-- The second norm (squared, complex valued) of a Green family `G` with kernel
`K_S`: `∫∫_{(0,∞)²} N2GreenOuter`. -/
def N2GreenSq (a θ : ℝ) (S : Set ℝ) (μ : Measure (Rd d)) (G : ℝ → Measure (Rd d)) : ℂ :=
  ∫ p, N2GreenOuter a θ S μ G p ∂P2

/-- Auxiliary to the Lean proof route.  The outer integrands of the second norms
of `p * G` with spectral measure
`μ` and of `G` with spectral measure `e^{-v|ξ|²}μ(dξ)` agree almost everywhere on
`(0,∞)²`, for `G_s` finite for `s > 0` and `v ≥ 0`. -/
theorem N2GreenOuter_gauss_ae (a θ : ℝ) (S : Set ℝ) (μ : Measure (Rd d))
    (G : ℝ → Measure (Rd d)) (hfin : ∀ s, 0 < s → IsFiniteMeasure (G s)) (v : ℝ) (hv : 0 ≤ v) :
    N2GreenOuter a θ S μ (fun s => gaussKernel v ∗ G s) =ᵐ[P2]
      N2GreenOuter a θ S (smoothed μ (gaussMult v)) G := by
  filter_upwards [ae_P2] with p hp
  have := hfin p.1 hp.1
  have := hfin p.2 hp.2.1
  unfold N2GreenOuter
  congr 1
  rw [smoothed, integral_withDensity_eq_integral_smul (isMultiplier_gaussMult v hv).1]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [NNReal.smul_def, Complex.real_smul]
  exact charFun_pair_gaussKernel_conv v hv (G p.1) (G p.2) ξ

/-- Gaussian Green smoothing is the Gaussian multiplier on the spectral measure:
for a family `G` with `G_s` finite for `s > 0` and `v ≥ 0`, the second norm of
`p * G` (`p = gaussKernel v`) with spectral measure `μ` equals the second norm
of `G` with spectral measure `e^{-v|ξ|²} μ(dξ)` (`smoothed μ (gaussMult v)`),
for every `a`, `θ`, `S` (TeX lines 845-846, 915-916; used at 1664-1676).  The
outer integrands agree almost everywhere on `(0,∞)²`
(`N2GreenOuter_gauss_ae`), so one is integrable exactly when the other is. -/
theorem N2GreenSq_gauss (a θ : ℝ) (S : Set ℝ) (μ : Measure (Rd d)) (G : ℝ → Measure (Rd d))
    (hfin : ∀ s, 0 < s → IsFiniteMeasure (G s)) (v : ℝ) (hv : 0 ≤ v) :
    N2GreenSq a θ S μ (fun s => gaussKernel v ∗ G s) =
      N2GreenSq a θ S (smoothed μ (gaussMult v)) G :=
  integral_congr_ae (N2GreenOuter_gauss_ae a θ S μ G hfin v hv)

/-- The Fourier identity of `E:damped-norm-definitions` (TeX lines 777-778,
`Ĝ_s(ξ) = sin(s|ξ|)/|ξ|`, i.e. `WaveKernel.waveHat`) for a family of measures:
for `s > 0`, `G_s` is finite and its characteristic function is `waveHat s`.
Discharged in `d = 1` by `waveGreen_fourier_one` (`greenFourier_one`). -/
structure GreenFourier (G : ℝ → Measure (Rd d)) : Prop where
  finite : ∀ s : ℝ, 0 < s → IsFiniteMeasure (G s)
  fourier : ∀ s : ℝ, 0 < s → ∀ ξ : Rd d, charFun (G s) ξ = (waveHat s ξ : ℂ)

/-- `GreenFourier (waveGreen 1)`: the `d = 1` wave Green measures have
transform `waveHat`. -/
theorem greenFourier_one : GreenFourier (waveGreen 1) := by
  refine ⟨fun s _ => isFiniteMeasure_waveGreen 1 s, fun s hs ξ => ?_⟩
  rw [charFun_apply, ← (waveGreen_fourier_one s hs ξ).2]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [real_inner_comm, mul_comm]

/-- Auxiliary to the Lean proof route.  Under `GreenFourier G`, the outer
integrand of the second norm of `G` agrees
almost everywhere on `(0,∞)²` with that of `N2onSq` (cast to `ℂ`). -/
theorem N2GreenOuter_ae_eq (a θ : ℝ) (S : Set ℝ) (μ : Measure (Rd d))
    {G : ℝ → Measure (Rd d)} (hF : GreenFourier G) :
    N2GreenOuter a θ S μ G =ᵐ[P2] fun p => (N2onOuter a θ S μ p : ℂ) := by
  filter_upwards [ae_P2] with p hp
  unfold N2GreenOuter N2onOuter
  have hin : ∫ ξ, charFun (G p.1) ξ * conj (charFun (G p.2) ξ) ∂μ =
      ((∫ ξ, waveHat p.1 ξ * waveHat p.2 ξ ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only
    rw [hF.fourier p.1 hp.1, hF.fourier p.2 hp.2.1, Complex.conj_ofReal]
    push_cast; ring
  rw [hin]
  push_cast
  ring

/-- Under `GreenFourier G`, the second norm of `G` (TeX
`E:damped-norm-definitions` with kernel `K_S`, transforms of `G_s`) is the
second norm `N2onSq` of `DampedNormsHomog` (defined through `waveHat`), for
every `a`, `θ`, `S`, `μ`; the outer integrands agree almost everywhere
(`N2GreenOuter_ae_eq`). -/
theorem N2GreenSq_eq (a θ : ℝ) (S : Set ℝ) (μ : Measure (Rd d)) {G : ℝ → Measure (Rd d)}
    (hF : GreenFourier G) : N2GreenSq a θ S μ G = (N2onSq a θ S μ : ℂ) := by
  unfold N2GreenSq N2onSq
  rw [← integral_complex_ofReal]
  exact integral_congr_ae (N2GreenOuter_ae_eq a θ S μ hF)

/-- Gaussian Green smoothing under `GreenFourier G` and `v ≥ 0`: the second norm
of `p * G` equals `N2onSq` of the multiplied spectral measure
`e^{-v|ξ|²} μ(dξ)`. -/
theorem N2GreenSq_gauss_eq (a θ : ℝ) (S : Set ℝ) (μ : Measure (Rd d))
    {G : ℝ → Measure (Rd d)} (hF : GreenFourier G) (v : ℝ) (hv : 0 ≤ v) :
    N2GreenSq a θ S μ (fun s => gaussKernel v ∗ G s) =
      (N2onSq a θ S (smoothed μ (gaussMult v)) : ℂ) := by
  rw [N2GreenSq_gauss a θ S μ G hF.finite v hv, N2GreenSq_eq a θ S _ hF]

/-! ### The extended lemma -/

/-- **`L:damped-homogeneous-norms`** (main TeX lines 803-848, proof 850-919),
extended: under `H:homog` (`HomogCovariance`, temporal exponent `a = α₀`; no
`Γ ≠ 0`) and the supplied mass identity `GreenMass G` (TeX line 881, as in
`DampedNormsHomog.damped_homogeneous_norms_paper`; used for `N₀` and, through
the finiteness of `G_s` for `s > 0`, for item 6).  Conclusions:
1. for every `θ > 0`: finiteness, `N₂(θ)² ≥ 0`, `N₀(θ) = θ^{-2}` with its
   integrand integrable, and the scaling identities (as in
   `damped_homogeneous_norms_paper`);
2. for every `M`: the tail integrands are integrable and `N₂^{(M)}(1)² ≥ 0`;
3. `E:damped-tail-norms`: `N₁^{(M)}(1) → 0`, `N₂^{(M)}(1)² → 0`,
   `N₂^{(M)}(1) → 0`;
4. `E:damped-multiplier-comparison` (lines 836-841) in full: for `θ > 0`, a
   multiplier `g` in the class (`IsMultiplier`: measurable, values in `[0,1]`)
   and measurable `S ⊆ S'`, `0 ≤ N_{1,g,S}(θ) ≤ N_{1,1,S'}(θ)` and
   `0 ≤ N_{2,g,S}(θ)² ≤ N_{2,1,S'}(θ)²`, with the integrands integrable;
5. the class contains the Gaussian multipliers `e^{-η|ξ|²}`, `η ≥ 0`, and is
   closed under products (lines 845-846, 915-916);
6. Gaussian Green smoothing (`p = gaussKernel v`, `v ≥ 0`): `p * G` satisfies
   the mass identity and `N₀` is unchanged, `N₀^{p*G}(θ) = N₀^{G}(θ) = θ^{-2}`
   (lines 846-847, 916-917); and the second norm of `p * G` (transforms
   `\widehat{p*G_s}`) equals the second norm of `G` with spectral measure
   `e^{-v|ξ|²}μ(dξ)` (`N2GreenSq_gauss`).
The identification of the second norm of `G` itself with `N2onSq` needs the
Fourier identity `GreenFourier G`; see `damped_homogeneous_norms_fourier_paper`.
The spectral identity for spatial covariance smoothing `p_ε * Γ` is not stated
(only the membership of its multiplier, item 5). -/
theorem damped_homogeneous_norms_full_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
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
    (∀ θ : ℝ, 0 < θ → ∀ g : Rd d → ℝ≥0, IsMultiplier g →
      ∀ S S' : Set ℝ, MeasurableSet S → MeasurableSet S' → S ⊆ S' →
        Integrable (fun l : ℝ => l ^ (alpha0 - 1) * resolvent (smoothed μ g) (θ + l)) L0 ∧
        0 ≤ N1on alpha0 θ S (smoothed μ g) ∧
        N1on alpha0 θ S (smoothed μ g) ≤ N1on alpha0 θ S' μ ∧
        Integrable (N2onOuter alpha0 θ S (smoothed μ g)) P2 ∧
        Integrable (N2onOuter alpha0 θ S' μ) P2 ∧
        0 ≤ N2onSq alpha0 θ S (smoothed μ g) ∧
        N2onSq alpha0 θ S (smoothed μ g) ≤ N2onSq alpha0 θ S' μ) ∧
    (∀ η : ℝ, 0 ≤ η → IsMultiplier (gaussMult (d := d) η)) ∧
    (∀ g g' : Rd d → ℝ≥0, IsMultiplier g → IsMultiplier g' → IsMultiplier (g * g')) ∧
    (∀ v : ℝ, 0 ≤ v →
      GreenMass (fun s => gaussKernel v ∗ G s) ∧
      (∀ θ : ℝ, 0 < θ →
        IntegrableOn (fun s => Real.exp (-(θ * s)) * ((gaussKernel v ∗ G s) univ).toReal)
          (Ioi 0) ∧
        N0 (fun s => gaussKernel v ∗ G s) θ = N0 G θ ∧
        N0 (fun s => gaussKernel v ∗ G s) θ = θ ^ (-(2 : ℝ))) ∧
      (∀ θ : ℝ, ∀ S : Set ℝ, N2GreenSq alpha0 θ S μ (fun s => gaussKernel v ∗ G s) =
        N2GreenSq alpha0 θ S (smoothed μ (gaussMult v)) G)) := by
  obtain ⟨hR, h0⟩ := homog_spectral_facts h
  have := h.μ_radon
  obtain ⟨A1, A2, A3, A4, A5, -⟩ := damped_homogeneous_norms_paper h G hG
  refine ⟨A1, A2, A3, A4, A5, fun θ hθ g hg S S' hS hS' hSS => ?_,
    fun η hη => isMultiplier_gaussMult η hη, fun g g' hg hg' => hg.mul hg',
    fun v hv => ⟨greenMass_conv _ hG, fun θ hθ => N0_conv _ hG θ hθ,
      fun θ S => N2GreenSq_gauss alpha0 θ S μ G (isFiniteMeasure_of_greenMass hG) v hv⟩⟩
  exact damped_multiplier_comparison μ hR h0 alpha0 θ h.alpha0_pos h.alpha0_lt_one hθ
    (ClockCopyHomog.damped_norms_finite_paper h θ hθ).2.2 g hg.1 hg.2 S S' hS hS' hSS

/-- `L:damped-homogeneous-norms`, the second norm of a Green family and its
Gaussian smoothing, under `H:homog` and the Fourier identity `GreenFourier G`
(TeX lines 777-778, the transform of `G_s` is `Ĝ_s = sin(s|ξ|)/|ξ|`): for `v ≥ 0`,
`θ > 0` and measurable `S ⊆ S'`, the second norm of `G` with kernel `K_S` is
`N2onSq α₀ θ S μ`; the second norm of the Gaussian-smoothed family `p * G` is
`N_{2,m,S}(θ)²` with `m = e^{-v|ξ|²}`, which lies in `[0, N_{2,1,S'}(θ)²]`; the
outer integrands of all four second norms are integrable (TeX lines 845-846, 915-916; used at
1664-1676). -/
theorem damped_homogeneous_norms_fourier_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (h : HomogCovariance d alpha alpha0 Γ μ) {G : ℝ → Measure (Rd d)} (hF : GreenFourier G)
    (v : ℝ) (hv : 0 ≤ v) (θ : ℝ) (hθ : 0 < θ) (S S' : Set ℝ) (hS : MeasurableSet S)
    (hS' : MeasurableSet S') (hSS : S ⊆ S') :
    Integrable (N2GreenOuter alpha0 θ S μ G) P2 ∧
      N2GreenSq alpha0 θ S μ G = (N2onSq alpha0 θ S μ : ℂ) ∧
      Integrable (N2GreenOuter alpha0 θ S μ (fun s => gaussKernel v ∗ G s)) P2 ∧
      N2GreenSq alpha0 θ S μ (fun s => gaussKernel v ∗ G s) =
        (N2onSq alpha0 θ S (smoothed μ (gaussMult v)) : ℂ) ∧
      Integrable (N2onOuter alpha0 θ S (smoothed μ (gaussMult v))) P2 ∧
      Integrable (N2onOuter alpha0 θ S' μ) P2 ∧
      0 ≤ N2onSq alpha0 θ S (smoothed μ (gaussMult v)) ∧
      N2onSq alpha0 θ S (smoothed μ (gaussMult v)) ≤ N2onSq alpha0 θ S' μ := by
  obtain ⟨hR, h0⟩ := homog_spectral_facts h
  have := h.μ_radon
  have hm := isMultiplier_gaussMult (d := d) v hv
  obtain ⟨-, -, -, h3, h4, h5, h6⟩ := damped_multiplier_comparison μ hR h0 alpha0 θ
    h.alpha0_pos h.alpha0_lt_one hθ (ClockCopyHomog.damped_norms_finite_paper h θ hθ).2.2
    _ hm.1 hm.2 S S' hS hS' hSS
  obtain ⟨-, hIS, -⟩ := N2onSq_eq μ hR h0 alpha0 θ S h.alpha0_pos h.alpha0_lt_one hθ hS
  have hIG : Integrable (N2GreenOuter alpha0 θ S μ G) P2 :=
    hIS.ofReal.congr (N2GreenOuter_ae_eq alpha0 θ S μ hF).symm
  have hIp : Integrable (N2GreenOuter alpha0 θ S μ (fun s => gaussKernel v ∗ G s)) P2 :=
    (h3.ofReal.congr (N2GreenOuter_ae_eq alpha0 θ S _ hF).symm).congr
      (N2GreenOuter_gauss_ae alpha0 θ S μ G hF.finite v hv).symm
  exact ⟨hIG, N2GreenSq_eq alpha0 θ S μ hF, hIp, N2GreenSq_gauss_eq alpha0 θ S μ hF v hv,
    h3, h4, h5, h6⟩

/-- `L:damped-homogeneous-norms` extended, with the wave Green measures
`waveGreen d` and the only hypothesis `H:homog` (the dimension condition is
`h.dim`; `GreenMass` discharged by `waveGreen_greenMass`): the conclusions of
`damped_homogeneous_norms_full_paper` with `G := waveGreen d`. -/
theorem damped_homogeneous_norms_full_wave {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (h : HomogCovariance d alpha alpha0 Γ μ) :
    (∀ θ : ℝ, 0 < θ →
      (Integrable (N2integrand (d := d) alpha0 θ) (P2.prod μ) ∧
        Integrable (fun p : ℝ × ℝ => Real.exp (-(θ * (p.1 + p.2))) * |p.1 - p.2| ^ (-alpha0) *
          ∫ ξ, waveHat p.1 ξ * waveHat p.2 ξ ∂μ) P2 ∧
        Integrable (fun l : ℝ => l ^ (alpha0 - 1) * resolvent μ (θ + l)) L0) ∧
      0 ≤ N2sq alpha0 θ μ ∧
      IntegrableOn (fun s => Real.exp (-(θ * s)) * (waveGreen d s univ).toReal) (Ioi 0) ∧
      N0 (waveGreen d) θ = θ ^ (-(2 : ℝ)) ∧
      N1 alpha0 θ μ = θ ^ (alpha + alpha0 - 2) * N1 alpha0 1 μ ∧
      N2sq alpha0 θ μ = θ ^ (-(4 - alpha - alpha0)) * N2sq alpha0 1 μ) ∧
    (∀ M : ℝ, Integrable (N2onIntegrand (d := d) alpha0 1 (Ioi M)) (P2.prod μ) ∧
      Integrable (N2onOuter alpha0 1 (Ioi M) μ) P2 ∧ 0 ≤ N2tailSq alpha0 M μ) ∧
    Tendsto (fun M => N1tail alpha0 M μ) atTop (𝓝 0) ∧
    Tendsto (fun M => N2tailSq alpha0 M μ) atTop (𝓝 0) ∧
    Tendsto (fun M => N2tail alpha0 M μ) atTop (𝓝 0) ∧
    (∀ θ : ℝ, 0 < θ → ∀ g : Rd d → ℝ≥0, IsMultiplier g →
      ∀ S S' : Set ℝ, MeasurableSet S → MeasurableSet S' → S ⊆ S' →
        Integrable (fun l : ℝ => l ^ (alpha0 - 1) * resolvent (smoothed μ g) (θ + l)) L0 ∧
        0 ≤ N1on alpha0 θ S (smoothed μ g) ∧
        N1on alpha0 θ S (smoothed μ g) ≤ N1on alpha0 θ S' μ ∧
        Integrable (N2onOuter alpha0 θ S (smoothed μ g)) P2 ∧
        Integrable (N2onOuter alpha0 θ S' μ) P2 ∧
        0 ≤ N2onSq alpha0 θ S (smoothed μ g) ∧
        N2onSq alpha0 θ S (smoothed μ g) ≤ N2onSq alpha0 θ S' μ) ∧
    (∀ η : ℝ, 0 ≤ η → IsMultiplier (gaussMult (d := d) η)) ∧
    (∀ g g' : Rd d → ℝ≥0, IsMultiplier g → IsMultiplier g' → IsMultiplier (g * g')) ∧
    (∀ v : ℝ, 0 ≤ v →
      GreenMass (fun s => gaussKernel v ∗ waveGreen d s) ∧
      (∀ θ : ℝ, 0 < θ →
        IntegrableOn (fun s => Real.exp (-(θ * s)) *
          ((gaussKernel v ∗ waveGreen d s) univ).toReal) (Ioi 0) ∧
        N0 (fun s => gaussKernel v ∗ waveGreen d s) θ = N0 (waveGreen d) θ ∧
        N0 (fun s => gaussKernel v ∗ waveGreen d s) θ = θ ^ (-(2 : ℝ))) ∧
      (∀ θ : ℝ, ∀ S : Set ℝ,
        N2GreenSq alpha0 θ S μ (fun s => gaussKernel v ∗ waveGreen d s) =
          N2GreenSq alpha0 θ S (smoothed μ (gaussMult v)) (waveGreen d))) :=
  damped_homogeneous_norms_full_paper h (waveGreen d) (waveGreen_greenMass d h.dim)

/-- In `d = 1`, under `H:homog` alone: the Fourier part with nothing supplied
(`GreenFourier (waveGreen 1)` is `greenFourier_one`).  For `v ≥ 0`, `θ > 0` and
measurable `S ⊆ S'`, the second norm of the wave Green measures is
`N2onSq α₀ θ S μ`, the second norm of the Gaussian-smoothed wave Green measures
is `N_{2,m,S}(θ)²` with `m = e^{-v|ξ|²}`, all four outer integrands are
integrable, and
`0 ≤ N_{2,m,S}(θ)² ≤ N_{2,1,S'}(θ)²`. -/
theorem damped_homogeneous_norms_fourier_one {alpha alpha0 : ℝ} {Γ μ : Measure (Rd 1)}
    (h : HomogCovariance 1 alpha alpha0 Γ μ) (v : ℝ) (hv : 0 ≤ v) (θ : ℝ) (hθ : 0 < θ)
    (S S' : Set ℝ) (hS : MeasurableSet S) (hS' : MeasurableSet S') (hSS : S ⊆ S') :
    Integrable (N2GreenOuter alpha0 θ S μ (waveGreen 1)) P2 ∧
      N2GreenSq alpha0 θ S μ (waveGreen 1) = (N2onSq alpha0 θ S μ : ℂ) ∧
      Integrable (N2GreenOuter alpha0 θ S μ (fun s => gaussKernel v ∗ waveGreen 1 s)) P2 ∧
      N2GreenSq alpha0 θ S μ (fun s => gaussKernel v ∗ waveGreen 1 s) =
        (N2onSq alpha0 θ S (smoothed μ (gaussMult v)) : ℂ) ∧
      Integrable (N2onOuter alpha0 θ S (smoothed μ (gaussMult v))) P2 ∧
      Integrable (N2onOuter alpha0 θ S' μ) P2 ∧
      0 ≤ N2onSq alpha0 θ S (smoothed μ (gaussMult v)) ∧
      N2onSq alpha0 θ S (smoothed μ (gaussMult v)) ≤ N2onSq alpha0 θ S' μ :=
  damped_homogeneous_norms_fourier_paper h greenFourier_one v hv θ hθ S S' hS hS' hSS

end StratonovichHAMSecondMoment.DampedMultiplier
