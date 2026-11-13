module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Integration of wave items L7-c (`H1Density`), L7-d (`SpatialFourLinear`) and L7-e
(`OccupationPhysicalClass`) for `notes/integrated_spatial_occupation.tex` (line numbers at
revision a284420).  This module discharges two cross-item inputs.

1. The density input `hdense` of `SpatialFourLinear`.  It stands for the sentence "Smooth
   compact functions are dense in `H¹`" in the proof of `P:spatial-four-linear` (TeX lines
   262-268), and its type is verbatim the body of `H1Density.H1TestDense d`, which
   `H1Density.h1TestDense d` proves for every `d`.  Every public `SpatialFourLinear` theorem
   that takes `hdense` and states a manuscript conclusion is re-issued here as
   `<name>_completed` (for example `spatial_four_linear_paper_completed`) without `hdense`;
   every other hypothesis is kept exactly and each proof is one line:
   * the `_paper` wrappers `spatial_four_linear_paper` (`P:spatial-four-linear`, lines
     219-298), `spatial_homogeneous_bound_paper`, `spatial_square_CS_paper`,
     `spatial_four_linear_bound_paper`, `spatial_four_linear_multilinear_paper`,
     `spatial_four_linear_continuous_paper`, `spatial_ratio_H1_paper`,
     `squarePairingBounds_paper`, `spatial_energy_value_paper` (`P:spatial-energy-map`, lines
     300-325, `E:spatial-energy-map`, lines 309-314), `spatial_static_energy_score_paper` and
     `spatial_static_energy_score_sSup_paper` (`E:spatial-static-energy-score`, lines 316-322);
   * the general theorems `squareBound_of_smooth` (the Fatou step, lines 270-275),
     `C4_square_CS` and `square_pairing_CS` (`E:spatial-square-CS` on `H¹`, lines 225-227).
   The auxiliary `SpatialFourLinear.squareBound_R0` (no manuscript label) is not re-issued.
   `spatial_Asp_pos_paper` takes no density input and is unchanged.
2. The input `OccupationPhysicalClass.SquarePairingBounds Γ α R_0` of
   `P:occupation-physical-class` (two conclusions of `P:spatial-four-linear`):
   `squarePairingBounds_holds` proves it under `H:homog` and `Γ ≠ 0`, and
   `occupation_physical_class_completed_paper` is
   `OccupationPhysicalClass.occupation_physical_class_paper` without it.
   `occupation_physical_class_Esp_paper` restates the bounds in the TeX's own constants
   (lines 395-397 and 399-403): `J(g) ≤ R_⋆ R_sp T(g)^{α/2}` and
   `𝓔_⋆^𝒪 ≤ R_⋆^{2/(2-α)} 𝓔_sp`, with `𝓔_sp = SpatialFourLinear.Esp Γ` and
   `R_sp = SpatialFourLinear.Rsp Γ α`, using `R_sp = R_0` and `E:spatial-energy-map`
   (`SpatialFourLinear.spatial_energy_value_paper`; `energyValue` and
   `OccupationPhysicalClass.spEnergyVal` have the same body).

Every narrowing recorded in the source modules is unchanged:
* `SpatialFourLinear`: joint continuity of `C₄` is stated sequentially for `H¹` convergence of
  the pairs; `E:spatial-static-energy-score` is in the existential form, and in the TeX's
  `sSup` form only on the named input `VariationalRate.S1Bdd α₀ Γ`, which remains supplied.
* `OccupationPhysicalClass`: the class `𝒪` is modelled through joint representatives
  (`IsOccField`: a.e.-strongly measurable `(s,x) ↦ g_s(x)` and `(s,x) ↦ ∇g_s(x)`); the
  construction of such representatives from strong `H¹`-measurability is not formalized, so
  `𝒪` and `𝓔_⋆^𝒪` here are over fields given by joint representatives.

The standing assumptions are those of the source wrappers (lines 4-10: `H:homog` via
`HomogHypothesis.HomogCovariance`, `a = α₀`, `Γ ≠ 0`; for `P:occupation-physical-class` also
`D = q - 2a`, `q = 4 - α`).  No new object is defined.  The existing modules are not modified.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.H1Density
public import StratonovichHAMSecondMoment.SpatialFourLinear
public import StratonovichHAMSecondMoment.OccupationPhysicalClass

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Real Filter Topology
open scoped ENNReal

namespace StratonovichHAMSecondMoment.SpatialOccupationL7Completed

open HomogHypothesis (Rd HomogCovariance IsSpectralMeasure IsEven)
open WeakSobolev (IsTestFunction HasWeakGradient)
open SpatialSmoothRatio (R0)
open SpatialStaticControls (IsUnitH1 zE)
open OccupationKernelRow (pairing pairMeasure Kstar Rstar)
open VariationalFloor (grad)
open SpatialFourLinear (Nnorm IsH1Pair H1Tendsto C4 SquareBound Rsp Esp energyValue F0)

variable {d : ℕ}

/-! ### `P:spatial-four-linear` and `P:spatial-energy-map` without the density input -/

/-- `SpatialFourLinear.squareBound_of_smooth` (the Fatou step of `P:spatial-four-linear`, TeX
lines 270-275) with the density input discharged by `H1Density.h1TestDense` (TeX lines
262-268): for a locally finite `Γ` and `0 ≤ α ≤ 4`, the smooth square bound with constant `R`
gives `SquareBound Γ α R` on all `H¹` pairs. -/
theorem squareBound_of_smooth_completed {Γ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ]
    {alpha R : ℝ} (ha0 : 0 ≤ alpha) (ha4 : alpha ≤ 4)
    (hsm : ∀ φ ψ, IsTestFunction φ → IsTestFunction ψ →
      pairing Γ (zE fun x => φ x ^ 2) (zE fun x => ψ x ^ 2) ≤
        ENNReal.ofReal (R * Nnorm alpha φ (grad φ) ^ 2 * Nnorm alpha ψ (grad ψ) ^ 2)) :
    SquareBound Γ alpha R :=
  SpatialFourLinear.squareBound_of_smooth ha0 ha4 (H1Density.h1TestDense d) hsm

/-- `SpatialFourLinear.C4_square_CS` (the squared form of `E:spatial-square-CS` on `H¹`, TeX
lines 225-227, 283-285) with the density input discharged by `H1Density.h1TestDense` (TeX
lines 262-268).  Hypotheses as there: locally finite even `Γ` with spectral measure `μ`,
`SquareBound Γ α R`, `R ≥ 0`, `0 < α < 4`. -/
theorem C4_square_CS_completed {Γ μ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ]
    (hE : IsEven Γ) (hsp : IsSpectralMeasure Γ μ) {alpha R : ℝ} (hB : SquareBound Γ alpha R)
    (hR0 : 0 ≤ R) (ha0 : 0 < alpha) (ha4 : alpha < 4)
    {f h : Rd d → ℝ} {g k : Rd d → Rd d} (hfg : IsH1Pair f g) (hhk : IsH1Pair h k) :
    C4 Γ f f h h ^ 2 ≤ C4 Γ f f f f * C4 Γ h h h h :=
  SpatialFourLinear.C4_square_CS hE hsp hB hR0 ha0 ha4 (H1Density.h1TestDense d) hfg hhk

/-- `SpatialFourLinear.square_pairing_CS` (`E:spatial-square-CS` on `H¹` pairs, TeX lines
225-227) with the density input discharged by `H1Density.h1TestDense` (TeX lines 262-268);
hypotheses as in `C4_square_CS_completed`. -/
theorem square_pairing_CS_completed {Γ μ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ]
    (hE : IsEven Γ) (hsp : IsSpectralMeasure Γ μ) {alpha R : ℝ} (hB : SquareBound Γ alpha R)
    (hR0 : 0 ≤ R) (ha0 : 0 < alpha) (ha4 : alpha < 4)
    {f h : Rd d → ℝ} {g k : Rd d → Rd d} (hfg : IsH1Pair f g) (hhk : IsH1Pair h k) :
    pairing Γ (zE fun x => f x ^ 2) (zE fun x => h x ^ 2) < ⊤ ∧
      0 ≤ (pairing Γ (zE fun x => f x ^ 2) (zE fun x => h x ^ 2)).toReal ∧
      (pairing Γ (zE fun x => f x ^ 2) (zE fun x => h x ^ 2)).toReal ≤
        Real.sqrt ((pairing Γ (zE fun x => f x ^ 2) (zE fun x => f x ^ 2)).toReal *
          (pairing Γ (zE fun x => h x ^ 2) (zE fun x => h x ^ 2)).toReal) :=
  SpatialFourLinear.square_pairing_CS hE hsp hB hR0 ha0 ha4 (H1Density.h1TestDense d) hfg hhk

/-- **`E:spatial-homogeneous-bound`** (TeX line 224):
`SpatialFourLinear.spatial_homogeneous_bound_paper` with the density input (TeX lines 262-268)
discharged by `H1Density.h1TestDense`.  Under the standing assumptions (`H:homog`, `a = α₀`,
`Γ ≠ 0`), for every real `H¹` pair `(f, g)`, `A_sp(f) ≤ R_0 N(f)⁴` in `[0,∞]`. -/
theorem spatial_homogeneous_bound_paper_completed {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0)
    {f : Rd d → ℝ} {g : Rd d → Rd d} (hfg : IsH1Pair f g) :
    pairing Γ (zE fun x => f x ^ 2) (zE fun x => f x ^ 2) ≤
      ENNReal.ofReal (R0 Γ alpha * Nnorm alpha f g ^ 4) :=
  SpatialFourLinear.spatial_homogeneous_bound_paper hH hΓ (H1Density.h1TestDense d) hfg

/-- **`E:spatial-square-CS`** (TeX lines 225-227): `SpatialFourLinear.spatial_square_CS_paper`
with the density input (TeX lines 262-268) discharged.  Under the standing assumptions, for real
`H¹` pairs, `B_Γ(f², h²)` is finite and `0 ≤ B_Γ(f²,h²) ≤ √(A_sp(f) A_sp(h))` (real values). -/
theorem spatial_square_CS_paper_completed {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0)
    {f h : Rd d → ℝ} {g k : Rd d → Rd d} (hfg : IsH1Pair f g) (hhk : IsH1Pair h k) :
    pairing Γ (zE fun x => f x ^ 2) (zE fun x => h x ^ 2) < ⊤ ∧
      0 ≤ (pairing Γ (zE fun x => f x ^ 2) (zE fun x => h x ^ 2)).toReal ∧
      (pairing Γ (zE fun x => f x ^ 2) (zE fun x => h x ^ 2)).toReal ≤
        Real.sqrt ((pairing Γ (zE fun x => f x ^ 2) (zE fun x => f x ^ 2)).toReal *
          (pairing Γ (zE fun x => h x ^ 2) (zE fun x => h x ^ 2)).toReal) :=
  SpatialFourLinear.spatial_square_CS_paper hH hΓ (H1Density.h1TestDense d) hfg hhk

/-- **`E:spatial-four-linear`** and absolute convergence of `C₄` (TeX lines 229-234):
`SpatialFourLinear.spatial_four_linear_bound_paper` with the density input (TeX lines 262-268)
discharged.  Under the standing assumptions, for four real `H¹` pairs,
`∫ |f₁ f₂ f₃(·-y) f₄(·-y)| dν ≤ R_0 ∏ N(f_j)`, the integrand is `ν`-integrable, and
`|C₄| ≤ R_0 ∏ N(f_j)`. -/
theorem spatial_four_linear_bound_paper_completed {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0)
    {f₁ f₂ f₃ f₄ : Rd d → ℝ} {g₁ g₂ g₃ g₄ : Rd d → Rd d} (h₁ : IsH1Pair f₁ g₁)
    (h₂ : IsH1Pair f₂ g₂) (h₃ : IsH1Pair f₃ g₃) (h₄ : IsH1Pair f₄ g₄) :
    ∫⁻ p, ‖f₁ p.1 * f₂ p.1 * f₃ (p.1 - p.2) * f₄ (p.1 - p.2)‖ₑ ∂(pairMeasure Γ) ≤
        ENNReal.ofReal (R0 Γ alpha * (Nnorm alpha f₁ g₁ * Nnorm alpha f₂ g₂ *
          Nnorm alpha f₃ g₃ * Nnorm alpha f₄ g₄)) ∧
      Integrable (fun p : Rd d × Rd d => f₁ p.1 * f₂ p.1 * f₃ (p.1 - p.2) * f₄ (p.1 - p.2))
        (pairMeasure Γ) ∧
      |C4 Γ f₁ f₂ f₃ f₄| ≤ R0 Γ alpha * (Nnorm alpha f₁ g₁ * Nnorm alpha f₂ g₂ *
          Nnorm alpha f₃ g₃ * Nnorm alpha f₄ g₄) :=
  SpatialFourLinear.spatial_four_linear_bound_paper hH hΓ (H1Density.h1TestDense d) h₁ h₂ h₃ h₄

/-- Multilinearity of `C₄` (TeX line 280): `SpatialFourLinear.spatial_four_linear_multilinear_paper`
with the density input (TeX lines 262-268) discharged.  Under the standing assumptions, `C₄` is
linear in each of its four `H¹` arguments. -/
theorem spatial_four_linear_multilinear_paper_completed {alpha alpha0 : ℝ}
    {Γ μ : Measure (Rd d)} (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0)
    {f f' f₁ f₂ f₃ f₄ : Rd d → ℝ} {g g' g₁ g₂ g₃ g₄ : Rd d → Rd d} (h : IsH1Pair f g)
    (h' : IsH1Pair f' g') (h₁ : IsH1Pair f₁ g₁) (h₂ : IsH1Pair f₂ g₂) (h₃ : IsH1Pair f₃ g₃)
    (h₄ : IsH1Pair f₄ g₄) (a b : ℝ) :
    C4 Γ (fun x => a * f x + b * f' x) f₂ f₃ f₄ = a * C4 Γ f f₂ f₃ f₄ + b * C4 Γ f' f₂ f₃ f₄ ∧
      C4 Γ f₁ (fun x => a * f x + b * f' x) f₃ f₄ =
        a * C4 Γ f₁ f f₃ f₄ + b * C4 Γ f₁ f' f₃ f₄ ∧
      C4 Γ f₁ f₂ (fun x => a * f x + b * f' x) f₄ =
        a * C4 Γ f₁ f₂ f f₄ + b * C4 Γ f₁ f₂ f' f₄ ∧
      C4 Γ f₁ f₂ f₃ (fun x => a * f x + b * f' x) =
        a * C4 Γ f₁ f₂ f₃ f + b * C4 Γ f₁ f₂ f₃ f' :=
  SpatialFourLinear.spatial_four_linear_multilinear_paper hH hΓ (H1Density.h1TestDense d)
    h h' h₁ h₂ h₃ h₄ a b

/-- Joint continuity of `C₄` on `(H¹)⁴` (TeX lines 229-230, 281-283):
`SpatialFourLinear.spatial_four_linear_continuous_paper` with the density input (TeX lines
262-268) discharged.  Narrower than the TeX, as in the source: sequential form (`H¹`
convergence of functions and weak gradients in `L²`). -/
theorem spatial_four_linear_continuous_paper_completed {alpha alpha0 : ℝ}
    {Γ μ : Measure (Rd d)} (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0)
    {u₁ u₂ u₃ u₄ : ℕ → Rd d → ℝ} {v₁ v₂ v₃ v₄ : ℕ → Rd d → Rd d}
    {f₁ f₂ f₃ f₄ : Rd d → ℝ} {g₁ g₂ g₃ g₄ : Rd d → Rd d}
    (hu₁ : ∀ n, IsH1Pair (u₁ n) (v₁ n)) (hu₂ : ∀ n, IsH1Pair (u₂ n) (v₂ n))
    (hu₃ : ∀ n, IsH1Pair (u₃ n) (v₃ n)) (hu₄ : ∀ n, IsH1Pair (u₄ n) (v₄ n))
    (hf₁ : IsH1Pair f₁ g₁) (hf₂ : IsH1Pair f₂ g₂) (hf₃ : IsH1Pair f₃ g₃)
    (hf₄ : IsH1Pair f₄ g₄)
    (hc₁ : H1Tendsto u₁ v₁ f₁ g₁) (hc₂ : H1Tendsto u₂ v₂ f₂ g₂) (hc₃ : H1Tendsto u₃ v₃ f₃ g₃)
    (hc₄ : H1Tendsto u₄ v₄ f₄ g₄) :
    Tendsto (fun n => C4 Γ (u₁ n) (u₂ n) (u₃ n) (u₄ n)) atTop (𝓝 (C4 Γ f₁ f₂ f₃ f₄)) :=
  SpatialFourLinear.spatial_four_linear_continuous_paper hH hΓ (H1Density.h1TestDense d)
    hu₁ hu₂ hu₃ hu₄ hf₁ hf₂ hf₃ hf₄ hc₁ hc₂ hc₃ hc₄

/-- **`R_sp = R_0`** (TeX lines 235-236, 288-291): `SpatialFourLinear.spatial_ratio_H1_paper` with
the density input (TeX lines 262-268) discharged.  Under the standing assumptions, every real
unit `H¹` profile has positive gradient energy and ratio at most `R_0`; the `H¹` ratio set is
nonempty and bounded above; `R_sp = R_0`. -/
theorem spatial_ratio_H1_paper_completed {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) :
    (∀ (f : Rd d → ℝ) (g : Rd d → Rd d), IsUnitH1 f g → 0 < ∫ x, ‖g x‖ ^ 2 ∧
      (pairing Γ (zE fun x => f x ^ 2) (zE fun x => f x ^ 2)).toReal /
        (∫ x, ‖g x‖ ^ 2) ^ (alpha / 2) ≤ R0 Γ alpha) ∧
      (SpatialFourLinear.ratioSetH1 Γ alpha).Nonempty ∧
      BddAbove (SpatialFourLinear.ratioSetH1 Γ alpha) ∧ Rsp Γ alpha = R0 Γ alpha :=
  SpatialFourLinear.spatial_ratio_H1_paper hH hΓ (H1Density.h1TestDense d)

/-- **`P:spatial-four-linear`** (`integrated_spatial_occupation.tex` lines 219-298):
`SpatialFourLinear.spatial_four_linear_paper` with the density sentence of its proof (TeX lines
262-268) discharged by `H1Density.h1TestDense`.  Under the section's standing assumptions only
(lines 4-10: `H:homog`, `a = α₀`, `Γ ≠ 0`), for real `H¹` profiles given as `H¹` pairs
`(f, g)`: `E:spatial-homogeneous-bound`; finiteness of every square pairing and
`E:spatial-square-CS`; `E:spatial-four-linear` with absolute convergence; joint continuity of
`C₄` (sequential form, as recorded in `SpatialFourLinear`); `R_sp = R_0`; positivity of `A_sp`
on nonzero profiles. -/
theorem spatial_four_linear_paper_completed {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) :
    (∀ (f : Rd d → ℝ) (g : Rd d → Rd d), IsH1Pair f g →
      pairing Γ (zE fun x => f x ^ 2) (zE fun x => f x ^ 2) ≤
        ENNReal.ofReal (R0 Γ alpha * Nnorm alpha f g ^ 4)) ∧
    (∀ (f h : Rd d → ℝ) (g k : Rd d → Rd d), IsH1Pair f g → IsH1Pair h k →
      pairing Γ (zE fun x => f x ^ 2) (zE fun x => h x ^ 2) < ⊤ ∧
      0 ≤ (pairing Γ (zE fun x => f x ^ 2) (zE fun x => h x ^ 2)).toReal ∧
      (pairing Γ (zE fun x => f x ^ 2) (zE fun x => h x ^ 2)).toReal ≤
        Real.sqrt ((pairing Γ (zE fun x => f x ^ 2) (zE fun x => f x ^ 2)).toReal *
          (pairing Γ (zE fun x => h x ^ 2) (zE fun x => h x ^ 2)).toReal)) ∧
    (∀ (f₁ f₂ f₃ f₄ : Rd d → ℝ) (g₁ g₂ g₃ g₄ : Rd d → Rd d), IsH1Pair f₁ g₁ →
      IsH1Pair f₂ g₂ → IsH1Pair f₃ g₃ → IsH1Pair f₄ g₄ →
      ∫⁻ p, ‖f₁ p.1 * f₂ p.1 * f₃ (p.1 - p.2) * f₄ (p.1 - p.2)‖ₑ ∂(pairMeasure Γ) ≤
        ENNReal.ofReal (R0 Γ alpha * (Nnorm alpha f₁ g₁ * Nnorm alpha f₂ g₂ *
          Nnorm alpha f₃ g₃ * Nnorm alpha f₄ g₄)) ∧
      Integrable (fun p : Rd d × Rd d => f₁ p.1 * f₂ p.1 * f₃ (p.1 - p.2) * f₄ (p.1 - p.2))
        (pairMeasure Γ)) ∧
    (∀ (u₁ u₂ u₃ u₄ : ℕ → Rd d → ℝ) (v₁ v₂ v₃ v₄ : ℕ → Rd d → Rd d)
      (f₁ f₂ f₃ f₄ : Rd d → ℝ) (g₁ g₂ g₃ g₄ : Rd d → Rd d),
      (∀ n, IsH1Pair (u₁ n) (v₁ n)) → (∀ n, IsH1Pair (u₂ n) (v₂ n)) →
      (∀ n, IsH1Pair (u₃ n) (v₃ n)) → (∀ n, IsH1Pair (u₄ n) (v₄ n)) →
      IsH1Pair f₁ g₁ → IsH1Pair f₂ g₂ → IsH1Pair f₃ g₃ → IsH1Pair f₄ g₄ →
      H1Tendsto u₁ v₁ f₁ g₁ → H1Tendsto u₂ v₂ f₂ g₂ → H1Tendsto u₃ v₃ f₃ g₃ →
      H1Tendsto u₄ v₄ f₄ g₄ →
      Tendsto (fun n => C4 Γ (u₁ n) (u₂ n) (u₃ n) (u₄ n)) atTop (𝓝 (C4 Γ f₁ f₂ f₃ f₄))) ∧
    Rsp Γ alpha = R0 Γ alpha ∧
    (∀ (f : Rd d → ℝ) (g : Rd d → Rd d), IsH1Pair f g → ¬ f =ᵐ[volume] 0 →
      0 < pairing Γ (zE fun x => f x ^ 2) (zE fun x => f x ^ 2)) :=
  SpatialFourLinear.spatial_four_linear_paper hH hΓ (H1Density.h1TestDense d)

/-- `SpatialFourLinear.squarePairingBounds_paper` with the density input (TeX lines 262-268)
discharged: under the standing assumptions, the two fields of
`OccupationPhysicalClass.SquarePairingBounds Γ α R_0` in that structure's spelling
(`E:spatial-homogeneous-bound`, line 224, and the squared `[0,∞]` form of
`E:spatial-square-CS`, lines 225-227). -/
theorem squarePairingBounds_paper_completed {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) :
    (∀ (f : Rd d → ℝ) (gf : Rd d → Rd d), MemLp f 2 volume → MemLp gf 2 volume →
      HasWeakGradient f gf →
      pairing Γ (fun x => ENNReal.ofReal (f x ^ 2)) (fun x => ENNReal.ofReal (f x ^ 2)) ≤
        ENNReal.ofReal (R0 Γ alpha * (Real.sqrt (∫ x, f x ^ 2) ^ (1 - alpha / 4) *
          Real.sqrt (∫ x, ‖gf x‖ ^ 2) ^ (alpha / 4)) ^ 4)) ∧
    (∀ (f : Rd d → ℝ) (gf : Rd d → Rd d) (h : Rd d → ℝ) (gh : Rd d → Rd d),
      MemLp f 2 volume → MemLp gf 2 volume → HasWeakGradient f gf →
      MemLp h 2 volume → MemLp gh 2 volume → HasWeakGradient h gh →
      pairing Γ (fun x => ENNReal.ofReal (f x ^ 2)) (fun x => ENNReal.ofReal (h x ^ 2)) ^ 2 ≤
        pairing Γ (fun x => ENNReal.ofReal (f x ^ 2)) (fun x => ENNReal.ofReal (f x ^ 2)) *
          pairing Γ (fun x => ENNReal.ofReal (h x ^ 2)) (fun x => ENNReal.ofReal (h x ^ 2))) :=
  SpatialFourLinear.squarePairingBounds_paper hH hΓ (H1Density.h1TestDense d)

/-- **`P:spatial-energy-map`, `E:spatial-energy-map`** (TeX lines 300-325, display 309-314):
`SpatialFourLinear.spatial_energy_value_paper` with the density input of `P:spatial-four-linear`
(TeX lines 262-268) discharged.  Under the standing assumptions, the energy set over real unit
`H¹` profiles is nonempty and bounded above,
`𝓔_sp = (2-α)/2 α^{α/(2-α)} R_sp^{2/(2-α)}`, `𝓔_sp > 0`, and `R_sp = R_0`. -/
theorem spatial_energy_value_paper_completed {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) :
    (SpatialFourLinear.energySet Γ).Nonempty ∧ BddAbove (SpatialFourLinear.energySet Γ) ∧
      Esp Γ = energyValue alpha (Rsp Γ alpha) ∧ 0 < Esp Γ ∧ Rsp Γ alpha = R0 Γ alpha :=
  SpatialFourLinear.spatial_energy_value_paper hH hΓ (H1Density.h1TestDense d)

/-- **`E:spatial-static-energy-score`** (TeX lines 316-322):
`SpatialFourLinear.spatial_static_energy_score_paper` with the density input (TeX lines
262-268) discharged.  Narrower than the TeX, as in the source: the existential form (every
`y < M_a^{-1/k} F₀(𝓔_sp)`, `k = 3-α`, `a = α₀`, is exceeded by `I_Ψ - v_Ψ/2` for some
`Ψ ∈ C_pos`). -/
theorem spatial_static_energy_score_paper_completed {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) :
    ∀ y < TemporalEquilibrium.mass alpha0 ^ (-(1 / (3 - alpha))) * F0 alpha (Esp Γ),
      ∃ Ψ ∈ VariationalDilation.CPos d,
        y < VariationalDilation.integratedRate alpha0 Γ Ψ -
          VariationalDilation.rawCost alpha0 Γ Ψ / 2 :=
  SpatialFourLinear.spatial_static_energy_score_paper hH hΓ (H1Density.h1TestDense d)

/-- **`E:spatial-static-energy-score`** in the TeX's `sSup` form (TeX lines 316-322):
`SpatialFourLinear.spatial_static_energy_score_sSup_paper` with the density input (TeX lines
262-268) discharged; the named input `VariationalRate.S1Bdd α₀ Γ` remains supplied, as in the
source.  Conclusion: `S_1^pos ≥ M_a^{-1/k} F₀(𝓔_sp)`. -/
theorem spatial_static_energy_score_sSup_paper_completed {alpha alpha0 : ℝ}
    {Γ μ : Measure (Rd d)} (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0)
    (hB1 : VariationalRate.S1Bdd alpha0 Γ) :
    TemporalEquilibrium.mass alpha0 ^ (-(1 / (3 - alpha))) * F0 alpha (Esp Γ) ≤
      VariationalRate.S1pos alpha0 Γ :=
  SpatialFourLinear.spatial_static_energy_score_sSup_paper hH hΓ (H1Density.h1TestDense d) hB1

/-! ### `P:occupation-physical-class` without the `SquarePairingBounds` input -/

/-- The input `OccupationPhysicalClass.SquarePairingBounds Γ α R_0` of
`P:occupation-physical-class` (two conclusions of `P:spatial-four-linear`:
`E:spatial-homogeneous-bound`, TeX line 224, and `E:spatial-square-CS` in the squared `[0,∞]`
form, lines 225-227) holds under the standing assumptions `H:homog` and `Γ ≠ 0`; proof:
`squarePairingBounds_paper_completed`. -/
theorem squarePairingBounds_holds {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) :
    OccupationPhysicalClass.SquarePairingBounds Γ alpha (R0 Γ alpha) :=
  ⟨(squarePairingBounds_paper_completed hH hΓ).1, (squarePairingBounds_paper_completed hH hΓ).2⟩

/-- **`P:occupation-physical-class`** (TeX lines 386-404):
`OccupationPhysicalClass.occupation_physical_class_paper` with its input
`SquarePairingBounds Γ α R_0` discharged by `squarePairingBounds_holds` (from
`P:spatial-four-linear`).  Standing assumptions: `H:homog` with `a = α₀`, `Γ ≠ 0`,
`D = (4 - α) - 2a`.  The conclusions are those of the source wrapper, with the constants `R_0`
and `R_⋆^{2/(2-α)} spEnergyVal α R_0`; see `occupation_physical_class_Esp_paper` for the TeX's
`R_sp` and `𝓔_sp`.  Narrower than the TeX, as in the source: `𝒪` is modelled through joint
representatives (`IsOccField`). -/
theorem occupation_physical_class_completed_paper {alpha a : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha a Γ μ) (hΓ : Γ ≠ 0) (D : ℝ) (hD : D = (4 - alpha) - 2 * a) :
    (∀ (G : ℝ → Rd d → ℝ) (DG : ℝ → Rd d → Rd d), OccupationPhysicalClass.IsOccField G DG →
      AEMeasurable (fun p : ℝ × ℝ => OccupationPhysicalClass.sqPair Γ (G p.1) (G p.2))
        (OccupationPhysicalClass.volI.prod OccupationPhysicalClass.volI) ∧
      (∀ G' : ℝ → Rd d → ℝ, (∀ᵐ s ∂OccupationPhysicalClass.volI, G s =ᵐ[volume] G' s) →
        (fun p : ℝ × ℝ => OccupationPhysicalClass.sqPair Γ (G p.1) (G p.2))
            =ᵐ[OccupationPhysicalClass.volI.prod OccupationPhysicalClass.volI]
          (fun p : ℝ × ℝ => OccupationPhysicalClass.sqPair Γ (G' p.1) (G' p.2)) ∧
        OccupationPhysicalClass.Jlin a D Γ G = OccupationPhysicalClass.Jlin a D Γ G') ∧
      Integrable (fun s => ∫ x, ‖DG s x‖ ^ 2) OccupationPhysicalClass.volI ∧
      ∫ s, (∫ x, ‖DG s x‖ ^ 2) ∂OccupationPhysicalClass.volI = OccupationPhysicalClass.T DG ∧
      OccupationPhysicalClass.Jlin a D Γ G < ⊤ ∧
      Integrable (fun p : ℝ × ℝ =>
          Kstar a D (p.1 - p.2) * (OccupationPhysicalClass.sqPair Γ (G p.1) (G p.2)).toReal)
        (OccupationPhysicalClass.volI.prod OccupationPhysicalClass.volI) ∧
      ∫ p, Kstar a D (p.1 - p.2) * (OccupationPhysicalClass.sqPair Γ (G p.1) (G p.2)).toReal
          ∂(OccupationPhysicalClass.volI.prod OccupationPhysicalClass.volI) =
        OccupationPhysicalClass.J a D Γ G ∧
      0 ≤ OccupationPhysicalClass.J a D Γ G ∧
      OccupationPhysicalClass.J a D Γ G ≤
        Rstar a D * R0 Γ alpha * OccupationPhysicalClass.T DG ^ (alpha / 2)) ∧
    (OccupationPhysicalClass.energySet a D Γ).Nonempty ∧
    BddAbove (OccupationPhysicalClass.energySet a D Γ) ∧
    0 < OccupationPhysicalClass.EstarO a D Γ ∧
    OccupationPhysicalClass.EstarO a D Γ ≤
      Rstar a D ^ (2 / (2 - alpha)) * OccupationPhysicalClass.spEnergyVal alpha (R0 Γ alpha) :=
  OccupationPhysicalClass.occupation_physical_class_paper hH hΓ D hD
    (squarePairingBounds_holds hH hΓ)

/-- **`E:occupation-physical-bound`** and **`E:occupation-own-energy`** in the TeX's constants
(lines 395-397 and 399-403), under the standing assumptions (`H:homog` with `a = α₀`, `Γ ≠ 0`,
`D = (4 - α) - 2a`), with no supplied input: for every field of `𝒪` (modelled as
`IsOccField`, narrower than the TeX as recorded in `OccupationPhysicalClass`),
`0 ≤ J(g) ≤ R_⋆ R_sp T(g)^{α/2}`; the energy value set is nonempty and bounded above and
`0 < 𝓔_⋆^𝒪 ≤ R_⋆^{2/(2-α)} 𝓔_sp` with `𝓔_sp = SpatialFourLinear.Esp Γ ∈ (0,∞)` (a real
number).  Route: `occupation_physical_class_completed_paper`, `R_sp = R_0` and
`E:spatial-energy-map` (`spatial_energy_value_paper_completed`;
`OccupationPhysicalClass.spEnergyVal` and `SpatialFourLinear.energyValue` have the same body).
Finiteness of `J(g)` and the Bochner forms are in `occupation_physical_class_completed_paper`. -/
theorem occupation_physical_class_Esp_paper {alpha a : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha a Γ μ) (hΓ : Γ ≠ 0) (D : ℝ) (hD : D = (4 - alpha) - 2 * a) :
    (∀ (G : ℝ → Rd d → ℝ) (DG : ℝ → Rd d → Rd d), OccupationPhysicalClass.IsOccField G DG →
      OccupationPhysicalClass.Jlin a D Γ G < ⊤ ∧
      0 ≤ OccupationPhysicalClass.J a D Γ G ∧
      OccupationPhysicalClass.J a D Γ G ≤
        Rstar a D * Rsp Γ alpha * OccupationPhysicalClass.T DG ^ (alpha / 2)) ∧
    (OccupationPhysicalClass.energySet a D Γ).Nonempty ∧
    BddAbove (OccupationPhysicalClass.energySet a D Γ) ∧
    0 < OccupationPhysicalClass.EstarO a D Γ ∧
    OccupationPhysicalClass.EstarO a D Γ ≤ Rstar a D ^ (2 / (2 - alpha)) * Esp Γ ∧
    0 < Esp Γ := by
  obtain ⟨-, -, hE, hEpos, hRsp⟩ := spatial_energy_value_paper_completed hH hΓ
  obtain ⟨hJ, h1, h2, h3, h4⟩ := occupation_physical_class_completed_paper hH hΓ D hD
  have hval : OccupationPhysicalClass.spEnergyVal alpha (R0 Γ alpha) = Esp Γ := by
    rw [hE, hRsp]; rfl
  refine ⟨fun G DG hO => ?_, h1, h2, h3, by rw [← hval]; exact h4, hEpos⟩
  obtain ⟨-, -, -, -, hfin, -, -, hJ0, hJle⟩ := hJ G DG hO
  exact ⟨hfin, hJ0, by rw [hRsp]; exact hJle⟩

end StratonovichHAMSecondMoment.SpatialOccupationL7Completed
