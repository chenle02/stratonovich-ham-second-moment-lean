module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Integration of wave L6 for Section `S:spatial-occupation-foundation` of
`notes/integrated_spatial_occupation.tex` (revision a284420): the named
inputs `SpatialStaticControls.RayleighFloor` and
`SpatialSmoothRatio.StaticControls` are discharged under the section's
standing assumptions (lines 4-10: a nonzero covariance satisfying `H:homog`,
`a = α₀`), and the manuscript statements that carried them are re-issued
without them.

* `rayleighFloor_of_homog`: under `H:homog` and `Γ ≠ 0`, `RayleighFloor Γ`
  holds.  It is `VariationalFloor.rayleighSet_floor` at the potential
  `V = U_z = Γ * z` (the dilation floor; uses `α < 2` from `H:homog`), with the
  integrability and the bound of `U_z` from
  `SpatialStaticControls.convZ_props`.
* `spatial_static_controls_completed_paper`: `L:spatial-static-controls`,
  part (i) (TeX lines 40-49), with exactly the manuscript's hypotheses;
  `SpatialStaticControls.spatial_static_controls_rate_paper` without
  `RayleighFloor`.
* `staticControls_of_homog`: under `H:homog` and `Γ ≠ 0`,
  `SpatialSmoothRatio.StaticControls α₀ Γ` holds.  It is
  `SpatialStaticControls.spatial_static_score_paper` (part (ii) of
  `L:spatial-static-controls`, existential form) with two conversions: the
  Rayleigh set of `x ↦ 1 · U_z(x)` is that of `U_z` (`one_mul`), and the
  extended pairing `B_Γ(z,z)` (`OccupationKernelRow.pairing`) has real value
  `SpatialFourierBound.spatialPair Γ z z`
  (`SpatialStaticControls.pairing_eq_spatialPair`).
* `spatial_smooth_score_completed_paper`,
  `spatial_smooth_score_sSup_completed_paper`,
  `R0_finite_of_S1Bdd_completed_paper`,
  `spatial_smooth_ratio_completed_paper`: the four `P:spatial-smooth-ratio`
  wrappers of `SpatialSmoothRatio` without `StaticControls`; the `sSup` forms
  keep the named input `VariationalRate.S1Bdd α₀ Γ` exactly where the
  originals had it.

Supplied inputs: none beyond `S1Bdd` in the two `sSup`-form statements (see
`VariationalRate.S1Bdd` for its provenance).  All boundaries of the
instantiated results (the Rayleigh-form rate, the integral form of the cost,
the existential form of the score bounds) are those recorded in
`SpatialStaticControls`, `SpatialSmoothRatio` and `VariationalRate`.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.SpatialStaticControls
public import StratonovichHAMSecondMoment.SpatialSmoothRatio

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set

namespace StratonovichHAMSecondMoment.SpatialOccupationCompleted

open HomogHypothesis (Rd HomogCovariance)
open WeakSobolev (IsTestFunction rayleighSet rayleighRate)
open VariationalDilation (CPos conv integratedRate rawCost)
open VariationalRate (S1Bdd S1pos)
open SpatialStaticControls (RayleighFloor lamSq lamZ convZ_props zE)
open SpatialSmoothRatio (StaticControls smoothScoreBound ratio ratioSet R0)

variable {d : ℕ}

/-- The named input `RayleighFloor` of `SpatialStaticControls` holds under the
section's standing assumptions (`H:homog`, `Γ ≠ 0`): for every nonnegative
nonzero test function `z`, the real Rayleigh set of `U_z = Γ * z` contains a
positive value.  Proof: the dilation floor `VariationalFloor.rayleighSet_floor`
at `V = U_z` (`α < 2` by `VariationalRate.alpha_lt_two`). -/
theorem rayleighFloor_of_homog {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ0 : Γ ≠ 0) : RayleighFloor Γ := by
  intro z hz hz0 hzne
  have := hH.Γ_radon
  obtain ⟨hint, hUc, hU0, M, hUM⟩ := convZ_props hH.Γ_tempered hH.μ_tempered hH.spectral hz hz0
  exact (VariationalFloor.rayleighSet_floor hH.scaling (VariationalRate.alpha_lt_two hH) hΓ0
    hz.1.continuous hz.2 hz0 hzne hint (V := conv Γ z) (fun _ => le_rfl)
    (fun f hf => VariationalMean.integrable_pot_of_bounded hUc (M := M) (fun x => by
      rw [abs_of_nonneg (hU0 x)]; exact hUM x) hf)).1

/-- **`L:spatial-static-controls`, part (i)** (TeX lines 40-49, proof 56-64),
with exactly the section's standing hypotheses (`H:homog`, `Γ ≠ 0`, `a = α₀`;
the potential does not depend on `a`): for every nonnegative nonzero
`z ∈ C_c^∞(ℝ^d)`, each `U_z(x)` is a genuine integral; for `c > 0` the set of
values `c ∫ U_z g² - ‖∇g‖₂²` over unit `g ∈ H^1` is nonempty and bounded above,
`λ_z(c)² > 0`, `λ_z(c) > 0`; and `λ_z` is Lipschitz on every `[c₁, c₂]` with
`c₁ > 0`.  This is `SpatialStaticControls.spatial_static_controls_rate_paper`
with its input `RayleighFloor Γ` discharged by `rayleighFloor_of_homog`
(positivity by the dilation floor, a different route from the TeX's lines
57-62). -/
theorem spatial_static_controls_completed_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ0 : Γ ≠ 0)
    {z : Rd d → ℝ} (hz : IsTestFunction z) (hz0 : ∀ x, 0 ≤ z x) (hzne : z ≠ 0) :
    (∀ x, Integrable (fun y => z (x - y)) Γ) ∧
    (∀ c : ℝ, 0 < c → (rayleighSet (fun x => c * conv Γ z x)).Nonempty ∧
      BddAbove (rayleighSet (fun x => c * conv Γ z x)) ∧
      0 < lamSq (conv Γ z) c ∧ 0 < lamZ Γ z c ∧ lamZ Γ z c ^ 2 = lamSq (conv Γ z) c) ∧
    (∀ c₁ c₂ : ℝ, 0 < c₁ → ∃ K : NNReal, LipschitzOnWith K (lamZ Γ z) (Icc c₁ c₂)) :=
  SpatialStaticControls.spatial_static_controls_rate_paper hH hΓ0
    (rayleighFloor_of_homog hH hΓ0) hz hz0 hzne

/-- The named input `StaticControls α₀ Γ` of `SpatialSmoothRatio` holds under
the section's standing assumptions (`H:homog`, `Γ ≠ 0`, `a = α₀`).  Proof:
`SpatialStaticControls.spatial_static_score_paper`, with
`x ↦ 1 · U_z(x) = U_z` and `B_Γ(z,z).toReal = spatialPair Γ z z`
(`SpatialStaticControls.pairing_eq_spatialPair`). -/
theorem staticControls_of_homog {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ0 : Γ ≠ 0) : StaticControls alpha0 Γ := by
  intro z hz hz0 hzne
  have := hH.Γ_radon
  obtain ⟨-, -, hbdd, h⟩ := SpatialStaticControls.spatial_static_score_paper hH hΓ0 hz hz0 hzne
  have e : (fun x => 1 * conv Γ z x) = conv Γ z := funext fun x => one_mul _
  have hP : (OccupationKernelRow.pairing Γ (zE z) (zE z)).toReal =
      SpatialFourierBound.spatialPair Γ z z :=
    (SpatialStaticControls.pairing_eq_spatialPair hz.1.continuous hz.2 hz0 hz.1.continuous
      hz.2 hz0).2.2
  have hlam : lamZ Γ z 1 = rayleighRate (conv Γ z) := by
    simp only [lamZ, SpatialStaticControls.lam, e]
  rw [e] at hbdd
  refine ⟨hbdd, fun y hy => ?_⟩
  obtain ⟨Ψ, hΨ, hlt, -⟩ := h y (by rw [hlam, hP]; exact hy)
  exact ⟨Ψ, hΨ, hlt⟩

/-- **`P:spatial-smooth-ratio`, `E:spatial-smooth-score`** (TeX lines 171-176,
proof 197-213), existential form (Le's decision 2), with exactly the
section's standing hypotheses (`H:homog`, `Γ ≠ 0`, `a = α₀`): for every real
unit `g ∈ C_c^∞(ℝ^d)` and every
`y < k [R(g) α^{α/2}/(8 M_a q^{q/2})]^{1/k}` there is `Ψ ∈ C_pos` with
`y < I_Ψ - v_Ψ/2`.  `SpatialSmoothRatio.spatial_smooth_score_paper` with
`StaticControls` discharged by `staticControls_of_homog`. -/
theorem spatial_smooth_score_completed_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) {g : Rd d → ℝ}
    (hg : SpatialFourierBound.IsUnitTest g) :
    ∀ y < smoothScoreBound alpha alpha0 (ratio Γ alpha g),
      ∃ Ψ ∈ CPos d, y < integratedRate alpha0 Γ Ψ - rawCost alpha0 Γ Ψ / 2 :=
  SpatialSmoothRatio.spatial_smooth_score_paper hH hΓ (staticControls_of_homog hH hΓ) hg

/-- `E:spatial-smooth-score` in the TeX's `sSup` form, with the section's
standing hypotheses and the named input `S1Bdd α₀ Γ` only:
`S_1^pos ≥ k [R(g) α^{α/2}/(8 M_a q^{q/2})]^{1/k}` for every real unit `g`.
`SpatialSmoothRatio.spatial_smooth_score_sSup_paper` without
`StaticControls`. -/
theorem spatial_smooth_score_sSup_completed_paper {alpha alpha0 : ℝ}
    {Γ μ : Measure (Rd d)} (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0)
    (hB : S1Bdd alpha0 Γ) {g : Rd d → ℝ} (hg : SpatialFourierBound.IsUnitTest g) :
    smoothScoreBound alpha alpha0 (ratio Γ alpha g) ≤ S1pos alpha0 Γ :=
  SpatialSmoothRatio.spatial_smooth_score_sSup_paper hH hΓ (staticControls_of_homog hH hΓ) hB hg

/-- "`S1Bdd ⇒ R_0` finite" (the manuscript's route before revision a284420, now
replaced by `L:spatial-fourier-bound`), with
the section's standing hypotheses and the named input `S1Bdd α₀ Γ` only:
the ratio set is bounded above and
`R_0 ≤ 8 M_a q^{q/2} (S_1^pos/k)^k / α^{α/2}`.
`SpatialSmoothRatio.R0_finite_of_S1Bdd_paper` without `StaticControls`. -/
theorem R0_finite_of_S1Bdd_completed_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) (hB : S1Bdd alpha0 Γ) :
    BddAbove (ratioSet Γ alpha) ∧
      R0 Γ alpha ≤ 8 * TemporalEquilibrium.mass alpha0 * (4 - alpha) ^ ((4 - alpha) / 2) *
        (S1pos alpha0 Γ / (3 - alpha)) ^ (3 - alpha) / alpha ^ (alpha / 2) :=
  SpatialSmoothRatio.R0_finite_of_S1Bdd_paper hH hΓ (staticControls_of_homog hH hΓ) hB

/-- **`P:spatial-smooth-ratio`** (TeX lines 166-176), both claims, with exactly
the section's standing hypotheses (`H:homog`, `Γ ≠ 0`, `a = α₀`): `R_0` is a
positive finite real number, and `E:spatial-smooth-score` holds for every real
unit `g` in the existential form.
`SpatialSmoothRatio.spatial_smooth_ratio_paper` without `StaticControls`. -/
theorem spatial_smooth_ratio_completed_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) :
    ((ratioSet Γ alpha).Nonempty ∧ BddAbove (ratioSet Γ alpha) ∧
      0 < R0 Γ alpha ∧ R0 Γ alpha ≤ 2 ^ (1 + alpha) * SpectralHomog.resolvent μ 1 ∧
      ∀ g, SpatialFourierBound.IsUnitTest g → ratio Γ alpha g ≤ R0 Γ alpha) ∧
    ∀ g, SpatialFourierBound.IsUnitTest g →
      ∀ y < smoothScoreBound alpha alpha0 (ratio Γ alpha g),
        ∃ Ψ ∈ CPos d, y < integratedRate alpha0 Γ Ψ - rawCost alpha0 Γ Ψ / 2 :=
  SpatialSmoothRatio.spatial_smooth_ratio_paper hH hΓ (staticControls_of_homog hH hΓ)

end StratonovichHAMSecondMoment.SpatialOccupationCompleted
