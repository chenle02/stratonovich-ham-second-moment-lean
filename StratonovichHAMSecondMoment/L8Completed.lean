module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Integration of wave items L8-c1 (`SpaceTimePositivity`), L8-c2 (`OccupationCeilingFinite`) and
L8-d (`SpatialBracket`) for `notes/integrated_occupation_ceiling.tex` and
`notes/integrated_unmasked_variational.tex` (line numbers at revision a284420).  This module
discharges three cross-item inputs, combines two L8 lemmas and checks that one supplied structure is
not vacuous; it modifies no existing module.

1. The named input `OccupationCeilingFinite.SpaceTimeCS α₀ Γ` (step (c) of the deterministic
   `S1Bdd` route: Cauchy-Schwarz for the space-time form, `F(Ψ,Ψ) = v_Ψ` and
   `∫∫ h_{Ψ,s} Φ_s = F(Ψ,Φ)`).  `SpaceTimePositivity.spaceTimeCS_holds` proves the structure
   `SpaceTimePositivity.SpaceTimeCS α₀ Γ` from `H:homog` alone; its form
   `SpaceTimePositivity.stFormIter` has the same body as `OccupationCeilingFinite.stForm`, so
   the two structures have definitionally equal fields and `spaceTimeCS_completed` is the
   anonymous constructor.  Every public `OccupationCeilingFinite` `_paper` wrapper that takes
   `SpaceTimeCS` is re-issued as `<name>_completed` without it; every other hypothesis
   (`H:homog` via `HomogHypothesis.HomogCovariance`, `Γ ≠ 0`, and the item hypotheses) is kept
   exactly and each proof is one line:
   `occupation_ceiling_K0_paper`, `s1Bdd_paper`, `occupation_ceiling_sSup_K0_paper`,
   `variational_positive_scores_sSup_st_paper`, `spatial_static_score_sSup_st_paper`,
   `spatial_smooth_score_sSup_st_paper`, `R0_le_of_st_paper`,
   `spatial_static_energy_score_sSup_st_paper`.  The auxiliary route lemmas
   `OccupationCeilingFinite.integratedRate_sq_le` and `score_le_ceiling` (no manuscript label)
   are not re-issued.
2. The named input `SpatialBracket.OccupationCeilingK0 α α₀ Γ` (`E:occupation-score-ceiling`,
   `integrated_occupation_ceiling.tex` lines 205-220, with `C_occ` replaced by `K_0 R_sp`).
   `occupationCeilingK0_holds` proves it from `occupation_ceiling_K0_paper_completed`:
   `SpatialBracket.K0` and `OccupationCeilingFinite.K0`, and `SpatialBracket.ceilingValue` and
   `OccupationCeilingFinite.ceilingValue`, are separate constants with the same bodies
   (`K0_eq`, `ceilingValue_eq` by `rfl`).  `spatial_bracket_upper_paper` and
   `intrinsic_spatial_bracket_paper` are re-issued without it.
3. The named input `VariationalRate.S1Bdd α₀ Γ` of `SpatialBracket.spatial_bracket_lower_sSup_paper`
   (the boundedness claim of `P:variational-positive-scores`,
   `integrated_unmasked_variational.tex` lines 272-274), discharged by `s1Bdd_paper_completed`.

4. `uniform_series_tail_terminal_wick_paper`: `L:uniform-series-tail` (main TeX
   `notes/notes_stratonovich_ham_second_moment.tex` lines 3703-3748) with its supplied
   input `UniformSeriesTail.TerminalWickInput` discharged by
   `TerminalWick.terminalWickInput_of_nonneg` (`L:terminal-wick`, lines 3600-3699) for the
   chain integrals of a nonnegative-covariance field; the remaining hypotheses of both
   lemmas stay hypotheses.
5. `freeWaveData_nonempty`: the supplied structure `SymplecticFree.FreeWaveData d E`
   (`notes/integrated_symplectic_phase.tex` lines 103-122) has an instance on
   `E = L²(ℝ^d)` with genuine translations and the trivial group `S_E = I`, `𝓡 = I`
   (non-vacuity only; the free wave group is not constructed).

After this module, the chain `S1Bdd` / ceiling / bracket for `S_c^pos` rests on `H:homog` and
`Γ ≠ 0` alone (no named input).  Every narrowing recorded in the source modules is unchanged:
* the ceiling constant is `K_0 R_sp` (an upper bound of `C_occ`, `P:raw-occupation-energy`,
  `integrated_occupation_ceiling.tex` line 96), not `C_occ`; the class `𝒪`, `A(g)`, `C_occ`,
  `𝓔_ζ^𝒪`, `L:occupation-raw-square`, `P:raw-occupation-energy` and the selection lemma
  `L:occupation-rayleigh-selection` are not formalized;
* the route is the finite partition of unity in time (`OccupationCeilingFinite.exists_near_field`)
  in place of the TeX's countable measurable selection, and `S1Bdd` is proved deterministically
  (the TeX's proof, `integrated_unmasked_variational.tex` lines 309-325, is stochastic);
* the bracket `C:intrinsic-spatial-bracket` is stated for `S_2^pos`, not `C_2`
  (`C_2 = S_2^pos` is `T:intrinsic-second-moment`, decision 4 of wave L8), and its comparison
  uses `energyValue α (K_0 R_sp)` in place of `𝓔_{1/2}^𝒪`; the moment statement `C_2 ≤ U_2` and
  the second form `c^m (2ζ)^{α/(2k)} F_0(𝓔_ζ^𝒪)` of `E:occupation-score-ceiling` are not
  formalized here;
* the direct zero case `Γ = 0` (`integrated_occupation_ceiling.tex` lines 302-307) is not
  formalized: every wrapper carries `Γ ≠ 0`, the section's standing assumption (lines 20-21).
-/
public import Mathlib
public import StratonovichHAMSecondMoment.SpaceTimePositivity
public import StratonovichHAMSecondMoment.OccupationCeilingFinite
public import StratonovichHAMSecondMoment.SpatialBracket
public import StratonovichHAMSecondMoment.TerminalWick
public import StratonovichHAMSecondMoment.UniformSeriesTail
public import StratonovichHAMSecondMoment.SymplecticFree

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory

namespace StratonovichHAMSecondMoment.L8Completed

open HomogHypothesis (Rd HomogCovariance)
open WeakSobolev (IsTestFunction)
open SpatialFourierBound (IsUnitTest)
open VariationalDilation (CPos rawCost integratedRate)
open VariationalRate (S1Bdd S1pos scoreSet)
open SpatialFourLinear (Rsp Esp energyValue F0)
open SpatialSmoothRatio (R0)

variable {d : ℕ}

/-! ### The bridges -/

/-- `SpatialBracket.K0` and `OccupationCeilingFinite.K0` are the same function
(`K_0 = 2^a/(1-a)`, `integrated_occupation_ceiling.tex` line 94); auxiliary to the
integration. -/
theorem K0_eq : SpatialBracket.K0 = OccupationCeilingFinite.K0 := rfl

/-- `SpatialBracket.ceilingValue` and `OccupationCeilingFinite.ceilingValue` are the same
function (`U_c` of `E:occupation-score-ceiling` with a real constant in place of `C_occ`,
`integrated_occupation_ceiling.tex` lines 208-213); auxiliary to the integration. -/
theorem ceilingValue_eq : SpatialBracket.ceilingValue = OccupationCeilingFinite.ceilingValue :=
  rfl

/-- **The named input `OccupationCeilingFinite.SpaceTimeCS α₀ Γ` holds under `H:homog`**
(`Γ ≠ 0` not needed): `SpaceTimePositivity.spaceTimeCS_holds` with its fields, which are
definitionally those of `OccupationCeilingFinite.SpaceTimeCS` (`stFormIter` and
`OccupationCeilingFinite.stForm` have the same body).  Provenance of the three facts:
`L:positive-raw-embedding` (`integrated_intrinsic_constant.tex` lines 22-39) and
`E:occupation-raw-identities` (`integrated_occupation_ceiling.tex` lines 33-37). -/
theorem spaceTimeCS_completed {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) : OccupationCeilingFinite.SpaceTimeCS alpha0 Γ :=
  let h := SpaceTimePositivity.spaceTimeCS_holds hH
  ⟨h.cs, h.self, h.mean⟩

/-! ### `OccupationCeilingFinite` without `SpaceTimeCS` -/

/-- **`T:intrinsic-occupation-ceiling`, `E:occupation-score-ceiling` with `C_occ` replaced by
`K_0 R_sp`** (`integrated_occupation_ceiling.tex` lines 205-220 at a284420), under the
standing assumptions (lines 4-21: `H:homog`, `a = α₀`, `Γ ≠ 0`) alone:
`OccupationCeilingFinite.occupation_ceiling_K0_paper` with `SpaceTimeCS` discharged by
`SpaceTimePositivity` (`spaceTimeCS_completed`).  For every `c > 0` and `Ψ ∈ C_pos`,
`c I_Ψ - v_Ψ/2 ≤ U_c[K_0 R_sp]`.  Narrower as the source: the constant is `K_0 R_sp ≥ C_occ`,
not `C_occ`; finite partition route in place of the countable selection. -/
theorem occupation_ceiling_K0_paper_completed {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ0 : Γ ≠ 0) :
    ∀ c : ℝ, 0 < c → ∀ Ψ ∈ CPos d, c * integratedRate alpha0 Γ Ψ - rawCost alpha0 Γ Ψ / 2 ≤
      OccupationCeilingFinite.ceilingValue alpha c
        (OccupationCeilingFinite.K0 alpha0 * Rsp Γ alpha) :=
  OccupationCeilingFinite.occupation_ceiling_K0_paper hH hΓ0 (spaceTimeCS_completed hH)

/-- **`P:variational-positive-scores`, the boundedness claim `S1Bdd`**
(`integrated_unmasked_variational.tex` lines 272-274 at a284420) under the standing assumptions
(`H:homog`, `Γ ≠ 0`, `a = α₀`) alone: `OccupationCeilingFinite.s1Bdd_paper` with
`SpaceTimeCS` discharged by `SpaceTimePositivity`.  Route difference: deterministic (the ceiling
at `c = 1`), where the TeX's proof (lines 309-325) is stochastic. -/
theorem s1Bdd_paper_completed {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ0 : Γ ≠ 0) : S1Bdd alpha0 Γ :=
  OccupationCeilingFinite.s1Bdd_paper hH hΓ0 (spaceTimeCS_completed hH)

/-- **`T:intrinsic-occupation-ceiling` for the suprema** (`integrated_occupation_ceiling.tex`
lines 209-212 and 245 at a284420) with `C_occ` replaced by `K_0 R_sp`, under the standing
assumptions alone: `OccupationCeilingFinite.occupation_ceiling_sSup_K0_paper` with
`SpaceTimeCS` discharged.  For every `c > 0` the value set is nonempty, bounded above and
`S_c^pos ≤ U_c[K_0 R_sp]`.  Narrower as `occupation_ceiling_K0_paper_completed`. -/
theorem occupation_ceiling_sSup_K0_paper_completed {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ0 : Γ ≠ 0) :
    ∀ c : ℝ, 0 < c → (scoreSet alpha0 Γ c).Nonempty ∧ BddAbove (scoreSet alpha0 Γ c) ∧
      sSup (scoreSet alpha0 Γ c) ≤
        OccupationCeilingFinite.ceilingValue alpha c
          (OccupationCeilingFinite.K0 alpha0 * Rsp Γ alpha) :=
  OccupationCeilingFinite.occupation_ceiling_sSup_K0_paper hH hΓ0 (spaceTimeCS_completed hH)

/-- **`P:variational-positive-scores`, supremum part** (`integrated_unmasked_variational.tex`
lines 272-277 and 327-332 at a284420) under the standing assumptions alone:
`OccupationCeilingFinite.variational_positive_scores_sSup_st_paper` with `SpaceTimeCS`
discharged.  `S_1^pos > 0` and for every `c > 0` the value set is nonempty, bounded above, with
`S_c^pos = c^{(4-α)/(3-α)} S_1^pos > 0`.  Narrower as the source: `Q_2 ≥ S_2^pos` is not
formalized. -/
theorem variational_positive_scores_sSup_st_paper_completed {alpha alpha0 : ℝ}
    {Γ μ : Measure (Rd d)} (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ0 : Γ ≠ 0) :
    0 < S1pos alpha0 Γ ∧
    ∀ c, 0 < c → (scoreSet alpha0 Γ c).Nonempty ∧ BddAbove (scoreSet alpha0 Γ c) ∧
      0 < sSup (scoreSet alpha0 Γ c) ∧
      sSup (scoreSet alpha0 Γ c) = c ^ ((4 - alpha) / (3 - alpha)) * S1pos alpha0 Γ :=
  OccupationCeilingFinite.variational_positive_scores_sSup_st_paper hH hΓ0
    (spaceTimeCS_completed hH)

/-- `E:spatial-static-score` in the `sSup` form (`integrated_spatial_occupation.tex` lines
50-53 at a284420) under the standing assumptions alone:
`OccupationCeilingFinite.spatial_static_score_sSup_st_paper` with `SpaceTimeCS` discharged:
`S_1^pos ≥ λ_z(1) - (M_a/2) B_Γ(z,z)` for every nonnegative nonzero test function `z`. -/
theorem spatial_static_score_sSup_st_paper_completed {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ0 : Γ ≠ 0)
    {z : Rd d → ℝ} (hz : IsTestFunction z) (hz0 : ∀ x, 0 ≤ z x) (hzne : z ≠ 0) :
    SpatialStaticControls.lamZ Γ z 1 - TemporalEquilibrium.mass alpha0 / 2 *
        (OccupationKernelRow.pairing Γ (SpatialStaticControls.zE z)
          (SpatialStaticControls.zE z)).toReal ≤ S1pos alpha0 Γ :=
  OccupationCeilingFinite.spatial_static_score_sSup_st_paper hH hΓ0 (spaceTimeCS_completed hH)
    hz hz0 hzne

/-- `E:spatial-smooth-score` in the `sSup` form (`integrated_spatial_occupation.tex` lines
171-176 at a284420) under the standing assumptions alone:
`OccupationCeilingFinite.spatial_smooth_score_sSup_st_paper` with `SpaceTimeCS` discharged:
`S_1^pos ≥ k [R(g) α^{α/2}/(8 M_a q^{q/2})]^{1/k}` for every real unit test `g`. -/
theorem spatial_smooth_score_sSup_st_paper_completed {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ0 : Γ ≠ 0)
    {g : Rd d → ℝ} (hg : IsUnitTest g) :
    SpatialSmoothRatio.smoothScoreBound alpha alpha0 (SpatialSmoothRatio.ratio Γ alpha g) ≤
      S1pos alpha0 Γ :=
  OccupationCeilingFinite.spatial_smooth_score_sSup_st_paper hH hΓ0 (spaceTimeCS_completed hH) hg

/-- "`S1Bdd ⇒ R_0` finite" (the manuscript's route before revision a284420) under the standing
assumptions alone: `OccupationCeilingFinite.R0_le_of_st_paper` with `SpaceTimeCS` discharged:
the ratio set is bounded above and `R_0 ≤ 8 M_a q^{q/2} (S_1^pos/k)^k / α^{α/2}`. -/
theorem R0_le_of_st_paper_completed {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ0 : Γ ≠ 0) :
    BddAbove (SpatialSmoothRatio.ratioSet Γ alpha) ∧
      R0 Γ alpha ≤ 8 * TemporalEquilibrium.mass alpha0 * (4 - alpha) ^ ((4 - alpha) / 2) *
        (S1pos alpha0 Γ / (3 - alpha)) ^ (3 - alpha) / alpha ^ (alpha / 2) :=
  OccupationCeilingFinite.R0_le_of_st_paper hH hΓ0 (spaceTimeCS_completed hH)

/-- `E:spatial-static-energy-score` in the `sSup` form (`integrated_spatial_occupation.tex`
lines 316-322 at a284420) under the standing assumptions alone:
`OccupationCeilingFinite.spatial_static_energy_score_sSup_st_paper` with `SpaceTimeCS`
discharged: `S_1^pos ≥ M_a^{-1/k} F₀(𝓔_sp)`. -/
theorem spatial_static_energy_score_sSup_st_paper_completed {alpha alpha0 : ℝ}
    {Γ μ : Measure (Rd d)} (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ0 : Γ ≠ 0) :
    TemporalEquilibrium.mass alpha0 ^ (-(1 / (3 - alpha))) * F0 alpha (Esp Γ) ≤
      S1pos alpha0 Γ :=
  OccupationCeilingFinite.spatial_static_energy_score_sSup_st_paper hH hΓ0
    (spaceTimeCS_completed hH)

/-! ### `SpatialBracket` without `OccupationCeilingK0` and `S1Bdd` -/

/-- **The named input `SpatialBracket.OccupationCeilingK0 α α₀ Γ` holds** under the standing
assumptions (`H:homog`, `a = α₀`, `Γ ≠ 0`): it is `occupation_ceiling_K0_paper_completed`
(`K0_eq`, `ceilingValue_eq`).  Narrower as that theorem: `K_0 R_sp` in place of `C_occ`. -/
theorem occupationCeilingK0_holds {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ0 : Γ ≠ 0) :
    SpatialBracket.OccupationCeilingK0 alpha alpha0 Γ :=
  occupation_ceiling_K0_paper_completed hH hΓ0

/-- **Lower half of `E:intrinsic-spatial-bracket` for `S_2^pos`, `sSup` form**
(`integrated_occupation_ceiling.tex` lines 256-260, 271-272 at a284420) under the standing
assumptions alone: `SpatialBracket.spatial_bracket_lower_sSup_paper` with `S1Bdd` discharged by
`s1Bdd_paper_completed`: `2^m M_a^{-1/k} F₀(𝓔_sp) ≤ S_2^pos`.  Narrower: `S_2^pos`, not
`C_2`. -/
theorem spatial_bracket_lower_sSup_paper_completed {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) :
    2 ^ ((4 - alpha) / (3 - alpha)) *
        (TemporalEquilibrium.mass alpha0 ^ (-(1 / (3 - alpha))) * F0 alpha (Esp Γ)) ≤
      sSup (scoreSet alpha0 Γ 2) :=
  SpatialBracket.spatial_bracket_lower_sSup_paper hH hΓ (s1Bdd_paper_completed hH hΓ)

/-- **Upper half of `E:intrinsic-spatial-bracket` for `S_2^pos`**
(`integrated_occupation_ceiling.tex` lines 256-260, 269-271 at a284420) under the standing
assumptions alone: `SpatialBracket.spatial_bracket_upper_paper` with `OccupationCeilingK0`
discharged by `occupationCeilingK0_holds`: the coefficient-two value set is bounded above and
`S_2^pos ≤ 2^m K_0^{1/k} F₀(𝓔_sp)`.  Narrower: `S_2^pos`, not `C_2`; the bound comes from the
ceiling with `K_0 R_sp`. -/
theorem spatial_bracket_upper_paper_completed {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) :
    BddAbove (scoreSet alpha0 Γ 2) ∧
      sSup (scoreSet alpha0 Γ 2) ≤
        2 ^ ((4 - alpha) / (3 - alpha)) * SpatialBracket.K0 alpha0 ^ (1 / (3 - alpha)) *
          F0 alpha (Esp Γ) :=
  SpatialBracket.spatial_bracket_upper_paper hH hΓ (occupationCeilingK0_holds hH hΓ)

/-- **`C:intrinsic-spatial-bracket` for `S_2^pos`** (`integrated_occupation_ceiling.tex` lines
252-300 at a284420) under the section's standing assumptions alone (lines 4-21: `H:homog`,
`a = α₀`, `Γ ≠ 0`): `SpatialBracket.intrinsic_spatial_bracket_paper` with
`OccupationCeilingK0` discharged by `occupationCeilingK0_holds`.  `S1Bdd α₀ Γ`, the
coefficient-two value set is bounded above,
`2^m M_a^{-1/k} F₀(𝓔_sp) ≤ S_2^pos ≤ 2^m K_0^{1/k} F₀(𝓔_sp)`, the comparison
`2^m F₀(E) = 2^m K_0^{1/k} F₀(𝓔_sp)` and `2^m F₀(E) < 2^m F_a(E)` at
`E = energyValue α (K_0 R_sp)`, and `Δ > 0`.  Narrower: `S_2^pos` in place of `C_2` and `E` in
place of `𝓔_{1/2}^𝒪`. -/
theorem intrinsic_spatial_bracket_paper_completed {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) :
    S1Bdd alpha0 Γ ∧ BddAbove (scoreSet alpha0 Γ 2) ∧
      2 ^ ((4 - alpha) / (3 - alpha)) *
          (TemporalEquilibrium.mass alpha0 ^ (-(1 / (3 - alpha))) * F0 alpha (Esp Γ)) ≤
        sSup (scoreSet alpha0 Γ 2) ∧
      sSup (scoreSet alpha0 Γ 2) ≤
        2 ^ ((4 - alpha) / (3 - alpha)) * SpatialBracket.K0 alpha0 ^ (1 / (3 - alpha)) *
          F0 alpha (Esp Γ) ∧
      2 ^ ((4 - alpha) / (3 - alpha)) *
          F0 alpha (energyValue alpha (SpatialBracket.K0 alpha0 * Rsp Γ alpha)) =
        2 ^ ((4 - alpha) / (3 - alpha)) * SpatialBracket.K0 alpha0 ^ (1 / (3 - alpha)) *
          F0 alpha (Esp Γ) ∧
      2 ^ ((4 - alpha) / (3 - alpha)) *
          F0 alpha (energyValue alpha (SpatialBracket.K0 alpha0 * Rsp Γ alpha)) <
        2 ^ ((4 - alpha) / (3 - alpha)) *
          SpatialBracket.Fb alpha alpha0
            (energyValue alpha (SpatialBracket.K0 alpha0 * Rsp Γ alpha)) ∧
      0 < SpatialBracket.logGap alpha alpha0 :=
  SpatialBracket.intrinsic_spatial_bracket_paper hH hΓ (occupationCeilingK0_holds hH hΓ)

/-! ### `L:uniform-series-tail` with the `L:terminal-wick` input discharged -/

/-- **`L:uniform-series-tail` with its `L:terminal-wick` input discharged**
(`notes/notes_stratonovich_ham_second_moment.tex` at revision a284420:
`L:uniform-series-tail`, statement lines 3703-3727, proof lines 3729-3748;
`L:terminal-wick`, statement lines 3600-3645, proof lines 3647-3699).

The regularized terms are the terminal-chain integrals of `L:terminal-wick`,
`Y^{ε,δ}_n = chainIntegral (ν ε δ) (hW ε δ) n`, for a centered real Gaussian field
`W ε δ` on `[0,T] × ℝ^d` with covariance `K ε δ`.  For every `ε, δ > 0` the
supplied structure `UniformSeriesTail.TerminalWickInput` (absolute `L²` convergence of
`Σ r^n Y^{ε,δ}_n` and nonnegative mixed moments) is proved by
`TerminalWick.terminalWickInput_of_nonneg` from `K ε δ ≥ 0`, so
`UniformSeriesTail.uniform_series_tail_paper` applies with its hypothesis `hTW`
discharged.  The conclusions are those of `uniform_series_tail_paper` (absolute
convergence of `Σ X_n`, `u^{ε,δ}(1) → u`, the term and tail bounds of
`E:uniform-series-tail`, absolute convergence of each `Σ Y^{ε,δ}_n`).

Still supplied, as hypotheses: from `L:uniform-series-tail`, `r > 1`, the uniform
bound `E|u^{ε,δ}(r)|² ≤ B` (`hB`) and the fixed-order limits `Y^{ε,δ}_n → X_n` (`hX`);
from `L:terminal-wick`, for `ε, δ > 0`, `d ∈ {1,2,3}`, `T > 0`, `V < ∞` (`hVfin`),
the chain measures with total mass `chainMass d n T` (`hmass`; the measures themselves
are not constructed, see `TerminalWick`), the strong measurability `hmeas`, and the
lemma's standing nonnegative covariance `K ≥ 0` (`hKpos`).  The cell continuity and
the measurability of `K` of `TerminalWick.terminal_wick_paper` are not needed for these
two facts and are not taken.  The chain measures may depend on `(ε, δ)`; the TeX's
fixed `g_n^{T,x}` is the constant case.  The field is given for every real pair
`(ε, δ)` (a Lean device so that `Y` is a total function); only positive pairs enter
the other hypotheses and the conclusions. -/
theorem uniform_series_tail_terminal_wick_paper {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hd : d = 1 ∨ d = 2 ∨ d = 3) (T : ℝ)
    (hT : 0 < T) (W : ℝ → ℝ → TerminalWick.Pt d T → Ω → ℝ)
    (K : ℝ → ℝ → TerminalWick.Pt d T → TerminalWick.Pt d T → ℝ)
    (hW : ∀ ε δ, FiniteWick.CenteredGaussianField (W ε δ) (K ε δ) P)
    (hVfin : ∀ ε δ : ℝ, 0 < ε → 0 < δ → BddAbove (Set.range fun p => K ε δ p p))
    (ν : ℝ → ℝ → ∀ n : ℕ, Measure (Fin n → TerminalWick.Pt d T))
    [∀ ε δ n, IsFiniteMeasure (ν ε δ n)]
    (hmass : ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ n, ν ε δ n Set.univ = TerminalWick.chainMass d n T)
    (hmeas : ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ n,
      AEStronglyMeasurable (fun z : Fin n → TerminalWick.Pt d T => TerminalWick.prodL2 (hW ε δ) z)
        (ν ε δ n))
    (hKpos : ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ p q, 0 ≤ K ε δ p q)
    (X : ℕ → Lp ℝ 2 P) (r B : ℝ) (hr : 1 < r)
    (hB : ∀ ε δ : ℝ, 0 < ε → 0 < δ →
      ∫ ω, ((∑' n, r ^ n • TerminalWick.chainIntegral (ν ε δ) (hW ε δ) n : Lp ℝ 2 P) ω) ^ 2
        ∂P ≤ B)
    (hX : ∀ n, Filter.Tendsto
      (fun p : ℝ × ℝ => TerminalWick.chainIntegral (ν p.1 p.2) (hW p.1 p.2) n)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0) ×ˢ nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (X n))) :
    (Summable fun n => ‖X n‖) ∧
      Filter.Tendsto (fun p : ℝ × ℝ => ∑' n, TerminalWick.chainIntegral (ν p.1 p.2) (hW p.1 p.2) n)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0) ×ˢ nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (∑' n, X n)) ∧
      (∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ n,
        ‖TerminalWick.chainIntegral (ν ε δ) (hW ε δ) n‖ ≤ Real.sqrt B * (r ^ n)⁻¹) ∧
      (∀ n, ‖X n‖ ≤ Real.sqrt B * (r ^ n)⁻¹) ∧
      (∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ N : ℕ,
        ‖∑' n, TerminalWick.chainIntegral (ν ε δ) (hW ε δ) (n + (N + 1))‖ ≤
          Real.sqrt B * (r ^ (N + 1))⁻¹ / (1 - r⁻¹)) ∧
      (∀ N : ℕ, ‖∑' n, X (n + (N + 1))‖ ≤
        Real.sqrt B * (r ^ (N + 1))⁻¹ / (1 - r⁻¹)) ∧
      (∀ ε δ : ℝ, 0 < ε → 0 < δ →
        Summable fun n => ‖TerminalWick.chainIntegral (ν ε δ) (hW ε δ) n‖) := by
  refine UniformSeriesTail.uniform_series_tail_paper
    (fun ε δ n => TerminalWick.chainIntegral (ν ε δ) (hW ε δ) n) X r B hr
    (fun ε δ hε hδ => ?_) hB hX
  have hV : ∀ p, K ε δ p p ≤ ⨆ p, K ε δ p p := fun p => le_ciSup (hVfin ε δ hε hδ) p
  have hV0 := TerminalWick.supVar_nonneg (hW ε δ) hT.le (hVfin ε δ hε hδ)
  have hmassR : ∀ n, (ν ε δ n).real Set.univ = T ^ (2 * n) / (2 * n).factorial := by
    intro n
    rw [measureReal_def, hmass ε δ hε hδ n, TerminalWick.chainMass_eq d hd n T hT.le,
      ENNReal.toReal_ofReal]
    positivity
  exact TerminalWick.terminalWickInput_of_nonneg (ν ε δ) (hW ε δ) _ hV0 hV
    (hmeas ε δ hε hδ) T hmassR (hKpos ε δ hε hδ) r

/-! ### `SymplecticFree.FreeWaveData` is not vacuous -/

/-- Auxiliary (Lean proof route): a real function tends to `0` along a filter if, for
every `ε > 0`, it lies within `ε` of a function that tends to `0`. -/
private theorem tendsto_zero_of_forall_approx {ι : Type*} {l : Filter ι} {F : ι → ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ G : ι → ℝ, Filter.Tendsto G l (nhds 0) ∧ ∀ i, |F i - G i| ≤ ε) :
    Filter.Tendsto F l (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨G, hG, hFG⟩ := h (ε / 2) (by positivity)
  filter_upwards [Metric.tendsto_nhds.mp hG (ε / 2) (by positivity)] with i hi
  rw [Real.dist_eq, sub_zero] at hi ⊢
  calc |F i| = |(F i - G i) + G i| := by ring_nf
    _ ≤ |F i - G i| + |G i| := abs_add_le _ _
    _ < ε := by linarith [hFG i]

/-- The translation `f ↦ f(· - y)` on `L²(ℝ^d)`, as a continuous linear isometry
(auxiliary to `freeWaveData_nonempty`). -/
private def transL2 (d : ℕ) (y : EuclideanSpace ℝ (Fin d)) :
    Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) →L[ℝ]
      Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (fun x => x - y)
    (measurePreserving_sub_right volume y)).toContinuousLinearMap

/-- Auxiliary: every `f ∈ L²(ℝ^d)` is within `η > 0` of a continuous compactly
supported function (Mathlib's `MemLp.exists_hasCompactSupport_eLpNorm_sub_le`). -/
private theorem exists_compact_approx (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    {η : ℝ} (hη : 0 < η) :
    ∃ (g : EuclideanSpace ℝ (Fin d) → ℝ) (hg : MemLp g 2 volume),
      HasCompactSupport g ∧ ‖f - hg.toLp g‖ ≤ η := by
  obtain ⟨g, hgc, hle, -, hg⟩ := (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le
    ENNReal.ofNat_ne_top (ENNReal.ofReal_pos.mpr hη).ne'
  refine ⟨g, hg, hgc, ?_⟩
  have hf : f = (Lp.memLp f).toLp f := (Lp.toLp_coeFn f (Lp.memLp f)).symm
  rw [hf, ← MemLp.toLp_sub, Lp.norm_toLp]
  exact ENNReal.toReal_le_of_le_ofReal hη.le hle

/-- Auxiliary: a compactly supported function vanishes outside a ball. -/
private theorem exists_bound_of_hasCompactSupport {g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hg : HasCompactSupport g) : ∃ R : ℝ, ∀ x, ‖x‖ > R → g x = 0 := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hg.isCompact.isBounded
  refine ⟨R, fun x hx => ?_⟩
  by_contra h
  exact absurd (hR x (subset_tsupport g h)) (not_le.mpr hx)

/-- Auxiliary: translated pairings of compactly supported `L²` functions vanish for
`|y|` large. -/
private theorem inner_transL2_eventually_zero {f g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (hfc : HasCompactSupport f)
    (hgc : HasCompactSupport g) :
    ∀ᶠ y in Filter.cocompact (EuclideanSpace ℝ (Fin d)),
      inner ℝ (transL2 d y (hf.toLp f)) (hg.toLp g) = 0 := by
  obtain ⟨R₁, hR₁⟩ := exists_bound_of_hasCompactSupport hfc
  obtain ⟨R₂, hR₂⟩ := exists_bound_of_hasCompactSupport hgc
  filter_upwards [tendsto_norm_cocompact_atTop.eventually (Filter.eventually_gt_atTop (R₁ + R₂))]
    with y hy
  rw [L2.inner_def]
  refine integral_eq_zero_of_ae ?_
  have h1 : (transL2 d y (hf.toLp f) : EuclideanSpace ℝ (Fin d) → ℝ) =ᵐ[volume]
      fun x => f (x - y) := by
    have := Lp.coeFn_compMeasurePreserving (hf.toLp f) (measurePreserving_sub_right volume y)
    refine this.trans ?_
    exact (measurePreserving_sub_right volume y).quasiMeasurePreserving.ae_eq_comp
      (MemLp.coeFn_toLp hf)
  filter_upwards [h1, MemLp.coeFn_toLp hg] with x hx1 hx2
  rw [hx1, hx2]
  by_cases hx : ‖x‖ > R₂
  · simp [hR₂ x hx]
  · have : ‖x - y‖ > R₁ := by
      have := norm_sub_norm_le y x
      rw [norm_sub_rev] at this
      linarith [not_lt.mp hx]
    simp [hR₁ _ this]

/-- Auxiliary: the translations of `L²(ℝ^d)` are weakly null as `|y| → ∞`, by
density of continuous compactly supported functions. -/
private theorem transL2_weak (z w : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    Filter.Tendsto (fun y => inner ℝ (transL2 d y z) w)
      (Filter.cocompact (EuclideanSpace ℝ (Fin d))) (nhds 0) := by
  have hnorm : ∀ y u, ‖transL2 d y u‖ = ‖u‖ := fun y u =>
    Lp.norm_compMeasurePreserving u (measurePreserving_sub_right volume y)
  -- Step 1: `w` compactly supported, `z` arbitrary.
  have step1 : ∀ (g : EuclideanSpace ℝ (Fin d) → ℝ) (hg : MemLp g 2 volume),
      HasCompactSupport g → ∀ z : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))),
      Filter.Tendsto (fun y => inner ℝ (transL2 d y z) (hg.toLp g))
        (Filter.cocompact (EuclideanSpace ℝ (Fin d))) (nhds 0) := by
    intro g hg hgc z
    refine tendsto_zero_of_forall_approx fun ε hε => ?_
    obtain ⟨f, hf, hfc, hzf⟩ := exists_compact_approx z
      (η := ε / (‖hg.toLp g‖ + 1)) (by positivity)
    refine ⟨fun y => inner ℝ (transL2 d y (hf.toLp f)) (hg.toLp g),
      tendsto_nhds_of_eventually_eq (inner_transL2_eventually_zero hf hg hfc hgc),
      fun y => ?_⟩
    rw [← inner_sub_left, ← map_sub]
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [hnorm]
    calc ‖z - hf.toLp f‖ * ‖hg.toLp g‖ ≤ ε / (‖hg.toLp g‖ + 1) * (‖hg.toLp g‖ + 1) := by
          gcongr; linarith
      _ = ε := by field_simp
  -- Step 2: arbitrary `w`.
  refine tendsto_zero_of_forall_approx fun ε hε => ?_
  obtain ⟨g, hg, hgc, hwg⟩ := exists_compact_approx w
    (η := ε / (‖z‖ + 1)) (by positivity)
  refine ⟨fun y => inner ℝ (transL2 d y z) (hg.toLp g), step1 g hg hgc z, fun y => ?_⟩
  rw [← inner_sub_right]
  refine (abs_real_inner_le_norm _ _).trans ?_
  rw [hnorm]
  calc ‖z‖ * ‖w - hg.toLp g‖ ≤ (‖z‖ + 1) * (ε / (‖z‖ + 1)) := by
        gcongr; linarith [norm_nonneg z]
    _ = ε := by field_simp

/-- **The supplied structure `SymplecticFree.FreeWaveData d E` is not vacuous**: for
every `d` it has an instance on the real Hilbert space `E = L²(ℝ^d)` (Lebesgue measure),
which is not the zero space.  The witness: `S_E(h) = I` for all `h`, `𝓡 = I`, and
`τ_y f = f(· - y)` the genuine spatial translations; they are isometric, commute with
`S_E`, and `⟨τ_y z, w⟩ → 0` as `|y| → ∞` is proved for all `z, w ∈ L²(ℝ^d)` (pairings of
compactly supported functions vanish for large `|y|`; general `z, w` by density of
continuous compactly supported functions, `transL2_weak`).

What this shows: the fields of `FreeWaveData` (the structure that stands for the
objects of `notes/integrated_symplectic_phase.tex` lines 103-122 at revision a284420,
used by `L:symplectic-free`, lines 30-133) are jointly satisfiable on a nonzero space
with translations that are genuinely weakly null, so the theorems taking a
`FreeWaveData` (for example `SymplecticFree.compact_young_baseline`) do not hold
vacuously.  What it does not show: the witness's `S_E` is the trivial group, not the
free wave group on `H^{1/2} × H^{-1/2}`, and `𝓡` is not the velocity reversal; the
concrete instance of the TeX (free wave group, Bessel-norm space, Riemann-Lebesgue
argument of lines 105-110) is not constructed. -/
theorem freeWaveData_nonempty (d : ℕ) :
    Nonempty (SymplecticFree.FreeWaveData d
      (Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))) :=
  ⟨{ S := fun _ => 1
     S_zero := rfl
     S_add := fun _ _ => (mul_one _).symm
     R := 1
     R_norm := fun _ => rfl
     S_neg := fun _ => by simp
     τ := transL2 d
     τ_norm := fun y u => Lp.norm_compMeasurePreserving u (measurePreserving_sub_right volume y)
     τ_comm := fun _ _ => by simp
     τ_weak := fun z w => transL2_weak z w }⟩

end StratonovichHAMSecondMoment.L8Completed
