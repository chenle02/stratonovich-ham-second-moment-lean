/-
Refutation for a dropped hypothesis of the strict comparison in
`StratonovichHAMSecondMoment.OccupationCeilingExact.intrinsic_spatial_comparison_paper`
(`S_2^pos ≤ 2^m F_0(𝓔_{1/2}^𝒪) < 2^m F_a(𝓔_{1/2}^𝒪)`,
`notes/integrated_occupation_ceiling.tex` lines 261-265 and 275-290 at a284420, which uses
`a > 0`, line 280), at the scalar step `SpatialBracket.F0_lt_Fa` it applies.

Wrong variant: `a ≥ 0` in place of `a > 0` in `F_0(z) < F_a(z)`.  Counterexample: `a = 0`
(`F_0 = F_0`), `α = 1`, `z = 1`.  `comparison_contrast` is the package inequality at `a = 1/2`,
same `α`, `z`.  No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.OccupationCeilingExact

set_option autoImplicit false

namespace Refutations.OccupationCeilingExact

open StratonovichHAMSecondMoment

/-- The strict comparison `F_0 < F_a` fails at `a = 0`. -/
theorem comparison_needs_a_refuted :
    ¬ (∀ alpha a z : ℝ, alpha < 2 → 0 ≤ a → 0 < 4 - alpha - 2 * a → 0 < z →
        SpatialFourLinear.F0 alpha z < SpatialBracket.Fb alpha a z) := by
  intro h
  have h1 := h 1 0 1 (by norm_num) le_rfl (by norm_num) one_pos
  rw [SpatialBracket.Fb_zero_eq_F0 (by norm_num)] at h1
  exact lt_irrefl _ h1

/-- The package inequality at `a = 1/2`. -/
theorem comparison_contrast :
    SpatialFourLinear.F0 1 1 < SpatialBracket.Fb 1 (1 / 2) 1 :=
  SpatialBracket.F0_lt_Fa (by norm_num) (by norm_num) (by norm_num) one_pos

end Refutations.OccupationCeilingExact
