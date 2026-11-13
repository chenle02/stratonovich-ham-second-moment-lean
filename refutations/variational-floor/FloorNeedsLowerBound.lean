/-
Refutation for (F1) of wave L6, package theorem
`StratonovichHAMSecondMoment.VariationalFloor.dilation_floor` (the dilation
floor behind the positivity in `P:variational-unmasked-rate`,
`notes/integrated_unmasked_variational.tex` lines 150-155 at a284420).

Wrong variant: the hypothesis `V ≥ Γ * z` dropped from the uniform floor,
i.e. one unit trial `(f, g)` and one `ε > 0` with `ε ≤ ∫ V f² - ∫ ‖g‖²` for
EVERY potential `V` with `V f²` integrable.  Counterexample: `V = 0`, whose
Rayleigh value `-∫ ‖g‖²` is `≤ 0`.  Holds in every dimension.  No junk-value
reliance (`0 · f²` is integrable).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.VariationalFloor

set_option autoImplicit false

open MeasureTheory
open StratonovichHAMSecondMoment HomogHypothesis WeakSobolev

namespace Refutations.VariationalFloor

/-- No unit trial has a positive Rayleigh value for every potential. -/
theorem floor_needs_lower_bound_refuted (d : ℕ) :
    ¬ (∃ (f : Rd d → ℝ) (g : Rd d → Rd d) (ε : ℝ), 0 < ε ∧
        ∀ V : Rd d → ℝ, Integrable (fun x => V x * f x ^ 2) volume →
          ε ≤ rayleighValue V f g) := by
  rintro ⟨f, g, ε, hε, h⟩
  have h0 := h 0 (by simp)
  have hg : 0 ≤ ∫ x, ‖g x‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  simp [rayleighValue] at h0
  linarith

end Refutations.VariationalFloor
