import StratonovichHAMSecondMoment.FockSandwichModel

/-!
Refutation for `StratonovichHAMSecondMoment.FockSandwichModel.abs_symA_le` (the symbol
`|η|² 1_{|η| ≤ b}` of `A_0` is bounded by `b²`; main TeX lines 3025-3026 at edf7085f:
"Boundedness of `-Δ` on `S_b` is explicit").

Wrong variant: drop the band `S_b` and claim the symbol `|η|²` of `-Δ` is bounded.
Counterexample in `d = 1`: at `|η| = |C| + 1` the symbol exceeds `C`.  Class (a):
manuscript-claim perturbation (removing the band cutoff the TeX relies on), in the manuscript
domain.  `symbol_band_contrast` is the package bound.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.FockSandwichModel

open StratonovichHAMSecondMoment.FockSandwichModel
open StratonovichHAMSecondMoment.HomogHypothesis (Rd)

/-- Without the band, `|η|²` is unbounded. -/
theorem symbol_needs_band_refuted : ¬ ∃ C : ℝ, ∀ η : Rd 1, ‖η‖ ^ 2 ≤ C := by
  rintro ⟨C, hC⟩
  have h := hC (EuclideanSpace.single 0 (|C| + 1))
  have hn : ‖EuclideanSpace.single (0 : Fin 1) (|C| + 1)‖ = |C| + 1 := by
    rw [EuclideanSpace.norm_eq]
    simp
    exact Real.sqrt_sq (by positivity)
  rw [hn] at h
  nlinarith [le_abs_self C, abs_nonneg C]

/-- Contrast: the package bound with the band. -/
theorem symbol_band_contrast (b : ℝ) (η : Rd 1) : |symA b η| ≤ b ^ 2 :=
  abs_symA_le b η

end Refutations.FockSandwichModel
