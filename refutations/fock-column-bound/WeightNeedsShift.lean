import StratonovichHAMSecondMoment.FockColumnBound

/-!
Refutation for `StratonovichHAMSecondMoment.FockColumnBound.abs_wt_le` (the multiplier
`w_ρ(η) = (ρ² + |η|²)^{-1/2}` of `A_ρ^{-1/2}` is bounded by `ρ^{-1}`, used for
`‖A_ρ^{-1/2}‖ ≤ ρ^{-1}` and the substitution of main TeX lines 3455-3459 at edf7085f).

Wrong variant: drop the shift (`ρ = 0`, the operator `(-Δ)^{-1/2}`) and claim the multiplier is
bounded by some constant.  Counterexample in `d = 1`: at `|η| = 1/(|C| + 1) > 0` the multiplier
is `|C| + 1 > C`.  No junk-value reliance (`η ≠ 0`).  `weight_shift_contrast` is the package
lemma at `ρ = 1`.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.FockColumnBound

open StratonovichHAMSecondMoment.FockColumnBound
open StratonovichHAMSecondMoment.HomogHypothesis (Rd)

/-- Without the shift `ρ² > 0` the multiplier `|η|^{-1}` is unbounded. -/
theorem weight_needs_shift_refuted : ¬ ∃ C : ℝ, ∀ η : Rd 1, |wt 0 η| ≤ C := by
  rintro ⟨C, hC⟩
  have ht : 0 < 1 / (|C| + 1) := by positivity
  have h := hC (EuclideanSpace.single 0 (1 / (|C| + 1)))
  have hn : ‖EuclideanSpace.single (0 : Fin 1) (1 / (|C| + 1))‖ = 1 / (|C| + 1) := by
    rw [EuclideanSpace.norm_eq]
    simp
    exact Real.sqrt_sq (by positivity)
  rw [wt, hn] at h
  norm_num at h
  rw [Real.sqrt_sq (by positivity), abs_of_pos (by positivity)] at h
  linarith [le_abs_self C]

/-- Contrast: the package bound at `ρ = 1`. -/
theorem weight_shift_contrast (η : Rd 1) : |wt 1 η| ≤ 1⁻¹ :=
  abs_wt_le one_pos η

end Refutations.FockColumnBound
