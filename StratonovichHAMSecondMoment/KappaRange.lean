/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

`E:kappa` of `notes/notes_stratonovich_ham_second_moment.tex` (manuscript
revision ba01d98): `κ = (4 - α - α₀)/(3 - α) ∈ (1, 2)` under the parameter
part of Hypothesis `H:homog`, namely `d ∈ {1,2,3}`, `0 < α₀ < 1`,
`α₀ + α < 2` (`E:threshold`), and `0 < α < d` or `α = d = 1`.
The covariance-measure part of `H:homog` imposes no constraint on the real
numbers `α, α₀` beyond these and is not represented.
-/
module

public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

namespace StratonovichHAMSecondMoment.KappaRange

/-- The growth exponent `κ = (4 - α - α₀)/(3 - α)` of `E:kappa`. -/
noncomputable def kappa (alpha alpha0 : ℝ) : ℝ := (4 - alpha - alpha0) / (3 - alpha)

/-- `E:kappa`: under the parameter assumptions of Hypothesis `H:homog`,
`1 < κ < 2`. -/
theorem kappa_mem_Ioo (d : ℕ) (alpha alpha0 : ℝ) (hd : d = 1 ∨ d = 2 ∨ d = 3)
    (h0 : 0 < alpha0) (h1 : alpha0 < 1) (hthr : alpha0 + alpha < 2)
    (halpha : (0 < alpha ∧ alpha < d) ∨ (alpha = d ∧ d = 1)) :
    kappa alpha alpha0 ∈ Set.Ioo 1 2 := by
  have hd3 : (d : ℝ) ≤ 3 := by
    rcases hd with rfl | rfl | rfl <;> norm_num
  have h3 : alpha < 3 := by
    rcases halpha with ⟨_, h⟩ | ⟨h, rfl⟩
    · linarith
    · rw [h]; norm_num
  have hpos : (0 : ℝ) < 3 - alpha := by linarith
  unfold kappa
  constructor
  · rw [lt_div_iff₀ hpos]; linarith
  · rw [div_lt_iff₀ hpos]; linarith

end StratonovichHAMSecondMoment.KappaRange
