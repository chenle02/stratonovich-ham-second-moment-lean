/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

`E:driver-parameters` of `notes/integrated_actual_operator_driver.tex`
(manuscript revision ba01d98): "The strict intervals are nonempty."
The section retains Hypothesis `H:homog` and sets `a = α₀`; its parameter part
is `d ∈ {1,2,3}`, `0 < a < 1`, `a + α < 2`, and `0 < α < d` or `α = d = 1`.
-/
module

public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

namespace StratonovichHAMSecondMoment.DriverParameters

/-- The parameter part of Hypothesis `H:homog`, with `a = α₀`. -/
def Homog (d : ℕ) (alpha a : ℝ) : Prop :=
  (d = 1 ∨ d = 2 ∨ d = 3) ∧ 0 < a ∧ a < 1 ∧ a + alpha < 2 ∧
    ((0 < alpha ∧ alpha < d) ∨ (alpha = d ∧ d = 1))

/-- The `γ`-interval `0 < γ < min(1/2, (2-α)/2)` is nonempty. -/
theorem gamma_interval_nonempty (d : ℕ) (alpha a : ℝ) (h : Homog d alpha a) :
    ∃ γ : ℝ, 0 < γ ∧ γ < min (1 / 2) ((2 - alpha) / 2) := by
  obtain ⟨-, ha0, -, hthr, -⟩ := h
  have hm : 0 < min (1 / 2 : ℝ) ((2 - alpha) / 2) :=
    lt_min (by norm_num) (by linarith)
  exact ⟨min (1 / 2) ((2 - alpha) / 2) / 2, by linarith, by linarith⟩

/-- The `(θ, β)`-interval `1/2 < θ < β < min(1 - a/2, (3-a-α)/2)` is nonempty. -/
theorem theta_beta_interval_nonempty (d : ℕ) (alpha a : ℝ) (h : Homog d alpha a) :
    ∃ θ β : ℝ, 1 / 2 < θ ∧ θ < β ∧ β < min (1 - a / 2) ((3 - a - alpha) / 2) := by
  obtain ⟨-, -, ha1, hthr, -⟩ := h
  set m := min (1 - a / 2) ((3 - a - alpha) / 2) with hm
  have hm' : 1 / 2 < m := lt_min (by linarith) (by linarith)
  exact ⟨1 / 2 + (m - 1 / 2) / 3, 1 / 2 + 2 * (m - 1 / 2) / 3,
    by linarith, by linarith, by linarith⟩

/-- `E:driver-parameters`: "The strict intervals are nonempty", i.e. there are
`γ, θ, β` with `0 < γ < min(1/2, (2-α)/2)` and
`1/2 < θ < β < min(1 - a/2, (3-a-α)/2)`. -/
theorem parameters_nonempty (d : ℕ) (alpha a : ℝ) (h : Homog d alpha a) :
    ∃ γ θ β : ℝ, (0 < γ ∧ γ < min (1 / 2) ((2 - alpha) / 2)) ∧
      (1 / 2 < θ ∧ θ < β ∧ β < min (1 - a / 2) ((3 - a - alpha) / 2)) := by
  obtain ⟨γ, hγ⟩ := gamma_interval_nonempty d alpha a h
  obtain ⟨θ, β, hθβ⟩ := theta_beta_interval_nonempty d alpha a h
  exact ⟨γ, θ, β, hγ, hθβ⟩

end StratonovichHAMSecondMoment.DriverParameters
