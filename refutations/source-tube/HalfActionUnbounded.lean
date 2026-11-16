/-
Refutation for `L:tube-half-action`
(`notes/integrated_gaussian_tubes.tex` lines 581-597 at 39f2597a), package
theorem `StratonovichHAMSecondMoment.SourceTube.tube_half_action`.

Class (c): control of Lean's totalized arithmetic outside the manuscript domain.
Wrong variant: the identity without "bounded above on every ball".  In the
TeX the hypothesis makes `g_J(r)` finite; for an unbounded `J` the extended
supremum would be `+∞` and the identity would survive, but the Lean
`ballSup` is the real `sSup`, which is `0` on unbounded sets.
Counterexample: `H = ℝ`, `J(h) = 1/h` (`J(0) = 0` in Lean): `ballSup J r = 0`
for every `r ≥ 0`, so the left side is `≤ 0`, while the right side is
`≥ J(1/4) - 1/32 = 4 - 1/32`.  This shows the hypothesis is load-bearing in Lean.
`unbounded_contrast` is the package identity for the bounded `J(h) = h`.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SourceTube

set_option autoImplicit false

open StratonovichHAMSecondMoment SourceTube

namespace Refutations.SourceTube

/-- Calibration: `h ↦ 1/h` is not bounded above on any ball of positive radius. -/
theorem unbounded_not_bdd {r : ℝ} (hr : 0 < r) :
    ¬ BddAbove ((fun h : ℝ => 1 / h) '' Metric.closedBall (0 : ℝ) r) := by
  rintro ⟨b, hb⟩
  set h : ℝ := r / (1 + r * |b|)
  have hden : 0 < 1 + r * |b| := by positivity
  have hpos : 0 < h := div_pos hr hden
  have hle : h ≤ r := div_le_self hr.le (by nlinarith [abs_nonneg b])
  have hmem : h ∈ Metric.closedBall (0 : ℝ) r := by
    rw [mem_closedBall_zero_iff, Real.norm_eq_abs, abs_of_pos hpos]
    exact hle
  have : 1 / h ≤ b := hb ⟨h, hmem, rfl⟩
  have hval : 1 / h = 1 / r + |b| := by
    simp only [h, one_div_div]
    field_simp
  rw [hval] at this
  have h1 : 0 < 1 / r := by positivity
  linarith [le_abs_self b]

/-- Calibration: `ballSup (1/h) r = 0` for `r ≥ 0` (Lean's `sSup`). -/
theorem unbounded_ballSup {r : ℝ} (hr : 0 ≤ r) : ballSup (fun h : ℝ => 1 / h) r = 0 := by
  rcases hr.eq_or_lt with h0 | hpos
  · subst h0
    simp [ballSup]
  · exact Real.sSup_of_not_bddAbove (unbounded_not_bdd hpos)

/-- The identity without the boundedness hypothesis is false in Lean. -/
theorem unbounded_refuted :
    ¬ (∀ J : ℝ → ℝ,
        (⨆ (r : ℝ) (_ : 0 ≤ r), ((ballSup J r - r ^ 2 / 2 : ℝ) : EReal)) =
          ⨆ h : ℝ, ((J h - ‖h‖ ^ 2 / 2 : ℝ) : EReal)) := by
  intro hall
  have heq := hall (fun h => 1 / h)
  have hl : (⨆ (r : ℝ) (_ : 0 ≤ r),
      ((ballSup (fun h : ℝ => 1 / h) r - r ^ 2 / 2 : ℝ) : EReal)) ≤ ((0 : ℝ) : EReal) := by
    refine iSup₂_le fun r hr => ?_
    rw [EReal.coe_le_coe_iff, unbounded_ballSup hr]
    nlinarith [sq_nonneg r]
  have hr : ((4 - 1 / 32 : ℝ) : EReal) ≤
      ⨆ h : ℝ, (((fun h : ℝ => 1 / h) h - ‖h‖ ^ 2 / 2 : ℝ) : EReal) :=
    le_iSup_of_le (1 / 4 : ℝ) (by rw [EReal.coe_le_coe_iff]; norm_num [Real.norm_eq_abs])
  rw [← heq] at hr
  have := hr.trans hl
  rw [EReal.coe_le_coe_iff] at this
  norm_num at this

/-- The package identity for the bounded `J(h) = h`. -/
theorem unbounded_contrast :
    (⨆ (r : ℝ) (_ : 0 ≤ r), ((ballSup (fun h : ℝ => h) r - r ^ 2 / 2 : ℝ) : EReal)) =
      ⨆ h : ℝ, (((fun h : ℝ => h) h - ‖h‖ ^ 2 / 2 : ℝ) : EReal) :=
  tube_half_action (fun h : ℝ => h) fun r _ => ⟨r, by
    rintro _ ⟨h, hh, rfl⟩
    exact (le_abs_self h).trans (by simpa [Real.norm_eq_abs] using hh)⟩

end Refutations.SourceTube
