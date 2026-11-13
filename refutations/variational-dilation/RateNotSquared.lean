/-
Refutation for the rate part of `L:variational-control-dilation`
(`notes/integrated_unmasked_variational.tex` lines 234-236 and 260-266),
package theorem `StratonovichHAMSecondMoment.WeakSobolev.rayleighRate_dil`
(which gives `VariationalDilation.rate_dil`) and package definitions
`rayleighRate`, `rayleighSet`, `IsRayleighTrial`, `HasWeakGradient`.

Wrong variant: `λ_{D_rΨ,s} = r² λ_{Ψ,s}` (confusing the rate with its square;
the Rayleigh supremum scales by `r²`, the rate by `r`).  Counterexample in
`d = 0`, where `ℝ^0` is a point of volume one: for the constant potential
`V ≡ 1` every trial has value `1` and the trial `f ≡ 1`, `g ≡ 0` exists, so
the Rayleigh set is `{1}` and the rate is `1` (no junk value: the set is
nonempty and bounded); the dilated potential `4·V(2·) ≡ 4` has rate `2`, not
`4`.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.VariationalDilation

set_option autoImplicit false

open MeasureTheory

namespace Refutations.VariationalDilation.Rate

open StratonovichHAMSecondMoment.WeakSobolev
open StratonovichHAMSecondMoment.HomogHypothesis (Rd)

theorem volume_univ_Rd0 : (volume : Measure (Rd 0)) Set.univ = 1 := by
  have h := (PiLp.volume_preserving_ofLp (ι := Fin 0)).measure_preimage
    (s := Set.univ) MeasurableSet.univ.nullMeasurableSet
  rw [Set.preimage_univ] at h
  rw [h, MeasureTheory.volume_pi, Measure.pi_univ]
  simp

instance : IsFiniteMeasure (volume : Measure (Rd 0)) :=
  ⟨by rw [volume_univ_Rd0]; exact ENNReal.one_lt_top⟩

/-- The Rayleigh set of the constant potential `1` on `ℝ^0` is `{1}`. -/
theorem rayleighSet_one : rayleighSet (fun _ : Rd 0 => (1 : ℝ)) = {1} := by
  ext q
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨f, g, hT, rfl⟩
    have hg : ∀ x, ‖g x‖ ^ 2 = 0 := fun x => by rw [Subsingleton.elim (g x) 0]; simp
    simp only [rayleighValue, one_mul, hg, integral_zero, sub_zero]
    exact hT.unit
  · rintro rfl
    refine ⟨fun _ => 1, 0, ⟨memLp_const 1, MeasureTheory.MemLp.zero, ?_, ?_, ?_⟩, ?_⟩
    · intro φ _ v
      rw [Subsingleton.elim v 0]
      simp
    · simp [measureReal_def, volume_univ_Rd0]
    · exact integrable_const _
    · simp [rayleighValue, measureReal_def, volume_univ_Rd0]

theorem rayleighRate_one : rayleighRate (fun _ : Rd 0 => (1 : ℝ)) = 1 := by
  simp [rayleighRate, rayleighSet_one]

/-- The wrong scaling `r²` of the rate fails. -/
theorem rate_squared_false :
    ¬ ∀ (d : ℕ) (V : Rd d → ℝ) (r : ℝ), 0 < r →
      rayleighRate (fun x => r ^ 2 * V (r • x)) = r ^ 2 * rayleighRate V := by
  intro h
  have hw := h 0 (fun _ => 1) 2 two_pos
  have hp := rayleighRate_dil (fun _ : Rd 0 => (1 : ℝ)) two_pos
  rw [hp, rayleighRate_one] at hw
  norm_num at hw

/-- Contrast: the package scaling at the same potential gives `2`. -/
theorem rate_linear_contrast :
    rayleighRate (fun x : Rd 0 => (2 : ℝ) ^ 2 * (fun _ : Rd 0 => (1 : ℝ)) ((2 : ℝ) • x)) = 2 := by
  rw [rayleighRate_dil (fun _ : Rd 0 => (1 : ℝ)) two_pos, rayleighRate_one, mul_one]

end Refutations.VariationalDilation.Rate
