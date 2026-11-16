/-
Refutation for `StratonovichHAMSecondMoment.RieszPositiveDefinite.prod_mixture` and
`riesz_mixture` (the Gaussian mixtures of main TeX lines 7255-7260, 7975-7978 at 39f2597a):
the Lean mixture identities hold only off the null sets `{u = 0}` (coordinate hyperplanes,
resp. the origin), and are stated almost everywhere.

Wrong variant: the one-dimensional mixture `ofReal |u|^{-1/2} = ∫ e^{-su²} mixOne (1/2) (ds)`
for every `u`, including `u = 0`.  At `u = 0` Lean's real power gives `|0|^{-1/2} = 0`, while
the mixture is the total mass of `mixOne (1/2)`, which is nonzero.
Class (b): Lean-route-only control (the a.e. form of the mixture identities is needed).
`mixture_at_zero_contrast` is the identity at `u = 1`.  Junk value: `0^{-1/2} = 0`.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.RieszPositiveDefinite

set_option autoImplicit false

namespace Refutations.RieszPositiveDefinite

open MeasureTheory Set Real StratonovichHAMSecondMoment.RieszPositiveDefinite

/-- The mixture identity at `u = 1`. -/
theorem mixture_at_zero_contrast :
    ENNReal.ofReal (|(1 : ℝ)| ^ (-((1 : ℝ) / 2))) =
      ∫⁻ s, ENNReal.ofReal (Real.exp (-s * (1 : ℝ) ^ 2)) ∂mixOne (1 / 2) := by
  obtain ⟨hI, hv⟩ := mixOne_spec (e := 1 / 2) (by norm_num) one_ne_zero
  rw [← hv, ofReal_integral_eq_lintegral_ofReal hI
    (ae_of_all _ fun _ => (Real.exp_pos _).le)]

/-- The mixture identity fails at `u = 0` (it holds only almost everywhere). -/
theorem mixture_at_zero_refuted :
    ¬ (∀ u : ℝ, ENNReal.ofReal (|u| ^ (-((1 : ℝ) / 2))) =
      ∫⁻ s, ENNReal.ofReal (Real.exp (-s * u ^ 2)) ∂mixOne (1 / 2)) := by
  intro h
  have h0 := h 0
  have hone : (fun s : ℝ => ENNReal.ofReal (Real.exp (-s * (0 : ℝ) ^ 2))) = fun _ => 1 := by
    funext s; simp
  rw [hone, lintegral_const, one_mul, abs_zero, Real.zero_rpow (by norm_num),
    ENNReal.ofReal_zero] at h0
  -- the mixing measure is nonzero: its integral of `e^{-s}` is `1`
  obtain ⟨-, hv⟩ := mixOne_spec (e := 1 / 2) (by norm_num) one_ne_zero
  have hne : mixOne (1 / 2) ≠ 0 := by
    intro hz
    rw [hz, integral_zero_measure] at hv
    norm_num at hv
  exact hne (Measure.measure_univ_eq_zero.1 h0.symm)

end Refutations.RieszPositiveDefinite
