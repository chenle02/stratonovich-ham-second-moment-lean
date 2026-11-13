import StratonovichHAMSecondMoment.PhaseBessel

/-!
Refutation for `StratonovichHAMSecondMoment.PhaseBessel.phase_bessel`
(manuscript `L:phase-bessel`, display `E:phase-bessel`,
`notes/integrated_wave_variance.tex` 346-355 at a284420): the square on the
left-hand norm cannot be dropped.

The wrong variant is the package statement with `∑ k, ‖x k‖` (exponent `1`)
in place of `∑ k, ‖x k‖²`. Witness: the one-point space `Unit` with the Dirac
measure, `u = 1`, `g = 1/2`: the left side is `1/2`, the right side `1/4`.
`wrong_exponent_contrast` applies the package theorem at the same witness:
`(1/2)² ≤ 1/4`. No junk-value reliance (constant functions on a probability
space).

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

open MeasureTheory

namespace Refutations.PhaseBessel

open StratonovichHAMSecondMoment.PhaseBessel

/-- The witness family `u = 1` is orthonormal for the Dirac measure. -/
private theorem one_orthonormal' :
    IsOrthonormalL2 (Measure.dirac ()) (fun (_ : Fin 1) (_ : Fin 1) (_ : Unit) => (1 : ℂ)) := by
  refine ⟨fun _ _ => memLp_const _, fun k l => ?_⟩
  simp [Subsingleton.elim k l]

/-- Exponent `1` on the left of `E:phase-bessel` is false. -/
theorem wrong_exponent_refuted :
    ¬ (∀ (X : Type) [MeasurableSpace X] (μ : Measure X)
        (u : Fin 1 → Fin 1 → X → ℂ) (g : Fin 1 → X → ℂ),
        IsOrthonormalL2 μ u → (∀ j, MemLp (g j) 2 μ) →
          ∑ k, ‖coeff μ u g k‖ ≤ ∫ η, ∑ j, ‖g j η‖ ^ 2 ∂μ) := by
  intro h
  have h1 := h Unit (Measure.dirac ()) _ (fun _ _ => (1 / 2 : ℂ)) one_orthonormal'
    (fun _ => memLp_const _)
  simp [coeff] at h1
  norm_num at h1

/-- The package theorem at the same witness: `(1/2)² ≤ 1/4`. -/
theorem wrong_exponent_contrast :
    ∑ k, ‖coeff (Measure.dirac ()) (fun (_ : Fin 1) (_ : Fin 1) (_ : Unit) => (1 : ℂ))
        (fun (_ : Fin 1) (_ : Unit) => (1 / 2 : ℂ)) k‖ ^ 2 ≤
      ∫ η, ∑ j : Fin 1, ‖(fun (_ : Fin 1) (_ : Unit) => (1 / 2 : ℂ)) j η‖ ^ 2
        ∂(Measure.dirac ()) :=
  (phase_bessel one_orthonormal' (fun _ => memLp_const _)).2.2

end Refutations.PhaseBessel
