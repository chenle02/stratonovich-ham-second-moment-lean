import StratonovichHAMSecondMoment.PhaseBessel

/-!
Refutation for `StratonovichHAMSecondMoment.PhaseBessel.phase_bessel`
(manuscript `L:phase-bessel`, display `E:phase-bessel`,
`notes/integrated_wave_variance.tex` 346-355 at a284420): the constant `1` on
the right-hand side cannot be lowered to `1/2`.

The wrong variant is the package statement (orthonormal `u`, `L²` data `g`)
with `1/2` in front of `∫ ∑ j, ‖g j‖²`, quantified over all measure spaces and
scalar data (`H = ℂ`, one family member, one component). Witness: the one-point
space `Unit` with the Dirac measure, `u = 1`, `g = 1`; both sides of
`E:phase-bessel` equal `1`, so the bound is attained (sharp).
`wrong_constant_contrast` applies the package theorem at the same witness.
No junk-value reliance: every function is constant on a probability space, so
all integrands are integrable.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

open MeasureTheory

namespace Refutations.PhaseBessel

open StratonovichHAMSecondMoment.PhaseBessel

/-- The witness family `u = 1` is orthonormal for the Dirac measure. -/
private theorem one_orthonormal :
    IsOrthonormalL2 (Measure.dirac ()) (fun (_ : Fin 1) (_ : Fin 1) (_ : Unit) => (1 : ℂ)) := by
  refine ⟨fun _ _ => memLp_const _, fun k l => ?_⟩
  simp [Subsingleton.elim k l]

/-- The `L²` component `g = 1`. -/
private theorem one_memLp :
    ∀ j : Fin 1, MemLp ((fun (_ : Fin 1) (_ : Unit) => (1 : ℂ)) j) 2 (Measure.dirac ()) :=
  fun _ => memLp_const _

/-- Halving the right-hand side of `E:phase-bessel` is false. -/
theorem wrong_constant_refuted :
    ¬ (∀ (X : Type) [MeasurableSpace X] (μ : Measure X)
        (u : Fin 1 → Fin 1 → X → ℂ) (g : Fin 1 → X → ℂ),
        IsOrthonormalL2 μ u → (∀ j, MemLp (g j) 2 μ) →
          ∑ k, ‖coeff μ u g k‖ ^ 2 ≤ (1 / 2) * ∫ η, ∑ j, ‖g j η‖ ^ 2 ∂μ) := by
  intro h
  have h1 := h Unit (Measure.dirac ()) _ _ one_orthonormal one_memLp
  simp [coeff] at h1
  norm_num at h1

/-- The package theorem at the same witness: `1 ≤ 1`. -/
theorem wrong_constant_contrast :
    ∑ k, ‖coeff (Measure.dirac ()) (fun (_ : Fin 1) (_ : Fin 1) (_ : Unit) => (1 : ℂ))
        (fun (_ : Fin 1) (_ : Unit) => (1 : ℂ)) k‖ ^ 2 ≤
      ∫ η, ∑ j : Fin 1, ‖(fun (_ : Fin 1) (_ : Unit) => (1 : ℂ)) j η‖ ^ 2 ∂(Measure.dirac ()) :=
  (phase_bessel one_orthonormal one_memLp).2.2

end Refutations.PhaseBessel
