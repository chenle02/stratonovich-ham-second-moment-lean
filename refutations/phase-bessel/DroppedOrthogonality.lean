import StratonovichHAMSecondMoment.PhaseBessel

/-!
Refutation for `StratonovichHAMSecondMoment.PhaseBessel.phase_bessel`
(manuscript `L:phase-bessel`, `notes/integrated_wave_variance.tex` 346-355 at
a284420): normalization alone does not suffice; orthogonality cannot be
dropped.

The wrong variant replaces `IsOrthonormalL2 μ u` by `L²` membership plus
normalization (`∫ ∑ j, |u k j|² = 1` for every `k`), keeping the conclusion of
`E:phase-bessel`. Witness: the one-point space `Unit` with the Dirac measure,
two equal family members `u 0 = u 1 = 1`, `g = 1`: the left side is `2`, the
right side `1`. `dropped_orthogonality_contrast` shows that the witness
violates exactly orthogonality (the off-diagonal integral is `1 ≠ 0`), and
applies the package theorem to the one-member subfamily, which is orthonormal.
No junk-value reliance (constant functions on a probability space).

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

open MeasureTheory ComplexConjugate

namespace Refutations.PhaseBessel

open StratonovichHAMSecondMoment.PhaseBessel

/-- Normalized but non-orthogonal families violate `E:phase-bessel`. -/
theorem dropped_orthogonality_refuted :
    ¬ (∀ (X : Type) [MeasurableSpace X] (μ : Measure X)
        (u : Fin 2 → Fin 1 → X → ℂ) (g : Fin 1 → X → ℂ),
        (∀ k j, MemLp (u k j) 2 μ) →
        (∀ k, ∫ η, ∑ j, u k j η * conj (u k j η) ∂μ = 1) →
        (∀ j, MemLp (g j) 2 μ) →
          ∑ k, ‖coeff μ u g k‖ ^ 2 ≤ ∫ η, ∑ j, ‖g j η‖ ^ 2 ∂μ) := by
  intro h
  have h1 := h Unit (Measure.dirac ()) (fun _ _ _ => (1 : ℂ)) (fun _ _ => (1 : ℂ))
    (fun _ _ => memLp_const _) (fun _ => by simp) (fun _ => memLp_const _)
  simp [coeff] at h1

/-- The witness violates exactly orthogonality, and the package theorem holds
for its one-member subfamily. -/
theorem dropped_orthogonality_contrast :
    ∫ η, ∑ j : Fin 1, (fun (_ : Fin 2) (_ : Fin 1) (_ : Unit) => (1 : ℂ)) 0 j η *
        conj ((fun (_ : Fin 2) (_ : Fin 1) (_ : Unit) => (1 : ℂ)) 1 j η)
        ∂(Measure.dirac ()) ≠ 0 ∧
      ∑ k, ‖coeff (Measure.dirac ()) (fun (_ : Fin 1) (_ : Fin 1) (_ : Unit) => (1 : ℂ))
          (fun (_ : Fin 1) (_ : Unit) => (1 : ℂ)) k‖ ^ 2 ≤
        ∫ η, ∑ j : Fin 1, ‖(fun (_ : Fin 1) (_ : Unit) => (1 : ℂ)) j η‖ ^ 2
          ∂(Measure.dirac ()) := by
  refine ⟨?_, (phase_bessel (μ := Measure.dirac ()) (H := ℂ)
    ⟨fun _ _ => memLp_const _, fun k l => by simp [Subsingleton.elim k l]⟩
    (fun _ => memLp_const _)).2.2⟩
  simp

end Refutations.PhaseBessel
