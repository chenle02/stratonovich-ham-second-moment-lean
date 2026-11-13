import StratonovichHAMSecondMoment.PhaseBessel

/-!
Refutation for `StratonovichHAMSecondMoment.PhaseBessel.phase_bessel`
(manuscript `L:phase-bessel`, `notes/integrated_wave_variance.tex` 346-355 at
a284420): orthogonality alone does not suffice; the normalization
`∫ ∑ j, |u k j|² = 1` cannot be dropped.

The wrong variant replaces `IsOrthonormalL2 μ u` by `L²` membership plus
orthogonality (`∫ ∑ j, u k j * conj (u l j) = 0` for `k ≠ l`), keeping the
conclusion of `E:phase-bessel`. Witness: the one-point space `Unit` with the
Dirac measure, one family member `u = 2`, `g = 1`: the left side is `4`, the
right side `1`. `dropped_normalization_contrast` shows that the witness
violates exactly the normalization (`∫ |u|² = 4 ≠ 1`), and applies the package
theorem to the normalized witness `u = 1`. No junk-value reliance (constant
functions on a probability space).

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

open MeasureTheory ComplexConjugate

namespace Refutations.PhaseBessel

open StratonovichHAMSecondMoment.PhaseBessel

/-- Orthonormality without normalization is not enough for `E:phase-bessel`. -/
theorem dropped_normalization_refuted :
    ¬ (∀ (X : Type) [MeasurableSpace X] (μ : Measure X)
        (u : Fin 1 → Fin 1 → X → ℂ) (g : Fin 1 → X → ℂ),
        (∀ k j, MemLp (u k j) 2 μ) →
        (∀ k l, k ≠ l → ∫ η, ∑ j, u k j η * conj (u l j η) ∂μ = 0) →
        (∀ j, MemLp (g j) 2 μ) →
          ∑ k, ‖coeff μ u g k‖ ^ 2 ≤ ∫ η, ∑ j, ‖g j η‖ ^ 2 ∂μ) := by
  intro h
  have h1 := h Unit (Measure.dirac ()) (fun _ _ _ => (2 : ℂ)) (fun _ _ => (1 : ℂ))
    (fun _ _ => memLp_const _)
    (fun k l hkl => absurd (Subsingleton.elim k l) hkl)
    (fun _ => memLp_const _)
  simp [coeff] at h1

/-- The witness violates exactly the normalization, and the package theorem
holds for the normalized witness `u = 1`. -/
theorem dropped_normalization_contrast :
    ∫ η, ∑ j : Fin 1, (fun (_ : Fin 1) (_ : Fin 1) (_ : Unit) => (2 : ℂ)) 0 j η *
        conj ((fun (_ : Fin 1) (_ : Fin 1) (_ : Unit) => (2 : ℂ)) 0 j η)
        ∂(Measure.dirac ()) ≠ 1 ∧
      ∑ k, ‖coeff (Measure.dirac ()) (fun (_ : Fin 1) (_ : Fin 1) (_ : Unit) => (1 : ℂ))
          (fun (_ : Fin 1) (_ : Unit) => (1 : ℂ)) k‖ ^ 2 ≤
        ∫ η, ∑ j : Fin 1, ‖(fun (_ : Fin 1) (_ : Unit) => (1 : ℂ)) j η‖ ^ 2
          ∂(Measure.dirac ()) := by
  refine ⟨?_, (phase_bessel (μ := Measure.dirac ()) (H := ℂ)
    ⟨fun _ _ => memLp_const _, fun k l => by simp [Subsingleton.elim k l]⟩
    (fun _ => memLp_const _)).2.2⟩
  simp only [integral_dirac, Finset.univ_unique, Finset.sum_singleton, map_ofNat]
  norm_num

end Refutations.PhaseBessel
