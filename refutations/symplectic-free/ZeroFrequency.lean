/-
Refutation for the frequency-zero value of the free matrix,
`StratonovichHAMSecondMoment.SymplecticFree.freeMatrixAt_zero`
(`W_t(0) = (1 t; 0 1)`; `L:symplectic-free`, `notes/integrated_symplectic_phase.tex`
line 78 at a284420).

Wrong variant: the frequency-zero matrix is the identity, which is what the B22
formula `forward (cos 0) (sin 0) (0/1)` gives through the junk value `0/0 = 0` of the
sine quotient.  Counterexample: `t = 1`, entry `(0,1)` is `1`, not `0`.
`zero_frequency_contrast` is the package value at `t = 1`, `d = 1`.
Junk-value reliance: the wrong variant is the junk-value reading; the refutation
itself uses none.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SymplecticFree

set_option autoImplicit false

namespace Refutations.SymplecticFree

open StratonovichHAMSecondMoment.SymplecticFree

/-- The free matrix at frequency zero is not the identity. -/
theorem zero_frequency_refuted :
    ¬ (∀ t : ℝ, freeMatrixAt t (0 : EuclideanSpace ℝ (Fin 1)) = 1) := by
  intro h
  have := congrFun (congrFun (h 1) 0) 1
  simp [freeMatrixAt_zero] at this

/-- The package value at `t = 1`. -/
theorem zero_frequency_contrast :
    freeMatrixAt 1 (0 : EuclideanSpace ℝ (Fin 1)) = !![1, 1; 0, 1] :=
  freeMatrixAt_zero 1

end Refutations.SymplecticFree
