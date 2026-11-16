/-
Refutation for the junk-value convention of `StratonovichHAMSecondMoment.EndpointLemmas
.prodRieszReal`, used by `RieszPositiveDefinite.prodRiesz_mixture` (the product density
`c ∏_j |x_j|^{-e_j}` of main TeX lines 7188-7195 at 39f2597a, infinite on the coordinate
planes for active exponents).

Wrong variant: the Lean density is positive everywhere for `c > 0` (as the TeX density is,
with value `+∞` on the coordinate planes).  Counterexample: at the origin with `e_j = 1/2`
Lean's real power gives `0^{-1/2} = 0`, so the density is `0`.
Class (c): control of Lean's totalized arithmetic (the mixture identity is therefore stated
off the Lebesgue-null coordinate hyperplanes).  `junk_at_origin_contrast` is positivity at
the point `(1, 1, 1)`.  Junk value: `0^{-1/2} = 0`.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.RieszPositiveDefinite

set_option autoImplicit false

namespace Refutations.RieszPositiveDefinite

open StratonovichHAMSecondMoment.EndpointLemmas
open StratonovichHAMSecondMoment.HomogHypothesis (Rd)

/-- The density is positive at `(1, 1, 1)`. -/
theorem junk_at_origin_contrast :
    0 < prodRieszReal 1 (fun _ : Fin 3 => (1 : ℝ) / 2) (WithLp.toLp 2 fun _ => 1) := by
  simp [prodRieszReal]

/-- The Lean density vanishes at the origin (junk value), so it is not positive everywhere. -/
theorem junk_at_origin_refuted :
    ¬ (∀ x : Rd 3, 0 < prodRieszReal 1 (fun _ : Fin 3 => (1 : ℝ) / 2) x) := by
  intro h
  have h0 := h 0
  simp only [prodRieszReal, one_mul] at h0
  rw [Finset.prod_eq_zero (Finset.mem_univ 0) (by simp [Real.zero_rpow])] at h0
  exact lt_irrefl _ h0

end Refutations.RieszPositiveDefinite
