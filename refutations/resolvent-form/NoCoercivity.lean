/-
Refutation for the coercivity hypothesis of the complex Lax-Milgram theorem (wave L13, item K5b),
package declarations `StratonovichHAMSecondMoment.ResolventForm.IsCoerciveSesq.equiv` and
`IsCoerciveSesq.range_eq_top`.

Wrong variant: a bounded Hermitian sesquilinear form with nonnegative diagonal (no coercivity)
already has a surjective Riesz map `B♯`. Counterexample: `V = ℂ`, `B = 0`; then `B♯ = 0` misses
`1`. Class (b): control of the Lean route (the coercivity hypothesis of the ported theorem; the
manuscript's form `q_V + c` is coercive by `E:signed-form-bounds`). `no_coercivity_contrast` is
the package statement with coercivity.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.ResolventForm

set_option autoImplicit false

namespace Refutations.ResolventForm

open StratonovichHAMSecondMoment.ResolventForm InnerProductSpace

/-- Hermitian with nonnegative diagonal is not enough for a surjective Riesz map. -/
theorem no_coercivity :
    ¬ ∀ B : ℂ →L⋆[ℂ] ℂ →L[ℂ] ℂ, IsHermitianForm B → (∀ u, 0 ≤ RCLike.re (B u u)) →
      Function.Surjective (continuousLinearMapOfBilin B) := by
  intro H
  obtain ⟨v, hv⟩ := H 0 (fun u w => by simp) (fun u => by simp) 1
  have h0 : continuousLinearMapOfBilin (0 : ℂ →L⋆[ℂ] ℂ →L[ℂ] ℂ) v = 0 := by
    simp [continuousLinearMapOfBilin]
  rw [h0] at hv
  exact zero_ne_one hv

/-- Contrast: a coercive form has a surjective Riesz map (Lax-Milgram over `RCLike`). -/
theorem no_coercivity_contrast :
    ∀ B : ℂ →L⋆[ℂ] ℂ →L[ℂ] ℂ, IsCoerciveSesq B →
      Function.Surjective (continuousLinearMapOfBilin B) :=
  fun _ h => LinearMap.range_eq_top.mp h.range_eq_top

end Refutations.ResolventForm
