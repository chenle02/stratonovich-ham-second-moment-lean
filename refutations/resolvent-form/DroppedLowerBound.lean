/-
Refutation for the lower-bound hypothesis of the formResolvent norm bound (wave L13, item K5b),
package theorem `StratonovichHAMSecondMoment.ResolventForm.norm_resolvent_le`.

Wrong variant: the formResolvent `R = ι S` of every coercive Hermitian form has `‖R‖ ≤ 1`, without
`‖ι u‖² ≤ re B(u,u)` (the form version of `A ≥ 1` in `E:signed-form-domain`, which the
manuscript obtains from `c = 2 + K²`). Counterexample: `V = L = ℂ`, `B(u,w) = ⟪u, w⟫`,
`ι = 2`; the weak solution is `S f = 2 f`, so `R = 4`. Class (b): control of the Lean route (the
hypothesis of the abstract formResolvent lemma; the manuscript's shift supplies it,
`norm_embL2_sq_le_form`). `dropped_lower_bound_contrast` is the package statement.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.ResolventForm

set_option autoImplicit false

namespace Refutations.ResolventForm

open StratonovichHAMSecondMoment.ResolventForm

/-- The identity form on `ℂ` is coercive. -/
theorem coercive_one : IsCoerciveSesq (sesqOf (1 : ℂ →L[ℂ] ℂ)) :=
  ⟨1, one_pos, fun u => by
    rw [sesqOf_apply, show (1 : ℂ →L[ℂ] ℂ) u = u from rfl, inner_self_eq_norm_sq, one_mul, sq]⟩

/-- The identity form on `ℂ` is Hermitian. -/
theorem hermitian_one : IsHermitianForm (sesqOf (1 : ℂ →L[ℂ] ℂ)) :=
  isHermitianForm_sesqOf (IsSelfAdjoint.one (ℂ →L[ℂ] ℂ))

/-- Dropping `‖ι u‖² ≤ re B(u,u)`, the formResolvent can have norm `4`. -/
theorem dropped_lower_bound :
    ¬ ∀ (B : ℂ →L⋆[ℂ] ℂ →L[ℂ] ℂ) (hB : IsCoerciveSesq B) (ι : ℂ →L[ℂ] ℂ),
      IsHermitianForm B → ‖formResolvent hB ι‖ ≤ 1 := by
  intro H
  set ι : ℂ →L[ℂ] ℂ := (2 : ℂ) • (1 : ℂ →L[ℂ] ℂ)
  have hS : (2 : ℂ) • (1 : ℂ) = solOp coercive_one ι 1 :=
    eq_solOp coercive_one ι hermitian_one fun w => by
      simp [ι, sesqOf_apply, map_ofNat]
  have hR : formResolvent coercive_one ι 1 = 4 := by
    change ι (solOp coercive_one ι 1) = 4
    rw [← hS]
    simp [ι]
    norm_num
  have h1 := (formResolvent coercive_one ι).le_opNorm 1
  rw [hR] at h1
  have h2 := H _ coercive_one ι hermitian_one
  norm_num at h1
  linarith

/-- Contrast: with `‖ι u‖² ≤ re B(u,u)` the formResolvent is a contraction. -/
theorem dropped_lower_bound_contrast :
    ∀ (B : ℂ →L⋆[ℂ] ℂ →L[ℂ] ℂ) (hB : IsCoerciveSesq B) (ι : ℂ →L[ℂ] ℂ),
      IsHermitianForm B → (∀ u, ‖ι u‖ ^ 2 ≤ RCLike.re (B u u)) → ‖formResolvent hB ι‖ ≤ 1 :=
  fun _ hB ι hH hlow => norm_resolvent_le hB ι hH hlow

end Refutations.ResolventForm
