/-
Refutation for the dense-range hypothesis of formResolvent injectivity (wave L13, item K5b), package
theorem `StratonovichHAMSecondMoment.ResolventForm.resolvent_injective`.

Wrong variant: the formResolvent of every coercive Hermitian form is injective, whatever `ι`.
Counterexample: `V = L = ℂ`, `B(u,w) = ⟪u, w⟫`, `ι = 0`; then `R = 0`. Class (b): control of the
Lean route (the hypothesis `(range ι)ᗮ = 0`; for the manuscript's `ι : H^1 → L²` it is proved,
`embL2_sep`). `no_dense_range_contrast` is the package statement.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.ResolventForm

set_option autoImplicit false

namespace Refutations.ResolventForm

open StratonovichHAMSecondMoment.ResolventForm

/-- The identity form on `ℂ` is coercive. -/
theorem coercive_one' : IsCoerciveSesq (sesqOf (1 : ℂ →L[ℂ] ℂ)) :=
  ⟨1, one_pos, fun u => by
    rw [sesqOf_apply, show (1 : ℂ →L[ℂ] ℂ) u = u from rfl, inner_self_eq_norm_sq, one_mul, sq]⟩

/-- Without dense range of `ι` the formResolvent need not be injective. -/
theorem no_dense_range :
    ¬ ∀ (B : ℂ →L⋆[ℂ] ℂ →L[ℂ] ℂ) (hB : IsCoerciveSesq B) (ι : ℂ →L[ℂ] ℂ),
      IsHermitianForm B → Function.Injective (formResolvent hB ι) := by
  intro H
  have h := H _ coercive_one' 0 (isHermitianForm_sesqOf (IsSelfAdjoint.one (ℂ →L[ℂ] ℂ)))
  have e : formResolvent coercive_one' (0 : ℂ →L[ℂ] ℂ) 1 = formResolvent coercive_one' 0 0 := by
    simp [formResolvent]
  exact one_ne_zero (h e)

/-- Contrast: with `(range ι)ᗮ = 0` the formResolvent is injective. -/
theorem no_dense_range_contrast :
    ∀ (B : ℂ →L⋆[ℂ] ℂ →L[ℂ] ℂ) (hB : IsCoerciveSesq B) (ι : ℂ →L[ℂ] ℂ),
      IsHermitianForm B → (∀ f, (∀ u, inner ℂ (ι u) f = 0) → f = 0) →
        Function.Injective (formResolvent hB ι) :=
  fun _ hB ι hH hsep => resolvent_injective hB ι hH hsep

end Refutations.ResolventForm
