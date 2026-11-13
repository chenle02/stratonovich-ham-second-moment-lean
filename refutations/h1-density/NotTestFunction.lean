/-
Refutation for the density theorem of `H1Density`, package theorem
`StratonovichHAMSecondMoment.H1Density.h1TestDense` (density of `C_c^∞` in
the weak-gradient `H^1`; `notes/integrated_spatial_occupation.tex`, proof of
`P:spatial-four-linear`, lines 262-266 at a284420).

Wrong variant: no approximation is needed because every `H^1` function is
itself a test function (equivalently, the constant sequence `φ n = f` would
always do).  Counterexample in `d = 1`: the indicator `f` of the origin is
`0` almost everywhere, so `f ∈ L²` with weak gradient `0`, but `f` is not
continuous (a continuous function a.e. equal to `0` is `0`, while
`f(0) = 1`), hence not a test function.  The statement of `h1TestDense` is
about `L²` classes, which is why it needs approximation.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.H1Density

set_option autoImplicit false

open MeasureTheory Filter Topology StratonovichHAMSecondMoment

namespace Refutations.H1Density

/-- Not every `H^1` function is a test function (`d = 1`). -/
theorem not_test_function_refuted :
    ¬ (∀ (f : HomogHypothesis.Rd 1 → ℝ) (g : HomogHypothesis.Rd 1 → HomogHypothesis.Rd 1),
        MemLp f 2 volume → MemLp g 2 volume → WeakSobolev.HasWeakGradient f g →
        WeakSobolev.IsTestFunction f) := by
  intro h
  set f : HomogHypothesis.Rd 1 → ℝ := fun x => if x = 0 then 1 else 0 with hf
  have hae : f =ᵐ[volume] 0 := by
    have hs : (volume : Measure (HomogHypothesis.Rd 1)) {0} = 0 := measure_singleton 0
    refine (measure_eq_zero_iff_ae_notMem.mp hs).mono fun x hx => ?_
    simp only [Set.mem_singleton_iff] at hx
    simp [hf, hx]
  have hfL : MemLp f 2 volume := (memLp_congr_ae hae).mpr MemLp.zero
  have hw : WeakSobolev.HasWeakGradient f 0 := by
    intro ψ _ v
    have : (∫ x, f x * fderiv ℝ ψ x v) = ∫ _ : HomogHypothesis.Rd 1, (0 : ℝ) :=
      integral_congr_ae (hae.mono fun x hx => by simp [hx])
    rw [this]; simp
  have ht := h f 0 hfL MemLp.zero hw
  have hall : f = 0 := (ht.1.continuous.ae_eq_iff_eq volume continuous_const).mp hae
  have := congrFun hall 0
  simp [hf] at this

end Refutations.H1Density
