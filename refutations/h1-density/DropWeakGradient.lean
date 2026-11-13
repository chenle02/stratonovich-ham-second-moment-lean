/-
Refutation for the density theorem of `H1Density`, package theorem
`StratonovichHAMSecondMoment.H1Density.h1TestDense` (density of `C_c^∞` in
the weak-gradient `H^1`; `notes/integrated_spatial_occupation.tex`, proof of
`P:spatial-four-linear`, lines 262-266 at a284420).

Wrong variant: drop the hypothesis that `g` is a weak gradient of `f`, i.e.
every pair `f, g ∈ L²` would be an `L²` graph limit of test functions.
Counterexample in `d = 1`: `f = 0` and `g = prof · e₀` (the smooth bump
`VariationalFloor.prof`, equal to `1` at the origin, times the first unit
vector).  By the package converse `hasWeakGradient_of_tendsto`, `g` would be
a weak gradient of `0`; so would `0`, and weak gradients are a.e. unique
(`WeakSobolev.weakGradient_ae_unique`), so the continuous `g` would vanish,
but `g(0) = e₀ ≠ 0`.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.H1Density

set_option autoImplicit false

open MeasureTheory Filter Topology StratonovichHAMSecondMoment

namespace Refutations.H1Density

/-- Without the weak-gradient hypothesis the density statement is false
(`d = 1`). -/
theorem drop_weak_gradient_refuted :
    ¬ (∀ (f : HomogHypothesis.Rd 1 → ℝ) (g : HomogHypothesis.Rd 1 → HomogHypothesis.Rd 1),
        MemLp f 2 volume → MemLp g 2 volume →
        ∃ φ : ℕ → HomogHypothesis.Rd 1 → ℝ, (∀ n, WeakSobolev.IsTestFunction (φ n)) ∧
          Tendsto (fun n => eLpNorm (fun x => φ n x - f x) 2 volume) atTop (𝓝 0) ∧
          Tendsto (fun n => eLpNorm (fun x => VariationalFloor.grad (φ n) x - g x) 2 volume)
            atTop (𝓝 0)) := by
  intro h
  set e : HomogHypothesis.Rd 1 := EuclideanSpace.single 0 (1 : ℝ) with he
  set g : HomogHypothesis.Rd 1 → HomogHypothesis.Rd 1 :=
    fun x => VariationalFloor.prof 1 x • e with hgdef
  have hgc : Continuous g := VariationalFloor.prof_test.1.continuous.smul continuous_const
  have hgs : HasCompactSupport g := VariationalFloor.prof_test.2.smul_right
  have hgL : MemLp g 2 volume := hgc.memLp_of_hasCompactSupport hgs
  have h0L : MemLp (fun _ : HomogHypothesis.Rd 1 => (0 : ℝ)) 2 volume := MemLp.zero
  obtain ⟨φ, hφt, h1, h2⟩ := h (fun _ => 0) g h0L hgL
  have hw : WeakSobolev.HasWeakGradient (fun _ => (0 : ℝ)) g :=
    H1Density.hasWeakGradient_of_tendsto h0L hgL hφt h1 h2
  have hw0 : WeakSobolev.HasWeakGradient (fun _ : HomogHypothesis.Rd 1 => (0 : ℝ)) 0 := by
    intro ψ _ v; simp
  have hae : g =ᵐ[volume] 0 :=
    WeakSobolev.weakGradient_ae_unique hw hw0 hgL MemLp.zero
  have hall : g = 0 := (hgc.ae_eq_iff_eq volume continuous_const).mp hae
  have hg0 : g 0 = e := by
    rw [hgdef]
    simp only
    rw [VariationalFloor.prof_eq_one (by simp), one_smul]
  have : e = 0 := by rw [← hg0, hall]; rfl
  rw [he] at this
  have h1 := congrArg (fun y : HomogHypothesis.Rd 1 => y 0) this
  simp at h1

end Refutations.H1Density
