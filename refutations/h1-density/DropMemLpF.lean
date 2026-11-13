/-
Refutation for the density theorem of `H1Density`, package theorem
`StratonovichHAMSecondMoment.H1Density.h1TestDense` (density of `C_c^∞` in
the weak-gradient `H^1`; `notes/integrated_spatial_occupation.tex`, proof of
`P:spatial-four-linear`, lines 262-266 at a284420).

Wrong variant: drop the hypothesis `f ∈ L²` (keep `g ∈ L²` and the weak
gradient).  Counterexample in `d = 1`: `f = 1` (constant) has weak gradient
`0 ∈ L²`, but `φ - 1` is never in `L²` for a compactly supported `φ`
(Lebesgue measure of `ℝ` is infinite), so `‖φ n - 1‖₂ = ∞` for every `n` and
cannot tend to `0`.
Junk-value note: the argument uses `eLpNorm = ∞` for a function not in `L²`,
which is the genuine value of the norm, not a junk value.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.H1Density

set_option autoImplicit false

open MeasureTheory Filter Topology StratonovichHAMSecondMoment

namespace Refutations.H1Density

/-- Without `f ∈ L²` the density statement is false (`d = 1`, `f = 1`). -/
theorem drop_memLp_f_refuted :
    ¬ (∀ (f : HomogHypothesis.Rd 1 → ℝ) (g : HomogHypothesis.Rd 1 → HomogHypothesis.Rd 1),
        MemLp g 2 volume → WeakSobolev.HasWeakGradient f g →
        ∃ φ : ℕ → HomogHypothesis.Rd 1 → ℝ, (∀ n, WeakSobolev.IsTestFunction (φ n)) ∧
          Tendsto (fun n => eLpNorm (fun x => φ n x - f x) 2 volume) atTop (𝓝 0) ∧
          Tendsto (fun n => eLpNorm (fun x => VariationalFloor.grad (φ n) x - g x) 2 volume)
            atTop (𝓝 0)) := by
  intro h
  have hw : WeakSobolev.HasWeakGradient (fun _ : HomogHypothesis.Rd 1 => (1 : ℝ)) 0 := by
    intro ψ hψ v
    have hψ1 : ContDiff ℝ 1 ψ := hψ.1.of_le (by exact_mod_cast le_top)
    have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      (f := fun _ : HomogHypothesis.Rd 1 => (1 : ℝ)) (g := ψ) (v := v)
      (by simp) (by
        simpa using ((hψ1.continuous_fderiv one_ne_zero).clm_apply
          continuous_const).integrable_of_hasCompactSupport
          ((hψ.2.fderiv ℝ).comp_left (g := fun L : HomogHypothesis.Rd 1 →L[ℝ] ℝ => L v)
            (by simp)))
      (by simpa using hψ1.continuous.integrable_of_hasCompactSupport hψ.2)
      (fun x _ => differentiableAt_const _) (fun x _ => hψ1.differentiable one_ne_zero x)
    simpa using key
  obtain ⟨φ, hφt, h1, -⟩ := h (fun _ => 1) 0 MemLp.zero hw
  obtain ⟨n, hn⟩ := (h1.eventually (gt_mem_nhds one_pos)).exists
  have hφL : MemLp (φ n) 2 volume := VariationalFloor.memLp_test (hφt n)
  have hdL : MemLp (fun x => φ n x - 1) 2 volume := memLp_iff.mpr (hn.trans ENNReal.one_lt_top)
  have hc : MemLp (fun _ : HomogHypothesis.Rd 1 => (1 : ℝ)) 2 volume := by
    have := hφL.sub hdL
    refine this.congr_norm ?_ (Eventually.of_forall fun x => ?_)
    · exact aestronglyMeasurable_const
    · simp
  rw [memLp_const_iff (by norm_num) (by norm_num)] at hc
  have htop : (volume : Measure (HomogHypothesis.Rd 1)) Set.univ = ⊤ :=
    measure_univ_of_isAddLeftInvariant _
  rcases hc with hc | hc
  · exact one_ne_zero hc
  · rw [htop] at hc; exact lt_irrefl _ hc

end Refutations.H1Density
