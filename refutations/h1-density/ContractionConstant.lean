/-
Refutation for the `L²` contraction of the mollification in `H1Density`,
package theorem `StratonovichHAMSecondMoment.H1Density.eLpNorm_mollify_le`
(`‖ρ_φ ⋆ u‖₂ ≤ ‖u‖₂`; auxiliary to the Lean proof route of the density
`h1TestDense`, `notes/integrated_spatial_occupation.tex`, lines 262-266 at
a284420).

Wrong variant: a smaller constant, `‖ρ_φ ⋆ u‖₂ ≤ ‖u‖₂ / 2` for every bump
`φ` and every `u ∈ L²`.  Counterexample in `d = 1`: `u = prof` (the bump of
`VariationalFloor`, `0 < ‖u‖₂ < ∞`).  By the package theorem
`tendsto_mollify`, `ρ_n ⋆ u → u` in `L²` along `VariationalFloor.bumpN`,
so eventually `‖u - ρ_n ⋆ u‖₂ < ‖u‖₂ / 2`, and then
`‖u‖₂ ≤ ‖ρ_n ⋆ u‖₂ + ‖u - ρ_n ⋆ u‖₂ < ‖u‖₂`.
`contraction_constant_contrast` is the package bound at the same point.
No junk-value reliance (`‖u‖₂` is finite and positive).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.H1Density

set_option autoImplicit false

open MeasureTheory Filter Topology StratonovichHAMSecondMoment

namespace Refutations.H1Density

/-- The `L²` contraction of the mollification does not hold with constant
`1/2` (`d = 1`). -/
theorem contraction_constant_refuted :
    ¬ (∀ (φ : ContDiffBump (0 : HomogHypothesis.Rd 1)) (u : HomogHypothesis.Rd 1 → ℝ),
        MemLp u 2 volume →
        eLpNorm (H1Density.mollify φ u) 2 volume ≤ eLpNorm u 2 volume / 2) := by
  intro h
  set u : HomogHypothesis.Rd 1 → ℝ := VariationalFloor.prof 1 with hu
  have huL : MemLp u 2 volume := VariationalFloor.memLp_test VariationalFloor.prof_test
  have hM0 : eLpNorm u 2 volume ≠ 0 := by
    intro h0
    rw [eLpNorm_eq_zero_iff (by norm_num)] at h0
    have hall : u = 0 :=
      (VariationalFloor.prof_test.1.continuous.ae_eq_iff_eq volume continuous_const).mp h0
    have h1 := congrFun hall 0
    rw [hu, VariationalFloor.prof_eq_one (by simp)] at h1
    exact one_ne_zero h1
  have hMt : eLpNorm u 2 volume ≠ ⊤ := huL.eLpNorm_lt_top.ne
  have hhalf : 0 < eLpNorm u 2 volume / 2 :=
    ENNReal.div_pos hM0 (by norm_num)
  have T := H1Density.tendsto_mollify huL (H1Density.tendsto_bumpN_rOut (d := 1))
  obtain ⟨n, hn⟩ := (T.eventually (gt_mem_nhds hhalf)).exists
  have hsplit : u = H1Density.mollify (VariationalFloor.bumpN 1 n) u -
      fun x => H1Density.mollify (VariationalFloor.bumpN 1 n) u x - u x := by
    funext x; simp
  have htri := eLpNorm_sub_le (μ := volume) (p := 2) (by norm_num)
    (f := H1Density.mollify (VariationalFloor.bumpN 1 n) u)
    (g := fun x => H1Density.mollify (VariationalFloor.bumpN 1 n) u x - u x)
  rw [← hsplit] at htri
  have hlt : eLpNorm u 2 volume < eLpNorm u 2 volume / 2 + eLpNorm u 2 volume / 2 :=
    htri.trans_lt (ENNReal.add_lt_add_of_le_of_lt
      (ne_top_of_le_ne_top (ENNReal.div_ne_top hMt (by norm_num : (2 : ENNReal) ≠ 0))
        (h _ u huL)) (h _ u huL) hn)
  rw [ENNReal.add_halves] at hlt
  exact lt_irrefl _ hlt

/-- The package bound at the same point: `‖ρ ⋆ prof‖₂ ≤ ‖prof‖₂`. -/
theorem contraction_constant_contrast (n : ℕ) :
    eLpNorm (H1Density.mollify (VariationalFloor.bumpN 1 n) (VariationalFloor.prof 1)) 2
      volume ≤ eLpNorm (VariationalFloor.prof 1) 2 volume :=
  H1Density.eLpNorm_mollify_le _ (VariationalFloor.memLp_test VariationalFloor.prof_test)

end Refutations.H1Density
