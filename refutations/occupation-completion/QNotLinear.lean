/-
Control for the square map `Q : H¹ → H_sp` of `L:occupation-raw-square`
(`integrated_occupation_ceiling.tex` lines 26-30 at edf7085f), package theorems
`StratonovichHAMSecondMoment.OccupationCompletion.Q_of_test`, `toHsp_smul` and
`occupation_raw_square_paper` (`‖Q(f)‖² = A_sp(f)`).

Wrong variant (class (b), a Lean-route control): "`Q` is linear", i.e. `Q(2f) = 2 Q(f)`.  The
manuscript's `Q` is the square map, so `Q(2f) = 4 Q(f)`; this control checks that the Lean `Q` is
not a degenerate (zero or linear) map.  Counterexample: under `H:homog` with `Γ ≠ 0`, the test
function `f = H1Density.cutoff 0` (equal to `1` near the origin): `Q(f) ≠ 0` because
`‖Q(f)‖² = A_sp(f) > 0` (`P:spatial-four-linear`, positivity of `A_sp` on nonzero profiles).  No
junk-value reliance (`f` is a test function, the domain of the definitions).
`q_not_linear_contrast` is the true scaling `Q(2f) = 4 Q(f)` for test functions.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.OccupationCompletion

set_option autoImplicit false

open MeasureTheory Set
open StratonovichHAMSecondMoment OccupationCompletion HomogHypothesis

namespace Refutations.OccupationCompletion

/-- The true scaling: `Q(2f) = 4 Q(f)` for a test function `f`, under `H:homog`, `Γ ≠ 0`. -/
theorem q_not_linear_contrast {d : ℕ} {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) {f : Rd d → ℝ}
    (hf : WeakSobolev.IsTestFunction f) :
    Q (SpData.ofHomog hH) (fun x => 2 * f x) = (4 : ℝ) • Q (SpData.ofHomog hH) f := by
  have := hH.Γ_radon
  obtain ⟨-, ha0, ha2, -, -, hR0, hB⟩ :=
    SpatialFourLinear.squareBound_R0 hH hΓ (H1Density.h1TestDense d)
  have h2f : WeakSobolev.IsTestFunction (fun x => 2 * f x) :=
    (testSub d).smul_mem (2 : ℝ) hf
  rw [Q_of_test (S := SpData.ofHomog hH) hB hR0.le ha0 (by linarith) h2f,
    Q_of_test (S := SpData.ofHomog hH) hB hR0.le ha0 (by linarith) hf]
  unfold sqHsp
  rw [← toHsp_smul (4 : ℝ) (SpatialFourLinear.isTest_sq hf)]
  congr 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- "`Q` is linear" fails under `H:homog` with `Γ ≠ 0`. -/
theorem q_not_linear_refuted {d : ℕ} {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) :
    ¬ ∀ f : Rd d → ℝ, WeakSobolev.IsTestFunction f →
      Q (SpData.ofHomog hH) (fun x => 2 * f x) = (2 : ℝ) • Q (SpData.ofHomog hH) f := by
  intro hall
  set f : Rd d → ℝ := H1Density.cutoff 0
  have hf : WeakSobolev.IsTestFunction f :=
    ⟨H1Density.cutoff_contDiff 0, H1Density.cutoff_hasCompactSupport 0⟩
  have h4 := q_not_linear_contrast hH hΓ hf
  have h2 := hall f hf
  rw [h4] at h2
  have hz : Q (SpData.ofHomog hH) f = 0 := by
    have : (2 : ℝ) • Q (SpData.ofHomog hH) f = 0 := by
      have e : (4 : ℝ) • Q (SpData.ofHomog hH) f - (2 : ℝ) • Q (SpData.ofHomog hH) f =
          (2 : ℝ) • Q (SpData.ofHomog hH) f := by
        rw [← sub_smul]; norm_num
      rw [← e, h2, sub_self]
    exact (smul_eq_zero.1 this).resolve_left (by norm_num)
  have hp := SpatialFourLinear.isH1Pair_test hf
  have hnorm := (occupation_raw_square_paper hH hΓ).2.1 f _ hp
  rw [hz, norm_zero, zero_pow two_ne_zero] at hnorm
  -- positivity of `A_sp(f)`
  have hnz : ¬ f =ᵐ[volume] 0 := by
    intro h0
    have hcont : Continuous f := hf.1.continuous
    have := (Continuous.ae_eq_iff_eq volume hcont continuous_const).1 h0
    have h1 : f 0 = 1 := H1Density.cutoff_eq_one (by simp)
    have h0' : f 0 = 0 := congrFun this 0
    rw [h0'] at h1
    norm_num at h1
  have hpos := (SpatialOccupationL7Completed.spatial_four_linear_paper_completed hH hΓ).2.2.2.2.2
    f _ hp hnz
  have hfin := ((SpatialOccupationL7Completed.spatial_four_linear_paper_completed hH hΓ).2.1
    f f _ _ hp hp).1
  have : 0 < (OccupationPhysicalClass.sqPair Γ f f).toReal :=
    ENNReal.toReal_pos hpos.ne' hfin.ne
  linarith

end Refutations.OccupationCompletion
