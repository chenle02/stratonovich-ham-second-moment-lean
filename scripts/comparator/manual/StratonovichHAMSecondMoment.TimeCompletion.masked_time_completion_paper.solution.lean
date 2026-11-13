namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TimeCompletion
open MeasureTheory Set
open scoped ComplexConjugate ENNReal
open StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TimeSchur
-- Statement copied from the source (the printed type writes `ContDiff ℝ (↑⊤)`, and its `Submodule.span ... : Set (Ha ..)` ascription does not elaborate).
/-- If 0<a<1, T>0, p=<a,T>: real compact smooth tests on (0,T) give an integrable form >= 0; Ha p is separable; ||emb f||^2 <= 2T^(1-a)/(1-a) int|f|^2; extL2 extends emb; ||emb f||^2 = timeForm f f; Re/Im split; interval amplitudes in L^2; real tests span a dense subspace. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.TimeCompletion.masked_time_completion_paper (a T : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hT : 0 < T) :
    (∀ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → tsupport f ⊆ Ioo 0 T →
        Integrable (fun q : ℝ × ℝ => f q.1 * f q.2 * |q.1 - q.2| ^ (-a))
          ((volume.restrict (Icc 0 T)).prod (volume.restrict (Icc 0 T))) ∧
        0 ≤ ∫ t in Icc 0 T, ∫ s in Icc 0 T, f t * f s * |t - s| ^ (-a)) ∧
      TopologicalSpace.SeparableSpace (Ha ⟨a, T, ha0, ha1, hT⟩) ∧
      (∀ (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Icc 0 T))),
        ‖emb ⟨a, T, ha0, ha1, hT⟩ ⟨f, hf⟩‖ ^ 2 ≤
          2 * T ^ (1 - a) / (1 - a) * ∫ t in Icc 0 T, ‖f t‖ ^ 2) ∧
      ((∀ (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Icc 0 T))),
          extL2 ⟨a, T, ha0, ha1, hT⟩ (hf.toLp f) = emb ⟨a, T, ha0, ha1, hT⟩ ⟨f, hf⟩) ∧
        ∀ w : Lp ℂ 2 (volume.restrict (Icc (0 : ℝ) T)),
          ‖extL2 ⟨a, T, ha0, ha1, hT⟩ w‖ ^ 2 ≤ 2 * T ^ (1 - a) / (1 - a) * ‖w‖ ^ 2) ∧
      (∀ (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Icc 0 T))),
        Integrable (fun q : ℝ × ℝ => f q.1 * conj (f q.2) * ((kern a (q.1 - q.2) : ℝ) : ℂ))
            ((volume.restrict (Icc 0 T)).prod (volume.restrict (Icc 0 T))) ∧
          ((‖emb ⟨a, T, ha0, ha1, hT⟩ ⟨f, hf⟩‖ ^ 2 : ℝ) : ℂ) = timeForm a T f f ∧
          ‖emb ⟨a, T, ha0, ha1, hT⟩ ⟨f, hf⟩‖ ^ 2 =
            ‖emb ⟨a, T, ha0, ha1, hT⟩ (reL2 ⟨f, hf⟩)‖ ^ 2 +
              ‖emb ⟨a, T, ha0, ha1, hT⟩ (imL2 ⟨f, hf⟩)‖ ^ 2) ∧
      (∀ (g : ℝ → ℝ) (hg : MemLp g 2 (volume.restrict (Icc 0 T))),
        ‖emb ⟨a, T, ha0, ha1, hT⟩ ⟨fun t => (g t : ℂ), hg.ofReal⟩‖ ^ 2 =
          ∫ t in Icc 0 T, ∫ s in Icc 0 T, g t * g s * |t - s| ^ (-a)) ∧
      (∀ (c d M : ℝ) (A : ℝ → ℂ), AEStronglyMeasurable A (volume.restrict (Icc c d)) →
        (∀ t ∈ Icc c d, ‖A t‖ ≤ M) → (Icc c d).indicator A ∈ L2fun T) ∧
      Dense (Submodule.span ℂ (emb ⟨a, T, ha0, ha1, hT⟩ '' realTestSet T) :
        Set (Ha ⟨a, T, ha0, ha1, hT⟩)) := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.TimeCompletion.masked_time_completion_paper
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TimeCompletion
