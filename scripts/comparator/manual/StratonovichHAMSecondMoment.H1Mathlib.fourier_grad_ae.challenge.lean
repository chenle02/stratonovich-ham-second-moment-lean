namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.H1Mathlib
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Filter Topology FourierTransform TemperedDistribution
open scoped ENNReal ContDiff SchwartzMap LineDeriv Real
open HomogHypothesis (Rd)
open WeakSobolev
open VariationalFloor (grad)
variable {d : ℕ}
/-- f, g in L^2 (real f, g : R^d -> R^d) with g a weak gradient of f, j: F(<g, e_j>) = 2 pi i xi_j F f almost everywhere (L^2 Fourier transform). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.H1Mathlib.fourier_grad_ae {f : Rd d → ℝ} {g : Rd d → Rd d} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) (hw : HasWeakGradient f g) (j : Fin d) :
    ((𝓕 (toL2C (memLp_inner hg (eb d j))) : Lp ℂ 2 volume) : Rd d → ℂ) =ᵐ[volume]
      fun x => (2 * π * Complex.I) * coordSym j x * (𝓕 (toL2C hf) : Lp ℂ 2 volume) x := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.H1Mathlib
