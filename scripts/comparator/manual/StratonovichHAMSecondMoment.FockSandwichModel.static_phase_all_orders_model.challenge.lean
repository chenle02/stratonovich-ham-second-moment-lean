namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockSandwichModel
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
open MeasureTheory Real Finset Filter Topology Set
open scoped ComplexConjugate Nat
open HomogHypothesis (Rd)
open HermiteFock (Supp degLE fieldOp mem_degLE deg gmul cre ann)
open GaussianHermite (unitIdx)
open FockColumnBound (mulOp mulOp_ae op_ext band measurable_band abs_band_le bandProj wt measurable_wt sqrtResolvent nuEps nuEps_finite modes)
open ComplexPhaseScalar (invSqrtShift shiftOp)
open StaticInteractionCompleted (FockSandwich CPInputs PropagatorBlock InDisc)
open StaticPhaseCauchy (fockD taylorCoeff allOrdersA)
open SpectralMassIdentity (ralpha)
open PhaseContractions (PhaseCovariance dGam)
open IntervalScalar (staticE)
/-- PhaseCovariance alpha Gamma mu, eps > 0, real orthonormal modes psi m, n >= 1, h > 0, CPInputs and PropagatorBlock at opA0 b, fieldB b (psi m), hentire, hz, hv, hband, hgauss: z <= (allOrdersA alpha sqrt(R_alpha))^n h^((4-alpha)n/2) / (n!)^((3-alpha)/2) N1. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FockSandwichModel.static_phase_all_orders_model (Ec : ℕ → ℕ → Type*) [∀ m b, NormedAddCommGroup (Ec m b)]
    [∀ m b, NormedSpace ℂ (Ec m b)] [∀ m b, CompleteSpace (Ec m b)]
    {alpha ε h z N1 : ℝ} {Γ μ : Measure (Rd 3)} (hcov : PhaseCovariance alpha Γ μ) (hε : 0 < ε)
    (ψ : ∀ m, Fin m → Lp ℂ 2 (nuEps μ ε)) (hψ : ∀ m, Orthonormal ℂ (ψ m))
    (hreal : ∀ m i, ∀ᵐ ξ ∂(nuEps μ ε), ψ m i (-ξ) = conj (ψ m i ξ))
    (F : ∀ m b, ℂ → Ec m b →L[ℂ] Ec m b) (v : ∀ m b, Ec m b) (zc : ℕ → ℕ → ℝ) (zm : ℕ → ℝ)
    {n : ℕ} (hn : 1 ≤ n) (hh : 0 < h)
    (Cop Fop Hop Q' : ∀ m (_ : ℕ), ℂ → FockH (L2 3) m n →L[ℂ] FockH (L2 3) m n)
    (J : ∀ m (_ : ℕ), ℂ → ℝ → FockH (L2 3) m n →L[ℂ] FockH (L2 3) m n)
    (hcp : ∀ m (b : ℕ), CPInputs (opA0 (b : ℝ)) (fieldB (b : ℝ) (nuEps_finite hcov.μ_tempered hε)
      (ψ m) (hψ m)) n alpha h (ralpha μ alpha) (Cop m b) (Fop m b) (Hop m b) (Q' m b) (J m b))
    (hprop : ∀ m b z, InDisc n alpha h (ralpha μ alpha) z →
      PropagatorBlock (F m b z) (Cop m b z) (Fop m b z) (Hop m b z) (Q' m b z))
    (hentire : ∀ m b, Differentiable ℂ (F m b))
    (hz : ∀ m b, zc m b ≤ n * ‖taylorCoeff (F m b) n (v m b)‖) (hv : ∀ m b, ‖v m b‖ ≤ N1)
    (hband : ∀ m, Tendsto (zc m) atTop (𝓝 (zm m))) (hgauss : Tendsto zm atTop (𝓝 z)) :
    z ≤ (allOrdersA alpha * √(ralpha μ alpha)) ^ n * h ^ ((4 - alpha) * n / 2) /
      (n ! : ℝ) ^ ((3 - alpha) / 2) * N1 := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockSandwichModel
