namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RadiusMeanAnchor
open MeasureTheory Filter Set Topology
-- Statement copied from the source (the printed type elides subterms as `⋯`); the
-- section variables {E} [NormedAddCommGroup E] [NormedSpace ℝ E] written as binders.
/-- Under H:homog, E:radius-anchor-parameters, E:radius-anchor-Q, B>=1, 0<delta<min(1,1/B), p>=1, R>=1, prob. mu, C:radius-covariance-residuals for M_m and hXmeas: E:radius-mean-anchor with integrability; e_anchor>0; R=1/delta+2 gives E:radius-mean-anchor-decay; bound -> 0. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.RadiusMeanAnchor.radius_mean_anchor_paper {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    -- `H:homog`
    (d : ℕ) (_hd : d = 1 ∨ d = 2 ∨ d = 3) (a α : ℝ) (_ha0 : 0 < a) (ha1 : a < 1)
    (_hα : (0 < α ∧ α < d) ∨ (α = d ∧ d = 1)) (_hthr : a + α < 2)
    -- `E:radius-anchor-parameters`
    (γ θ ηt βt : ℝ) (_hγ0 : 0 < γ) (_hγ : γ < min (1 / 2) ((2 - α) / 2))
    (hθ : 1 / 2 < θ) (_hθη : θ < ηt) (_hηβ : ηt < βt)
    (_hβ : βt < min (1 - a / 2) ((3 - a - α) / 2))
    -- `E:radius-anchor-Q`
    (Q : ℕ) (_hQeven : Even Q) (hQ2 : 2 ≤ Q) (_hQγ : (d : ℝ) < Q * γ)
    (_hQβ : 0 < βt - ηt - 1 / Q) (hQa : 2 * (d : ℝ) / (1 - a) < Q)
    -- block partition
    (B : ℕ) (hB : 1 ≤ B) (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ < min 1 (1 / (B : ℝ)))
    (p : ℝ) (hp : 1 ≤ p) (R : ℝ) (hR : 1 ≤ R) (C : ℝ)
    -- the transferred residual paths `M_R(Y_m)`, `m = 0, …, N`
    (M : ℕ → Ω → ℝ → E)
    -- supplied input (`C:radius-covariance-residuals`, `C = 1`, `v = p`)
    (hMC : ∀ m ∈ Finset.range (⌊1 / (δ * B)⌋₊ + 1), ∀ᵐ ω ∂μ, IsCHolder θ B (M m ω))
    (hMint : ∀ m ∈ Finset.range (⌊1 / (δ * B)⌋₊ + 1),
      Integrable (fun ω => holderNorm θ B (M m ω) ^ p) μ)
    (hMmom : ∀ m ∈ Finset.range (⌊1 / (δ * B)⌋₊ + 1),
      (∫ ω, holderNorm θ B (M m ω) ^ p ∂μ) ^ (1 / p) ≤
        C * Real.sqrt p * R ^ ((d : ℝ) / Q))
    -- implicit side condition: `‖X_m‖_{C^θ}` is a random variable
    (hXmeas : ∀ m ∈ Finset.range (⌊1 / (δ * B)⌋₊ + 1),
      AEStronglyMeasurable (fun ω =>
        holderNorm θ B (blockPath (δ ^ ((1 - a) / 2)) (ell δ B m) (M m ω))) μ) :
    (Integrable (fun ω => (δ * ∑ m ∈ Finset.range (⌊1 / (δ * B)⌋₊ + 1),
        holderNorm θ B (blockPath (δ ^ ((1 - a) / 2)) (ell δ B m) (M m ω)) ^ p)
          ^ (1 / p)) μ ∧
      ∫ ω, (δ * ∑ m ∈ Finset.range (⌊1 / (δ * B)⌋₊ + 1),
        holderNorm θ B (blockPath (δ ^ ((1 - a) / 2)) (ell δ B m) (M m ω)) ^ p)
          ^ (1 / p) ∂μ ≤
        (2 / (B : ℝ)) ^ (1 / p) * C * Real.sqrt p * δ ^ ((1 - a) / 2) *
          R ^ ((d : ℝ) / Q)) ∧
    0 < (1 - a) / 2 - (d : ℝ) / Q ∧
    (R = δ⁻¹ + 2 →
      2 * ∫ ω, (δ * ∑ m ∈ Finset.range (⌊1 / (δ * B)⌋₊ + 1),
        holderNorm θ B (blockPath (δ ^ ((1 - a) / 2)) (ell δ B m) (M m ω)) ^ p)
          ^ (1 / p) ∂μ ≤
        2 * (2 / (B : ℝ)) ^ (1 / p) * C * Real.sqrt p * 3 ^ ((d : ℝ) / Q) *
          δ ^ ((1 - a) / 2 - (d : ℝ) / Q)) ∧
    Tendsto (fun δ' : ℝ => 2 * (2 / (B : ℝ)) ^ (1 / p) * C * Real.sqrt p *
        3 ^ ((d : ℝ) / Q) * δ' ^ ((1 - a) / 2 - (d : ℝ) / Q)) (𝓝[>] 0) (𝓝 0) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RadiusMeanAnchor
