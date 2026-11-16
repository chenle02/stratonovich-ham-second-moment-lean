namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceHeatGram
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
open MeasureTheory Set Filter Metric Topology
open scoped ContDiff ENNReal ComplexConjugate
open HomogHypothesis (Rd HomogCovariance IsSpectralMeasure IsEven IsTempered)
open WeakSobolev (IsTestFunction)
open SpatialFourierBound (spatialPair fourierQ ex ex_continuous norm_ex ex_sub)
open LowAlphaConvolution (heatDens gaussFactor gaussFactor_pos gaussFactor_le_one)
variable {d : ℕ}
variable {μ : Measure (Rd d)}
open SpaceTimePositivity (timeMeasure timeMeasure_eq_Icc)
open TimeSchur (kern kern_nonneg measurable_kern kern_sub_comm)
variable {μ : Measure (Rd d)}
/-- Under H:homog, Gamma != 0 (unused), cells A_i, tests f_i, |f_i|_2 = 1, smooth cutoff eta, R >= 1: k_i^R = J(h_i (x) m_R f_i^2), k_i^infty = J(h_i (x) f_i^2) in H_I; entries = tPair * B_Gamma; both Grams PSD. Label row and entrywise order not stated. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceHeatGram.positive_physical_gram_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (_hΓ0 : Γ ≠ 0)
    {ι : Type*} [Fintype ι] (A : ι → Set ℝ) (hA : ∀ i, MeasurableSet (A i))
    (_hAI : ∀ i, A i ⊆ Ioo 0 1) (_hdisj : Pairwise (Function.onFun Disjoint A))
    (_hne : ∀ i, (A i).Nonempty) (_hpos : ∀ i, 0 < volume.real (A i))
    (_hsum : ∑ i, volume.real (A i) = 1)
    (f : ι → Rd d → ℝ) (hf : ∀ i, IsTestFunction (f i)) (_hf2 : ∀ i, ∫ x, f i x ^ 2 = 1)
    (η : Rd d → ℝ) (hη : ContDiff ℝ ∞ η) (_hη01 : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    (_hη1 : ∀ x, ‖x‖ ≤ 1 → η x = 1) (_hη2 : ∀ x, 2 < ‖x‖ → η x = 0) {R : ℝ} (_hR : 1 ≤ R) :
    let p : KernParams := ⟨alpha0, hH.alpha0_pos, hH.alpha0_lt_one⟩
    let qR : ι → Rd d → ℝ := fun i x => η (R⁻¹ • x) ^ 2 * f i x ^ 2
    let qI : ι → Rd d → ℝ := fun i x => f i x ^ 2
    let kR : ι → HI p (HGamma μ) := fun i => gramVec p μ (A i) (hA i) (qR i)
    let kI : ι → HI p (HGamma μ) := fun i => gramVec p μ (A i) (hA i) (qI i)
    (∀ i j, inner ℝ (kR i) (kR j) = tPair alpha0 (A i) (A j) * spatialPair Γ (qR i) (qR j)) ∧
    (∀ i j, inner ℝ (kI i) (kI j) = tPair alpha0 (A i) (A j) * spatialPair Γ (qI i) (qI j)) ∧
    (Matrix.of fun i j => inner ℝ (kR i) (kR j)).PosSemidef ∧
    (Matrix.of fun i j => inner ℝ (kI i) (kI j)).PosSemidef := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceHeatGram
