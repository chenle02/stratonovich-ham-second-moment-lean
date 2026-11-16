namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FixedSplit
open Finset Real MeasureTheory
open scoped Nat
open StratonovichHAMSecondMoment.IntervalScalar StratonovichHAMSecondMoment.FixedSplitCore
-- Statement copied from the source (the printed type elides a term as `_`, which the round trip cannot elaborate).
-- The section variables of the source, as there:
variable {ι : Type*} [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
/-- For a strict partition 0 = tau_0 < ... < tau_M = T, M <= 3k+1, cutting at the endpoints in (0,T) of A and at distinct insertion times in (0,T): from the norm comparison, v in Z(empty), Z(S) invariance, segment and insertion bounds, ||w_M||_(k/T) <= M_k D_A (prod c_i) ||v||_(k/T). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FixedSplit.word_chain (A C : Finset ι) (Z : Finset ι → Set E) (emb : ℝ → E →L[ℂ] F)
    (J : ι → E → E) (P : ℝ → ℝ → E → E) (v : E) (a b h t cI : ι → ℝ) (κ : ι → ℕ) (k : ℕ)
    (T : ℝ) (τ : ℕ → ℝ) (M : ℕ) (hT : 0 < T) (hk : 1 ≤ k)
    (hτ0 : τ 0 = 0) (hτM : τ M = T) (hst : ∀ j < M, τ j < τ (j + 1))
    (hcutA : ∀ i ∈ A, (0 < a i → a i < T → ∃ m ≤ M, τ m = a i) ∧
      (0 < b i → b i < T → ∃ m ≤ M, τ m = b i))
    (hcutC : ∀ i ∈ C, ∃ m ≤ M, τ m = t i) (htC : ∀ i ∈ C, 0 < t i ∧ t i < T)
    (hinj : Set.InjOn t C) (hM : M ≤ 3 * k + 1)
    (hh : ∀ i ∈ A, 0 < h i) (hlen : ∀ i ∈ A, b i - a i ≤ h i) (hκ : ∑ i ∈ A, κ i ≤ k)
    (hcI : ∀ i ∈ C, 0 ≤ cI i)
    (hcmp : ∀ ρ ρ' : ℝ, 0 < ρ → 0 < ρ' → ∀ x, ‖emb ρ' x‖ ≤ max 1 (ρ / ρ') * ‖emb ρ x‖)
    (hv : v ∈ Z ∅) (hPZ : ∀ S ⊆ C, ∀ s t', ∀ x ∈ Z S, P t' s x ∈ Z S)
    (hseg : ∀ s t', 0 ≤ s → s < t' → t' ≤ T →
      (∀ i ∈ A, a i ∉ Set.Ioo s t' ∧ b i ∉ Set.Ioo s t') → ∀ x,
        ‖emb (segLam A a b h κ k T ((s + t') / 2)) (P t' s x)‖ ≤
          100 * Real.exp (2 * (segLam A a b h κ k T ((s + t') / 2) * (t' - s))) *
            ‖emb (segLam A a b h κ k T ((s + t') / 2)) x‖)
    (hJ : ∀ i ∈ C, ∀ S ⊆ C, i ∉ S → ∀ x ∈ Z S, J i x ∈ Z (insert i S) ∧
      ∀ ρ, (k : ℝ) / T ≤ ρ → ‖emb ρ (J i x)‖ ≤ cI i * ‖emb ρ x‖) :
    ‖emb ((k : ℝ) / T) (wordSeq P τ (cutOp C J t) v M)‖ ≤
      Mk k * metricD ((k : ℝ) / T) h κ A * (∏ i ∈ C, cI i) * ‖emb ((k : ℝ) / T) v‖ := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.FixedSplit.word_chain
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FixedSplit
