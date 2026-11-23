module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L12, item TW: the two parts of `L:terminal-wick` (The finite terminal-chain Wick formula)
of the main TeX file `notes/notes_stratonovich_ham_second_moment.tex` at revision edf7085f
(statement lines 4291-4336, proof 4338-4410) that `TerminalWick` and `TerminalWickInputs` left
narrower, for the constructed terminal-chain measures `g_n^{T,x}` of
`E:terminal-chain-measure` (lines 4275-4288, `TerminalWickInputs.chainMeasure`).

What the TeX claims (read at 39f2597a; the same lines at edf7085f):
* Lines 4331-4333: "If `K ≥ 0`, every integral above is nonnegative.  Consequently, entrywise
  comparison `0 ≤ K₁ ≤ K₂` compares all finite partial-order second moments in the same
  direction."  The proof (lines 4404-4406) compares the covariance products pairing by pairing,
  "including self-pairs and unequal chains", i.e. every mixed moment `E[Y_m Y_n]`.  The phrase
  "finite partial-order second moments" is read here in both senses: the mixed moments
  `E[Y_m Y_n]` (already `terminal_wick_mono_constructed_paper`) and the second moments
  `E(Σ_{n ≤ N} r^n Y_n)²` of the partial sums of finite order `N`, for real `r`.  The TeX does
  not state the comparison for complex `r` (and it is not a consequence of the entrywise
  comparison of mixed moments: `refutations/terminal-wick-complete/ComplexComparison.lean`).
* Lines 4333-4335: "The series `Σ_{n≥0} r^n Y_n` converges absolutely in `L²` for every real or
  complex `r`."  For complex `r` the series lives in the complex `L²(Ω)`; `Y_n` enters it through
  the isometric embedding `toC` (`Complex.ofRealCLM.compLp`, `norm_toC`).

Formalized here:
* (1) Partial-sum comparison for every real `r` and every finite order `N`:
  `E(Σ_{n≤N} r^n Y¹_n)² ≤ E(Σ_{n≤N} r^n Y²_n)²` (`norm_sq_partial_le`, from the entrywise
  comparison of the mixed moments and the vanishing of the odd ones: every surviving coefficient
  `r^{m+n}` has even exponent, hence is nonnegative).  The full-series comparison
  `E(Σ_n r^n Y¹_n)² ≤ E(Σ_n r^n Y²_n)²` follows by passing to the limit (`norm_sq_tsum_le`);
  it is a Lean-side corollary, not a sentence of the TeX.
* (2) Complex `r`: absolute convergence of `Σ r^n Y_n` in the complex `L²(Ω)`
  (`summable_norm_smul_toC`, `summable_smul_toC`); and the second-moment formula
  `E|Σ_{n≤N} r^n Y_n|² = Σ_{m,n≤N} r^m conj(r)^n E[Y_m Y_n]` (`norm_sq_sum_smul_toC`, with
  `integral_norm_sq_eq`), with its limit for the full series (`tendsto_norm_sq_tsum_toC`).  The
  formula is not a sentence of the TeX; it is the identity behind "absolute convergence" being
  the same statement for real and complex `r`, and is recorded as a Lean-side addition.
* Wrapper `terminal_wick_full_constructed_paper`: every conclusion of `L:terminal-wick` for the
  constructed chain measures, under the TeX hypotheses only.

Supplied inputs: none.  Implicit hypotheses made explicit: none beyond those of
`TerminalWickInputs.terminal_wick_constructed_paper` (`0 ≤ T` for `chainMeasure`; `T > 0` as
in that wrapper).  Hypotheses carried but unused: `IsProbabilityMeasure` of both laws (the
TeX's setting; the field laws force it).

Differences from the TeX: the open ordered simplex, `G` in `d = 3`, the unformalized
symmetrization (lines 4384-4390) and the `d = 3` Green-regularization paragraph (lines
4392-4398) are as documented in `TerminalWickInputs`; both paragraphs are proof remarks that
identify conventions, not conclusions of the lemma statement.
Lemmas marked "Auxiliary" serve only the Lean proof route.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.TerminalWickInputs

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology Finset
open scoped ComplexConjugate

namespace StratonovichHAMSecondMoment.TerminalWickComplete

open TerminalWick TerminalWickInputs FiniteWick HomogHypothesis

/-! ### Real Hilbert-space algebra of the partial sums -/

section Hilbert
variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E']

/-- Auxiliary: `‖Σ_{n∈s} a_n Y_n‖² = Σ_{m,n∈s} a_m a_n ⟪Y_m, Y_n⟫`. -/
theorem norm_sq_sum_smul (Y : ℕ → E) (a : ℕ → ℝ) (s : Finset ℕ) :
    ‖∑ n ∈ s, a n • Y n‖ ^ 2 = ∑ m ∈ s, ∑ n ∈ s, a m * a n * inner ℝ (Y m) (Y n) := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [real_inner_smul_left, real_inner_smul_right]
  ring

/-- Partial-sum comparison (TeX lines 4331-4333, 4404-4406), abstract form: if the Gram entries
are entrywise comparable, `⟪Y_m, Y_n⟫ ≤ ⟪Y'_m, Y'_n⟫`, and vanish for odd `m + n` in both
families, then `‖Σ_{n∈s} r^n Y_n‖² ≤ ‖Σ_{n∈s} r^n Y'_n‖²` for every real `r` and every finite
index set `s` (each surviving coefficient `r^m r^n = r^{m+n}` has even exponent). -/
theorem norm_sq_partial_le (Y : ℕ → E) (Y' : ℕ → E')
    (hodd : ∀ m n, Odd (m + n) → inner ℝ (Y m) (Y n) = 0)
    (hodd' : ∀ m n, Odd (m + n) → inner ℝ (Y' m) (Y' n) = 0)
    (hmono : ∀ m n, inner ℝ (Y m) (Y n) ≤ inner ℝ (Y' m) (Y' n)) (r : ℝ) (s : Finset ℕ) :
    ‖∑ n ∈ s, r ^ n • Y n‖ ^ 2 ≤ ‖∑ n ∈ s, r ^ n • Y' n‖ ^ 2 := by
  rw [norm_sq_sum_smul, norm_sq_sum_smul]
  refine Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun n _ => ?_
  rcases Nat.even_or_odd (m + n) with h | h
  · have hc : 0 ≤ r ^ m * r ^ n := by rw [← pow_add]; exact h.pow_nonneg r
    exact mul_le_mul_of_nonneg_left (hmono m n) hc
  · rw [hodd m n h, hodd' m n h]

/-- Full-series comparison: under the hypotheses of `norm_sq_partial_le` and the convergence of
both series, `‖Σ_n r^n Y_n‖² ≤ ‖Σ_n r^n Y'_n‖²` (limit of the partial sums). -/
theorem norm_sq_tsum_le (Y : ℕ → E) (Y' : ℕ → E')
    (hodd : ∀ m n, Odd (m + n) → inner ℝ (Y m) (Y n) = 0)
    (hodd' : ∀ m n, Odd (m + n) → inner ℝ (Y' m) (Y' n) = 0)
    (hmono : ∀ m n, inner ℝ (Y m) (Y n) ≤ inner ℝ (Y' m) (Y' n)) (r : ℝ)
    (hs : Summable fun n => r ^ n • Y n) (hs' : Summable fun n => r ^ n • Y' n) :
    ‖∑' n, r ^ n • Y n‖ ^ 2 ≤ ‖∑' n, r ^ n • Y' n‖ ^ 2 :=
  le_of_tendsto_of_tendsto' ((hs.hasSum.tendsto_sum_nat).norm.pow 2)
    ((hs'.hasSum.tendsto_sum_nat).norm.pow 2)
    fun N => norm_sq_partial_le Y Y' hodd hodd' hmono r (range N)

end Hilbert

/-! ### The complex `L²` and complex `r` -/

section Complex
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The embedding of the real `L²(Ω)` into the complex `L²(Ω)`, `f ↦ (ω ↦ (f ω : ℂ))`. -/
def toC (f : Lp ℝ 2 P) : Lp ℂ 2 P := Complex.ofRealCLM.compLp f

/-- Auxiliary: `toC f = f` (as complex numbers) almost everywhere. -/
theorem coeFn_toC (f : Lp ℝ 2 P) : (toC f : Ω → ℂ) =ᵐ[P] fun ω => (f ω : ℂ) := by
  filter_upwards [Complex.ofRealCLM.coeFn_compLp f] with ω h
  rw [toC, h, Complex.ofRealCLM_apply]

/-- `⟪toC f, toC g⟫_ℂ = ⟪f, g⟫_ℝ`: the embedding preserves the inner product. -/
theorem inner_toC (f g : Lp ℝ 2 P) : inner ℂ (toC f) (toC g) = (inner ℝ f g : ℂ) := by
  rw [L2.inner_def, L2.inner_def, ← integral_complex_ofReal]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toC f, coeFn_toC g] with ω hf hg
  simp only [hf, hg, RCLike.inner_apply, Complex.conj_ofReal]
  simp [mul_comm]

/-- Auxiliary: `⟪g, g⟫_ℂ = ‖g‖²` with the complex-number cast. -/
theorem inner_self_eq_ofReal (g : Lp ℂ 2 P) : inner ℂ g g = ((‖g‖ ^ 2 : ℝ) : ℂ) := by
  simp

/-- `‖toC f‖ = ‖f‖`: the embedding is isometric. -/
theorem norm_toC (f : Lp ℝ 2 P) : ‖toC f‖ = ‖f‖ := by
  have h := inner_toC f f
  rw [inner_self_eq_ofReal, real_inner_self_eq_norm_sq] at h
  have h2 : ‖toC f‖ ^ 2 = ‖f‖ ^ 2 := by exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

/-- `E|f|² = ‖f‖²` in the complex `L²(Ω)` (so the integral is never a junk value). -/
theorem integral_norm_sq_eq (f : Lp ℂ 2 P) : ∫ ω, ‖f ω‖ ^ 2 ∂P = ‖f‖ ^ 2 := by
  have h := L2.inner_def (𝕜 := ℂ) f f
  rw [inner_self_eq_norm_sq_to_K] at h
  simp_rw [inner_self_eq_norm_sq_to_K] at h
  have h3 : ((∫ ω, ‖f ω‖ ^ 2 ∂P : ℝ) : ℂ) = ((‖f‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]; push_cast; exact h.symm
  exact_mod_cast h3

/-- Absolute convergence for complex `r` (TeX lines 4333-4335, "for every real or complex
`r`"), reduced to the real case: if `Σ_n ‖ρ^n Y_n‖` converges for the real `ρ = |r|`, then
`Σ_n ‖r^n Y_n‖` converges in the complex `L²`. -/
theorem summable_norm_smul_toC (Y : ℕ → Lp ℝ 2 P) (r : ℂ)
    (h : Summable fun n => ‖‖r‖ ^ n • Y n‖) :
    Summable fun n => ‖r ^ n • toC (Y n)‖ := by
  refine h.congr fun n => ?_
  rw [norm_smul, norm_smul, norm_toC, norm_pow, norm_pow, norm_norm]

/-- Convergence of `Σ_n r^n Y_n` in the complex `L²` (a complete space) from its absolute
convergence. -/
theorem summable_smul_toC (Y : ℕ → Lp ℝ 2 P) (r : ℂ)
    (h : Summable fun n => ‖‖r‖ ^ n • Y n‖) :
    Summable fun n => r ^ n • toC (Y n) :=
  (summable_norm_smul_toC Y r h).of_norm

/-- The complex second-moment formula for a finite partial sum (a Lean-side addition; see the
module doc): `‖Σ_{n∈s} r^n Y_n‖² = Σ_{m,n∈s} r^m conj(r)^n ⟪Y_m, Y_n⟫` in the complex `L²`. -/
theorem norm_sq_sum_smul_toC (Y : ℕ → Lp ℝ 2 P) (r : ℂ) (s : Finset ℕ) :
    ((‖∑ n ∈ s, r ^ n • toC (Y n)‖ ^ 2 : ℝ) : ℂ) =
      ∑ m ∈ s, ∑ n ∈ s, r ^ m * conj r ^ n * (inner ℝ (Y m) (Y n) : ℂ) := by
  rw [← inner_self_eq_ofReal, sum_inner]
  simp_rw [inner_sum, inner_smul_left, inner_smul_right, inner_toC, map_pow]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
  rw [real_inner_comm]
  ring

/-- The complex second-moment formula for the full series (Lean-side addition):
`‖Σ_n r^n Y_n‖²` is the limit of `Σ_{m,n<N} r^m conj(r)^n ⟪Y_m, Y_n⟫`. -/
theorem tendsto_norm_sq_tsum_toC (Y : ℕ → Lp ℝ 2 P) (r : ℂ)
    (h : Summable fun n => ‖‖r‖ ^ n • Y n‖) :
    Tendsto (fun N => ∑ m ∈ range N, ∑ n ∈ range N,
        r ^ m * conj r ^ n * (inner ℝ (Y m) (Y n) : ℂ)) atTop
      (𝓝 ((‖∑' n, r ^ n • toC (Y n)‖ ^ 2 : ℝ) : ℂ)) := by
  have ht := (((summable_smul_toC Y r h).hasSum.tendsto_sum_nat).norm.pow 2)
  have hc := (Complex.continuous_ofReal.tendsto _).comp ht
  refine hc.congr fun N => ?_
  exact norm_sq_sum_smul_toC Y r (range N)

end Complex

/-! ### The constructed terminal-chain measures -/

section Constructed

/-- Auxiliary: for the constructed chain measures, `⟪Y_m, Y_n⟫ = 0` when `m + n` is odd (TeX
line 4329, from `terminal_wick_constructed_paper`). -/
theorem inner_odd_constructed {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) (T : ℝ) (hT : 0 < T)
    (x : Rd d) (W : Pt d T → Ω → ℝ) (K : Pt d T → Pt d T → ℝ)
    (hW : CenteredGaussianField W K P) (hVfin : BddAbove (Set.range fun p => K p p))
    (hcell : MeanSquareCellContinuous K) (m n : ℕ) (hodd : Odd (m + n)) :
    inner ℝ (chainIntegral (fun n => chainMeasure d n T hT.le x) hW m)
      (chainIntegral (fun n => chainMeasure d n T hT.le x) hW n) = 0 := by
  rw [← mixed_moment_eq_inner]
  exact (terminal_wick_constructed_paper P d hd T hT x W K hW hVfin hcell).2.2.2.2.2.1 m n hodd

/-- Auxiliary: absolute `L²` convergence of `Σ ρ^n Y_n` for real `ρ` (TeX lines 4333-4335, from
`terminal_wick_constructed_paper`). -/
theorem summable_constructed {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) (T : ℝ) (hT : 0 < T)
    (x : Rd d) (W : Pt d T → Ω → ℝ) (K : Pt d T → Pt d T → ℝ)
    (hW : CenteredGaussianField W K P) (hVfin : BddAbove (Set.range fun p => K p p))
    (hcell : MeanSquareCellContinuous K) (ρ : ℝ) :
    Summable fun n => ‖ρ ^ n • chainIntegral (fun n => chainMeasure d n T hT.le x) hW n‖ :=
  (terminal_wick_constructed_paper P d hd T hT x W K hW hVfin hcell).2.2.2.2.2.2.2.1 ρ

/-- The partial-sum comparison of `L:terminal-wick` (main TeX lines 4331-4333, proof 4404-4406
at edf7085f) for the constructed terminal-chain measures `g_n^{T,x}`, with the full-series
comparison as a Lean-side corollary (not a sentence of the TeX).
Hypotheses, all the TeX's (those of `terminal_wick_mono_constructed_paper`): `d ∈ {1,2,3}`,
`T > 0`, `x ∈ ℝ^d`; two centered real Gaussian fields on `[0,T] × ℝ^d` with covariances `K₁`,
`K₂`, each with bounded variance and mean-square continuity on the cells of a finite
partition; `0 ≤ K₁ ≤ K₂` entrywise.  Conclusions: for every real `r` and every `N`,
`E(Σ_{n≤N} r^n Y¹_n)² ≤ E(Σ_{n≤N} r^n Y²_n)²`, and `E(Σ_n r^n Y¹_n)² ≤ E(Σ_n r^n Y²_n)²`.
`IsProbabilityMeasure` is carried, unused. -/
theorem partial_sum_mono_constructed_paper {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁]
    [MeasurableSpace Ω₂] (P₁ : Measure Ω₁) (P₂ : Measure Ω₂) [IsProbabilityMeasure P₁]
    [IsProbabilityMeasure P₂] (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) (T : ℝ) (hT : 0 < T)
    (x : Rd d)
    (W₁ : Pt d T → Ω₁ → ℝ) (K₁ : Pt d T → Pt d T → ℝ) (hW₁ : CenteredGaussianField W₁ K₁ P₁)
    (W₂ : Pt d T → Ω₂ → ℝ) (K₂ : Pt d T → Pt d T → ℝ) (hW₂ : CenteredGaussianField W₂ K₂ P₂)
    (hV₁fin : BddAbove (Set.range fun p => K₁ p p))
    (hV₂fin : BddAbove (Set.range fun p => K₂ p p))
    (hcell₁ : MeanSquareCellContinuous K₁) (hcell₂ : MeanSquareCellContinuous K₂)
    (h0 : ∀ p q, 0 ≤ K₁ p q) (h12 : ∀ p q, K₁ p q ≤ K₂ p q) :
    let ν : ∀ n : ℕ, Measure (Fin n → Pt d T) := fun n => chainMeasure d n T hT.le x
    (∀ (r : ℝ) (N : ℕ),
      ∫ ω, ((∑ n ∈ range (N + 1), r ^ n • chainIntegral ν hW₁ n : Lp ℝ 2 P₁) ω) ^ 2 ∂P₁ ≤
        ∫ ω, ((∑ n ∈ range (N + 1), r ^ n • chainIntegral ν hW₂ n : Lp ℝ 2 P₂) ω) ^ 2 ∂P₂) ∧
      ∀ r : ℝ,
        ∫ ω, ((∑' n, r ^ n • chainIntegral ν hW₁ n : Lp ℝ 2 P₁) ω) ^ 2 ∂P₁ ≤
          ∫ ω, ((∑' n, r ^ n • chainIntegral ν hW₂ n : Lp ℝ 2 P₂) ω) ^ 2 ∂P₂ := by
  intro ν
  have hodd₁ := inner_odd_constructed P₁ d hd T hT x W₁ K₁ hW₁ hV₁fin hcell₁
  have hodd₂ := inner_odd_constructed P₂ d hd T hT x W₂ K₂ hW₂ hV₂fin hcell₂
  have hmono : ∀ m n, inner ℝ (chainIntegral ν hW₁ m) (chainIntegral ν hW₁ n) ≤
      inner ℝ (chainIntegral ν hW₂ m) (chainIntegral ν hW₂ n) := fun m n => by
    rw [← mixed_moment_eq_inner, ← mixed_moment_eq_inner]
    exact terminal_wick_mono_constructed_paper P₁ P₂ d hd T hT x W₁ K₁ hW₁ W₂ K₂ hW₂
      hV₁fin hV₂fin hcell₁ hcell₂ h0 h12 m n
  refine ⟨fun r N => ?_, fun r => ?_⟩
  · rw [UniformSeriesTail.integral_sq_eq_norm_sq, UniformSeriesTail.integral_sq_eq_norm_sq]
    exact norm_sq_partial_le _ _ hodd₁ hodd₂ hmono r _
  · rw [UniformSeriesTail.integral_sq_eq_norm_sq, UniformSeriesTail.integral_sq_eq_norm_sq]
    exact norm_sq_tsum_le _ _ hodd₁ hodd₂ hmono r
      (summable_constructed P₁ d hd T hT x W₁ K₁ hW₁ hV₁fin hcell₁ r).of_norm
      (summable_constructed P₂ d hd T hT x W₂ K₂ hW₂ hV₂fin hcell₂ r).of_norm

/-- The complex-`r` sentence of `L:terminal-wick` (main TeX lines 4333-4335, proof 4406-4409 at
edf7085f) for the constructed terminal-chain measures `g_n^{T,x}`, under the hypotheses of the
lemma for one field.  Conclusions, for every complex `r`: `Σ_n r^n Y_n` converges absolutely,
hence converges, in the complex `L²(Ω)` (the TeX's sentence); and (Lean-side addition, not a
TeX sentence) `E|Σ_{n≤N} r^n Y_n|² = Σ_{m,n≤N} r^m conj(r)^n E[Y_m Y_n]` for every `N`, with
the full-series second moment `E|Σ_n r^n Y_n|²` the limit of the same double sums over
`m, n < N`.  `IsProbabilityMeasure` is carried, unused. -/
theorem terminal_wick_complex_constructed_paper {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) (T : ℝ)
    (hT : 0 < T) (x : Rd d) (W : Pt d T → Ω → ℝ) (K : Pt d T → Pt d T → ℝ)
    (hW : CenteredGaussianField W K P) (hVfin : BddAbove (Set.range fun p => K p p))
    (hcell : MeanSquareCellContinuous K) :
    let ν : ∀ n : ℕ, Measure (Fin n → Pt d T) := fun n => chainMeasure d n T hT.le x
    (∀ r : ℂ, Summable (fun n => ‖r ^ n • toC (chainIntegral ν hW n)‖) ∧
      Summable (fun n => r ^ n • toC (chainIntegral ν hW n))) ∧
    (∀ (r : ℂ) (N : ℕ),
      ((∫ ω, ‖(∑ n ∈ range (N + 1), r ^ n • toC (chainIntegral ν hW n) : Lp ℂ 2 P) ω‖ ^ 2
        ∂P : ℝ) : ℂ) =
        ∑ m ∈ range (N + 1), ∑ n ∈ range (N + 1), r ^ m * conj r ^ n *
          ((∫ ω, chainIntegral ν hW m ω * chainIntegral ν hW n ω ∂P : ℝ) : ℂ)) ∧
    ∀ r : ℂ, Tendsto (fun N => ∑ m ∈ range N, ∑ n ∈ range N, r ^ m * conj r ^ n *
        ((∫ ω, chainIntegral ν hW m ω * chainIntegral ν hW n ω ∂P : ℝ) : ℂ)) atTop
      (𝓝 ((∫ ω, ‖(∑' n, r ^ n • toC (chainIntegral ν hW n) : Lp ℂ 2 P) ω‖ ^ 2 ∂P : ℝ) : ℂ)) := by
  intro ν
  have hs := summable_constructed P d hd T hT x W K hW hVfin hcell
  refine ⟨fun r => ⟨summable_norm_smul_toC _ r (hs ‖r‖), summable_smul_toC _ r (hs ‖r‖)⟩,
    fun r N => ?_, fun r => ?_⟩
  · rw [integral_norm_sq_eq, norm_sq_sum_smul_toC]
    simp_rw [mixed_moment_eq_inner]
  · rw [integral_norm_sq_eq]
    simp_rw [mixed_moment_eq_inner]
    exact tendsto_norm_sq_tsum_toC _ r (hs ‖r‖)

/-- `L:terminal-wick` (main TeX lines 4291-4336, proof 4338-4410 at edf7085f) in full, for the
terminal-chain measures `g_n^{T,x}` of `E:terminal-chain-measure` (lines 4275-4288) constructed
in `TerminalWickInputs`.  Hypotheses, all the TeX's: `d ∈ {1,2,3}`, `T > 0`, `x ∈ ℝ^d`; a
centered real Gaussian field `W₁` on `[0,T] × ℝ^d` with covariance `K₁` (lines 4292-4293),
`V = sup K₁(p,p) < ∞` (line 4294), mean-square continuity on the open cells of a finite
partition (lines 4294-4296); and, for the comparison sentence (lines 4331-4333), a second field
`W₂` with covariance `K₂` under the same hypotheses.  Conclusions:
* every conclusion of `terminal_wick_constructed_paper` for `W₁` (existence of the Bochner
  integrals, `Y_0 = 1`, `E:terminal-term-majorant`, `E:terminal-wick-formula` with integrable
  pairing integrands, zero for odd `m + n`, nonnegativity when `K₁ ≥ 0`, absolute convergence
  for real `r`, and the `TerminalWickInput` package);
* absolute convergence for complex `r`, with the complex second-moment formula
  (`terminal_wick_complex_constructed_paper`);
* if `0 ≤ K₁ ≤ K₂`: `E[Y¹_m Y¹_n] ≤ E[Y²_m Y²_n]` for all `m, n`,
  `E(Σ_{n≤N} r^n Y¹_n)² ≤ E(Σ_{n≤N} r^n Y²_n)²` for all real `r` and all `N`, and the same for
  the full series (a Lean-side corollary, not a sentence of the TeX).
No hypothesis is added; `IsProbabilityMeasure` (the TeX's setting) is carried, unused. -/
theorem terminal_wick_full_constructed_paper {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁]
    [MeasurableSpace Ω₂] (P₁ : Measure Ω₁) (P₂ : Measure Ω₂) [IsProbabilityMeasure P₁]
    [IsProbabilityMeasure P₂] (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) (T : ℝ) (hT : 0 < T)
    (x : Rd d)
    (W₁ : Pt d T → Ω₁ → ℝ) (K₁ : Pt d T → Pt d T → ℝ) (hW₁ : CenteredGaussianField W₁ K₁ P₁)
    (hV₁fin : BddAbove (Set.range fun p => K₁ p p)) (hcell₁ : MeanSquareCellContinuous K₁)
    (W₂ : Pt d T → Ω₂ → ℝ) (K₂ : Pt d T → Pt d T → ℝ) (hW₂ : CenteredGaussianField W₂ K₂ P₂)
    (hV₂fin : BddAbove (Set.range fun p => K₂ p p)) (hcell₂ : MeanSquareCellContinuous K₂) :
    let ν : ∀ n : ℕ, Measure (Fin n → Pt d T) := fun n => chainMeasure d n T hT.le x
    ((∀ n, Integrable (fun z : Fin n → Pt d T => prodL2 hW₁ z) (ν n)) ∧
      ((chainIntegral ν hW₁ 0 : Ω₁ → ℝ) =ᵐ[P₁] fun _ => 1) ∧
      (∀ n, ‖chainIntegral ν hW₁ n‖ ≤ Real.sqrt ((2 * n - 1).doubleFactorial) *
        (⨆ p, K₁ p p) ^ ((n : ℝ) / 2) * (T ^ (2 * n) / (2 * n).factorial)) ∧
      (∀ m n, ∫ ω, chainIntegral ν hW₁ m ω * chainIntegral ν hW₁ n ω ∂P₁ =
        ∑ D ∈ pairings (univ : Finset (Fin (m + n))), pairingIntegral ν K₁ m n D) ∧
      (∀ m n (D : Fin (m + n) → Fin (m + n)),
        Integrable (fun q : (Fin m → Pt d T) × (Fin n → Pt d T) =>
          pairWeight (fun a b => K₁ (Fin.append q.1 q.2 a) (Fin.append q.1 q.2 b)) univ D)
          ((ν m).prod (ν n))) ∧
      (∀ m n, Odd (m + n) → ∫ ω, chainIntegral ν hW₁ m ω * chainIntegral ν hW₁ n ω ∂P₁ = 0) ∧
      ((∀ p q, 0 ≤ K₁ p q) →
        (∀ m n (D : Fin (m + n) → Fin (m + n)), 0 ≤ pairingIntegral ν K₁ m n D) ∧
        ∀ m n, 0 ≤ ∫ ω, chainIntegral ν hW₁ m ω * chainIntegral ν hW₁ n ω ∂P₁) ∧
      (∀ r : ℝ, Summable fun n => ‖r ^ n • chainIntegral ν hW₁ n‖) ∧
      ((∀ p q, 0 ≤ K₁ p q) → ∀ r : ℝ,
        UniformSeriesTail.TerminalWickInput P₁ (fun n => chainIntegral ν hW₁ n) r)) ∧
    ((∀ r : ℂ, Summable (fun n => ‖r ^ n • toC (chainIntegral ν hW₁ n)‖) ∧
      Summable (fun n => r ^ n • toC (chainIntegral ν hW₁ n))) ∧
    (∀ (r : ℂ) (N : ℕ),
      ((∫ ω, ‖(∑ n ∈ range (N + 1), r ^ n • toC (chainIntegral ν hW₁ n) : Lp ℂ 2 P₁) ω‖ ^ 2
        ∂P₁ : ℝ) : ℂ) =
        ∑ m ∈ range (N + 1), ∑ n ∈ range (N + 1), r ^ m * conj r ^ n *
          ((∫ ω, chainIntegral ν hW₁ m ω * chainIntegral ν hW₁ n ω ∂P₁ : ℝ) : ℂ)) ∧
    ∀ r : ℂ, Tendsto (fun N => ∑ m ∈ range N, ∑ n ∈ range N, r ^ m * conj r ^ n *
        ((∫ ω, chainIntegral ν hW₁ m ω * chainIntegral ν hW₁ n ω ∂P₁ : ℝ) : ℂ)) atTop
      (𝓝 ((∫ ω, ‖(∑' n, r ^ n • toC (chainIntegral ν hW₁ n) : Lp ℂ 2 P₁) ω‖ ^ 2
        ∂P₁ : ℝ) : ℂ))) ∧
    ((∀ p q, 0 ≤ K₁ p q) → (∀ p q, K₁ p q ≤ K₂ p q) →
      (∀ m n, ∫ ω, chainIntegral ν hW₁ m ω * chainIntegral ν hW₁ n ω ∂P₁ ≤
        ∫ ω, chainIntegral ν hW₂ m ω * chainIntegral ν hW₂ n ω ∂P₂) ∧
      (∀ (r : ℝ) (N : ℕ),
        ∫ ω, ((∑ n ∈ range (N + 1), r ^ n • chainIntegral ν hW₁ n : Lp ℝ 2 P₁) ω) ^ 2 ∂P₁ ≤
          ∫ ω, ((∑ n ∈ range (N + 1), r ^ n • chainIntegral ν hW₂ n : Lp ℝ 2 P₂) ω) ^ 2
            ∂P₂) ∧
      ∀ r : ℝ,
        ∫ ω, ((∑' n, r ^ n • chainIntegral ν hW₁ n : Lp ℝ 2 P₁) ω) ^ 2 ∂P₁ ≤
          ∫ ω, ((∑' n, r ^ n • chainIntegral ν hW₂ n : Lp ℝ 2 P₂) ω) ^ 2 ∂P₂) :=
  ⟨terminal_wick_constructed_paper P₁ d hd T hT x W₁ K₁ hW₁ hV₁fin hcell₁,
    terminal_wick_complex_constructed_paper P₁ d hd T hT x W₁ K₁ hW₁ hV₁fin hcell₁,
    fun h0 h12 => ⟨terminal_wick_mono_constructed_paper P₁ P₂ d hd T hT x W₁ K₁ hW₁ W₂ K₂ hW₂
      hV₁fin hV₂fin hcell₁ hcell₂ h0 h12,
      partial_sum_mono_constructed_paper P₁ P₂ d hd T hT x W₁ K₁ hW₁ W₂ K₂ hW₂
        hV₁fin hV₂fin hcell₁ hcell₂ h0 h12⟩⟩

end Constructed

end StratonovichHAMSecondMoment.TerminalWickComplete
