module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L15, item L15-UM (interface; scope (a), approved by Le on 2026-11-19).  The frozen Lean
objects and statement shapes for `L:uniform-E-lift` (UM-1, agent A) and the mean identity of
`E:positive-raw-mean` (UM-2, agent B).  Nothing in this module proves a UM-1 or UM-2 result.

TeX anchors (all at revision 0788ddee, book 1.1.0, read with `git show 0788ddee:notes/...`; the
same line numbers at edf7085f, book 1.1.3):
* `notes/integrated_intrinsic_constant.tex`: section setup lines 1-21 (`J_R = T_R`,
  `𝒯_R = T_R(C_t ⊗ I)`, `B_E(V)(u,v) = (0,Vu)` line 10-11, `m_R = η(·/R)²` line 12);
  `L:positive-raw-embedding` statement lines 23-40, `E:positive-raw-mean` line 34-37, the
  canonical-version sentence lines 38-39, proof lines 42-132.
* `notes/integrated_uniform_products.tex`: setup lines 1-31 (`E = H^{1/2} × H^{-1/2}`, `m_R`,
  `𝒯_R = T_R(C_t ⊗ I_{H_sp})` with its `L^r` bound, lines 17-21; `V_q = m_R(Γ*q)`, `M_q`,
  `L_q^E(u,v) = (0, M_q u)`, `𝒱_{E,R}` lines 29-31); `L:uniform-E-lift` lines 33-69
  (`E:uniform-E-pairing` lines 39-41).
* `notes/integrated_uniform_mean.tex`: setup lines 1-32 (the cutoff profile `η` lines 7-9,
  `η_R`, `m_R = η_R²` line 9-10, the inner product of `E` lines 10-17, `E:uniform-mean-row`
  lines 22-27); the definitions of `U`, `c_t` and `𝒯_R = T_R U` lines 257-270;
  `P:uniform-mean-regulator` lines 272-288 (statement), 290-334 (proof).
* `notes/integrated_cameron_mean.tex`: `Λ = (1-Δ)^{1/2}` line 6, `H_sp`, `H_t` lines 8-11;
  `P:cameron-temporal-map` lines 225-237 (statement; `C_t f = K f` on tests, line 273);
  `P:cameron-spatial-map` lines 104-119 (statement), 121-140 (row step of the proof).
* `notes/integrated_compact_gaussian.tex` lines 275-277: the norm of `H^r(ℝ^d)` is
  `‖⟨ξ⟩^r û‖₂` for the unitary Fourier transform, `Λ = (1-Δ)^{1/2}`.

Objects (new):
* `CutoffProfile d`: the fixed cutoff `η` (uniform-mean lines 7-9); `etaR η R = η(·/R)`,
  `mR η R = η_R²` (`mRfun` on a bare function).
* `msWeight σ ξ = (1 + 4π²|ξ|²)^{σ/2}` (the manuscript's `⟨ζ⟩^σ` at `ζ = 2πξ`, Mathlib's `𝓕`
  being `e^{-2πi⟪x,ξ⟫}`); `coord σ φ = msWeight σ · 𝓕φ ∈ L²(ℝ^d; ℂ)` for a real test `φ`.
  `‖coord σ φ‖₂ = ‖φ‖_{H^σ}` in the manuscript's norm (substitute `ζ = 2πξ` in
  `∫ ⟨ζ⟩^{2σ} |ũ(ζ)|² dζ`, `ũ` the unitary transform).
* `HR d`: the closed real subspace of Hermitian-symmetric classes `U(-ξ) = conj U(ξ)` of
  `L²(ℝ^d; ℂ)` (the Fourier images of real distributions), viewed as a real Hilbert space.
* `Hhalf d`, `Hmhalf d`: the real spaces `H^{1/2}(ℝ^d)`, `H^{-1/2}(ℝ^d)`, both realized on
  `HR d` through the coordinate `u ↦ ⟨2πξ⟩^{±1/2} 𝓕u` (type synonyms, so they cannot be
  confused); `toHhalf φ`, `toHmhalf φ` the classes of a real test function.
* `lam : Hhalf d ≃ₗᵢ[ℝ] Hmhalf d` (the TeX's `Λ`), the identity in coordinates; `dpair v u`
  the duality `⟨v,u⟩_{H^{-1/2},H^{1/2}} = ⟪Λ⁻¹ v, u⟫_{H^{1/2}}`.
* `E d = WithLp 2 (Hhalf d × Hmhalf d)` with `⟪(u,v),(u',v')⟫_E = ⟪u,u'⟫ + ⟪v,v'⟫`; `toE`.
* `BE M (u,v) = (0, M u)` (`B_E`), `IsMultiplier V M` (`M` is the multiplier by the smooth
  function `V`), `vPair M u w = ⟨M u, w⟩` (the TeX's `v_V(u,w)`), `SupportedIn`, `ActsAs`.
* `rowTest η R f g = (η_R f)(η_R g)` (the row `k_R(z,w)` of `E:uniform-mean-row` at
  `z₁ = f`, `Λ⁻¹ w₂ = g`).
* `VER S η R` (`𝒱_{E,R}`), `meanOp T U = T ∘ U` pointwise in time (`𝒯_R = T_R U`).

Named inputs (true inputs of scope (a), not formalized in L15; no `sorry`, no axiom):
* `CameronSpatialMap S η R`: the `E` restriction of `P:cameron-spatial-map` at radius `R`.
* `UniformMeanRegulator p S η r`: the data `T_R` (all `R ≥ 1`), `C_t`, `U` that
  `P:uniform-mean-regulator` is stated about, with the facts of `P:cameron-temporal-map`,
  `P:cameron-full-mean`/`L:uniform-mean-tensor` and the first bound of
  `E:uniform-completed-mean` (see its docstring for exactly what is and is not carried).

Statement shapes (definitions `: Prop`, not proved here):
* UM-1: `UniformELiftTarget S η` (operator form, norm equality, unique potential of
  `L:uniform-E-lift`) and `UniformEPairingTarget S η` (symmetry and `E:uniform-E-pairing`).
* UM-2: `PositiveRawMeanTarget U` (`E:positive-raw-mean`, mean identity, a.e. and canonical).

Proved here (small, interface sanity only): `coordSchwartz_neg` (real tests have Hermitian
coordinates), `coord_mem_HR`, `toHhalf_coe`, `toHmhalf_coe`, `mRfun_chiRoot` (the relation of
`RemoveMask.mask` with `m_R`).

Relation to `RemoveMask` (decision 7 of L15).  `RemoveMask.mask R x = χ(|x|/R)` is the mask of
`P:variational-remove-mask` (unmasked file, revision edf7085f).  With the radial profile
`chiRoot x = √χ(|x|)` one has `mRfun chiRoot R = RemoveMask.mask R` for `R > 0`
(`mRfun_chiRoot`).  `chiRoot` satisfies every clause of `CutoffProfile` (`√F(t) = e^{-1/(2t)}`
is smooth, the denominator of `χ` is positive, and `χ(|x|) = 1` near `0`); that smoothness is
not proved here and is not used in L15.  The new modules use `mR` and never change `RemoveMask`.

Modelling choices (see `docs/l15/INTERFACE.md` for the full list):
* `H_sp` and `H_I` are `OccupationCompletion.Hsp S` and `OccupationCompletion.HI p S`
  (the kernel completion of `L²(I; H_sp)`, decision 4 of L9/L14: not a tensor product).
* The row of `E:uniform-mean-row` is carried on test states only (`z₁ = f`, `w₂ = Λ g`, tests
  `f,g`, arbitrary `z₂, w₁`).  These states are dense and `T_R q` is bounded, so this
  determines `T_R q`; for rough states `k_R(z,w)` needs the fractional product map of
  `L:cameron-fractional-products`, which is not formalized.
* Only the `E` part of the `F = E ⊕ ℝ²` map is carried (the constant columns enter only the
  lift `L_F` of `L:uniform-E-lift`, which is not a UM-1 target).
-/
public import Mathlib
public import StratonovichHAMSecondMoment.OccupationCompletion
public import StratonovichHAMSecondMoment.RemoveMask
public import StratonovichHAMSecondMoment.H1Mathlib

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology FourierTransform
open scoped ENNReal ContDiff SchwartzMap RealInnerProductSpace ComplexConjugate Real

namespace StratonovichHAMSecondMoment.UniformMeanInterface

open HomogHypothesis (Rd)
open WeakSobolev (IsTestFunction)
open OccupationCompletion (TParams SpData Hsp toHsp Ht HI J incl)
open VariationalDilation (CPos conv mean)
open SpaceTimePositivity (timeMeasure)
open TimeSchur (kern)

variable {d : ℕ}

/-! ### The cutoff profile `η`, `η_R` and `m_R` -/

/-- **The fixed cutoff profile** of `integrated_uniform_mean.tex` lines 7-9 at revision
edf7085f (book 1.1.3): a real even smooth compactly supported `η`, equal to one on the unit
ball, with `0 ≤ η ≤ 1` and support in the closed radius-two ball. -/
structure CutoffProfile (d : ℕ) where
  /-- the profile `η`. -/
  η : Rd d → ℝ
  smooth : ContDiff ℝ ∞ η
  even : ∀ x, η (-x) = η x
  nonneg : ∀ x, 0 ≤ η x
  le_one : ∀ x, η x ≤ 1
  eq_one : ∀ x, ‖x‖ ≤ 1 → η x = 1
  support_subset : tsupport η ⊆ Metric.closedBall 0 2

/-- `η_R(x) = η(x/R)` (`integrated_uniform_mean.tex` line 9 at revision edf7085f, book
1.1.3). -/
def etaR (η : CutoffProfile d) (R : ℝ) (x : Rd d) : ℝ := η.η (R⁻¹ • x)

/-- `m_R = η(·/R)²` for a bare function `η` (the form used by `SourceHeatGram`, line 1401). -/
def mRfun (η : Rd d → ℝ) (R : ℝ) (x : Rd d) : ℝ := η (R⁻¹ • x) ^ 2

/-- **The physical mask** `m_R = η_R² = η(·/R)²` (`integrated_uniform_mean.tex` lines 9-10,
`integrated_intrinsic_constant.tex` line 12, `integrated_uniform_products.tex` line 5, all at
revision edf7085f, book 1.1.3). -/
def mR (η : CutoffProfile d) (R : ℝ) (x : Rd d) : ℝ := mRfun η.η R x

/-- `m_R = η_R²` (definitional). -/
theorem mR_eq (η : CutoffProfile d) (R : ℝ) (x : Rd d) : mR η R x = etaR η R x ^ 2 := rfl

/-- The radial profile `√χ(|x|)` of `RemoveMask` (`χ = RemoveMask.chi`). -/
def chiRoot (x : Rd d) : ℝ := Real.sqrt (RemoveMask.chi ‖x‖)

/-- **Relation of `RemoveMask.mask` with `m_R`** (decision 7 of L15): for `R > 0`,
`RemoveMask.mask R = (√χ(|·|/R))²`, i.e. the mask of `P:variational-remove-mask` is the
`m_R` of the profile `chiRoot`. -/
theorem mRfun_chiRoot {R : ℝ} (hR : 0 < R) (x : Rd d) :
    mRfun chiRoot R x = RemoveMask.mask R x := by
  unfold mRfun chiRoot RemoveMask.mask
  rw [Real.sq_sqrt (RemoveMask.chi_mem _).1, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hR), inv_mul_eq_div]

/-! ### Fourier coordinates of real test functions -/

/-- The manuscript's weight `⟨2πξ⟩^σ = (1 + |2πξ|²)^{σ/2} = (1 + 4π²|ξ|²)^{σ/2}`,
complexified.  With Mathlib's
`𝓕` (`e^{-2πi⟪x,ξ⟫}`, unitary on `L²`), `‖msWeight σ · 𝓕u‖₂` is the manuscript's `H^σ`
norm `‖⟨ζ⟩^σ ũ‖₂` (`integrated_compact_gaussian.tex` lines 275-277 at revision edf7085f,
book 1.1.3; `ũ` unitary, `ζ = 2πξ`). -/
def msWeight (σ : ℝ) (ξ : Rd d) : ℂ := (((1 + ‖(2 * π) • ξ‖ ^ 2) ^ (σ / 2) : ℝ) : ℂ)

/-- Auxiliary: the weight has temperate growth. -/
theorem msWeight_growth (σ : ℝ) : (msWeight (d := d) σ).HasTemperateGrowth := by
  have hl : (fun ξ : Rd d => (2 * π) • ξ).HasTemperateGrowth :=
    ((2 * π) • ContinuousLinearMap.id ℝ (Rd d)).hasTemperateGrowth
  exact Complex.hasTemperateGrowth_ofReal.comp
    ((Function.hasTemperateGrowth_one_add_norm_sq_rpow (Rd d) (σ / 2)).comp hl)

/-- The coordinate `msWeight σ · 𝓕φ` of a real test function, as a Schwartz function. -/
def coordSchwartz (σ : ℝ) {φ : Rd d → ℝ} (hφ : IsTestFunction φ) : 𝓢(Rd d, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (msWeight σ) (𝓕 (H1Mathlib.testSchwartz hφ))

open Classical in
/-- The coordinate `msWeight σ · 𝓕φ ∈ L²(ℝ^d; ℂ)` of a real test function `φ` (the value `0`
is taken off the tests, as for `OccupationCompletion.toHsp`). -/
def coord (σ : ℝ) (φ : Rd d → ℝ) : Lp ℂ 2 (volume : Measure (Rd d)) :=
  if hφ : IsTestFunction φ then (coordSchwartz σ hφ).toLp 2 else 0

/-- Auxiliary: the Fourier transform of a real integrable-type function is Hermitian,
`𝓕φ(-ξ) = conj 𝓕φ(ξ)`. -/
theorem fourier_real_neg (φ : Rd d → ℝ) (ξ : Rd d) :
    𝓕 (fun x => (φ x : ℂ)) (-ξ) = conj (𝓕 (fun x => (φ x : ℂ)) ξ) := by
  rw [Real.fourier_eq', Real.fourier_eq', ← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [smul_eq_mul, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I,
    inner_neg_right]
  congr 2
  push_cast
  ring

/-- Auxiliary: the coordinate of a real test is Hermitian. -/
theorem coordSchwartz_neg (σ : ℝ) {φ : Rd d → ℝ} (hφ : IsTestFunction φ) (ξ : Rd d) :
    coordSchwartz σ hφ (-ξ) = conj (coordSchwartz σ hφ ξ) := by
  simp only [coordSchwartz, SchwartzMap.smulLeftCLM_apply_apply (msWeight_growth σ),
    SchwartzMap.fourier_coe, smul_eq_mul, map_mul]
  have h1 : (⇑(H1Mathlib.testSchwartz hφ)) = fun x => (φ x : ℂ) := rfl
  rw [h1, fourier_real_neg]
  congr 1
  simp [msWeight, norm_neg, Complex.conj_ofReal]

/-- Auxiliary: almost-everywhere statements transfer along `ξ ↦ -ξ`. -/
theorem ae_comp_neg {p : Rd d → Prop} (h : ∀ᵐ ξ, p ξ) : ∀ᵐ ξ : Rd d, p (-ξ) :=
  (Measure.measurePreserving_neg (volume : Measure (Rd d))).quasiMeasurePreserving.ae h

/-- The Hermitian-symmetric classes `U(-ξ) = conj U(ξ)` of `L²(ℝ^d; ℂ)`, a real subspace. -/
def herm (d : ℕ) : Submodule ℝ (Lp ℂ 2 (volume : Measure (Rd d))) where
  carrier := {U | ∀ᵐ ξ, (U : Rd d → ℂ) (-ξ) = conj ((U : Rd d → ℂ) ξ)}
  zero_mem' := by
    have h0 := Lp.coeFn_zero ℂ 2 (volume : Measure (Rd d))
    filter_upwards [h0, ae_comp_neg h0] with ξ h1 h2
    simp
  add_mem' := by
    intro U V hU hV
    have h0 := Lp.coeFn_add U V
    filter_upwards [hU, hV, h0, ae_comp_neg h0] with ξ h1 h2 h3 h4
    rw [h3, h4, Pi.add_apply, Pi.add_apply, h1, h2, map_add]
  smul_mem' := by
    intro c U hU
    have h0 := Lp.coeFn_smul c U
    filter_upwards [hU, h0, ae_comp_neg h0] with ξ h1 h3 h4
    rw [h3, h4, Pi.smul_apply, Pi.smul_apply, h1, Complex.real_smul, Complex.real_smul,
      map_mul, Complex.conj_ofReal]

/-- **The real Fourier-coordinate space** `HR d`: the closure of `herm d` (closed already;
taking the closure gives completeness without a separate proof). -/
def HR (d : ℕ) : Submodule ℝ (Lp ℂ 2 (volume : Measure (Rd d))) := (herm d).topologicalClosure

/-- Auxiliary: `HR d` is complete. -/
instance instCompleteSpaceHR : CompleteSpace (HR d) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

/-- Auxiliary: the coordinate of a real test lies in `HR d`. -/
theorem coord_mem_HR (σ : ℝ) {φ : Rd d → ℝ} (hφ : IsTestFunction φ) : coord σ φ ∈ HR d := by
  refine Submodule.le_topologicalClosure _ ?_
  have h0 := (coordSchwartz σ hφ).coeFn_toLp 2 (volume : Measure (Rd d))
  show ∀ᵐ ξ, (coord σ φ : Rd d → ℂ) (-ξ) = conj ((coord σ φ : Rd d → ℂ) ξ)
  simp only [coord, hφ, dite_true]
  filter_upwards [h0, ae_comp_neg h0] with ξ h1 h2
  rw [h1, h2, coordSchwartz_neg]

/-! ### The spaces `H^{±1/2}`, `Λ`, the duality and `E` -/

/-- **`H^{1/2}(ℝ^d)` (real)** of `E = H^{1/2} × H^{-1/2}` (`integrated_uniform_mean.tex`
line 10, `integrated_uniform_products.tex` line 4, at revision edf7085f, book 1.1.3),
realized through the unitary coordinate `u ↦ ⟨2πξ⟩^{1/2} 𝓕u` on `HR d`. -/
def Hhalf (d : ℕ) : Type := HR d

/-- **`H^{-1/2}(ℝ^d)` (real)**, realized through `v ↦ ⟨2πξ⟩^{-1/2} 𝓕v` on `HR d`. -/
def Hmhalf (d : ℕ) : Type := HR d

instance : NormedAddCommGroup (Hhalf d) := inferInstanceAs (NormedAddCommGroup (HR d))
instance : InnerProductSpace ℝ (Hhalf d) := inferInstanceAs (InnerProductSpace ℝ (HR d))
instance : CompleteSpace (Hhalf d) := inferInstanceAs (CompleteSpace (HR d))
instance : NormedAddCommGroup (Hmhalf d) := inferInstanceAs (NormedAddCommGroup (HR d))
instance : InnerProductSpace ℝ (Hmhalf d) := inferInstanceAs (InnerProductSpace ℝ (HR d))
instance : CompleteSpace (Hmhalf d) := inferInstanceAs (CompleteSpace (HR d))

/-- The class in `H^{1/2}` of a real test function (coordinate `⟨2πξ⟩^{1/2} 𝓕φ`; `0` off the
tests). -/
def toHhalf (φ : Rd d → ℝ) : Hhalf d :=
  open Classical in
  if hφ : IsTestFunction φ then (⟨coord (1 / 2) φ, coord_mem_HR _ hφ⟩ : HR d) else (0 : HR d)

/-- The class in `H^{-1/2}` of a real test function (coordinate `⟨2πξ⟩^{-1/2} 𝓕φ`; `0` off
the tests). -/
def toHmhalf (φ : Rd d → ℝ) : Hmhalf d :=
  open Classical in
  if hφ : IsTestFunction φ then (⟨coord (-1 / 2) φ, coord_mem_HR _ hφ⟩ : HR d) else (0 : HR d)

/-- Auxiliary: the coordinate of `toHhalf φ` for a test `φ`. -/
theorem toHhalf_coe {φ : Rd d → ℝ} (hφ : IsTestFunction φ) :
    ((show HR d from toHhalf φ) : Lp ℂ 2 (volume : Measure (Rd d))) = coord (1 / 2) φ := by
  simp [toHhalf, hφ]

/-- Auxiliary: the coordinate of `toHmhalf φ` for a test `φ`. -/
theorem toHmhalf_coe {φ : Rd d → ℝ} (hφ : IsTestFunction φ) :
    ((show HR d from toHmhalf φ) : Lp ℂ 2 (volume : Measure (Rd d))) = coord (-1 / 2) φ := by
  simp [toHmhalf, hφ]

/-- **`Λ = (1-Δ)^{1/2} : H^{1/2} → H^{-1/2}`** (`integrated_cameron_mean.tex` line 6 at revision
edf7085f, book 1.1.3), an isometric isomorphism; in the Fourier coordinates it is the
identity (`⟨2πξ⟩^{-1/2} · ⟨2πξ⟩ · 𝓕u = ⟨2πξ⟩^{1/2} 𝓕u`).  `lam.symm` is `Λ⁻¹`. -/
def lam : Hhalf d ≃ₗᵢ[ℝ] Hmhalf d := LinearIsometryEquiv.refl ℝ (HR d)

/-- **The duality** `⟨v, u⟩_{H^{-1/2},H^{1/2}} = ⟪Λ⁻¹ v, u⟫_{H^{1/2}}`; for real tests it is
`∫ v u` (Plancherel), and `⟪v, Λ u⟫_{H^{-1/2}} = ⟨v, u⟩` (the "velocity pairing with weight
`Λ⁻¹`" of `integrated_cameron_mean.tex` line 133-134 at revision edf7085f, book 1.1.3). -/
def dpair (v : Hmhalf d) (u : Hhalf d) : ℝ := ⟪lam.symm v, u⟫

/-- **The phase `E = H^{1/2} × H^{-1/2}`** (`integrated_uniform_mean.tex` lines 10-17 at
revision edf7085f, book 1.1.3) with the Hilbert product `⟪(u,v),(u',v')⟫_E = ⟪u,u'⟫ + ⟪v,v'⟫`
(in the coordinates of `Hhalf`, `Hmhalf`, the TeX's displayed inner product
`⟨Λ^{1/2}z₁,Λ^{1/2}w₁⟩_{L²} + ⟨Λ^{-1/2}z₂,Λ^{-1/2}w₂⟩_{L²}`, lines 12-17). -/
def E (d : ℕ) : Type := WithLp 2 (Hhalf d × Hmhalf d)

instance : NormedAddCommGroup (E d) :=
  inferInstanceAs (NormedAddCommGroup (WithLp 2 (Hhalf d × Hmhalf d)))
instance : InnerProductSpace ℝ (E d) :=
  inferInstanceAs (InnerProductSpace ℝ (WithLp 2 (Hhalf d × Hmhalf d)))
instance : CompleteSpace (E d) := inferInstanceAs (CompleteSpace (WithLp 2 (Hhalf d × Hmhalf d)))

/-- The identification `E ≃ H^{1/2} × H^{-1/2}` (continuous linear). -/
def eEquiv : E d ≃L[ℝ] Hhalf d × Hmhalf d := WithLp.prodContinuousLinearEquiv 2 ℝ _ _

/-- The state `(u, v) ∈ E`. -/
def toE (u : Hhalf d) (v : Hmhalf d) : E d := eEquiv.symm (u, v)

/-- **`B_E(V)(u,v) = (0, V u)`** for a bounded `V : H^{1/2} → H^{-1/2}`
(`integrated_intrinsic_constant.tex` lines 10-11 at revision edf7085f, book 1.1.3). -/
def BE (M : Hhalf d →L[ℝ] Hmhalf d) : E d →L[ℝ] E d :=
  (eEquiv (d := d)).symm.toContinuousLinearMap ∘L
    ((0 : Hhalf d × Hmhalf d →L[ℝ] Hhalf d).prod
      (M ∘L ContinuousLinearMap.fst ℝ (Hhalf d) (Hmhalf d))) ∘L
    (eEquiv (d := d)).toContinuousLinearMap

/-- **`M` is the multiplier by the smooth function `V`**: `V` is `C^∞` and `M φ = V φ` for
every real test `φ` (then `V φ` is a test).  Tests are dense in `H^{1/2}`, so this determines
`M`.  This is the meaning of "`V_q` and its multiplier `M_q : H^{1/2} → H^{-1/2}`"
(`integrated_uniform_products.tex` lines 29-30) and of `B_E(m_R h_{Ψ,s})`
(`integrated_intrinsic_constant.tex` line 36), at revision edf7085f, book 1.1.3. -/
def IsMultiplier (V : Rd d → ℝ) (M : Hhalf d →L[ℝ] Hmhalf d) : Prop :=
  ContDiff ℝ ∞ V ∧ ∀ φ : Rd d → ℝ, IsTestFunction φ → M (toHhalf φ) = toHmhalf (fun x => V x * φ x)

/-- **The pairing `v_V(u,w) = ⟨V u, w⟩_{H^{-1/2},H^{1/2}}`** of `L:uniform-E-lift`
(`integrated_uniform_products.tex` lines 44-45 at revision edf7085f, book 1.1.3), where
`V u = M u` (the TeX identifies `M u = V u` on tests and then by density, lines 55-56). -/
def vPair (M : Hhalf d →L[ℝ] Hmhalf d) (u w : Hhalf d) : ℝ := dpair (M u) w

/-- `V ∈ H^{-1/2}` is **supported in** the set `K`: `⟨V, φ⟩ = 0` for every real test `φ` whose
support does not meet `K`. -/
def SupportedIn (V : Hmhalf d) (K : Set (Rd d)) : Prop :=
  ∀ φ : Rd d → ℝ, IsTestFunction φ → Disjoint (tsupport φ) K → dpair V (toHhalf φ) = 0

/-- **`M u = V u` on compact tests** (`integrated_uniform_products.tex` lines 55-56 at revision
edf7085f, book 1.1.3): `⟨M u, φ⟩ = ⟨V, u φ⟩` for real tests `u, φ` (the distribution `V u`
is `φ ↦ V(uφ)`). -/
def ActsAs (V : Hmhalf d) (M : Hhalf d →L[ℝ] Hmhalf d) : Prop :=
  ∀ u φ : Rd d → ℝ, IsTestFunction u → IsTestFunction φ →
    dpair (M (toHhalf u)) (toHhalf φ) = dpair V (toHhalf fun x => u x * φ x)

/-! ### The row and the named input `CameronSpatialMap` -/

/-- **The row `k_R(z,w) = (η_R z₁)(η_R Λ⁻¹ w₂)`** of `E:uniform-mean-row`
(`integrated_uniform_mean.tex` lines 22-27 at revision edf7085f, book 1.1.3) for a test
displacement `z₁ = f` and a dual component `w₂ = Λ g`, `g` a test (`Λ⁻¹ w₂ = g`); then
`k_R = m_R f g` is a test function and this is its class in `H_sp`. -/
def rowTest (S : SpData d) (η : CutoffProfile d) (R : ℝ) (f g : Rd d → ℝ) : Hsp S :=
  toHsp S fun x => (etaR η R x * f x) * (etaR η R x * g x)

/-- **Named input: the compact spatial mean map** `P:cameron-spatial-map`
(`integrated_cameron_mean.tex` lines 104-119 at revision edf7085f, book 1.1.3), restricted to
`E` as in `integrated_uniform_mean.tex` lines 19-27, at the radius `R` with `η_R = η(·/R)`.
Fields:
* `T : H_sp → 𝓛(E)` linear and bounded (the TeX's `T_R`, `J_R`);
* `isCompactOperator_T`: `T` is a compact map ("extends to a compact linear map");
* `isCompactOperator_apply`: its values are compact (values in `𝒦(E)`);
* `smooth`: for a real test `q`, `T q = B_E(M)` with `M` the multiplier by
  `m_R (Γ * q)` (the smooth-test map `T_sp q = i B_F(m_R(Γ*q))`, `E` part, line 107);
* `row`: `⟨T q z, w⟩_E = ⟨q, k_R(z,w)⟩_{H_sp}` (`E:cameron-spatial-row` at `c₁ = 0`, i.e.
  `E:uniform-mean-row`) for every `q ∈ H_sp` and the dense test states `z = (f, z₂)`,
  `w = (w₁, Λ g)`.
Not carried: the constant columns of `F` (the `c₁ η_R` term of the row), the row at rough
states (needs `L:cameron-fractional-products`). -/
structure CameronSpatialMap (S : SpData d) (η : CutoffProfile d) (R : ℝ) where
  /-- the spatial mean map `T_R : H_sp → 𝓛(E)`. -/
  T : Hsp S →L[ℝ] (E d →L[ℝ] E d)
  isCompactOperator_T : IsCompactOperator T
  isCompactOperator_apply : ∀ q, IsCompactOperator (T q)
  smooth : ∀ q : Rd d → ℝ, IsTestFunction q →
    ∃ M : Hhalf d →L[ℝ] Hmhalf d, IsMultiplier (fun x => mR η R x * conv S.Γ q x) M ∧
      T (toHsp S q) = BE M
  row : ∀ (q : Hsp S) (f g : Rd d → ℝ), IsTestFunction f → IsTestFunction g →
    ∀ (z₂ : Hmhalf d) (w₁ : Hhalf d),
      ⟪T q (toE (toHhalf f) z₂), toE w₁ (lam (toHhalf g))⟫ = ⟪q, rowTest S η R f g⟫

/-! ### The completed mean and the named input `UniformMeanRegulator` -/

variable {p : TParams} {S : SpData d}

/-- **The completed mean `𝒯_R = T_R U`** (`integrated_uniform_mean.tex` lines 257-270,
`integrated_uniform_products.tex` lines 17-21, at revision edf7085f, book 1.1.3): composition
of the time map `U : H_I → L^r(I; H_sp)` with `T_R`, pointwise in time. -/
def meanOp {r : ℝ≥0∞} [Fact (1 ≤ r)] (T : Hsp S →L[ℝ] (E d →L[ℝ] E d))
    (U : HI p S →L[ℝ] Lp (Hsp S) r timeMeasure) :
    HI p S →L[ℝ] Lp (E d →L[ℝ] E d) r timeMeasure :=
  (T.compLpL r timeMeasure) ∘L U

/-- The temporal mean `(Kf)(s) = ∫_I |s-t|^{-a} f(t) dt`. -/
def kMean (a : ℝ) (f : ℝ → ℝ) (s : ℝ) : ℝ := ∫ t, kern a (s - t) * f t ∂timeMeasure

/-- A smooth test function of the time interval: `C^∞`, compact support inside `I = (0,1)`. -/
def IsTimeTest (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ Ioo (0 : ℝ) 1

/-- **Named input: the regulated completed mean** of `P:uniform-mean-regulator`
(`integrated_uniform_mean.tex` lines 272-288 at revision edf7085f, book 1.1.3), with the data
it is stated about.  Parameters: `a = p.a`, the covariance `S`, the profile `η` and the
exponent `r` (`2 < r < 2/a`).  Fields:
* `Tsp R` (`R ≥ 1`): the `E` spatial map `T_R` (`CameronSpatialMap`);
* `Ct : H_t → L^r(I)` (`P:cameron-temporal-map`, lines 225-237 of
  `integrated_cameron_mean.tex`): compact, and `C_t f = K f` on time tests (line 273);
* `U : H_I → L^r(I; H_sp)` (`U = C_t ⊗ I_{H_sp}`, lines 257-261; `P:cameron-full-mean` lines
  322-342 of `integrated_cameron_mean.tex`): on single smooth tensors
  `U(f ⊗ q)(s) = (Kf)(s) q`, `f` a time test, `q ∈ H_sp` (the TeX's defining formula of `𝒰`);
  `‖U‖ ≤ ‖C_t‖ = c_t` (`L:uniform-mean-tensor` with `A = C_t`);
* `mean_bound`: the first bound of `E:uniform-completed-mean`, `‖𝒯_R‖ ≤ M_0 c_t` uniformly in
  `R ≥ 1`, norms `H_I → L^r(I; 𝓛(E))`, with a constant `M0 ≥ 0` (the TeX's explicit
  `M_0 = A_s M²` is not carried).
Not carried (not used by UM-1/UM-2): the projections `P_ret = π_J ⊗ P_K`, `Q_{J,K}`,
`ε_J → 0` and the tail bound `‖𝒯_R Q_{J,K}‖ ≤ M_0 ε_J + M_f c_t K^{-β}`; the Lean `H_I` is
the kernel completion of `L²(I; H_sp)`, not a tensor product, so `π_J ⊗ P_K` has no Lean
meaning yet (decision 4).  Strong measurability of the field is automatic in `Lp`. -/
structure UniformMeanRegulator (p : TParams) (S : SpData d) (η : CutoffProfile d)
    (r : ℝ≥0∞) [Fact (1 ≤ r)] where
  two_lt_r : 2 < r
  r_lt : r < ENNReal.ofReal (2 / p.a)
  /-- the spatial maps `T_R`, `R ≥ 1`. -/
  Tsp : ∀ R : ℝ, 1 ≤ R → CameronSpatialMap S η R
  /-- the temporal mean `C_t : H_t → L^r(I)`. -/
  Ct : Ht p →L[ℝ] Lp ℝ r timeMeasure
  isCompactOperator_Ct : IsCompactOperator Ct
  Ct_test : ∀ f : ℝ → ℝ, IsTimeTest f → ∀ hf : MemLp f 2 timeMeasure,
    (Ct (J p ℝ (hf.toLp f)) : ℝ → ℝ) =ᵐ[timeMeasure] kMean p.a f
  /-- the time map `U = C_t ⊗ I_{H_sp} : H_I → L^r(I; H_sp)`. -/
  U : HI p S →L[ℝ] Lp (Hsp S) r timeMeasure
  U_tensor : ∀ f : ℝ → ℝ, IsTimeTest f → ∀ q : Hsp S,
    ∀ hF : MemLp (fun t => f t • q) 2 timeMeasure,
      (U (J p (Hsp S) (hF.toLp fun t => f t • q)) : ℝ → Hsp S) =ᵐ[timeMeasure]
        fun s => kMean p.a f s • q
  norm_U_le : ‖U‖ ≤ ‖Ct‖
  /-- a constant `M_0` of the first bound of `E:uniform-completed-mean`. -/
  M0 : ℝ
  M0_nonneg : 0 ≤ M0
  mean_bound : ∀ R (hR : 1 ≤ R), ‖meanOp (Tsp R hR).T U‖ ≤ M0 * ‖Ct‖

/-! ### UM-1 statement shapes: `L:uniform-E-lift` -/

/-- **The operator class `𝒱_{E,R}`** (`integrated_uniform_products.tex` lines 29-31 at revision
edf7085f, book 1.1.3): the operator-norm closure of `L_q^E = B_E(M_q)`, `M_q` the multiplier by
`V_q = m_R (Γ * q)`, `q` a real test.  (Closure in `𝓛(E)`; it equals the closure in `𝒦(E)`
since the `L_q^E` are compact and `𝒦(E)` is closed.) -/
def VER (S : SpData d) (η : CutoffProfile d) (R : ℝ) : Set (E d →L[ℝ] E d) :=
  closure {L | ∃ (q : Rd d → ℝ) (M : Hhalf d →L[ℝ] Hmhalf d), IsTestFunction q ∧
    IsMultiplier (fun x => mR η R x * conv S.Γ q x) M ∧ L = BE M}

/-- **UM-1 target, operator form of `L:uniform-E-lift`** (`integrated_uniform_products.tex`
lines 33-38 at revision edf7085f, book 1.1.3): for `R ≥ 1`, every `L ∈ 𝒱_{E,R}` is
`B_E(M)` with `‖L‖ = ‖M‖`, and determines a unique real `V ∈ H^{-1/2}` supported in
`supp m_R` with `M u = V u` on tests.  The lift `L_F` (lines 42-43) is not part of the target. -/
def UniformELiftTarget (S : SpData d) (η : CutoffProfile d) : Prop :=
  ∀ R : ℝ, 1 ≤ R → ∀ L ∈ VER S η R, ∃ M : Hhalf d →L[ℝ] Hmhalf d,
    L = BE M ∧ ‖L‖ = ‖M‖ ∧ ∃! V : Hmhalf d, SupportedIn V (tsupport (mR η R)) ∧ ActsAs V M

/-- **UM-1 target, `E:uniform-E-pairing`** (`integrated_uniform_products.tex` lines 38-41 and
44-45 at revision edf7085f, book 1.1.3): for `R ≥ 1`, `L = B_E(M) ∈ 𝒱_{E,R}` and
`k = ‖L‖`, the pairing `v_V(u,w) = ⟨M u, w⟩` is symmetric and
`|v_V(u,w)| ≤ k ‖u‖_{H^{1/2}} ‖w‖_{H^{1/2}}`.  (Real states; the Hermitian extension to
complex states is not part of the target.) -/
def UniformEPairingTarget (S : SpData d) (η : CutoffProfile d) : Prop :=
  ∀ R : ℝ, 1 ≤ R → ∀ L ∈ VER S η R, ∀ M : Hhalf d →L[ℝ] Hmhalf d, L = BE M →
    (∀ u w, vPair M u w = vPair M w u) ∧ ∀ u w, |vPair M u w| ≤ ‖L‖ * ‖u‖ * ‖w‖

/-! ### UM-2 statement shape: the mean identity of `E:positive-raw-mean` -/

/-- **UM-2 target, the mean identity of `E:positive-raw-mean` and the canonical-version
sentence** (`integrated_intrinsic_constant.tex` lines 32-39 at revision edf7085f, book
1.1.3).  For every `Ψ ∈ C_pos` and `R ≥ 1`, with `𝒯_R = meanOp (Tsp R).T U` and the
inclusion `incl Ψ ∈ H_I` of `OccupationCompletion`:
(a) for a.e. `s ∈ I`, `𝒯_R Ψ(s) = B_E(M)` with `M` the multiplier by `m_R h_{Ψ,s}`;
(b) the canonical version: there are multipliers `M_s` by `m_R h_{Ψ,s}` for EVERY `s ∈ I`, and
`s ↦ B_E(M_s)` is a version of the class `𝒯_R Ψ`.
(`h_{Ψ,s} = VariationalDilation.mean a Γ Ψ s`, `E:compact-raw-mean`; (b) implies (a); the first
identity `‖Ψ‖²_{H_I} = v_Ψ` is `OccupationCompletion.norm_incl_sq`.) -/
def PositiveRawMeanTarget {η : CutoffProfile d} {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (Ureg : UniformMeanRegulator p S η r) : Prop :=
  ∀ Ψ ∈ CPos d, ∀ R : ℝ, ∀ hR : 1 ≤ R,
    (∀ᵐ s ∂timeMeasure, ∃ M : Hhalf d →L[ℝ] Hmhalf d,
        IsMultiplier (fun x => mR η R x * mean p.a S.Γ Ψ s x) M ∧
        (meanOp (Ureg.Tsp R hR).T Ureg.U (incl p S Ψ) : ℝ → E d →L[ℝ] E d) s = BE M) ∧
    ∃ Mf : ℝ → (Hhalf d →L[ℝ] Hmhalf d),
      (∀ s ∈ Ioo (0 : ℝ) 1, IsMultiplier (fun x => mR η R x * mean p.a S.Γ Ψ s x) (Mf s)) ∧
      (meanOp (Ureg.Tsp R hR).T Ureg.U (incl p S Ψ) : ℝ → E d →L[ℝ] E d) =ᵐ[timeMeasure]
        fun s => BE (Mf s)

end StratonovichHAMSecondMoment.UniformMeanInterface
