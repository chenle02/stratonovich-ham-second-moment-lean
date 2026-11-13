/-! ## Bridges (untrusted helpers)

The copies in `ChallengeDefs` that the elaborator does not identify with the project's
definitions by unfolding: the inductive `Trig` and the structure `HomogCovariance`
(new inductive types, so only equivalent, not equal) and the structurally recursive
`counts`, `raw`, `cut` (equal pointwise, proved by induction). Everything here is
proved; nothing is assumed. -/

namespace StratonovichHamSecondMomentLeanAuditBridge

namespace HermiteWord

variable {C B V : Type} [DecidableEq C]

theorem counts_eq (w : List (C × B)) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMAudit.HermiteWord.counts w =
      StratonovichHAMAudit.HermiteWord.counts w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    show StratonovichHamSecondMomentLeanDefs.StratonovichHAMAudit.HermiteWord.bump a.1
        (StratonovichHamSecondMomentLeanDefs.StratonovichHAMAudit.HermiteWord.counts w) =
      StratonovichHAMAudit.HermiteWord.bump a.1 (StratonovichHAMAudit.HermiteWord.counts w)
    rw [ih]; rfl

theorem raw_eq (J : C → V → V) (F : B → V → V) (v₀ : V) (w : List (C × B)) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMAudit.HermiteWord.raw J F v₀ w =
      StratonovichHAMAudit.HermiteWord.raw J F v₀ w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    show F a.2 (J a.1 (StratonovichHamSecondMomentLeanDefs.StratonovichHAMAudit.HermiteWord.raw
        J F v₀ w)) = F a.2 (J a.1 (StratonovichHAMAudit.HermiteWord.raw J F v₀ w))
    rw [ih]

theorem cut_eq (P : V → V) (J : C → V → V) (F : B → V → V) (v₀ : V) (w : List (C × B)) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMAudit.HermiteWord.cut P J F v₀ w =
      StratonovichHAMAudit.HermiteWord.cut P J F v₀ w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    show F a.2 (P (J a.1 (P (StratonovichHamSecondMomentLeanDefs.StratonovichHAMAudit.HermiteWord.cut
        P J F v₀ w)))) = F a.2 (P (J a.1 (P (StratonovichHAMAudit.HermiteWord.cut P J F v₀ w))))
    rw [ih]

end HermiteWord

namespace MaskedTrigProducts

/-- The copied `Trig` to the project's, constructor by constructor. -/
def toP : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedTrigProducts.Trig →
    StratonovichHAMSecondMoment.MaskedTrigProducts.Trig
  | .cos => .cos
  | .sin => .sin

theorem eval_eq (k : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedTrigProducts.Trig)
    (x : ℝ) : k.eval x = (toP k).eval x := by
  cases k <;> rfl

theorem coef1_eq (k : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedTrigProducts.Trig)
    (σ : Bool) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedTrigProducts.coef1 k σ =
      StratonovichHAMSecondMoment.MaskedTrigProducts.coef1 (toP k) σ := by
  cases k <;> cases σ <;> rfl

theorem coef_eq (P Q : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedTrigProducts.Trig)
    (j : Bool × Bool) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedTrigProducts.coef P Q j =
      StratonovichHAMSecondMoment.MaskedTrigProducts.coef (toP P) (toP Q) j := by
  show StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedTrigProducts.coef1 P j.1 *
      StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedTrigProducts.coef1 Q j.2 =
    StratonovichHAMSecondMoment.MaskedTrigProducts.coef1 (toP P) j.1 *
      StratonovichHAMSecondMoment.MaskedTrigProducts.coef1 (toP Q) j.2
  rw [coef1_eq, coef1_eq]

theorem prodFn_eq (I : Set ℝ) (A : ℝ → ℂ)
    (P Q : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedTrigProducts.Trig)
    (r ρ : ℝ) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedTrigProducts.prodFn I A P Q r ρ =
      StratonovichHAMSecondMoment.MaskedTrigProducts.prodFn I A (toP P) (toP Q) r ρ := by
  show I.indicator (fun t => A t * P.eval (r * t) * Q.eval (ρ * t)) =
    I.indicator (fun t => A t * (toP P).eval (r * t) * (toP Q).eval (ρ * t))
  simp only [eval_eq]

end MaskedTrigProducts

namespace HomogHypothesis

/-- The copied `HomogCovariance` gives the project's, field by field (each field's type
unfolds to the same proposition). -/
theorem homog_toP {d : ℕ} {alpha alpha0 : ℝ}
    {Γ μ : MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd d)}
    (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.HomogCovariance
      d alpha alpha0 Γ μ) :
    StratonovichHAMSecondMoment.HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ :=
  ⟨h.dim, h.alpha0_pos, h.alpha0_lt_one, h.Γ_radon, h.Γ_even, h.Γ_tempered, h.Γ_posdef,
    h.μ_radon, h.μ_even, h.μ_tempered, h.spectral, h.scaling, h.threshold, h.alpha_range⟩

end HomogHypothesis


/-! ### Structures copied in `ChallengeDefs`: field-by-field conversions both ways

Each copy has the project's fields with the same (unfolding-equal) types, so the anonymous
constructor over the numeric projections converts in either direction. -/

namespace IndexedCone

universe u

variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]

def gToP (G : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.IndexedCone.GroundFamily F) : StratonovichHAMSecondMoment.IndexedCone.GroundFamily F :=
  ⟨G.1, G.2, G.3, G.4, G.5, G.6, G.7, G.8, G.9, G.10, G.11, G.12, G.13, G.14, G.15, G.16, G.17⟩

def gOfP (G : StratonovichHAMSecondMoment.IndexedCone.GroundFamily F) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.IndexedCone.GroundFamily F :=
  ⟨G.1, G.2, G.3, G.4, G.5, G.6, G.7, G.8, G.9, G.10, G.11, G.12, G.13, G.14, G.15, G.16, G.17⟩

def cToP {G : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.IndexedCone.GroundFamily F} {ϱ : ℝ}
    (C : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.IndexedCone.ConeConstants G ϱ) : StratonovichHAMSecondMoment.IndexedCone.ConeConstants (gToP G) ϱ :=
  ⟨C.1, C.2, C.3, C.4, C.5, C.6, C.7, C.8, C.9, C.10, C.11, C.12, C.13, C.14, C.15, C.16, C.17, C.18, C.19, C.20, C.21, C.22, C.23, C.24, C.25, C.26, C.27, C.28, C.29, C.30, C.31, C.32, C.33, C.34, C.35, C.36, C.37, C.38, C.39, C.40, C.41, C.42, C.43, C.44, C.45, C.46⟩

def cOfP {G : StratonovichHAMSecondMoment.IndexedCone.GroundFamily F} {ϱ : ℝ}
    (C : StratonovichHAMSecondMoment.IndexedCone.ConeConstants G ϱ) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.IndexedCone.ConeConstants (gOfP G) ϱ :=
  ⟨C.1, C.2, C.3, C.4, C.5, C.6, C.7, C.8, C.9, C.10, C.11, C.12, C.13, C.14, C.15, C.16, C.17, C.18, C.19, C.20, C.21, C.22, C.23, C.24, C.25, C.26, C.27, C.28, C.29, C.30, C.31, C.32, C.33, C.34, C.35, C.36, C.37, C.38, C.39, C.40, C.41, C.42, C.43, C.44, C.45, C.46⟩

end IndexedCone

namespace WeakSobolev

variable {d : ℕ}

theorem rtToP {V : StratonovichHAMSecondMoment.HomogHypothesis.Rd d → ℝ} {f : StratonovichHAMSecondMoment.HomogHypothesis.Rd d → ℝ}
    {g : StratonovichHAMSecondMoment.HomogHypothesis.Rd d → StratonovichHAMSecondMoment.HomogHypothesis.Rd d}
    (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WeakSobolev.IsRayleighTrial V f g) : StratonovichHAMSecondMoment.WeakSobolev.IsRayleighTrial V f g :=
  ⟨h.1, h.2, h.3, h.4, h.5⟩

theorem rtOfP {V : StratonovichHAMSecondMoment.HomogHypothesis.Rd d → ℝ} {f : StratonovichHAMSecondMoment.HomogHypothesis.Rd d → ℝ}
    {g : StratonovichHAMSecondMoment.HomogHypothesis.Rd d → StratonovichHAMSecondMoment.HomogHypothesis.Rd d}
    (h : StratonovichHAMSecondMoment.WeakSobolev.IsRayleighTrial V f g) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WeakSobolev.IsRayleighTrial V f g :=
  ⟨h.1, h.2, h.3, h.4, h.5⟩

/-- The copied predicate is the project's (`propext`), as functions. -/
theorem rt_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WeakSobolev.IsRayleighTrial = @StratonovichHAMSecondMoment.WeakSobolev.IsRayleighTrial := by
  funext d V f g
  exact propext ⟨rtToP, rtOfP⟩

end WeakSobolev

namespace HomogHypothesis

theorem homog_ofP {d : ℕ} {alpha alpha0 : ℝ}
    {Γ μ : MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd d)}
    (h : StratonovichHAMSecondMoment.HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ :=
  ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11, h.12, h.13, h.14⟩

/-- The copied predicate is the project's (`propext`), as functions. -/
theorem homog_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis.HomogCovariance = @StratonovichHAMSecondMoment.HomogHypothesis.HomogCovariance := by
  funext d alpha alpha0 Γ μ
  exact propext ⟨homog_toP, homog_ofP⟩

end HomogHypothesis



/-! ### Definitions whose copies unfold to a copied predicate: equal as functions -/

namespace WeakSobolev

theorem rayleighSet_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WeakSobolev.rayleighSet = @StratonovichHAMSecondMoment.WeakSobolev.rayleighSet := by
  funext d V
  show {q | ∃ f g, StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WeakSobolev.IsRayleighTrial V f g ∧
      StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WeakSobolev.rayleighValue V f g = q} =
    {q | ∃ f g, StratonovichHAMSecondMoment.WeakSobolev.IsRayleighTrial V f g ∧ StratonovichHAMSecondMoment.WeakSobolev.rayleighValue V f g = q}
  rw [rt_eq]
  rfl

theorem rayleighRate_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WeakSobolev.rayleighRate = @StratonovichHAMSecondMoment.WeakSobolev.rayleighRate := by
  funext d V
  show Real.sqrt (sSup (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WeakSobolev.rayleighSet V)) =
    Real.sqrt (sSup (StratonovichHAMSecondMoment.WeakSobolev.rayleighSet V))
  rw [rayleighSet_eq]

end WeakSobolev

namespace VariationalDilation

theorem rate_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalDilation.rate = @StratonovichHAMSecondMoment.VariationalDilation.rate := by
  funext d a Γ Ψ s
  show StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WeakSobolev.rayleighRate (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalDilation.mean a Γ Ψ s) =
    StratonovichHAMSecondMoment.WeakSobolev.rayleighRate (StratonovichHAMSecondMoment.VariationalDilation.mean a Γ Ψ s)
  rw [WeakSobolev.rayleighRate_eq]
  rfl

theorem integratedRate_eq :
    @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalDilation.integratedRate = @StratonovichHAMSecondMoment.VariationalDilation.integratedRate := by
  funext d a Γ Ψ
  show ∫ s in Set.Ioo (0 : ℝ) 1, StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalDilation.rate a Γ Ψ s =
    ∫ s in Set.Ioo (0 : ℝ) 1, StratonovichHAMSecondMoment.VariationalDilation.rate a Γ Ψ s
  rw [rate_eq]

end VariationalDilation

namespace IndexedCone

theorem chainState_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.IndexedCone.chainState = @StratonovichHAMSecondMoment.IndexedCone.chainState := by
  funext F _ _ D B e0 m
  induction m with
  | zero => rfl
  | succ m ih =>
    show D m B (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.IndexedCone.chainState D B e0 m) = D m B (StratonovichHAMSecondMoment.IndexedCone.chainState D B e0 m)
    rw [ih]

theorem scalarFamily_eq : gToP StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.IndexedCone.scalarFamily = StratonovichHAMSecondMoment.IndexedCone.scalarFamily := rfl

end IndexedCone

namespace TimeCompletion

/-- The copied `TimeParams` to the project's, field by field. -/
def tpToP (p : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TimeCompletion.TimeParams) : StratonovichHAMSecondMoment.TimeCompletion.TimeParams :=
  ⟨p.1, p.2, p.3, p.4, p.5⟩

def tpOfP (p : StratonovichHAMSecondMoment.TimeCompletion.TimeParams) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TimeCompletion.TimeParams :=
  ⟨p.1, p.2, p.3, p.4, p.5⟩

end TimeCompletion

namespace DampedNormsHomog

theorem gmToP {d : ℕ} {G : ℝ → MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd d)}
    (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.DampedNormsHomog.GreenMass G) : StratonovichHAMSecondMoment.DampedNormsHomog.GreenMass G :=
  ⟨h.1⟩

theorem gmOfP {d : ℕ} {G : ℝ → MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd d)}
    (h : StratonovichHAMSecondMoment.DampedNormsHomog.GreenMass G) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.DampedNormsHomog.GreenMass G :=
  ⟨h.1⟩

end DampedNormsHomog

namespace MaskedContinuousWave

/-- The copied `Wave` to the project's, constructor by constructor. -/
def toP : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedContinuousWave.Wave → StratonovichHAMSecondMoment.MaskedContinuousWave.Wave
  | .c => .c
  | .b => .b

theorem weval_eq (W : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedContinuousWave.Wave) (r t : ℝ) :
    W.eval r t = (toP W).eval r t := by
  cases W <;> rfl

theorem amp_eq (W : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedContinuousWave.Wave) (r : ℝ) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedContinuousWave.amp W r = StratonovichHAMSecondMoment.MaskedContinuousWave.amp (toP W) r := by
  cases W <;> rfl

theorem fr_eq (W : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedContinuousWave.Wave) (r : ℝ) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedContinuousWave.fr W r = StratonovichHAMSecondMoment.MaskedContinuousWave.fr (toP W) r := by
  cases W <;> rfl

theorem trig_eq (W : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedContinuousWave.Wave) (r : ℝ) :
    MaskedTrigProducts.toP (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedContinuousWave.trig W r) =
      StratonovichHAMSecondMoment.MaskedContinuousWave.trig (toP W) r := by
  cases W
  · rfl
  · show MaskedTrigProducts.toP (if r < 1 then .cos else .sin) = (if r < 1 then .cos else .sin)
    split_ifs <;> rfl

theorem waveFn_eq (I : Set ℝ) (F G : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedContinuousWave.Wave) (r ρ : ℝ) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedContinuousWave.waveFn I F G r ρ =
      StratonovichHAMSecondMoment.MaskedContinuousWave.waveFn I (toP F) (toP G) r ρ := by
  cases F <;> cases G <;> rfl

end MaskedContinuousWave

/-! ### Wave L6: the structure `TypeContinuityInputs`, and definitions whose copies unfold
to a copied structure, predicate or inductive (equal as functions) -/

namespace TypeContinuity

theorem tciToP {d : ℕ} {alpha : ℝ} {mom : ℕ → ℝ → ℝ → ℝ} {c : ℕ → ℝ → ℕ → ℝ} {L0 : ℝ}
    (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TypeContinuity.TypeContinuityInputs d alpha mom c L0) :
    StratonovichHAMSecondMoment.TypeContinuity.TypeContinuityInputs d alpha mom c L0 :=
  ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7⟩

theorem tciOfP {d : ℕ} {alpha : ℝ} {mom : ℕ → ℝ → ℝ → ℝ} {c : ℕ → ℝ → ℕ → ℝ} {L0 : ℝ}
    (h : StratonovichHAMSecondMoment.TypeContinuity.TypeContinuityInputs d alpha mom c L0) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TypeContinuity.TypeContinuityInputs d alpha mom c L0 :=
  ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7⟩

/-- The copied predicate is the project's (`propext`), as functions. -/
theorem tci_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TypeContinuity.TypeContinuityInputs =
    @StratonovichHAMSecondMoment.TypeContinuity.TypeContinuityInputs := by
  funext d alpha mom c L0
  exact propext ⟨tciToP, tciOfP⟩

end TypeContinuity

namespace VariationalRate

theorem scoreSet_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalRate.scoreSet =
    @StratonovichHAMSecondMoment.VariationalRate.scoreSet := by
  funext d a Γ c
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalRate.scoreSet
    StratonovichHAMSecondMoment.VariationalRate.scoreSet
  rw [VariationalDilation.integratedRate_eq]
  rfl

theorem score1Set_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalRate.score1Set =
    @StratonovichHAMSecondMoment.VariationalRate.score1Set := by
  funext d a Γ
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalRate.score1Set
    StratonovichHAMSecondMoment.VariationalRate.score1Set
  rw [VariationalDilation.integratedRate_eq]
  rfl

theorem testRadius_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalRate.testRadius =
    @StratonovichHAMSecondMoment.VariationalRate.testRadius := by
  funext d alpha a Γ Ψ₀
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalRate.testRadius
    StratonovichHAMSecondMoment.VariationalRate.testRadius
  rw [VariationalDilation.integratedRate_eq]
  rfl

theorem S1Bdd_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalRate.S1Bdd =
    @StratonovichHAMSecondMoment.VariationalRate.S1Bdd := by
  funext d a Γ
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalRate.S1Bdd
    StratonovichHAMSecondMoment.VariationalRate.S1Bdd
  rw [score1Set_eq]

theorem S1pos_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalRate.S1pos =
    @StratonovichHAMSecondMoment.VariationalRate.S1pos := by
  funext d a Γ
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalRate.S1pos
    StratonovichHAMSecondMoment.VariationalRate.S1pos
  rw [score1Set_eq]

end VariationalRate

namespace SpatialStaticControls

theorem lamSq_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpatialStaticControls.lamSq =
    @StratonovichHAMSecondMoment.SpatialStaticControls.lamSq := by
  funext d U c
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpatialStaticControls.lamSq
    StratonovichHAMSecondMoment.SpatialStaticControls.lamSq
  rw [WeakSobolev.rayleighSet_eq]

theorem lam_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpatialStaticControls.lam =
    @StratonovichHAMSecondMoment.SpatialStaticControls.lam := by
  funext d U c
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpatialStaticControls.lam
    StratonovichHAMSecondMoment.SpatialStaticControls.lam
  rw [WeakSobolev.rayleighRate_eq]

theorem lamZ_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpatialStaticControls.lamZ =
    @StratonovichHAMSecondMoment.SpatialStaticControls.lamZ := by
  funext d Γ z c
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpatialStaticControls.lamZ
    StratonovichHAMSecondMoment.SpatialStaticControls.lamZ
  rw [lam_eq]
  rfl

theorem rayleighFloor_eq :
    @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpatialStaticControls.RayleighFloor =
      @StratonovichHAMSecondMoment.SpatialStaticControls.RayleighFloor := by
  funext d Γ
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpatialStaticControls.RayleighFloor
    StratonovichHAMSecondMoment.SpatialStaticControls.RayleighFloor
  rw [WeakSobolev.rayleighSet_eq]
  rfl

end SpatialStaticControls

namespace SpatialSmoothRatio

theorem staticControls_eq :
    @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpatialSmoothRatio.StaticControls =
      @StratonovichHAMSecondMoment.SpatialSmoothRatio.StaticControls := by
  funext d a Γ
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpatialSmoothRatio.StaticControls
    StratonovichHAMSecondMoment.SpatialSmoothRatio.StaticControls
  rw [WeakSobolev.rayleighSet_eq, WeakSobolev.rayleighRate_eq, VariationalDilation.integratedRate_eq]
  rfl

end SpatialSmoothRatio

namespace WaveTwoVariances

/-- The kernel entries agree: for each of the four index pairs the copied `rowWave`,
`colWave` reduce to the copied constructors, whose `eval` unfolds to the project's. -/
theorem kernelEntry_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveTwoVariances.kernelEntry =
    @StratonovichHAMSecondMoment.WaveTwoVariances.kernelEntry := by
  funext d i j ξ η t
  fin_cases i <;> fin_cases j <;> rfl

theorem maskedKernel_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveTwoVariances.maskedKernel =
    @StratonovichHAMSecondMoment.WaveTwoVariances.maskedKernel := by
  funext d s h i j ξ η
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveTwoVariances.maskedKernel
    StratonovichHAMSecondMoment.WaveTwoVariances.maskedKernel
  rw [kernelEntry_eq]

theorem kernelLp_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveTwoVariances.kernelLp =
    @StratonovichHAMSecondMoment.WaveTwoVariances.kernelLp := by
  funext d T s h i j ξ η
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveTwoVariances.kernelLp
    StratonovichHAMSecondMoment.WaveTwoVariances.kernelLp
  exact MeasureTheory.MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => by rw [maskedKernel_eq])

theorem rowWave_toP (i : Fin 2) :
    MaskedContinuousWave.toP (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveTwoVariances.rowWave i) =
      StratonovichHAMSecondMoment.WaveTwoVariances.rowWave i := by
  fin_cases i <;> rfl

theorem colWave_toP (j : Fin 2) :
    MaskedContinuousWave.toP (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveTwoVariances.colWave j) =
      StratonovichHAMSecondMoment.WaveTwoVariances.colWave j := by
  fin_cases j <;> rfl

/-- The copied `emb` over a copied `TimeParams` is the project's over the converted
parameters, on equal functions. -/
theorem emb_eq (p : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TimeCompletion.TimeParams)
    (f g : ℝ → ℂ) (hf : f ∈ StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TimeCompletion.L2fun p.T)
    (hg : g ∈ StratonovichHAMSecondMoment.TimeCompletion.L2fun (TimeCompletion.tpToP p).T) (e : f = g) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TimeCompletion.emb p ⟨f, hf⟩ =
      StratonovichHAMSecondMoment.TimeCompletion.emb (TimeCompletion.tpToP p) ⟨g, hg⟩ := by
  subst e
  rfl

/-- `kerH` over a copied `TimeParams` is the project's over the converted parameters. -/
theorem kerH_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveTwoVariances.kerH =
    fun p => @StratonovichHAMSecondMoment.WaveTwoVariances.kerH (TimeCompletion.tpToP p) := by
  funext p d s h i j ξ η
  show StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TimeCompletion.extL2 p
      (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveTwoVariances.kernelLp p.T s h i j ξ η) =
    StratonovichHAMSecondMoment.TimeCompletion.extL2 (TimeCompletion.tpToP p)
      (StratonovichHAMSecondMoment.WaveTwoVariances.kernelLp p.T s h i j ξ η)
  rw [kernelLp_eq]
  rfl

theorem coef_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveTwoVariances.coef =
    fun p => @StratonovichHAMSecondMoment.WaveTwoVariances.coef (TimeCompletion.tpToP p) := by
  funext p d s h U V l
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveTwoVariances.coef
  rw [kerH_eq]
  rfl

theorem inputBound_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveTwoVariances.InputBound =
    fun p => @StratonovichHAMSecondMoment.WaveTwoVariances.InputBound (TimeCompletion.tpToP p) := by
  funext p d s h ν γ M
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveTwoVariances.InputBound
  rw [kerH_eq, coef_eq]
  rfl

theorem outputBound_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveTwoVariances.OutputBound =
    fun p => @StratonovichHAMSecondMoment.WaveTwoVariances.OutputBound (TimeCompletion.tpToP p) := by
  funext p d s h ν γ M
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveTwoVariances.OutputBound
  rw [kerH_eq, coef_eq]
  rfl

end WaveTwoVariances

namespace UniformSeriesTail

/-! The copied structure `TerminalWickInput` (wave L7) is a new `Prop`-valued structure:
equivalent to the project's, hence equal by `propext`. -/

theorem twiToP {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    {Y : ℕ → MeasureTheory.Lp ℝ 2 μ} {r : ℝ}
    (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformSeriesTail.TerminalWickInput μ Y r) :
    StratonovichHAMSecondMoment.UniformSeriesTail.TerminalWickInput μ Y r :=
  ⟨h.1, h.2⟩

theorem twiOfP {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    {Y : ℕ → MeasureTheory.Lp ℝ 2 μ} {r : ℝ}
    (h : StratonovichHAMSecondMoment.UniformSeriesTail.TerminalWickInput μ Y r) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformSeriesTail.TerminalWickInput μ Y r :=
  ⟨h.1, h.2⟩

theorem twi_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.UniformSeriesTail.TerminalWickInput =
    @StratonovichHAMSecondMoment.UniformSeriesTail.TerminalWickInput := by
  funext Ω _ μ Y r
  exact propext ⟨twiToP, twiOfP⟩

end UniformSeriesTail

namespace OccupationPhysicalClass

/-! The copied structures `SquarePairingBounds` and `IsOccField` (wave L7) are new
`Prop`-valued structures: equivalent to the project's, hence equal by `propext`; the copied
`energySet` and `EstarO`, which mention `IsOccField`, are then equal to the project's. -/

theorem spbToP {d : ℕ} {Γ : MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd d)} {alpha R : ℝ}
    (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationPhysicalClass.SquarePairingBounds Γ alpha R) :
    StratonovichHAMSecondMoment.OccupationPhysicalClass.SquarePairingBounds Γ alpha R :=
  ⟨h.1, h.2⟩

theorem spbOfP {d : ℕ} {Γ : MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd d)} {alpha R : ℝ}
    (h : StratonovichHAMSecondMoment.OccupationPhysicalClass.SquarePairingBounds Γ alpha R) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationPhysicalClass.SquarePairingBounds Γ alpha R :=
  ⟨h.1, h.2⟩

theorem spb_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationPhysicalClass.SquarePairingBounds =
    @StratonovichHAMSecondMoment.OccupationPhysicalClass.SquarePairingBounds := by
  funext d Γ alpha R
  exact propext ⟨spbToP, spbOfP⟩

theorem occToP {d : ℕ} {G : ℝ → StratonovichHAMSecondMoment.HomogHypothesis.Rd d → ℝ}
    {DG : ℝ → StratonovichHAMSecondMoment.HomogHypothesis.Rd d → StratonovichHAMSecondMoment.HomogHypothesis.Rd d}
    (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationPhysicalClass.IsOccField G DG) :
    StratonovichHAMSecondMoment.OccupationPhysicalClass.IsOccField G DG :=
  ⟨h.1, h.2, h.3, h.4⟩

theorem occOfP {d : ℕ} {G : ℝ → StratonovichHAMSecondMoment.HomogHypothesis.Rd d → ℝ}
    {DG : ℝ → StratonovichHAMSecondMoment.HomogHypothesis.Rd d → StratonovichHAMSecondMoment.HomogHypothesis.Rd d}
    (h : StratonovichHAMSecondMoment.OccupationPhysicalClass.IsOccField G DG) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationPhysicalClass.IsOccField G DG :=
  ⟨h.1, h.2, h.3, h.4⟩

theorem occ_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationPhysicalClass.IsOccField =
    @StratonovichHAMSecondMoment.OccupationPhysicalClass.IsOccField := by
  funext d G DG
  exact propext ⟨occToP, occOfP⟩

theorem energySet_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationPhysicalClass.energySet =
    @StratonovichHAMSecondMoment.OccupationPhysicalClass.energySet := by
  funext d a D Γ
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationPhysicalClass.energySet StratonovichHAMSecondMoment.OccupationPhysicalClass.energySet
  rw [occ_eq]
  rfl

theorem EstarO_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationPhysicalClass.EstarO =
    @StratonovichHAMSecondMoment.OccupationPhysicalClass.EstarO := by
  funext d a D Γ
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationPhysicalClass.EstarO StratonovichHAMSecondMoment.OccupationPhysicalClass.EstarO
  rw [energySet_eq]

end OccupationPhysicalClass

namespace DampedMultiplier

/-! The copied structure `GreenFourier` (wave L8) is a new `Prop`-valued structure:
equivalent to the project's, hence equal by `propext`. -/

theorem gfToP {d : ℕ} {G : ℝ → MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd d)}
    (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.DampedMultiplier.GreenFourier G) : StratonovichHAMSecondMoment.DampedMultiplier.GreenFourier G :=
  ⟨h.1, h.2⟩

theorem gfOfP {d : ℕ} {G : ℝ → MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd d)}
    (h : StratonovichHAMSecondMoment.DampedMultiplier.GreenFourier G) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.DampedMultiplier.GreenFourier G :=
  ⟨h.1, h.2⟩

theorem gf_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.DampedMultiplier.GreenFourier = @StratonovichHAMSecondMoment.DampedMultiplier.GreenFourier := by
  funext d G
  exact propext ⟨gfToP, gfOfP⟩

end DampedMultiplier

namespace SpaceTimePositivity

/-! The copied structure `SpaceTimeCS` of `SpaceTimePositivity` (wave L8): a new
`Prop`-valued structure, equal to the project's by `propext`. -/

theorem stcsToP {d : ℕ} {a : ℝ} {Γ : MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd d)}
    (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpaceTimePositivity.SpaceTimeCS a Γ) : StratonovichHAMSecondMoment.SpaceTimePositivity.SpaceTimeCS a Γ :=
  ⟨h.1, h.2, h.3⟩

theorem stcsOfP {d : ℕ} {a : ℝ} {Γ : MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd d)}
    (h : StratonovichHAMSecondMoment.SpaceTimePositivity.SpaceTimeCS a Γ) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpaceTimePositivity.SpaceTimeCS a Γ :=
  ⟨h.1, h.2, h.3⟩

theorem stcs_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpaceTimePositivity.SpaceTimeCS = @StratonovichHAMSecondMoment.SpaceTimePositivity.SpaceTimeCS := by
  funext d a Γ
  exact propext ⟨stcsToP, stcsOfP⟩

end SpaceTimePositivity

namespace OccupationCeilingFinite

/-! The copied structure `SpaceTimeCS` of `OccupationCeilingFinite` (wave L8): a new
`Prop`-valued structure, equal to the project's by `propext`. -/

theorem stcsToP {d : ℕ} {a : ℝ} {Γ : MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd d)}
    (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCeilingFinite.SpaceTimeCS a Γ) : StratonovichHAMSecondMoment.OccupationCeilingFinite.SpaceTimeCS a Γ :=
  ⟨h.1, h.2, h.3⟩

theorem stcsOfP {d : ℕ} {a : ℝ} {Γ : MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd d)}
    (h : StratonovichHAMSecondMoment.OccupationCeilingFinite.SpaceTimeCS a Γ) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCeilingFinite.SpaceTimeCS a Γ :=
  ⟨h.1, h.2, h.3⟩

theorem stcs_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCeilingFinite.SpaceTimeCS = @StratonovichHAMSecondMoment.OccupationCeilingFinite.SpaceTimeCS := by
  funext d a Γ
  exact propext ⟨stcsToP, stcsOfP⟩

end OccupationCeilingFinite

namespace FiniteWick

/-! The copied structure `CenteredGaussianField` (wave L8): a new `Prop`-valued
structure, equal to the project's by `propext`. -/

theorem cgfToP {X Ω : Type*} [MeasurableSpace Ω] {W : X → Ω → ℝ} {K : X → X → ℝ}
    {P : MeasureTheory.Measure Ω} (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FiniteWick.CenteredGaussianField W K P) :
    StratonovichHAMSecondMoment.FiniteWick.CenteredGaussianField W K P :=
  ⟨h.1, h.2⟩

theorem cgfOfP {X Ω : Type*} [MeasurableSpace Ω] {W : X → Ω → ℝ} {K : X → X → ℝ}
    {P : MeasureTheory.Measure Ω} (h : StratonovichHAMSecondMoment.FiniteWick.CenteredGaussianField W K P) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FiniteWick.CenteredGaussianField W K P :=
  ⟨h.1, h.2⟩

theorem cgf_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FiniteWick.CenteredGaussianField =
    @StratonovichHAMSecondMoment.FiniteWick.CenteredGaussianField := by
  funext X Ω _ W K P
  exact propext ⟨cgfToP, cgfOfP⟩

end FiniteWick

namespace SymplecticFree

/-! The copied structure `FreeWaveData` (wave L8) carries data (the group `S`, the
reversal `R`, the translations `τ`), so it is not equal to the project's; the converters
rebuild one from the other field by field, and the fields of the result reduce to those
of the argument. -/

/-- A copied `FreeWaveData` as the project's (same fields). -/
def fwdToP {d : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SymplecticFree.FreeWaveData d E) : StratonovichHAMSecondMoment.SymplecticFree.FreeWaveData d E :=
  ⟨F.1, F.2, F.3, F.4, F.5, F.6, F.7, F.8, F.9, F.10⟩

/-- A project `FreeWaveData` as the copy (same fields). -/
def fwdOfP {d : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : StratonovichHAMSecondMoment.SymplecticFree.FreeWaveData d E) : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SymplecticFree.FreeWaveData d E :=
  ⟨F.1, F.2, F.3, F.4, F.5, F.6, F.7, F.8, F.9, F.10⟩

/-- The structurally recursive `orderedProd` (wave L8): equal to the project's, by
induction on the index. -/
theorem orderedProd_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SymplecticFree.orderedProd = @StratonovichHAMSecondMoment.SymplecticFree.orderedProd := by
  funext E _ _ Q n
  induction n with
  | zero => rfl
  | succ n ih =>
    show Q (n + 1) * StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SymplecticFree.orderedProd Q n = Q (n + 1) * StratonovichHAMSecondMoment.SymplecticFree.orderedProd Q n
    rw [ih]

end SymplecticFree

namespace TerminalWick

/-! The structurally recursive `chainWeight` and `chainWeightReal` (wave L8): equal to the
project's, by induction on the number of points; the copied `chainMass` and
`chainMassReal`, their integrals, are then equal to the project's. -/

theorem chainWeight_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWick.chainWeight = @StratonovichHAMSecondMoment.TerminalWick.chainWeight := by
  funext d n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext T s
    show (if 0 < s (Fin.last n) ∧ s (Fin.last n) < T then
          StratonovichHAMSecondMoment.WaveGreen.waveGreen d (T - s (Fin.last n)) Set.univ else 0) *
        StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWick.chainWeight d n (s (Fin.last n)) (Fin.init s) =
      (if 0 < s (Fin.last n) ∧ s (Fin.last n) < T then
          StratonovichHAMSecondMoment.WaveGreen.waveGreen d (T - s (Fin.last n)) Set.univ else 0) *
        StratonovichHAMSecondMoment.TerminalWick.chainWeight d n (s (Fin.last n)) (Fin.init s)
    rw [ih]

theorem chainWeightReal_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWick.chainWeightReal = @StratonovichHAMSecondMoment.TerminalWick.chainWeightReal := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext T s
    show (if 0 < s (Fin.last n) ∧ s (Fin.last n) < T then ENNReal.ofReal (T - s (Fin.last n)) else 0) *
        StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWick.chainWeightReal n (s (Fin.last n)) (Fin.init s) =
      (if 0 < s (Fin.last n) ∧ s (Fin.last n) < T then ENNReal.ofReal (T - s (Fin.last n)) else 0) *
        StratonovichHAMSecondMoment.TerminalWick.chainWeightReal n (s (Fin.last n)) (Fin.init s)
    rw [ih]

theorem chainMass_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWick.chainMass = @StratonovichHAMSecondMoment.TerminalWick.chainMass := by
  funext d n T
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWick.chainMass StratonovichHAMSecondMoment.TerminalWick.chainMass
  rw [chainWeight_eq]

theorem chainMassReal_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWick.chainMassReal = @StratonovichHAMSecondMoment.TerminalWick.chainMassReal := by
  funext n T
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWick.chainMassReal StratonovichHAMSecondMoment.TerminalWick.chainMassReal
  rw [chainWeightReal_eq]

end TerminalWick

namespace DampedNormsHomog

/-- `GreenMass` as an equation, for the wave-L8 statements that mention it inside a
conjunction (where the converters above do not reach). -/
theorem gm_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.DampedNormsHomog.GreenMass = @StratonovichHAMSecondMoment.DampedNormsHomog.GreenMass := by
  funext d G
  exact propext ⟨gmToP, gmOfP⟩

end DampedNormsHomog

namespace RemoveMask

/-! The copied `maskedRate` (wave L8) is `rayleighRate` of a masked mean, and the copied
`rayleighRate` is equal to the project's only by `rayleighRate_eq`; so are `maskedRate`,
`maskedIntegratedRate` and the named input `RawBlockOriginalLower` built from them. -/

theorem maskedRate_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RemoveMask.maskedRate = @StratonovichHAMSecondMoment.RemoveMask.maskedRate := by
  funext d a Γ Ψ R t
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RemoveMask.maskedRate StratonovichHAMSecondMoment.RemoveMask.maskedRate
  rw [WeakSobolev.rayleighRate_eq]
  try rfl

theorem maskedIntegratedRate_eq :
    @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RemoveMask.maskedIntegratedRate = @StratonovichHAMSecondMoment.RemoveMask.maskedIntegratedRate := by
  funext d a Γ Ψ R
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RemoveMask.maskedIntegratedRate StratonovichHAMSecondMoment.RemoveMask.maskedIntegratedRate
  rw [maskedRate_eq]

theorem rawBlock_eq :
    @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RemoveMask.RawBlockOriginalLower = @StratonovichHAMSecondMoment.RemoveMask.RawBlockOriginalLower := by
  funext d a Γ Ψ v L
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RemoveMask.RawBlockOriginalLower StratonovichHAMSecondMoment.RemoveMask.RawBlockOriginalLower
  rw [maskedIntegratedRate_eq]

end RemoveMask

namespace SpatialBracket

/-- The copied named input `OccupationCeilingK0` (wave L8) mentions `integratedRate`,
equal to the project's only by `integratedRate_eq`. -/
theorem occK0_eq :
    @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpatialBracket.OccupationCeilingK0 = @StratonovichHAMSecondMoment.SpatialBracket.OccupationCeilingK0 := by
  funext d alpha a Γ
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpatialBracket.OccupationCeilingK0 StratonovichHAMSecondMoment.SpatialBracket.OccupationCeilingK0
  rw [VariationalDilation.integratedRate_eq]
  try rfl

end SpatialBracket

namespace RawOccupationEnergy

/-! The copied sets `ratioSet` and `energySet` of `RawOccupationEnergy` (wave L9) quantify over
the copied structure `IsOccField`: equal to the project's through `occ_eq`, and hence so are
their suprema `Cocc` and `EO`. -/

theorem ratioSet_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RawOccupationEnergy.ratioSet = @StratonovichHAMSecondMoment.RawOccupationEnergy.ratioSet := by
  funext d a alpha Γ
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RawOccupationEnergy.ratioSet StratonovichHAMSecondMoment.RawOccupationEnergy.ratioSet
  rw [OccupationPhysicalClass.occ_eq]
  rfl

theorem Cocc_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RawOccupationEnergy.Cocc = @StratonovichHAMSecondMoment.RawOccupationEnergy.Cocc := by
  funext d a alpha Γ
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RawOccupationEnergy.Cocc StratonovichHAMSecondMoment.RawOccupationEnergy.Cocc
  rw [ratioSet_eq]

theorem energySet_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RawOccupationEnergy.energySet = @StratonovichHAMSecondMoment.RawOccupationEnergy.energySet := by
  funext d a Γ ζ
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RawOccupationEnergy.energySet StratonovichHAMSecondMoment.RawOccupationEnergy.energySet
  rw [OccupationPhysicalClass.occ_eq]
  rfl

theorem EO_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RawOccupationEnergy.EO = @StratonovichHAMSecondMoment.RawOccupationEnergy.EO := by
  funext d a Γ ζ
  unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RawOccupationEnergy.EO StratonovichHAMSecondMoment.RawOccupationEnergy.EO
  rw [energySet_eq]

end RawOccupationEnergy

namespace PhaseContractions

/-! The copied structure `PhaseCovariance` (wave L9) is a new `Prop`-valued structure:
equivalent to the project's, hence equal by `propext`. -/

theorem pcToP {alpha : ℝ} {Γ μ : MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd 3)}
    (h : StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PhaseContractions.PhaseCovariance alpha Γ μ) :
    StratonovichHAMSecondMoment.PhaseContractions.PhaseCovariance alpha Γ μ :=
  ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11⟩

theorem pcOfP {alpha : ℝ} {Γ μ : MeasureTheory.Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd 3)}
    (h : StratonovichHAMSecondMoment.PhaseContractions.PhaseCovariance alpha Γ μ) :
    StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PhaseContractions.PhaseCovariance alpha Γ μ :=
  ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11⟩

theorem pc_eq : @StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.PhaseContractions.PhaseCovariance = @StratonovichHAMSecondMoment.PhaseContractions.PhaseCovariance := by
  funext alpha Γ μ
  exact propext ⟨pcToP, pcOfP⟩

end PhaseContractions

/-- Rewrite every copy that is not equal to the project's definition by unfolding. -/
macro "bridge_rw" : tactic =>
  `(tactic| repeat (first
    | rw [StratonovichHamSecondMomentLeanAuditBridge.VariationalDilation.integratedRate_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.VariationalDilation.rate_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.WeakSobolev.rayleighRate_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.WeakSobolev.rayleighSet_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.WeakSobolev.rt_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.IndexedCone.chainState_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.TypeContinuity.tci_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.VariationalRate.scoreSet_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.VariationalRate.score1Set_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.VariationalRate.testRadius_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.VariationalRate.S1Bdd_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.VariationalRate.S1pos_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.SpatialStaticControls.lamSq_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.SpatialStaticControls.lam_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.SpatialStaticControls.lamZ_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.SpatialStaticControls.rayleighFloor_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.SpatialSmoothRatio.staticControls_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.WaveTwoVariances.kernelEntry_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.WaveTwoVariances.maskedKernel_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.WaveTwoVariances.kernelLp_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.WaveTwoVariances.inputBound_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.WaveTwoVariances.outputBound_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.WaveTwoVariances.coef_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.WaveTwoVariances.kerH_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.UniformSeriesTail.twi_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.OccupationPhysicalClass.spb_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.OccupationPhysicalClass.EstarO_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.OccupationPhysicalClass.energySet_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.OccupationPhysicalClass.occ_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.DampedMultiplier.gf_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.SpaceTimePositivity.stcs_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.OccupationCeilingFinite.stcs_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.FiniteWick.cgf_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.SymplecticFree.orderedProd_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.TerminalWick.chainWeight_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.TerminalWick.chainWeightReal_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.TerminalWick.chainMass_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.TerminalWick.chainMassReal_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.DampedNormsHomog.gm_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.RemoveMask.maskedRate_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.RemoveMask.maskedIntegratedRate_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.RemoveMask.rawBlock_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.SpatialBracket.occK0_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.PhaseContractions.pc_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.RawOccupationEnergy.ratioSet_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.RawOccupationEnergy.Cocc_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.RawOccupationEnergy.energySet_eq]
    | rw [StratonovichHamSecondMomentLeanAuditBridge.RawOccupationEnergy.EO_eq]))

/-- `bridge_exact d [c₁, …]` introduces every binder of the goal and closes it with the
constant `d` applied to the introduced variables, in order: each variable is passed as it
is when its type matches `d`'s binder up to unfolding, else through the first converter
`cᵢ` (a function from a copied structure or predicate to the project's) that makes it
match; the result is accepted as it is or through a converter back. It builds an
ordinary proof term, checked by the kernel; it fails when no match is found. -/
syntax (name := bridgeExact) "bridge_exact " ident " [" ident,* "]" : tactic

open Lean Meta Elab Tactic in
@[tactic bridgeExact] def evalBridgeExact : Tactic := fun stx => do
  let d := stx[1]
  let cs := stx[3].getSepArgs
  let g ← getMainGoal
  let (xs, g) ← g.intros
  g.withContext do
    let f ← mkConstWithFreshMVarLevels (← realizeGlobalConstNoOverload d)
    let convs ← cs.mapM fun c => realizeGlobalConstNoOverload c
    let conv (x : Expr) (target : Expr) : MetaM (Option Expr) := do
      if ← isDefEq (← inferType x) target then return some x
      for c in convs do
        let some a ← observing? (mkAppM c #[x]) | continue
        if ← isDefEq (← inferType a) target then return some a
      return none
    let mut e := f
    let mut ty ← inferType f
    for xv in xs do
      let x := mkFVar xv
      ty ← whnf ty
      let .forallE _ dom body _ := ty
        | throwError "bridge_exact: {d} has fewer binders than the goal"
      let some a ← conv x dom
        | throwError "bridge_exact: no conversion of {x} : {← inferType x} to {dom}"
      e := mkApp e a
      ty := body.instantiate1 a
    let goalTy ← g.getType
    let some r ← conv e goalTy
      | throwError "bridge_exact: result {ty} does not match the goal {goalTy}"
    let r ← instantiateMVars r
    if r.hasExprMVar then throwError "bridge_exact: unassigned metavariables remain"
    g.assign r

/-- `bridge_exact` with every converter of this file. -/
macro "bridge_auto " d:ident : tactic =>
  `(tactic| (bridge_rw; bridge_exact $d [StratonovichHamSecondMomentLeanAuditBridge.IndexedCone.gToP, StratonovichHamSecondMomentLeanAuditBridge.IndexedCone.cToP,
      StratonovichHamSecondMomentLeanAuditBridge.WeakSobolev.rtToP, StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP, StratonovichHamSecondMomentLeanAuditBridge.MaskedTrigProducts.toP,
      StratonovichHamSecondMomentLeanAuditBridge.IndexedCone.gOfP, StratonovichHamSecondMomentLeanAuditBridge.IndexedCone.cOfP, StratonovichHamSecondMomentLeanAuditBridge.WeakSobolev.rtOfP,
      StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP,
      StratonovichHamSecondMomentLeanAuditBridge.TimeCompletion.tpToP, StratonovichHamSecondMomentLeanAuditBridge.TimeCompletion.tpOfP,
      StratonovichHamSecondMomentLeanAuditBridge.DampedNormsHomog.gmToP, StratonovichHamSecondMomentLeanAuditBridge.DampedNormsHomog.gmOfP,
      StratonovichHamSecondMomentLeanAuditBridge.TypeContinuity.tciToP, StratonovichHamSecondMomentLeanAuditBridge.TypeContinuity.tciOfP,
      StratonovichHamSecondMomentLeanAuditBridge.UniformSeriesTail.twiToP, StratonovichHamSecondMomentLeanAuditBridge.UniformSeriesTail.twiOfP,
      StratonovichHamSecondMomentLeanAuditBridge.OccupationPhysicalClass.spbToP, StratonovichHamSecondMomentLeanAuditBridge.OccupationPhysicalClass.spbOfP,
      StratonovichHamSecondMomentLeanAuditBridge.OccupationPhysicalClass.occToP, StratonovichHamSecondMomentLeanAuditBridge.OccupationPhysicalClass.occOfP,
      StratonovichHamSecondMomentLeanAuditBridge.DampedMultiplier.gfToP, StratonovichHamSecondMomentLeanAuditBridge.DampedMultiplier.gfOfP,
      StratonovichHamSecondMomentLeanAuditBridge.SpaceTimePositivity.stcsToP, StratonovichHamSecondMomentLeanAuditBridge.SpaceTimePositivity.stcsOfP,
      StratonovichHamSecondMomentLeanAuditBridge.OccupationCeilingFinite.stcsToP, StratonovichHamSecondMomentLeanAuditBridge.OccupationCeilingFinite.stcsOfP,
      StratonovichHamSecondMomentLeanAuditBridge.FiniteWick.cgfToP, StratonovichHamSecondMomentLeanAuditBridge.FiniteWick.cgfOfP,
      StratonovichHamSecondMomentLeanAuditBridge.SymplecticFree.fwdToP, StratonovichHamSecondMomentLeanAuditBridge.SymplecticFree.fwdOfP,
      StratonovichHamSecondMomentLeanAuditBridge.PhaseContractions.pcToP, StratonovichHamSecondMomentLeanAuditBridge.PhaseContractions.pcOfP]))

/-- Revert every local hypothesis of the goal (in context order), so that a statement
written with binders before the colon can be closed by `bridge_auto`. -/
elab "bridge_revert_all" : tactic => do
  let g ← Lean.Elab.Tactic.getMainGoal
  let fvs ← g.withContext do
    let lctx ← Lean.getLCtx
    return lctx.getFVarIds.filter fun f => !(lctx.get! f).isImplementationDetail
  let (_, g) ← g.revert fvs (preserveOrder := true)
  Lean.Elab.Tactic.replaceMainGoal [g]

/-- `bridge_cases d [c₁, …]`: as `bridge_exact`, but after introducing the binders it
splits every variable whose type is the copied inductive `Wave` or `Trig` into its
constructors (the copies then unfold to the project's terms), and closes each case with
`d` applied to the introduced variables, a split variable replaced by its constructor
passed through the converters. It builds an ordinary proof term, checked by the kernel. -/
syntax (name := bridgeCases) "bridge_cases " ident " [" ident,* "]" : tactic

open Lean Meta Elab Tactic in
@[tactic bridgeCases] def evalBridgeCases : Tactic := fun stx => do
  let d := stx[1]
  let cs := stx[3].getSepArgs
  let g ← getMainGoal
  let (xs, g) ← g.intros
  let isSplit (t : Expr) : MetaM Bool := do
    let t ← whnf t
    match t.getAppFn with
    | .const n _ => return n == ``StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedContinuousWave.Wave
        || n == ``StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedTrigProducts.Trig
    | _ => return false
  -- the goals with, for each, the expressions standing for `xs`
  let mut work : Array (MVarId × Array Expr) := #[(g, xs.map mkFVar)]
  let mut done : Array (MVarId × Array Expr) := #[]
  while h : work.size > 0 do
    let (g, es) := work.back
    work := work.pop
    let next? ← g.withContext do
      es.findM? fun e => do return e.isFVar && (← isSplit (← inferType e))
    match next? with
    | none => done := done.push (g, es)
    | some e =>
      let subs ← g.cases e.fvarId!
      for sg in subs do
        work := work.push (sg.mvarId, es.map fun x => sg.subst.apply x)
  let f0 ← realizeGlobalConstNoOverload d
  let convs ← cs.mapM fun c => realizeGlobalConstNoOverload c
  for (g, es) in done do
    g.withContext do
      let conv (x : Expr) (target : Expr) : MetaM (Option Expr) := do
        if ← isDefEq (← inferType x) target then return some x
        for c in convs do
          let some a ← observing? (mkAppM c #[x]) | continue
          if ← isDefEq (← inferType a) target then return some a
        return none
      let mut e ← mkConstWithFreshMVarLevels f0
      let mut ty ← inferType e
      for x in es do
        ty ← whnf ty
        let .forallE _ dom body _ := ty
          | throwError "bridge_cases: {d} has fewer binders than the goal"
        let some a ← conv x dom
          | throwError "bridge_cases: no conversion of {x} : {← inferType x} to {dom}"
        e := mkApp e a
        ty := body.instantiate1 a
      let goalTy ← g.getType
      let some r ← conv e goalTy
        | throwError "bridge_cases: result {ty} does not match the goal {goalTy}"
      let r ← instantiateMVars r
      if r.hasExprMVar then throwError "bridge_cases: unassigned metavariables remain"
      g.assign r
  replaceMainGoal []

/-- `bridge_cases` with every converter of this file. -/
macro "bridge_cases_auto " d:ident : tactic =>
  `(tactic| (bridge_rw; bridge_cases $d [StratonovichHamSecondMomentLeanAuditBridge.MaskedContinuousWave.toP,
      StratonovichHamSecondMomentLeanAuditBridge.MaskedTrigProducts.toP,
      StratonovichHamSecondMomentLeanAuditBridge.TimeCompletion.tpToP, StratonovichHamSecondMomentLeanAuditBridge.TimeCompletion.tpOfP,
      StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP, StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_ofP,
      StratonovichHamSecondMomentLeanAuditBridge.DampedNormsHomog.gmToP, StratonovichHamSecondMomentLeanAuditBridge.DampedNormsHomog.gmOfP,
      StratonovichHamSecondMomentLeanAuditBridge.TypeContinuity.tciToP, StratonovichHamSecondMomentLeanAuditBridge.TypeContinuity.tciOfP,
      StratonovichHamSecondMomentLeanAuditBridge.UniformSeriesTail.twiToP, StratonovichHamSecondMomentLeanAuditBridge.UniformSeriesTail.twiOfP,
      StratonovichHamSecondMomentLeanAuditBridge.OccupationPhysicalClass.spbToP, StratonovichHamSecondMomentLeanAuditBridge.OccupationPhysicalClass.spbOfP,
      StratonovichHamSecondMomentLeanAuditBridge.OccupationPhysicalClass.occToP, StratonovichHamSecondMomentLeanAuditBridge.OccupationPhysicalClass.occOfP,
      StratonovichHamSecondMomentLeanAuditBridge.DampedMultiplier.gfToP, StratonovichHamSecondMomentLeanAuditBridge.DampedMultiplier.gfOfP,
      StratonovichHamSecondMomentLeanAuditBridge.SpaceTimePositivity.stcsToP, StratonovichHamSecondMomentLeanAuditBridge.SpaceTimePositivity.stcsOfP,
      StratonovichHamSecondMomentLeanAuditBridge.OccupationCeilingFinite.stcsToP, StratonovichHamSecondMomentLeanAuditBridge.OccupationCeilingFinite.stcsOfP,
      StratonovichHamSecondMomentLeanAuditBridge.FiniteWick.cgfToP, StratonovichHamSecondMomentLeanAuditBridge.FiniteWick.cgfOfP,
      StratonovichHamSecondMomentLeanAuditBridge.SymplecticFree.fwdToP, StratonovichHamSecondMomentLeanAuditBridge.SymplecticFree.fwdOfP,
      StratonovichHamSecondMomentLeanAuditBridge.PhaseContractions.pcToP, StratonovichHamSecondMomentLeanAuditBridge.PhaseContractions.pcOfP]))

end StratonovichHamSecondMomentLeanAuditBridge
