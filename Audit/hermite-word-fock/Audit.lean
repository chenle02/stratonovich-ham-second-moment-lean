import StratonovichHAMAudit.HermiteWordFock
#print StratonovichHAMAudit.HermiteWordFock.cut_eq_raw_fock
#print axioms StratonovichHAMAudit.HermiteWordFock.cut_eq_raw_fock

open StratonovichHAMAudit.HermiteWord in
/-- Consumer: a two-letter word of one color at cutoff `2` is unchanged by the cutoffs. -/
example {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    (K : Fin 1 → X →L[ℂ] X) (T : Unit → X →L[ℂ] X) (u : X) :
    cut (StratonovichHAMSecondMoment.FockForm.truncC (fun _ => 2))
        (fun i v => StratonovichHAMSecondMoment.HermiteFock.gmul i (fun l => K i (v l)))
        (fun b v => fun l => T b (v l)) (StratonovichHAMSecondMoment.HermiteFock.vac u)
        [(0, ()), (0, ())] =
      raw (fun i v => StratonovichHAMSecondMoment.HermiteFock.gmul i (fun l => K i (v l)))
        (fun b v => fun l => T b (v l)) (StratonovichHAMSecondMoment.HermiteFock.vac u)
        [(0, ()), (0, ())] :=
  StratonovichHAMAudit.HermiteWordFock.cut_eq_raw_fock K T u _ _ (by
    intro c
    fin_cases c
    simp [counts, bump])
