/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Statement-fidelity check for the comparator tier (read-only; writes nothing).

  lake env lean --run scripts/comparator/CheckFidelity.lean

It loads `Challenge` (which imports every `ChallengeDefs` module) together with the
project umbrella `StratonovichHAMSecondMoment`, and checks, with `Expr` equality
(no unfolding, no definitional equality):

1. every constant declared by a `ChallengeDefs` module is `StratonovichHamSecondMomentLeanDefs.N`
   for a project constant `N` of the same kind, universe parameters, type and value
   (definitions, opaque; for a theorem the type only, proofs being irrelevant) or constructor/recursor data (inductives), once
   every constant name `StratonovichHamSecondMomentLeanDefs.M` inside it is read as `M`
   (a private auxiliary of a copy, such as a match splitter, is read as the project's
   private constant of the same user-facing name);
2. every theorem of `comparator.json`'s `theorem_names` is declared by `Challenge`,
   is `StratonovichHamSecondMomentLeanAudit.D` for a project theorem `D`, and its type
   equals the type of `D` under the same renaming.

So each Challenge statement is the claimed declaration's elaborated type verbatim, with
the project definitions it mentions replaced by verbatim copies. It prints one line per
problem and a summary; exit 0 only when there is none.
-/
import Lean
import Challenge
import StratonovichHAMSecondMoment
open Lean

/-- The prefix of the copied definitions (`ChallengeDefs`). -/
def pfx : Name := `StratonovichHamSecondMomentLeanDefs
/-- The prefix of the Challenge theorems. -/
def cpfx : Name := `StratonovichHamSecondMomentLeanAudit

def stripWith (q : Name) (n : Name) : Name :=
  let s := n.toString (escape := false)
  let p := q.toString ++ "."
  if s.startsWith p then (s.drop p.length).toString.toName else n

/-- `pfx ++ N ↦ N`, every other name unchanged; a private name `_private.M.0.(pfx ++ N)`
of a copy maps through `pm` to the project's private constant with user name `N`, when
there is one (a private auxiliary of a copy, such as a match splitter, is generated in
whichever module first needs it, which need not be the module of its copy). -/
def strip (pm : NameMap Name) (n : Name) : Name :=
  match privateToUserName? n with
  | some u => (pm.find? (stripWith pfx u)).getD n
  | none => stripWith pfx n

partial def ren (pm : NameMap Name) (e : Expr) : Expr :=
  e.replace fun
    | .const n us => some (.const (strip pm n) us)
    | .proj s i b => some (.proj (strip pm s) i (ren pm b))
    | _ => none

/-- The first differing pair of subterms (for the problem report only). -/
partial def firstDiff (a b : Expr) : Option (Expr × Expr) :=
  if a == b then none else
  match a, b with
  | .app f x, .app g y => (firstDiff f g).orElse fun _ => firstDiff x y
  | .lam _ t x _, .lam _ u y _ => (firstDiff t u).orElse fun _ => firstDiff x y
  | .forallE _ t x _, .forallE _ u y _ => (firstDiff t u).orElse fun _ => firstDiff x y
  | .letE _ t v x _, .letE _ u w y _ =>
    ((firstDiff t u).orElse fun _ => firstDiff v w).orElse fun _ => firstDiff x y
  | .mdata _ x, .mdata _ y => firstDiff x y
  | .proj _ i x, .proj _ j y => if i == j then firstDiff x y else some (a, b)
  | _, _ => some (a, b)

def showDiff (a b : Expr) : String :=
  match firstDiff a b with
  | some (x, y) => s!"\n    copy/challenge: {(toString x).take 300}\n    project:        {(toString y).take 300}"
  | none => ""

def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

/-- The differing field of a copy `c` and the project constant `p`, if any. Universe
parameter names are compared up to macro scopes (a generated `noConfusion` carries a
hygienic name that includes its module), and the copy's are renamed to the project's
before the comparison. -/
def differs (pm : NameMap Name) (c p : ConstantInfo) : Option String :=
  let lc := c.levelParams; let lp := p.levelParams
  -- rename universe parameters only when the names differ: instantiation also
  -- normalizes level expressions (`max (u+1) 1` becomes `u+1`)
  let sub (e : Expr) : Expr :=
    if lc == lp then ren pm e else ren pm (e.instantiateLevelParams lc (lp.map Level.param))
  if kind c != kind p then some s!"kind {kind c} vs {kind p}"
  else if lc.map Name.eraseMacroScopes != lp.map Name.eraseMacroScopes then
    some s!"universe parameters {lc} vs {lp}"
  else if sub c.type != p.type then some "type"
  else match c, p with
    | .defnInfo a, .defnInfo b =>
      if sub a.value != b.value then some "value"
      else if a.safety != b.safety then some "safety" else none
    | .thmInfo _, .thmInfo _ => none  -- a proof is irrelevant: the type is compared above
    | .opaqueInfo a, .opaqueInfo b => if sub a.value != b.value then some "value" else none
    | .inductInfo a, .inductInfo b =>
      if a.ctors.map (strip pm) != b.ctors || a.all.map (strip pm) != b.all
        || a.numParams != b.numParams || a.numIndices != b.numIndices
        || a.isRec != b.isRec || a.isUnsafe != b.isUnsafe || a.isReflexive != b.isReflexive
      then some "inductive data" else none
    | .ctorInfo a, .ctorInfo b =>
      if strip pm a.induct != b.induct || a.cidx != b.cidx || a.numParams != b.numParams
        || a.numFields != b.numFields then some "constructor data" else none
    | .recInfo a, .recInfo b =>
      if a.all.map (strip pm) != b.all || a.numParams != b.numParams || a.numIndices != b.numIndices
        || a.numMotives != b.numMotives || a.numMinors != b.numMinors || a.k != b.k
        || a.rules.length != b.rules.length
        || (a.rules.zip b.rules).any (fun (x, y) =>
             strip pm x.ctor != y.ctor || x.nfields != y.nfields || sub x.rhs != y.rhs)
      then some "recursor data" else none
    | _, _ => none

/-- Parser, macro and unexpander constants that a `notation` command generates. -/
def syntaxOnly (c : ConstantInfo) : Bool :=
  match c.type.getAppFn with
  | .const n _ => n == ``Lean.ParserDescr || n == ``Lean.TrailingParserDescr
      || n == ``Lean.Macro || n == ``Lean.PrettyPrinter.Unexpander
  | _ => false

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Challenge }, { module := `StratonovichHAMSecondMoment }] {}
  let mut problems := 0
  let mut nDefs := 0
  let mut nSyntax := 0
  let mut nPriv := 0
  -- the project's private constants by their user-facing name
  let mut pm : NameMap Name := {}
  for (n, _) in env.constants.toList do
    if let some u := privateToUserName? n then
      if let some i := env.getModuleIdxFor? n then
        let m := env.header.moduleNames[i.toNat]!
        if (`StratonovichHAMAudit).isPrefixOf m || (`StratonovichHAMSecondMoment).isPrefixOf m then
          pm := pm.insert u n
  -- 1. the copied definitions
  for mi in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[mi]!
    unless (`ChallengeDefs).isPrefixOf m do continue
    for n in env.header.moduleData[mi]!.constNames do
      let some c := env.find? n | continue
      -- a kept `local notation` compiles to parser, macro and unexpander constants; they
      -- are syntax, never part of an elaborated statement or definition
      if syntaxOnly c then nSyntax := nSyntax + 1; continue
      -- a private proof auxiliary of a copied theorem (its name carries the module)
      if isPrivateName n && c.isTheorem then nPriv := nPriv + 1; continue
      let s := strip pm n
      if s == n && isPrivateName n then
        IO.println s!"PROBLEM {n} ({m}): a private copy with no project counterpart"; problems := problems + 1; continue
      if s == n then
        IO.println s!"PROBLEM {n} ({m}): not under the prefix {pfx}"; problems := problems + 1; continue
      match env.find? s with
      | none => IO.println s!"PROBLEM {n} ({m}): no project constant {s}"; problems := problems + 1
      | some p =>
        match differs pm c p with
        | some f =>
          let detail := match c, p with
            | .defnInfo a, .defnInfo b => showDiff (ren pm a.value) b.value
            | _, _ => ""
          IO.println s!"PROBLEM {n}: {f} differs from {s}{detail}"; problems := problems + 1
        | none => nDefs := nDefs + 1
  -- 2. the Challenge theorems
  let cfg ← IO.ofExcept <| Json.parse (← IO.FS.readFile "comparator.json")
  let names ← IO.ofExcept <| (cfg.getObjValAs? (Array String) "theorem_names")
  let some chIdx := env.getModuleIdx? `Challenge | throw <| IO.userError "Challenge not loaded"
  let mut nThms := 0
  for s in names do
    let n := s.toName
    let some c := env.find? n | IO.println s!"PROBLEM {n}: not in the environment"; problems := problems + 1; continue
    if env.getModuleIdxFor? n != some chIdx then
      IO.println s!"PROBLEM {n}: not declared by Challenge"; problems := problems + 1
    let d := stripWith cpfx n
    match env.find? d with
    | none => IO.println s!"PROBLEM {n}: no project declaration {d}"; problems := problems + 1
    | some p =>
      if !p.isTheorem then IO.println s!"PROBLEM {n}: {d} is not a theorem"; problems := problems + 1
      else if c.levelParams != p.levelParams then
        IO.println s!"PROBLEM {n}: universe parameters {c.levelParams} vs {p.levelParams}"; problems := problems + 1
      else if ren pm c.type != p.type then
        IO.println s!"PROBLEM {n}: type differs from {d}{showDiff (ren pm c.type) p.type}"; problems := problems + 1
      else nThms := nThms + 1
  IO.println s!"fidelity: {nDefs} copied constant(s) equal to the project's ({nSyntax} notation syntax constant(s) and {nPriv} private proof auxiliary(ies) skipped), {nThms} of {names.size} Challenge theorem type(s) equal to the claimed declaration's; {problems} problem(s)"
  return if problems == 0 then 0 else 1
