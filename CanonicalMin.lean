import Canonical
import CanonicalMin.Search
open Lean Parser Tactic Meta Elab Tactic Core PremiseSelection

abbrev DfsM := StateT CanonicalState IO
instance : MonadLiftT CanonicalM DfsM where
  monadLift m s := do m s

mutual
  partial def Canonical.Term.toTerm (t : Canonical.Term) (ctx : List (Array String) := []) : CanonicalM MVar := do
    let names := t.lets.map (·.name) ++ t.params.map (·.name)
    t.spine.toSpine (if names.isEmpty then ctx else names :: ctx) names

  partial def Canonical.Spine.toSpine (s : Canonical.Spine) (ctx : List (Array String) := []) (names : Array String) : CanonicalM MVar := do
    let (d, i) := (ctx.zipIdx.findSome? (fun (l, d) => (l.idxOf? s.head).map (d, ·))).get!
    let assn : Assignment := { debruijn := d, index := i, args := (← s.args.mapM (·.toTerm ctx)) }
    let size := (← get).constraints.size
    modify fun x => { x with
      constraints := x.constraints.push #[]
      assignments := x.assignments.push assn
    }
    pure ⟨size, [], names⟩
end

partial def Canonical.Typ.toType (ty : Canonical.Typ) (ctx : List (Array String) := []) : CanonicalM TypeMVar := do
  let preferredNames := ty.lets.map (·.name) ++ ty.params.map (·.name)
  let types := ty.letTypes ++ ty.paramTypes
  pure { inputs := ← types.mapM (·.get!.toType (if preferredNames.isEmpty then ctx else preferredNames :: ctx)), output := ← ty.toTerm.toTerm ctx, preferredNames }

def disambiguate (str : String) (set : Std.HashSet String) : String := Id.run do
  let mut count := 0
  let mut name := str
  while set.contains name do
    count := count + 1
    name := s!"{str}{count}"
  name

mutual
  partial def MVar.toTerm (s : MVar) (ctx : List (Array String) := []) (set : Std.HashSet String := {}) : CanonicalM Canonical.Term := do
    let mut set := set
    let mut disambiguated := #[]
    for name in s.preferredNames do
      let name := disambiguate name set
      set := set.insert name
      disambiguated := disambiguated.push name
    return Canonical.Term.mk (disambiguated.map (Canonical.Var.mk ·)) #[] (← s.toSpine (if disambiguated.isEmpty then ctx else disambiguated :: ctx) set) #[]

  partial def MVar.toSpine (s : MVar) (ctx : List (Array String)) (set : Std.HashSet String) : CanonicalM Canonical.Spine := do
    match (← get).assignments[s.id]! with
    | none => return Canonical.Spine.mk "_" #[] #[]
    | some assn =>
      let name := (ctx[assn.debruijn]?.bind (·[assn.index]?)).getD "?"
      let args ← assn.args.mapM (·.toTerm ctx set)
      return Canonical.Spine.mk name args #[]
end

partial def MVar.toString (s : MVar) : CanonicalM String := do
  match (← get).assignments[s.id]! with
  | none => pure "_"
  | some assn =>
    let name := (s.lctx[assn.debruijn]?.bind (·.preferredNames[assn.index]?)).getD "?"
    let params := (s.lctx[0]?.map (·.preferredNames)).getD #[]
    let args := (← assn.args.mapM (·.toString))
    if params.isEmpty && args.isEmpty then return name
    let params := params.foldl (fun x y => s!"{x} {y}") ""
    let args := args.foldl (s!"{·} {·}") ""
    pure s!"(λ{params}. {name}{args})"

def add (arr : Array Constraint) : CanonicalM Unit := do
  for c in arr do modify fun x => { x with
    constraints := x.constraints.modify c.stuck.id (·.push c)
  }

syntax premises := " [" withoutPosition(term,*,?) "]"

partial def consistentWith (t1 t2 : Canonical.Term) : Bool :=
  t1.spine.head == "_" || (
    t1.spine.head == t2.spine.head &&
    (t1.spine.args.zip t2.spine.args).all fun (arg1, arg2) => consistentWith arg1 arg2
  )

def removeTypeInType (typ : Canonical.Typ) : Canonical.Typ :=
  if let some idx := typ.lets.findIdx? (fun v => v.name == "Sort") then
    let uType : Canonical.Typ := ⟨⟨#[], #[], ⟨"_u", #[], #[]⟩, #[]⟩, #[], #[]⟩
    { typ with
      lets := typ.lets.push ⟨⟨"_u"⟩, #[]⟩,
      letTypes := (typ.letTypes.set! idx uType).push uType }
  else typ

partial def depth (t : Canonical.Term) : Nat :=
  1 + t.spine.args.foldl (fun n t => max n (depth t)) 0

def inhabit (typ : Canonical.Typ) (timeout : Nat) (count : Nat) : DfsM (Array Canonical.Term) := do
  -- let desired := (← Canonical.canonical typ timeout.toUInt64 count.toUSize).terms[0]!

  let result : IO.Ref (Array Canonical.Term) ← IO.mkRef #[]
  let tsk ← typ.toType
  let typ := Typ.mk tsk []
  let size : Nat := (← get).constraints.size
  let _ ← (do pure (← modify fun x =>
    { x with
      constraints := x.constraints.push #[]
      assignments := x.assignments.push none
    }
  ) : CanonicalM Unit)
  let sk := MVar.mk size [tsk] tsk.preferredNames
  let tm := Term.mk sk []
  let time ← IO.monoMsNow
  -- let steps ← IO.mkRef 0

  add (← run (do constraint (check tm typ) 0)).get!
  try
    iddfs sk (do
      let tm ← sk.toTerm
      result.modify (·.push tm)
      dbg_trace (depth tm)
      if (← result.get).size >= count then
        IO.throwServerError ""
    ) (do
      -- steps.modify (· + 1)
      -- IO.println (← sk.toTerm).spine
      if (← IO.checkCanceled) || timeout*1000 <= (← IO.monoMsNow) - time then IO.throwServerError ""
      -- pure (consistentWith (← sk.toTerm) desired)
    )
  catch _ => pure ()
  -- dbg_trace ← steps.get
  dbg_trace ((← IO.monoMsNow) - time).toFloat / 1000.0
  result.get

def preprocessIntros (goal : MVarId) (reconstruct : Expr → MetaM Expr) : MetaM (MVarId × (Expr → MetaM Expr)) := do
  let goal := (← mkFreshExprMVar (← goal.getType)).mvarId!
  let (fvars, mvar) ← goal.intros
  let reconstruct' := fun e : Expr => do
    reconstruct (← mkLambdaFVars (fvars.map (.fvar)) e)
  return (mvar, reconstruct')

def preprocessCanonical (goal : MVarId) (premises : Array Name) (config : Canonical.CanonicalConfig) : MetaM (Canonical.Typ × MVarId × (Expr → MetaM Expr)) := do
  let mut premises := premises
  if config.suggestions then
    let found ← select goal
    let found := found.insertionSort (fun a b => a.score > b.score)
    let found := found.map (fun x => x.name)
    let found := found.take 3
    premises := premises ++ found

  let mut structs := #[]
  if config.destruct then
    let env ← getEnv
    structs := premises.filter fun name => isStructure env name
    premises := premises.filter fun name => !isStructure env name

  if config.pi then
    premises := premises.push ``Canonical.Pi

  let (goal', reconstruct) ← Canonical.preprocess goal config structs
  let (goal', reconstruct) ← preprocessIntros goal' reconstruct

  let typ ← Canonical.withArityUnfold config.monomorphize do goal'.withContext do
    let goal ← goal'.getType
    Canonical.toCanonical goal premises (structs.push ``Canonical.Pi) config

  return (removeTypeInType typ, goal', reconstruct)

elab (name := canonicalSeq) "canonical_min" timeout_syntax:(num)? config:optConfig premises_syntax:(premises)? : tactic => unsafe do
  let mut premises ← if let some premises := premises_syntax then
    match premises with
    | `(premises| [$args,*]) => args.getElems.raw.mapM resolveGlobalConstNoOverload
    | _ => Elab.throwUnsupportedSyntax
    else pure #[]

  let timeout := if let some timeout := timeout_syntax then timeout.getNat else 5

  let config ← Canonical.canonicalConfig config

  let (typ, goal', reconstruct) ← preprocessCanonical (← getMainGoal) premises config

  let (proofs, _) ← inhabit typ timeout config.count.toNat {}

  Canonical.withArityUnfold config.monomorphize do goal'.withContext do
    let proofs ← proofs.mapM fun term =>
      let term := { term with params := #[] }
      do Canonical.fromCanonical term (← goal'.getType)
    let proofs ← proofs.mapM (fun x => reconstruct x)

    if proofs.isEmpty then
      match premises_syntax with
      | some _ => match timeout_syntax with
        | some _ => throwError "No proof found."
        | none => throwError "No proof found. Change timeout to `n` with `canonical n`"
      | none => throwError "No proof found. Supply constant symbols with `canonical [name, ...]`"

    (← getMainGoal).withContext do
      withOptions Canonical.applyOptions do
        Elab.admitGoal (← getMainGoal)
        if h : proofs.size = 1 then
          Meta.Tactic.TryThis.addExactSuggestion (← getRef) proofs[0]
        else
          Meta.Tactic.TryThis.addExactSuggestions (← getRef) proofs
