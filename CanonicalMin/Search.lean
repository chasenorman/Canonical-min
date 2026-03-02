import CanonicalMin.Checker
open Array Ord Constraint TypeMVar

structure CanonicalState where
  assignments: Array (Option Assignment) := {}
  constraints: Array (Array Constraint) := {}

abbrev CanonicalM := StateM CanonicalState

def run (x : ConstraintM T) : CanonicalM (Option T) := do
  return x.run (← get).assignments

def capacity : CanonicalM Nat := do pure (← get).assignments.size

def MVar.assign : MVar → Option Assignment → CanonicalM Unit :=
  fun m assn => do modify ({ · with assignments[m.id] := assn })

def process (f : Array Constraint → Constraint → Array Constraint)
  (cs : Array Constraint) : CanonicalM Unit := do
  for c in cs do modify fun state => { state with
    constraints := state.constraints.modify c.stuck.id (f · c)
  }

def MVar.domain (m : MVar) (pos : Nat) :
  CanonicalM (Array (Assignment × Array Constraint)) := do
  let mut result := #[]
  for (blockType, debruijn) in m.lctx.zipIdx do
    for (headType, index) in blockType.inputs.zipIdx do
      if pos + headType.inputs.size > (← capacity) then continue
      let args := headType.inputs.zipIdx.map fun (input, k) => {
        id := pos + k, lctx := if (inputs input).isEmpty then m.lctx else input :: m.lctx,
        preferredNames := input.preferredNames
      }
      let assn : Assignment := { debruijn, index, args }
      m.assign assn
      if let some constraints ← run
        ((← get).constraints[m.id]!.flatMapM continuation)
        then result := result.push (assn, constraints)
  return result

instance : Ord (MVar × Bool) where
  compare a b := compare a.2 b.2

abbrev Next := Option (MVar × Bool) × Float
partial def next (m : MVar) : CanonicalM Next := do
  if let some assn := (← get).assignments[m.id]! then
    assn.args.foldlM (init := (none, 1)) fun (fst, e1) s => do
      let (snd, e2) ← next s
      pure (if compare fst snd == .gt then fst else snd, e1 * e2)
  else
    let rigid ← run ((← get).constraints[m.id]!.anyM rigid)
    return (some (m, rigid.get!), if rigid.get! then 1 else 5)

variable [Monad m] (root : MVar) (cb step : m Unit) in
partial def dfs [MonadLiftT CanonicalM m]
  (entropy : Float) (pos : Nat) : m Unit := do
  step
  let (some (mvar, _), predicted) ← next root | cb
  if entropy < predicted then return
  let domain ← mvar.domain pos
  for (assn, constraints) in domain do
    mvar.assign assn
    process (·.push ·) constraints
    dfs (entropy / domain.size.toFloat) (pos + assn.args.size)
    process (fun _ => ·.pop) constraints
  mvar.assign none

def extend (size : Nat) : CanonicalM Unit := do
  modify fun state => { state with
    assignments := state.assignments ++ replicate size none
    constraints := state.constraints ++ replicate size #[]
  }

def iddfs [Monad m] [MonadLiftT CanonicalM m]
  (root : MVar) (cb step : m Unit) : m Unit := do
  let start ← capacity
  let mut entropy := 1000
  while true do
    extend 4
    dfs root cb step entropy start
    entropy := entropy * 3
