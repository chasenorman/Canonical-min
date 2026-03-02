import CanonicalMin.Checker
open Array Ord Constraint TypeMVar

structure CanonicalState where
  assignments: Array (Option Assignment) := {}
  constraints: Array (Array Constraint) := {}

/--
The computation in `dfs` is performed in the `CanonicalM` monad. `CanonicalM` is a
state monad with access to two arrays, each indexed by the `id` of a metavariable.
We have `assignments` as in `ConstraintM`, and we have `constraints` which for
each metavariable identifier stores an array of constraints that are stuck on that
metavariable.
-/
abbrev CanonicalM := StateM CanonicalState

def run (x : ConstraintM T) : CanonicalM (Option T) := do
  return x.run (← get).assignments

/--
We define `capacity` to be the size of `assignments`.
-/
def capacity : CanonicalM Nat := do pure (← get).assignments.size

/--
When assigning a metavariable, we simply modify the assignments array at the
index defined by the identifier for the metavariable. This can be done with the
`modify` function for `StateM`.
-/
def MVar.assign : MVar → Option Assignment → CanonicalM Unit :=
  fun m assn => do modify ({ · with assignments[m.id] := assn })

/--
The `process` function modifies the `constraints` array for the stuck
metavariables of an input array of constraints `cs`. The modification function `f` is `push`
when adding constraints and `pop` when removing them.
-/
def process (f : Array Constraint → Constraint → Array Constraint)
  (cs : Array Constraint) : CanonicalM Unit := do
  for c in cs do modify fun state => { state with
    constraints := state.constraints.modify c.stuck.id (f · c)
  }

/--
To demonstrate the use of `MVar`, we show how to compute the domain of a
metavariable `m`. The valid `debruijn` values for the assignment of `m` are the indices
of a `TypeMVar` `blockType` in `m.lctx`. For that `debruijn` index, the valid `index`
values are the indices of a `TypeMVar` `headType` in `blockType.inputs`. Our plan
is to construct an assignment with its head defined by `debruijn` and `index`, with
arguments that are fresh metavariables. First, we check if we have the capacity
in the `assignments` array to create the number of metavariables expected by
`headType.inputs`. If so, we create a new metavariable for each `input`, adding
the bindings of `input` to the `lctx`, and choosing the `preferredNames` of the
metavariable’s bindings to be the `preferredNames` for `input`.

Then, we construct this assignment and assign `m` to it. We invoke the callbacks
of the constraints that were previously stuck on `m`, to obtain an array of new
constraints. If no exception is thrown, the assignment is valid and we add the
assignment and its constraints to the `result` array.
-/
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

/--
We define an ordering on a pair containing a metavariable and a `Bool` for
whether the metavariable has a rigid constraint:
-/
instance : Ord (MVar × Bool) where
  compare a b := compare a.2 b.2

abbrev Next := Option (MVar × Bool) × Float
/--
The `next` function, to select the next metavariable to refine and estimate the
remaining work to be done, can be implemented with an arbitrary heuristic.
Since we uniformly and independently process arguments in `WHNF.eq` and inputs
in `check`, we are free to select unassigned metavariable in any order. In fact,
the ability to assign later metavariables before their dependencies are assigned
is the essential property that makes the algorithm performant in practice. The
only constraint to ensure completeness is that `next` only returns `none` when all
metavariables are assigned.

For this minimal implementation we use a simple heuristic. We select the
rightmost metavariable in the term, unless an earlier metavariable has a
constraint that is a _rigid_ equation, that is, an equation `?X` ≡ M where M is not
a metavariable. We prioritize metavariables with rigid equations because they
are heavily constrained, and rightmost metavariables as they generate strong
unification constraints on earlier metavariables.

We choose the next metavariable to be maximum metavariable according to
this ordering. Furthermore, we estimate that each metavariable multiplies the
predicted entropy by 5, unless the metavariable has a rigid equation:
-/
partial def next (m : MVar) : CanonicalM Next := do
  if let some assn := (← get).assignments[m.id]! then
    assn.args.foldlM (init := (none, 1)) fun (fst, e1) s => do
      let (snd, e2) ← next s
      pure (if compare fst snd == .gt then fst else snd, e1 * e2)
  else
    let rigid ← run ((← get).constraints[m.id]!.anyM rigid)
    return (some (m, rigid.get!), if rigid.get! then 1 else 5)

variable [Monad m] (root : MVar) (cb step : m Unit) in
/--
The `dfs` function takes a `root` metavariable representing the expression that we
would like to assign all unassigned metavariables within. We invoke a heuristic
function `next` to select an unassigned metavariable `mvar` from the expression
tree of `root`. If no such metavariable exists, we have found a solution, and we
invoke a user-provided callback `cb`.

The `next` function also predicts the entropy that will be required to solve
the remaining metavariables. If this prediction exceeds the remaining entropy,
we backtrack. Otherwise, we compute the array of valid head assignments for
`mvar`, called the _domain_. For each of these assignments, we perform the
assignment, file away the generated constraints, recursively call `dfs`, and remove
the constraints. Finally, we unassign `mvar`. For the purposes of allocating new
metavariable identifiers, we keep track of the first unused identifier, `pos`.
-/
partial def dfs [MonadLiftT CanonicalM m]
  (entropy : Float) (pos : Nat) : m Unit := do
  step -- user-provided function for logging, cancelling, etc.
  let (some (mvar, _), predicted) ← next root | cb
  if entropy < predicted then return
  let domain ← mvar.domain pos
  for (assn, constraints) in domain do
    mvar.assign assn
    process (·.push ·) constraints
    dfs (entropy / domain.size.toFloat) (pos + assn.args.size)
    process (fun _ => ·.pop) constraints
  mvar.assign none -- unassign mvar

/--
The `extend` function appends `none` values to `assignment` and empty arrays to
`constraints`.
-/
def extend (size : Nat) : CanonicalM Unit := do
  modify fun state => { state with
    assignments := state.assignments ++ replicate size none
    constraints := state.constraints ++ replicate size #[]
  }

/--
Now that our type checker can generate constraints on unassigned metavariables,
we implement term enumeration via iterative deepening depth-first search.
Instead of using tree height as our metric for depth, we use a custom fuel parameter,
called entropy, which increases each iteration. We also limit the size of the
generated terms, which we extend each iteration and run depth-first search.
-/
def iddfs [Monad m] [MonadLiftT CanonicalM m]
  (root : MVar) (cb step : m Unit) : m Unit := do
  let start ← capacity
  let mut entropy := 1000
  while true do
    extend 4
    dfs root cb step entropy start
    entropy := entropy * 3

/-
This concludes the implementation of inhabitation and unification. As a
final performance note, we recommend only adding blocks to linked lists when
the block is non-empty, which can be achieved with the following changes in
`Term.apply`, `Typ.inputs`, and `domain`:
-/
