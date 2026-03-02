import CanonicalMin.Data

/--
Thus far, we have shown the implementation of a type checker for DTT. It
remains to be shown how to implement inhabitation and unification procedures.
In fact, the code we have shown is already capable of this, with an artful choice
of _monads_. A monad is a type transformer; if `m` is a monad and α is a type, then
`m` α is a type, representing the type of computations that return an element of
α. These computations may use different effects, depending on `m`. For instance,
`Option` is a monad where `Option` α is the type of computations returning an
element of α or throwing an exception.

We would like to extend our type checker to support unassigned
metavariables. If an unassigned metavariable is encountered during type checking, we
should produce a _constraint_ on that metavariable, representing the remaining
checks to be performed once the metavariable is given an assignment. This will
allow us to perform a backtracking search over the assignments to metavariables,
and defer type-checking constraints until they can be further evaluated.

We define ConstraintM α to be the type of computations that can read from
an array of assignments and return an element of α or throw an exception.
Each metavariable will have an id which serves as an index into this array. We
say the metavariable is unassigned if the value at this index is `none`. `ReaderT`
is a _monad transformer_, meaning it can extend an existing monad to add the
additional capability of accessing a read-only value. In this case, we extend the
`Option` monad, which allows us to throw an exception with `failure` when a
constraint has been violated.
-/
abbrev ConstraintM := ReaderT (Array (Option Assignment)) Option

/--
We now define a `Constraint` to be a continuation and the unassigned
metavariable that prevented further progress, called `stuck`. The continuation is a
computation which either throws an exception in the case that the `Constraint` has
been violated, or otherwise returns an array of `Constraint` with any remaining
work to be done.
-/
structure Constraint where
  continuation: Array (Option Assignment) → Option (Array Constraint)
  stuck: MVar
  rigid: ConstraintM Bool

/--
Next, we define the `JudgmentM` monad, and `Judgment` type for `Term.eq`, `WHNF.eq`,
and `check`:
-/
abbrev JudgmentM := StateT (Nat × Array Constraint) ConstraintM
/--
The second state variable of `JudgmentM` is an array of `Constraint`, which we will
accumulate as the judgment is evaluated. A `Judgment` is defined as a `JudgmentM`
`Unit`, as the only information returned from a `Judgment` is whether an
exception was thrown, the current value of the `Nat`, and the accumulated `Array`
`Constraint`.
-/
abbrev Judgment := JudgmentM Unit

/--
`JudgmentM` extends `ConstraintM` with two state variables. The first is a `Nat`,
which is used to create identifiers for fresh blocks of variables. When creating
fresh variables, we return a `Block.vars` with identifier equal to the state variable
`n`, and the state variable is incremented. When creating typed variables, we set
the `Types` of the variables to be the `inputs` of a given type `ty`.
-/
def fresh (ty : Option Typ := none) : JudgmentM Block :=
  modifyGet fun (n, l) =>
    (.vars n (ty >>= (·.inputs (.vars n none))), n.succ, l)

/--
We will now define the workhorse of the algorithm, the _continuation monad_.
Consider a function with return type β which calls a function with return type
α in the continuation monad. The caller will provide a callback function from
α to β to the callee, representing all the remaining code the caller intends to
perform with the return value from the callee. The caller then immediately cedes
control, leaving it up to the callee to decide how many times (if any) to invoke
the callback.

Observe how the following definition of `ContT m r a` accepts a callback
describing what should be done with the return type `a`. Rather than returning type
`a`, the computation returns the same result type `r` as the callback.
-/
def ContT (m : Type → Type) (r a : Type) := (a → m r) → m r

instance : Monad (ContT m r) where
  pure a f := f a
  bind a f c := a (fun a' => f a' c)

instance [Monad m] : MonadLift m (ContT m r) where
  monadLift m k := do k (← m)

/--
We define a specialized version of the continuation monad that extends `JudgmentM`
with fixed result type `Unit`:

Our intention is to use this continuation monad for `MVar.assignment`.
-/
abbrev SearchM := ContT JudgmentM Unit

/--
The constraint function converts a `SearchM T` into a `ConstraintM (Array`
`Constraint)` by passing an empty continuation, a designated `start` value for
the state `Nat`, and returning only the accumulated array of `Constraint`.
-/
def constraint (t : SearchM T)
  (start : Nat) : ConstraintM (Array Constraint) := do
  return (← t (fun _ s => pure ((), s)) (start, #[])).2.2

/--
Recall that the `MVar.assignment` function is supposed to access the
assignment of a metavariable. If the metavariable is assigned, we will directly invoke
the callback with the assignment, continuing normal execution. Otherwise, we
sequester the callback as a new `Constraint` in the state array, to be invoked
later. To access the assignments array, `ReaderT` provides the `read` function. In
the following code, `k` is the callback and `l` is the array of constraints.

With this implementation, if `Term.apply` is called on a term with an unassigned
mvar, the computation is paused and is stored in the form of a constraint on
that metavariable.
-/
partial def MVar.assignment (m : MVar)
  (rigid : ConstraintM Bool) : SearchM Assignment := do
  (← read)[m.id]!.getDM fun k (n, l) => return ((), n, l.push {
    continuation := constraint (do k (← m.assignment rigid)) n,
    stuck := m,
    rigid
  })

/--
Lastly, we define a conversion from `SearchM Unit` to `Judgment`, using a trivial
continuation:

The `judgment` function is essential to ensure that each iteration of the `for` loops
in `WHNF.eq` and `check` execute independently of one another (as opposed to each
iteration being the continuation of the previous), such that we can accumulate
constraints from subsequent iterations even when the previous iteration is stuck.
-/
def judgment (j : SearchM Unit) : Judgment := j pure
