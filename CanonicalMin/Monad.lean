import CanonicalMin.Data

abbrev ConstraintM := ReaderT (Array (Option Assignment)) Option
structure Constraint where
  continuation: Array (Option Assignment) → Option (Array Constraint)
  stuck: MVar
  rigid: ConstraintM Bool

abbrev JudgmentM := StateT (Nat × Array Constraint) ConstraintM
abbrev Judgment := JudgmentM Unit

def fresh (ty : Option Typ := none) : JudgmentM Block :=
  modifyGet fun (n, l) =>
    (.vars n (ty >>= (·.inputs (.vars n none))), n.succ, l)

def ContT (m : Type → Type) (r a : Type) := (a → m r) → m r

instance : Monad (ContT m r) where
  pure a f := f a
  bind a f c := a (fun a' => f a' c)

instance [Monad m] : MonadLift m (ContT m r) where
  monadLift m k := do k (← m)

abbrev SearchM := ContT JudgmentM Unit

def constraint (t : SearchM T)
  (start : Nat) : ConstraintM (Array Constraint) := do
  return (← t (fun _ s => pure ((), s)) (start, #[])).2.2

partial def MVar.assignment (m : MVar)
  (rigid : ConstraintM Bool) : SearchM Assignment := do
  (← read)[m.id]!.getDM fun k (n, l) => return ((), n, l.push {
    continuation := constraint (do k (← m.assignment rigid)) n,
    stuck := m,
    rigid
  })

def judgment (j : SearchM Unit) : Judgment := j pure
