import CanonicalMin.Monad

partial def Term.apply (t : Term) (args : Block)
  (rigid : ConstraintM Bool := pure false) : SearchM WHNF := do
  let es := if t.mvar.preferredNames.isEmpty then t.es else args :: t.es
  let assn ← t.mvar.assignment rigid
  let args : Terms := { mvars := assn.args, es }
  match es[assn.debruijn]! with
  | .vars blockId types => pure {
      head := { blockId, index := assn.index },
      type := types >>= (·[assn.index]!), args
    }
  | .terms ts => ts[assn.index]!.apply args rigid

def rigid : ConstraintM Bool := return true
def other (t : Term) (args : Block) : ConstraintM Bool :=
  return (← constraint (do t.apply args rigid) 0).isEmpty

mutual
  partial def Term.eq (t1 t2 : Term) : Judgment := judgment do
    let vars ← fresh
    (← t1.apply vars (other t2 vars)).eq (← t2.apply vars rigid)

  partial def WHNF.eq (w1 w2 : WHNF) : Judgment := do
    if w1.head == w2.head then
      for i in [0:w1.args.size] do
        w1.args[i]!.eq w2.args[i]!
    else failure -- throw an exception
end

partial def check (t : Term) (ty : Typ) : Judgment := judgment do
  let vars ← fresh ty
  let ⟨_head, headType, args⟩ ← t.apply vars
  let inputs := headType.get!.inputs args
  for i in [0:args.size] do
    check args[i]! inputs[i]!
  (← headType.get!.output.apply args (other ty.output vars)).eq
    (← ty.output.apply vars rigid)
