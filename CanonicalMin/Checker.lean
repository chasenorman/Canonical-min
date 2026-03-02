import CanonicalMin.Monad

/--
Now, we put everything together to define `apply`. To apply a term `t` to a
block of arguments `args`, we begin by extending the ES of `t` to contain `args`
at de Bruijn index 0, substituting for the bindings of `t`. Next, we access the
assignment `assn` of `t.mvar` and index into the ES at `assn.debruijn`. If the
block at this position consists of variables, we have reached WHNF. The head
symbol is the variable from that block at index `assn.index`, and the arguments
are `assn.args` under the extended ES. If the variables are typed, the type of
the head symbol is the type at index `assn.index`.

Otherwise, if the block consists of terms, we must β-reduce. We access the
term at index `assn.index` and apply it to assn.args under the extended ES.
Note that apply does not create new metavariables or assignments.
-/
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

/--
To determine whether m has a rigid constraint, we invoke the `rigid` predicate
for each of its stuck constraints. The `rigid` predicate was passed into the `apply`
function by the type checker, and was added to the constraint by `assignment`.
To facilitate this, we have the following templates for the predicate:
-/
def rigid : ConstraintM Bool := return true
/--
Here, `rigid` indicates that the constraint is unconditionally rigid, and `other`
indicates that the constraint is rigid when `t` applied with `args` does not get
stuck on a metavariable.
-/
def other (t : Term) (args : Block) : ConstraintM Bool :=
  return (← constraint (do t.apply args rigid) 0).isEmpty

mutual
  /--
  A type theory defines a language, where the set of syntactically valid expressions
  are called _terms_. Typically, this set consists of expressions from the lambda
  calculus, such as (λ x y ↦ y). We refer to x and y as the _bindings_.

  Suppose you wish to determine whether two lambda terms are equivalent,
  known as judgmental or definitional equality. Two terms with distinct bindings
  may still considered equal if they have the same behavior, such as (λ x ↦ f x)
  and (λ y ↦ f y). To account for this α-equivalence, we generate fresh variables
  and apply both terms to them.

  When we call the function `Term.apply`, to perform
  these applications, the resulting expressions will be β-reduced until they are
  in _weak head normal form_ (WHNF), to account for β-equivalence. A term in
  WHNF is a function symbol (called the _head symbol_) applied to a sequence of
  terms (called _arguments_). We say the original lambda terms are equivalent if
  and only if these WHNF terms are equivalent.

  We implement this procedure as a function `Term.eq` in Lean. In the following
  code, the left arrow (`←`) indicates that a function call is monadic, which can be
  ignored for now. The function is labeled `partial` in Lean since we do not provide proof of
  termination. We assume that `t1` and `t2` have the same arity, and we will see later how
  our representation ensures that `vars` consists of the correct number of variables.
  -/
  partial def Term.eq (t1 t2 : Term) : Judgment := judgment do
    let vars ← fresh
    (← t1.apply vars (other t2 vars)).eq (← t2.apply vars rigid)

  /--
  To determine whether two WHNF expressions are equal, we compare their
  head symbol. If these are not equal, we will throw an exception. Otherwise, we
  iterate through the arguments of this head symbol in both expressions, and
  compare them with `Term.eq`. If the head symbol and arguments are all determined
  to be equal, no exception is thrown.

  It will be essential that we use exceptions, as this prevents unnecessary calls
  to `apply` after two terms have already been determined not to be equal. We
  assume that `w1` and `w2` have exactly as many arguments as the arity of their
  head symbols, and therefore have the same number of arguments when they
  have the same head symbol. The exclamation point (`!`) is necessary in Lean
  since we do not provide proof that the array index is in bounds.
  -/
  partial def WHNF.eq (w1 w2 : WHNF) : Judgment := do
    if w1.head == w2.head then
      for i in [0:w1.args.size] do
        w1.args[i]!.eq w2.args[i]!
    else failure -- throw an exception
end

/--
Type theories also define a set of _types_, and a set of rules for determining whether
a term is a member of a given type. In DTT, the types of lambda expressions
are given by _dependent function types_, for example:

                        (T : Type) → (t : T) → T

We call the first T and t the _bindings_, Type and the second T the _inputs_, and
the last T the _output_. This type represents all functions with this signature of
input types and output type.

To determine whether a term `t` is a member of a type `ty`, we again account
for α-equivalence by creating fresh variables. The types of these variables will
be the inputs of `ty`. When we apply `t` to these variables and reduce to WHNF,
we obtain the head symbol, its type `headType`, and the arguments.

Our first obligation is to ensure that the arguments have the types the head
symbol expects. To do this, we extract the inputs of `headType`. Necessarily, this
operation will require the arguments, as `headType` is a dependent function type.
Then, we recursively type check each argument against the corresponding input.

Our final obligation is to ensure that the output of `headType` matches the
output of ty. As we are working with dependent types, the output of `headType`
may depend on the arguments, and the output of ty may depend on the fresh
variables. We will observe in the following section that the output of a type is a
term, so we use `Term.apply` to substitute the bindings with these expressions.
We then check that these are equal with `WHNF.eq`, completing the type checker.
We assume that `t` and `ty` have the same arity.
-/
partial def check (t : Term) (ty : Typ) : Judgment := judgment do
  let vars ← fresh ty
  let ⟨_head, headType, args⟩ ← t.apply vars
  let inputs := headType.get!.inputs args
  for i in [0:args.size] do
    check args[i]! inputs[i]!
  (← headType.get!.output.apply args (other ty.output vars)).eq
    (← ty.output.apply vars rigid)
