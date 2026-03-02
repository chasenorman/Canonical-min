mutual
  /--
  To understand `domain`, we need a proper definition of `MVar`. In addition to the
  `id`, we store the preferred names for the bindings of this lambda expression (as
  with `TypeMVar`), and a linked list of `TypeMVar` called `lctx`. The `lctx` will tell us
  the valid `debruijn` and `index` pairs for the head of this `MVar` by collecting each
  `TypeMVar` whose inputs were added to the local context.
  -/
  structure MVar where
    id: Nat
    lctx: List TypeMVar
    preferredNames : Array String
  deriving Inhabited

  /--
  The distinction between `TypeMVar` and `MVar` is that `TypeMVar` also contains an
  array of `TypeMVar` for the input types, as well as an array of preferred names for
  the bindings (which are exclusively used for printing, and are never compared).

  Note that the output is not itself a dependent function type, as we expect
  functions to be uncurried. As such it is represented as a metavariable expression.
  -/
  structure TypeMVar where
    inputs: Array TypeMVar
    output: MVar
    preferredNames: Array String
  deriving Inhabited
end

/--
Our representation of lambda expressions decomposes them into three parts: a
sequence of _bindings_, a _head_, and a spine of _arguments_. Unlike WHNF terms,
which must have a variable head symbol, we allow the head of a term to be a term
itself for representing reducible expressions. Observe how this decomposition
behaves on the following terms:

  λ f x ↦ f x x        _  (λ x ↦ x) (λ y ↦ y)       _  a  _
    ┗━┛  ┗━┛┗━┛       ┗━┛ ┗━━━━━━━┛ ┗━━━━━━━┛      ┗━┛┗━┛┗━┛

This decomposition is distinct from the standard inductive definition of terms
(with constructors for variables, applications, and lambda bindings) in that it has
only a single constructor, improving uniformity. Furthermore, it keeps bindings
and arguments in contiguous blocks with efficient random access.

We will encode terms using exclusively _de Bruijn indices_. We store an
index for the head and references to the arguments in a structure called the
_assignment_. The index is composed of two numbers, `debruijn` and `index`, which
will be explained shortly.

We intend for terms to be mutable, so we use references to assignments, which
we call _metavariables_. Below is the definition of Assignment.

Notably, the assignment does not store information about the bindings. We do
not need to store the names of the bindings, since we are using de Bruijn indices
(a similar trick is used for the locally nameless representation), and we do
not need to store the number of bindings, since all terms have exactly one block
of bindings.
-/
structure Assignment where
  debruijn: Nat
  index: Nat
  args: Array MVar

mutual
  /--
  To associate an index with the head, we maintain a bank of all head variables
  and head terms in the local context, called the _explicit substitution_ (ES). An ES
  is a linked list of blocks, where each is either a block of variables (with a block
  identifier, and optionally with types) or a block of terms.
  -/
  inductive Block where
  | vars: Nat → Option Types → Block
  | terms: Terms → Block
  deriving Inhabited

  /--
  Terms and variables will always be added to the ES directly as blocks,
  allowing for efficient and uniform behavior regardless of block size. The `debruijn`
  field of `MVar` is the position of a block in the linked list, and the `index` field is
  the position of the head in this block. Since blocks can be added to the ES, the
  meaning of `debruijn` is dependent on its depth in the term. The ES is a linked
  list because it must be a fully persistent data structure. Our use of blocks will
  decrease the length of the linked list, improving access times.

  A term is defined as a metavariable, and an ES.

  It is essential that we separate the ES from the de Bruijn indices, since
  metavariables will have indices that are mutable, and may even be unassigned.
  To properly resolve the head after changes in index, and to perform β-reduction
  on terms with unassigned indices, we require the bank of head expressions.
  -/
  structure Term where
    mvar: MVar
    es: List Block
  deriving Inhabited

  /--
  The type `Terms` is an efficient way to represent an array of terms that all
  share an ES. The term at index _i_ is defined as the metavariable at index _i_ paired
  with the ES:
  -/
  structure Terms where
    mvars: Array MVar
    es: List Block

  /--
  Just like `Term`, `Typ` consists of a de-Bruijn-indexed type-metavariable and an ES.
  -/
  structure Typ where
    mvar: TypeMVar
    es: List Block
  deriving Inhabited

  /--
  `Types` is defined like `Terms`, with an array of type-metavariables that share an
  ES. The type at index _i_ is defined as the type-metavariable at index _i_ paired
  with the ES.
  -/
  structure Types where
    mvars: Array TypeMVar
    es: List Block
end

def Terms.size (ts : Terms) : Nat := ts.mvars.size

instance : GetElem Terms Nat Term (fun ts i => i < ts.size) where
  getElem ts i _ := { mvar := ts.mvars[i], es := ts.es }

instance : Coe Terms Block where coe t := .terms t

def Types.size (ts : Types) : Nat := ts.mvars.size

instance : GetElem Types Nat Typ (fun ts i => i < ts.size) where
  getElem ts i _ := { mvar := ts.mvars[i], es := ts.es }

/--
A variable is uniquely identified by the identifier of the block it
comes from, and the index into that block.
-/
structure Var where
  blockId: Nat
  index: Nat
deriving BEq

/--
A WHNF term consists of a head variable, an optional type for that head
variable, and arguments which are terms.
-/
structure WHNF where
  head: Var
  type: Option Typ
  args: Terms

/--
The output of a type is the `output` `MVar` paired with the explicit substitution.
This is a lambda term, whose bindings must be instantiated using `Term.apply`.

As an example of `Typ.output`, here is the behavior on an example type:

                                       output
          (T : Type) → (t : T) → T     =====>     λ T t ↦ T
-/
def Typ.output (ty : Typ) : Term :=
  { mvar := ty.mvar.output, es := ty.es }

/--
Accessing the input types of a given type requires a block of arguments, as
later inputs may depend on earlier inputs. The inputs are obtained by pairing the
inputs array of `TypeMVar` with the explicit substitution, extended to instantiate
the bindings at de Bruijn index 0 with the block of arguments.

We do not structurally enforce telescoping, i.e. that the input at index _i_ should
only refer to the elements of `args` at indices _j_ < _i_. Instead, we use the same
explicit substitution for all the inputs, which includes all `args`.
-/
def Typ.inputs (ty : Typ) (args : Block) : Types :=
  { mvars := ty.mvar.inputs, es := if ty.mvar.inputs.isEmpty then ty.es else args :: ty.es }
