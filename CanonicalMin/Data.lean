mutual
  structure MVar where
    id: Nat
    lctx: List TypeMVar
    preferredNames : Array String
  deriving Inhabited

  structure TypeMVar where
    inputs: Array TypeMVar
    output: MVar
    preferredNames: Array String
  deriving Inhabited
end

structure Assignment where
  debruijn: Nat
  index: Nat
  args: Array MVar

mutual
  inductive Block where
  | vars: Nat → Option Types → Block
  | terms: Terms → Block
  deriving Inhabited

  structure Term where
    mvar: MVar
    es: List Block
  deriving Inhabited

  structure Terms where
    mvars: Array MVar
    es: List Block

  structure Typ where
    mvar: TypeMVar
    es: List Block
  deriving Inhabited

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

structure Var where
  blockId: Nat
  index: Nat
deriving BEq

structure WHNF where
  head: Var
  type: Option Typ
  args: Terms

def Typ.output (ty : Typ) : Term :=
  { mvar := ty.mvar.output, es := ty.es }

def Typ.inputs (ty : Typ) (args : Block) : Types :=
  { mvars := ty.mvar.inputs, es := if ty.mvar.inputs.isEmpty then ty.es else args :: ty.es }
