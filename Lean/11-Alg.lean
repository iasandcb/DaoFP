namespace DaoFP.Algebras

-- Simple expression type
inductive Expr where
  | Val  : Int → Expr
  | Plus : Expr → Expr → Expr

-- Pattern functor for Expr
inductive ExprF (χ : Type) where
  | ValF  : Int → ExprF χ
  | PlusF : χ → χ → ExprF χ

instance : Functor ExprF where
  map f
    | ExprF.ValF n    => ExprF.ValF n
    | ExprF.PlusF m n => ExprF.PlusF (f m) (f n)

-- Algebra definition
def Algebra (F : Type → Type) (C : Type) := F C → C

def eval : Algebra ExprF Int
  | ExprF.ValF n    => n
  | ExprF.PlusF m n => m + n

def pretty : Algebra ExprF String
  | ExprF.ValF n    => toString n
  | ExprF.PlusF s t => s ++ " + " ++ t

-- Exercise: Float expression pattern functor
inductive FloatF (χ : Type) where
  | Num : Float → FloatF χ
  | Op  : χ → χ → FloatF χ

instance : Functor FloatF where
  map f
    | FloatF.Num x  => FloatF.Num x
    | FloatF.Op x y => FloatF.Op (f x) (f y)

def addAlg : Algebra FloatF Float
  | FloatF.Num x  => Float.log x
  | FloatF.Op x y => x + y

def mulAlg : Algebra FloatF Float
  | FloatF.Num x  => x
  | FloatF.Op x y => x * y

-- Two paths through the algebra morphism diagram
def logMul (x : FloatF Float) : Float :=
  Float.log (mulAlg x)

def addLog (x : FloatF Float) : Float :=
  addAlg (Functor.map Float.log x)

def x_val : FloatF Float := FloatF.Op 2.3 13.1

end DaoFP.Algebras
