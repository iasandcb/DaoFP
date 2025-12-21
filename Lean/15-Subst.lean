namespace DaoFP.Substitution

-- Expression type parameterized by variable type
inductive Expr (α : Type) where
  | Val  : Int → Expr α
  | Var  : α → Expr α
  | Plus : Expr α → Expr α → Expr α
  deriving Repr

instance : Functor Expr where
  map f
    | Expr.Val n      => Expr.Val n
    | Expr.Var x      => Expr.Var (f x)
    | Expr.Plus e1 e2 => Expr.Plus (Functor.map f e1) (Functor.map f e2)

instance : Monad Expr where
  pure := Expr.Var
  bind m k := match m with
    | Expr.Val n      => Expr.Val n
    | Expr.Var x      => k x
    | Expr.Plus e1 e2 => Expr.Plus (Monad.bind e1 k) (Monad.bind e2 k)

-- Example substitution
def ex : Expr Char :=
  Expr.Plus (Expr.Plus (Expr.Val 2) (Expr.Var 'a')) (Expr.Var 'b')

def sub : Char → Expr String
  | 'a' => Expr.Plus (Expr.Var "x1") (Expr.Val 2)
  | 'b' => Expr.Var "x2"
  | _   => Expr.Var "unknown"

def ex_substituted : Expr String :=
  ex >>= sub

end DaoFP.Substitution
