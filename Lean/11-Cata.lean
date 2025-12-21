namespace DaoFP.Catamorphisms

-- Fixed point of a functor
inductive Fix (F : Type → Type) where
  | mk : F (Fix F) → Fix F

def unFix {F : Type → Type} : Fix F → F (Fix F)
  | Fix.mk x => x

def Algebra (F : Type → Type) (C : Type) := F C → C

-- Catamorphism: folding a structure using an algebra
def cata {F : Type → Type} [Functor F] {α : Type} (alg : Algebra F α) : Fix F → α
  | Fix.mk x => alg (Functor.map (cata alg) x)

-- ExprF example
inductive ExprF (χ : Type) where
  | ValF  : Int → ExprF χ
  | PlusF : χ → χ → ExprF χ

instance : Functor ExprF where
  map f
    | ExprF.ValF n    => ExprF.ValF n
    | ExprF.PlusF m n => ExprF.PlusF (f m) (f n)

def val (n : Int) : Fix ExprF := Fix.mk (ExprF.ValF n)
def plus (e1 e2 : Fix ExprF) : Fix ExprF := Fix.mk (ExprF.PlusF e1 e2)

def e9 : Fix ExprF := plus (plus (val 2) (val 3)) (val 4)

def eval : Algebra ExprF Int
  | ExprF.ValF n    => n
  | ExprF.PlusF m n => m + n

def pretty : Algebra ExprF String
  | ExprF.ValF n    => toString n
  | ExprF.PlusF s t => s ++ " + " ++ t

def test1 := cata eval e9
def test2 := cata pretty e9

-- Indented pretty printer
def indent (n : Nat) : String :=
  String.replicate (n * 2) ' '

def pretty_indent : Algebra ExprF (Nat → String)
  | ExprF.ValF n,    i => indent i ++ toString n
  | ExprF.PlusF f g, i => 
    f (i + 1) ++ "\n" ++
    indent i ++ "+" ++ "\n" ++
    g (i + 1)

def test3 := cata pretty_indent e9 0

-- List pattern functor
inductive ListF (α χ : Type) where
  | NilF  : ListF α χ
  | ConsF : α → χ → ListF α χ

instance : Functor (ListF α) where
  map f
    | ListF.NilF      => ListF.NilF
    | ListF.ConsF a x => ListF.ConsF a (f x)

abbrev MyList (α : Type) := Fix (ListF α)

def recList {α γ : Type} (init : γ) (step : α × γ → γ) : MyList α → γ :=
  cata (fun 
    | ListF.NilF      => init
    | ListF.ConsF a c => step (a, c))

-- Reverse using catamorphism
def revAlg {α : Type} : Algebra (ListF α) (List α → List α)
  | ListF.NilF      => id
  | ListF.ConsF a f => fun as => f (a :: as)

def reverse_fix {α : Type} (as : MyList α) : List α :=
  (cata revAlg as) []

end DaoFP.Catamorphisms
