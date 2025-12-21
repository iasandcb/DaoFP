namespace DaoFP.InitialAlgebras

-- Fixed point of a functor
inductive Fix (F : Type → Type) where
  | mk : F (Fix F) → Fix F

def unFix {F : Type → Type} : Fix F → F (Fix F)
  | Fix.mk x => x

def Algebra (F : Type → Type) (A : Type) := F A → A

-- Catamorphism for Fix
def cata {F : Type → Type} [Functor F] {α : Type} (alg : Algebra F α) : Fix F → α
  | Fix.mk x => alg (Functor.map (cata alg) x)

-- Church-encoded fixed point (Mu)
structure Mu (F : Type → Type) where
  val : ∀ {α : Type}, Algebra F α → α

-- Catamorphism for Mu
def cataMu {F : Type → Type} {α : Type} (alg : Algebra F α) (m : Mu F) : α :=
  m.val alg

-- List pattern functor
inductive ListF (α χ : Type) where
  | NilF  : ListF α χ
  | ConsF : α → χ → ListF α χ

instance : Functor (ListF α) where
  map f
    | ListF.NilF      => ListF.NilF
    | ListF.ConsF a x => ListF.ConsF a (f x)

-- Converting standard List to Mu (ListF)
def fromList {α : Type} (as : List α) : Mu (ListF α) where
  val alg :=
    let rec go : List α → _
      | []      => alg ListF.NilF
      | n :: ns => alg (ListF.ConsF n (go ns))
    go as

-- Exercise: Summing a list using catamorphism
def sumAlg : Algebra (ListF Int) Int
  | ListF.NilF      => 0
  | ListF.ConsF n x => n + x

def sumList (is : List Int) : Int :=
  cataMu sumAlg (fromList is)

end DaoFP.InitialAlgebras
