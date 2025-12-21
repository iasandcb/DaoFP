namespace DaoFP.Coalgebras

abbrev Algebra (F : Type → Type) (C : Type) := F C → C
abbrev Coalgebra (F : Type → Type) (A : Type) := A → F A

-- Tree pattern functor
inductive TreeF (χ : Type) where
  | LeafF : TreeF χ
  | NodeF : Int → χ → χ → TreeF χ

instance : Functor TreeF where
  map f
    | TreeF.LeafF        => TreeF.LeafF
    | TreeF.NodeF n l r  => TreeF.NodeF n (f l) (f r)

-- Coalgebra for Quicksort: partition a list
def split : Coalgebra TreeF (List Int)
  | []      => TreeF.LeafF
  | n :: ns => 
    let (left, right) := ns.partition (· ≤ n)
    TreeF.NodeF n left right

-- Fixed point of a functor (Inductive for finite trees)
inductive Fix (F : Type → Type) where
  | mk : F (Fix F) → Fix F

def unFix {F : Type → Type} : Fix F → F (Fix F)
  | Fix.mk x => x

-- Anamorphism: unfolding a structure from a seed
partial def ana {F : Type → Type} [Functor F] {α : Type} (coa : Coalgebra F α) (a : α) : Fix F :=
  Fix.mk (Functor.map (ana coa) (coa a))

-- Catamorphism: folding a structure
def cata {F : Type → Type} [Functor F] {α : Type} (alg : Algebra F α) : Fix F → α
  | Fix.mk x => alg (Functor.map (cata alg) x)

-- Algebra for Quicksort: join sorted lists
def toList : Algebra TreeF (List Int)
  | TreeF.LeafF         => []
  | TreeF.NodeF n ns ms => ns ++ [n] ++ ms

-- Quicksort as cata . ana
partial def qsort (is : List Int) : List Int :=
  cata toList (ana split is)

-- Hylomorphism: folding after unfolding without intermediate structure
partial def hylo {F : Type → Type} [Functor F] {α β : Type} 
  (alg : Algebra F β) (coa : Coalgebra F α) (a : α) : β :=
  alg (Functor.map (hylo alg coa) (coa a))

def qsort_hylo (is : List Int) : List Int :=
  hylo toList split is

-- Infinite structures: Stream
inductive StreamF (α χ : Type) where
  | mk : α → χ → StreamF α χ

instance : Functor (StreamF α) where
  map f (StreamF.mk a x) := StreamF.mk a (f x)

-- Nu: Final Coalgebra represented as an existential (using a structure)
structure Nu (F : Type → Type) where
  State : Type
  unf   : Coalgebra F State
  curr  : State

def anaNu {F : Type → Type} {α : Type} (coa : Coalgebra F α) (a : α) : Nu F :=
  { State := α, unf := coa, curr := a }

def head {α : Type} (s : Nu (StreamF α)) : α :=
  match s.unf s.curr with
  | StreamF.mk a _ => a

def tail {α : Type} (s : Nu (StreamF α)) : Nu (StreamF α) :=
  match s.unf s.curr with
  | StreamF.mk _ s' => { s with curr := s' }

-- allNats as an infinite stream
def nats_coa : Coalgebra (StreamF Int) Int
  | n => StreamF.mk n (n + 1)

def allNats : Nu (StreamF Int) := anaNu nats_coa 0

end DaoFP.Coalgebras
