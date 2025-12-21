namespace DaoFP.Universals

-- curry / uncurry review
def curry' {α β γ : Type} (f : α × β → γ) : α → β → γ :=
  fun a b => f (a, b)

def uncurry' {α β γ : Type} (f : α → β → γ) : α × β → γ :=
  fun (a, b) => f a b

def apply' {α β : Type} : (α → β) × α → β :=
  uncurry' (fun f x => f x)

-- Functors for universal properties
structure LeftFunctor (α β χ : Type) where
  val : (χ × α) → β

structure RightFunctor (α β χ : Type) where
  val : χ → (α → β)

class Contravariant (F : Type → Type) where
  contramap {α β : Type} : (β → α) → (F α → F β)

class Bifunctor (F : Type → Type → Type) where
  bimap {α α' β β' : Type} : (α → α') → (β → β') → (F α β → F α' β')

instance : Bifunctor Prod where
  bimap g h p := (g p.1, h p.2)

instance : Contravariant (LeftFunctor α β) where
  contramap g f := { val := f.val ∘ (bimap g id) }

-- Natural transformations representing the isomorphism
def alpha {α β χ : Type} (f : LeftFunctor α β χ) : RightFunctor α β χ :=
  { val := curry' f.val }

def alpha_1 {α β χ : Type} (h : RightFunctor α β χ) : LeftFunctor α β χ :=
  { val := uncurry' h.val }

-- Examples
def q (n : Int) : Bool := n % 2 == 0

def h_fun {α : Type} (q_func : Int → α) (b : Bool) : α :=
  if b then q_func 0 else q_func 1

-- Exercises
-- Haskell testBit x 0 checks the least significant bit.
def q_prime (x : Int) : Bool := x % 2 != 0

def test1 := List.map (fun n => h_fun q_prime (q n)) [-1, 0, 1, 2, 3]
def test2 := List.map q_prime [-1, 0, 1, 2, 3]

-- Equalizer of id and reverse (centers of strings)
def q_double_prime (s : String) : Option Char :=
  let len := s.length
  if len % 2 == 0 then
    none
  else
    let chars := s.toList
    chars.get? (len / 2)

end DaoFP.Universals
