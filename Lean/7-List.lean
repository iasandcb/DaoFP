namespace DaoFP.Lists

inductive List' (α : Type) where
  | Nil  : List' α
  | Cons : α × List' α → List' α

-- Elimination rule
def recList {α γ : Type} (init : γ) (step : α × γ → γ) : List' α → γ
  | List'.Nil          => init
  | List'.Cons (a, as) => step (a, recList init step as)

def foldr' {α γ : Type} (step : α → γ → γ) (init : γ) : List α → γ
  | []      => init
  | a :: as => step a (foldr' step init as)

-- Minimal Nat definition within this file to match the Haskell source
inductive Nat where
  | Z : Nat
  | S : Nat → Nat

def plus : Nat → Nat → Nat
  | Nat.Z, n   => n
  | Nat.S n, m => Nat.S (plus n m)

def sum : List Nat → Nat
  | []      => Nat.Z
  | a :: as => plus a (sum as)

-- Functoriality
def mapList {α β : Type} (f : α → β) : List' α → List' β :=
  recList List'.Nil (fun (a, bs) => List'.Cons (f a, bs))

def map' {α β : Type} (f : α → β) : List α → List β
  | []      => []
  | a :: as => f a :: map' f as

def badMap {α β : Type} (f : α → β) : List α → List β
  | []      => []
  | _ :: as => badMap f as

-- Exercises
def h {α : Type} : List α → Option α
  | []      => Option.none
  | a :: _  => Option.some a

def h' {α : Type} : List α → Option α
  | []      => Option.none
  | _ :: as => h as

def second {α : Type} : List α → Option α
  | []      => Option.none
  | _ :: as => h as

def third {α : Type} : List α → Option α
  | []      => Option.none
  | _ :: as => second as

end DaoFP.Lists
