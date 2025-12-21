namespace DaoFP.Nats

inductive Nat where
  | Z : Nat
  | S : Nat → Nat

def zero  : Nat := Nat.Z
def one   : Nat := Nat.S zero
def two   : Nat := Nat.S one
def three : Nat := Nat.S two

-- Elimination rule
def rec {α : Type} (init : α) (step : α → α) : Nat → α
  | Nat.Z   => init
  | Nat.S m => step (rec init step m)

def plus0 : Nat → Nat → Nat
  | Nat.Z, n   => n
  | Nat.S n, m => Nat.S (plus0 n m)

def plus (n : Nat) : Nat → Nat :=
  rec n Nat.S

def plus' (n m : Nat) : Nat :=
  match m with
  | Nat.Z   => n
  | Nat.S k => Nat.S (plus' k n)

-- Exercises

def plus'' (n : Nat) : Nat → Nat :=
  rec (fun x => x) (fun f => Nat.S ∘ f) n

def toInt (n : Nat) : Int :=
  rec 0 (fun m => m + 1) n

end DaoFP.Nats
