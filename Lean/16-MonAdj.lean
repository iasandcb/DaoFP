namespace DaoFP.MonadsAdjunctions

-- Functors for string diagram examples
def F (α : Type) := Int → α
def G (α : Type) := List α
def H (α : Type) := Option α

def alpha {α : Type} (f : F α) : G α :=
  [0, 1, 2].map f

def beta {α : Type} : G α → H α
  | []      => none
  | a :: _  => some a

def beta_alpha {α : Type} (f : F α) : H α :=
  beta (alpha f)

-- Adjunction definition
class Adjunction (L R : Type → Type) [Functor L] [Functor R] where
  unit   : {α : Type} → α → R (L α)
  counit : {α : Type} → L (R α) → α

-- Triangle identities
def triangle {L R : Type → Type} [Functor L] [Functor R] [Adjunction L R] {α : Type} : R α → R α :=
  Functor.map Adjunction.counit ∘ Adjunction.unit

def triangle_prime {L R : Type → Type} [Functor L] [Functor R] [Adjunction L R] {α : Type} : L α → L α :=
  Adjunction.counit ∘ Functor.map Adjunction.unit

-- Monad associated with an adjunction: T = R ∘ L
def unit_T {L R : Type → Type} [Functor L] [Functor R] [Adjunction L R] {α : Type} (a : α) : R (L α) :=
  Adjunction.unit a

def mu_T {L R : Type → Type} [Functor L] [Functor R] [Adjunction L R] {α : Type} (rrlra : R (L (R (L α)))) : R (L α) :=
  Functor.map (fun lra => (Adjunction.counit lra : L α)) rrlra

end DaoFP.MonadsAdjunctions
