namespace DaoFP.Monads

-- Different styles of Monad definitions

-- 1. Kleisli composition style
class MonadK (M : Type → Type) [Functor M] where
  kleisli : {α β γ : Type} → (β → M γ) → (α → M β) → (α → M γ)
  pureK   : {α : Type} → α → M α

infixr:5 " <=< " => MonadK.kleisli

instance : MonadK Option where
  pureK := some
  kleisli g f a := 
    match f a with
    | none   => none
    | some b => g b

-- 2. Join style
class MonadJ (M : Type → Type) [Functor M] where
  join   : {α : Type} → M (M α) → M α
  pureJ : {α : Type} → α → M α

-- 3. Bind style (Standard)
class Monad' (M : Type → Type) [Functor M] where
  bind : {α β : Type} → M α → (α → M β) → M β
  pure : {α : Type} → α → M α

infixl:1 " >>= " => Monad'.bind

-- Relationships between definitions
def join_from_K {M : Type → Type} [Functor M] [MonadK M] {α : Type} (mma : M (M α)) : M α :=
  (id <=< id) mma

def bind_from_K {M : Type → Type} [Functor M] [MonadK M] {α β : Type} 
  (ma : M α) (k : α → M β) : M β :=
  (k <=< id) ma

def join_from_B {M : Type → Type} [Functor M] [Monad' M] {α : Type} (mma : M (M α)) : M α :=
  mma >>= id

def liftM {M : Type → Type} [Functor M] [Monad' M] {α β : Type} (f : α → β) (ma : M α) : M β :=
  ma >>= (fun a => Monad'.pure (f a))

-- Monoidal Functors can be derived from Monads
class Monoidal (F : Type → Type) where
  unit    : F Unit
  combine : {α β : Type} → F α → F β → F (α × β)

instance [Functor M] [Monad' M] : Monoidal M where
  unit := Monad'.pure ()
  combine ma mb := 
    ma >>= fun a => 
    mb >>= fun b => 
    Monad'.pure (a, b)

-- Applicative 'ap' (splat) derived from Monad
def ap {M : Type → Type} [Functor M] [Monad' M] {α β : Type} (mf : M (α → β)) (ma : M α) : M β :=
  mf >>= fun f => 
  ma >>= fun a => 
  Monad'.pure (f a)

end DaoFP.Monads
