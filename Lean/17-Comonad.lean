namespace DaoFP.Comonads

-- Comonad definition
class Comonad (W : Type → Type) [Functor W] where
  extract : {α : Type} → W α → α
  extend  : {α β : Type} → (W α → β) → W α → W β

-- Duplicate can be defined using extend
def duplicate {W : Type → Type} [Functor W] [Comonad W] {α : Type} (wa : W α) : W (W α) :=
  Comonad.extend id wa

-- Kleisli-like composition for Comonads (co-Kleisli)
def cokleisli {W : Type → Type} [Functor W] [Comonad W] {α β γ : Type}
  (g : W β → γ) (f : W α → β) (wa : W α) : γ :=
  g (Comonad.extend f wa)

infixr:5 " =<= " => cokleisli

-- Example: Environment/Coreader Comonad (Product Comonad)
-- Haskell: instance Comonad ((,) e) where
-- Note: Haskell's (,) e a is (e, a).
-- I'll use α × ε to match the extraction of the first element.
instance : Comonad (fun α => α × ε) where
  extract p := p.1
  extend f p := (f p, p.2)

-- Composition with Environment example
def composeWithEnv {α β γ ε : Type} (g : β × ε → γ) (f : α × ε → β) : α × ε → γ :=
  fun p => g (f p, p.2)

def idWithEnv {α ε : Type} : α × ε → α :=
  fun p => p.1

-- Exercise: duplicate' and extend'
def duplicate_prime {W : Type → Type} [Functor W] [Comonad W] {α : Type} (wa : W α) : W (W α) :=
  Comonad.extend id wa

def extend_prime {W : Type → Type} [Functor W] [Comonad W] {α β : Type}
  (k : W α → β) (wa : W α) : W β :=
  Functor.map k (duplicate wa)

end DaoFP.Comonads
