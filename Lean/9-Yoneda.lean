namespace DaoFP.Yoneda

-- Functor and Contravariant classes (self-contained as in previous files)
class Functor (F : Type → Type) where
  fmap {α β : Type} : (α → β) → (F α → F β)

class Contravariant (F : Type → Type) where
  contramap {α β : Type} : (β → α) → (F α → F β)

-- Yoneda Lemma
def yoneda {F : Type → Type} [Functor F] {α : Type}
  (g : ∀ {χ : Type}, (α → χ) → F χ) : F α :=
  g id

-- The inverse to yoneda
def yoneda_1 {F : Type → Type} [Functor F] {α : Type}
  (y : F α) : ∀ {χ : Type}, (α → χ) → F χ :=
  fun h => Functor.fmap h y

-- Coyoneda Lemma (for contravariant functors)
def coyoneda {F : Type → Type} [Contravariant F] {α : Type}
  (g : ∀ {χ : Type}, (χ → α) → F χ) : F α :=
  g id

-- The inverse to coyoneda
def coyoneda_1 {F : Type → Type} [Contravariant F] {α : Type}
  (y : F α) : ∀ {χ : Type}, (χ → α) → F χ :=
  fun h => Contravariant.contramap h y

-- Yoneda for the reader functor (F X = Z -> X)
def toNatural {X Y : Type} (f : X → Y) : ∀ {Z : Type}, (Z → X) → (Z → Y) :=
  fun h => f ∘ h

def fromNatural {X Y : Type} (alpha : ∀ {Z : Type}, (Z → X) → (Z → Y)) : X → Y :=
  alpha id

end DaoFP.Yoneda
