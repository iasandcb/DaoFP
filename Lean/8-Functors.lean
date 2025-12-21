namespace DaoFP.Functors

-- Functor class
class Functor (F : Type → Type) where
  fmap {α β : Type} : (α → β) → (F α → F β)

-- In Lean, the standard Functor class uses `map`.
-- Here we define our own to match the tutorial style.

instance : Functor Option where
  fmap g
    | none   => none
    | some a => some (g a)

structure WithInt (α : Type) where
  val : α
  int : Int

instance : Functor WithInt where
  fmap f w := { val := f w.val, int := w.int }

structure Identity (α : Type) where
  val : α

instance : Functor Identity where
  fmap f i := { val := f i.val }

structure Constant (γ α : Type) where
  val : γ

instance : Functor (Constant γ) where
  fmap _ c := { val := c.val }

-- Bifunctor
class Bifunctor (F : Type → Type → Type) where
  bimap {α α' β β' : Type} : (α → α') → (β → β') → (F α β → F α' β')

instance : Bifunctor Prod where
  bimap g h p := (g p.1, h p.2)

inductive MoreThanA (α β : Type) where
  | More : α → Option β → MoreThanA α β

instance : Bifunctor MoreThanA where
  bimap g h
    | MoreThanA.More a none     => MoreThanA.More (g a) none
    | MoreThanA.More a (some b) => MoreThanA.More (g a) (some (h b))

-- Contravariant
class Contravariant (F : Type → Type) where
  contramap {α β : Type} : (β → α) → (F α → F β)

structure Predicate (α : Type) where
  pred : α → Bool

instance : Contravariant Predicate where
  contramap f p := { pred := p.pred ∘ f }

structure Tester (α : Type) where
  test : (α → Bool) → Bool

instance : Functor Tester where
  fmap f t := { test := fun h => t.test (h ∘ f) }

-- Profunctor
class Profunctor (F : Type → Type → Type) where
  dimap {α' α β β' : Type} : (α' → α) → (β → β') → (F α β → F α' β')

-- Function type as a Profunctor
instance : Profunctor (fun α β => α → β) where
  dimap f g h := g ∘ h ∘ f

-- Composition of functors
structure Compose (G F : Type → Type) (α : Type) where
  val : G (F α)

instance [Functor G] [Functor F] : Functor (Compose G F) where
  fmap h c := { val := Functor.fmap (Functor.fmap h) c.val }

instance [Functor G] [Contravariant F] : Contravariant (Compose G F) where
  contramap h c := { val := Functor.fmap (Contravariant.contramap h) c.val }

end DaoFP.Functors
