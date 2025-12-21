namespace DaoFP.ProductTypes

-- Triple projection
def thrd {α β γ : Type} : (α × β × γ) → γ
  | (_, _, c) => c

-- Custom product type using structure
structure Product (α β : Type) where
  fst' : α
  snd' : β

def ic : Product Int Char := { fst' := 10, snd' := 'A' }

-- Swapping using projections
def swap' {α β : Type} (p : α × β) : β × α :=
  (p.2, p.1)

-- Swapping using pattern matching
def swap {α β : Type} : α × β → β × α
  | (x, y) => (y, x)

-- Associativity of products
def assoc {α β γ : Type} : ((α × β) × γ) → (α × (β × γ))
  | ((a, b), c) => (a, (b, c))

-- Right unit of product
def runit {α : Type} : (α × Unit) → α
  | (a, ()) => a

-- Custom Monoid class to match the tutorial style
-- In Lean, classes are often defined over Types.
class MyMonoid (m : Type) where
  mappend : m × m → m
  mempty  : Unit → m

-- Exercise: Converting between Either/Product and Maybe/Product
-- Using Lean's standard Sum (Either) and Option (Maybe)
def maybeAB {α β : Type} : Sum β (α × β) → (Option α × β)
  | Sum.inl b      => (Option.none, b)
  | Sum.inr (a, b) => (Option.some a, b)

end DaoFP.ProductTypes
