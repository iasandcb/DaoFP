namespace DaoFP.FunctionTypes

-- Curry function
-- Haskell: curry :: ((c, a) -> b) -> (c -> (a -> b))
def curry {α β γ : Type} (f : (α × β) → γ) : α → β → γ :=
  fun a b => f (a, b)

-- Uncurry function
-- Haskell: uncurry :: (c -> (a -> b)) -> ((c, a) -> b)
def uncurry {α β γ : Type} (f : α → β → γ) : (α × β) → γ :=
  fun (a, b) => f a b

-- Apply function
-- Haskell: apply :: (a -> b, a) -> b
def apply {α β : Type} : (α → β) × α → β
  | (f, x) => f x

-- The $ operator in Haskell is function application.
-- In Lean, function application is just space. 
-- Lean also has `<|` which is similar to `$`.
def dollar {α β : Type} (f : α → β) (x : α) : β := f x

-- Pair function
-- Haskell: pair :: a -> b -> (a, b)
def pair {α β : Type} (a : α) (b : β) : α × β := (a, b)

-- Partial application of pair
-- Haskell: pairWithTen :: a -> (Int, a)
def pairWithTen {α : Type} : α → Int × α := pair 10

-- For the complex number example, we can define a simple Complex structure
structure Complex where
  re : Float
  im : Float

-- Haskell's :+ is a constructor.
def mkComplex (re im : Float) : Complex := ⟨re, im⟩

-- Simple multiplication for the quadratic example
instance : Mul Complex where
  mul c1 c2 := { 
    re := c1.re * c2.re - c1.im * c2.im, 
    im := c1.re * c2.im + c1.im * c2.re 
  }

-- Simple addition
instance : Add Complex where
  add c1 c2 := { re := c1.re + c2.re, im := c1.im + c2.im }

def C := Complex

-- Quadratic function
-- Haskell: h (a, b, c) = \x -> (a :+ 0) * x * x + (b :+ 0) * x + (c :+ 0)
def h (abc : Float × Float × Float) : C → C :=
  let (a, b, c) := abc
  fun x => (mkComplex a 0) * x * x + (mkComplex b 0) * x + (mkComplex c 0)

end DaoFP.FunctionTypes
