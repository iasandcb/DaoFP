namespace DaoFP.NaturalTransformations

-- A natural transformation from F to G is a polymorphic function.
def Natural (F G : Type → Type) := ∀ {α : Type}, F α → G α

-- Naturality condition: fmap g h . alpha = alpha . fmap f h
-- (In Lean, we can write the terms expressing each side)

def oneWay {F G : Type → Type} [Functor F] [Functor G]
  (alpha : Natural F G) {α β : Type} (h : α → β) (x : F α) : G β :=
  Functor.map h (alpha x)

def otherWay {F G : Type → Type} [Functor F] [Functor G]
  (alpha : Natural F G) {α β : Type} (h : α → β) (x : F α) : G β :=
  alpha (Functor.map h x)

-- Examples
def safeHead : Natural List Option
  | []      => none
  | a :: _  => some a

def reverse_trans : Natural List List
  | []      => []
  | a :: as => reverse_trans as ++ [a]

-- Horizontal composition and Whiskering
section Composition

variable {F F' G G' H : Type → Type}
variable [Functor G] [Functor G'] [Functor H]

-- Placeholder natural transformations
variable (alpha : Natural F F')
variable (beta : Natural G G')

-- Horizontal composition: beta ∘ alpha
def beta_alpha {α : Type} (x : G (F α)) : G' (F' α) :=
  beta (Functor.map alpha x)

-- Whiskering
-- beta_F: applying beta after F
def beta_f {α : Type} (x : G (F α)) : G' (F α) :=
  beta x

-- G_alpha: applying alpha inside G
def g_alpha {α : Type} (x : G (F α)) : G (F' α) :=
  Functor.map alpha x

-- H_beta_F
def h_beta_f {α : Type} (x : H (G (F α))) : H (G' (F α)) :=
  Functor.map beta x

end Composition

-- Exercises
-- Applying safeHead after map reverse
def comp1 {α : Type} : List (List α) → Option (List α) :=
  fun x => safeHead (Functor.map List.reverse x)

-- Applying map reverse after safeHead
def comp2 {α : Type} : List (List α) → Option (List α) :=
  fun x => Functor.map List.reverse (safeHead x)

-- Applying reverse after map safeHead
def comp1' {α : Type} : List (List α) → List (Option α) :=
  fun x => List.reverse (Functor.map safeHead x)

-- Applying map safeHead after reverse
def comp2' {α : Type} : List (List α) → List (Option α) :=
  fun x => Functor.map safeHead (List.reverse x)

end DaoFP.NaturalTransformations
