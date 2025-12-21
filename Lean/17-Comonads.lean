namespace DaoFP.MoreComonads

-- Comonad definition
class Comonad (W : Type → Type) [Functor W] where
  extract : {α : Type} → W α → α
  extend  : {α β : Type} → (W α → β) → W α → W β

-- Infinite Stream
inductive Stream' (α : Type) where
  | Cons : α → Stream' α → Stream' α

instance : Functor Stream' where
  map f
    | Stream'.Cons a as => Stream'.Cons (f a) (Functor.map f as)

partial instance : Comonad Stream' where
  extract
    | Stream'.Cons a _ => a
  extend f
    | s@(Stream'.Cons _ as) => Stream'.Cons (f s) (Comonad.extend f as)

def stmTake {α : Type} : Nat → Stream' α → List α
  | 0, _ => []
  | n + 1, Stream'.Cons a as => a :: stmTake n as

partial def avg (s : Stream' Float) : Float :=
  let vals := stmTake 5 s
  vals.foldl (· + ·) 0 / 5.0

partial def smooth (s : Stream' Float) : Stream' Float :=
  Comonad.extend avg s

-- Signal Comonad (Current value + function)
structure Signal (α : Type) where
  val_at : Float → α
  current : Float

instance : Functor Signal where
  map f s := { val_at := f ∘ s.val_at, current := s.current }

instance : Comonad Signal where
  extract s := s.val_at s.current
  extend g s := { 
    val_at := fun y => g { s with current := s.current - y },
    current := s.current 
  }

-- BiStream (Ziupper on streams)
inductive BiStream (α : Type) where
  | BStr : List α → List α → BiStream α

instance : Functor BiStream where
  map f
    | BiStream.BStr past future => BiStream.BStr (past.map f) (future.map f)

def fwd {α : Type} : BiStream α → BiStream α
  | BiStream.BStr past (b :: bs) => BiStream.BStr (b :: past) bs
  | b => b

def bwd {α : Type} : BiStream α → BiStream α
  | BiStream.BStr (a :: as) future => BiStream.BStr as (a :: future)
  | b => b

def iterate' (f : α → α) (x : α) : Stream' α :=
  Stream'.Cons x (iterate' f (f x))

-- Comonoid
class Comonoid (W : Type) where
  split   : W → W × W
  destroy : W → Unit

instance : Comonoid W where
  split w   := (w, w)
  destroy _ := ()

-- Store Comonad
structure Store (σ α : Type) where
  lookup : σ → α
  state  : σ

instance : Functor (Store σ) where
  map f s := { lookup := f ∘ s.lookup, state := s.state }

instance : Comonad (Store σ) where
  extract s := s.lookup s.state
  extend g s := {
    lookup := fun s' => g { s with state := s' },
    state  := s.state
  }

end DaoFP.MoreComonads
