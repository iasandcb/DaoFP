namespace DaoFP.MonadInstances

-- Monoid class for specific instances
class MyMonoid (M : Type) where
  mempty  : M
  mappend : M → M → M

-- Maybe (Option in Lean)
-- Standard library already has Monad Option, but we can redefine for the tutorial
instance : Monad Option where
  pure := some
  bind
    | none, _   => none
    | some a, k => k a

-- Writer Monad
structure Writer (ω α : Type) where
  runWriter : α × ω

instance : Functor (Writer ω) where
  map f w := { runWriter := (f w.runWriter.1, w.runWriter.2) }

instance [MyMonoid ω] : Monad (Writer ω) where
  pure a := { runWriter := (a, MyMonoid.mempty) }
  bind w k := 
    let (a, ω₁) := w.runWriter
    let (b, ω₂) := (k a).runWriter
    { runWriter := (b, MyMonoid.mappend ω₁ ω₂) }

-- Reader Monad
structure Reader (ε α : Type) where
  runReader : ε → α

instance : Functor (Reader ε) where
  map f r := { runReader := f ∘ r.runReader }

instance : Monad (Reader ε) where
  pure a := { runReader := fun _ => a }
  bind r k := { runReader := fun e => (k (r.runReader e)).runReader e }

-- State Monad
structure State (σ α : Type) where
  runState : σ → α × σ

instance : Functor (State σ) where
  map f s := { runState := fun σ₀ => 
    let (a, σ₁) := s.runState σ₀
    (f a, σ₁) }

instance : Monad (State σ) where
  pure a := { runState := fun s => (a, s) }
  bind s k := { runState := fun σ₀ =>
    let (a, σ₁) := s.runState σ₀
    (k a).runState σ₁ }

def get {σ : Type} : State σ σ :=
  { runState := fun s => (s, s) }

def set {σ : Type} (s : σ) : State σ Unit :=
  { runState := fun _ => ((), s) }

-- List Monad
-- Standard library already has Monad List
instance : Monad List where
  pure a := [a]
  bind as k := (as.map k).join

-- Continuation Monad
structure Cont (ρ α : Type) where
  runCont : (α → ρ) → ρ

instance : Functor (Cont ρ) where
  map f c := { runCont := fun k => c.runCont (k ∘ f) }

instance : Monad (Cont ρ) where
  pure a := { runCont := fun k => k a }
  bind c k := { runCont := fun r => 
    c.runCont (fun a => (k a).runCont r) }

-- Example using do-notation
def pairs {α β : Type} (as : List α) (bs : List β) : List (α × β) := do
  let a ← as
  let b ← bs
  pure (a, b)

end DaoFP.MonadInstances
