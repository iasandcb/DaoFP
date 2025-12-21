namespace DaoFP.Applicatives

-- Monoid class for specific instances
class MyMonoid (M : Type) where
  mempty  : M
  mappend : M → M → M

-- Applicative class matching the tutorial style
class Applicative' (F : Type → Type) [Functor F] where
  pure  : {α : Type} → α → F α
  seq   : {α β : Type} → F (α → β) → F α → F β

-- Notation mirroring Haskell
infixl:4 " <*> " => Applicative'.seq
infixl:4 " <$> " => Functor.map

-- Maybe instance
instance : Applicative' Option where
  pure := Option.some
  seq
    | some f, some a => some (f a)
    | _, _           => none

-- Validation instance
inductive Validation (ε α : Type) where
  | Failure : ε → Validation ε α
  | Success : α → Validation ε α

instance : Functor (Validation ε) where
  map f
    | Validation.Failure e => Validation.Failure e
    | Validation.Success a => Validation.Success (f a)

instance [MyMonoid ε] : Applicative' (Validation ε) where
  pure := Validation.Success
  seq
    | Validation.Failure e1, Validation.Failure e2 => Validation.Failure (MyMonoid.mappend e1 e2)
    | Validation.Failure e,  _                     => Validation.Failure e
    | _,                     Validation.Failure e  => Validation.Failure e
    | Validation.Success f,  Validation.Success x  => Validation.Success (f x)

-- Writer instance
structure Writer (ω α : Type) where
  runWriter : α × ω

instance : Functor (Writer ω) where
  map f w := { runWriter := (f w.runWriter.1, w.runWriter.2) }

instance [MyMonoid ω] : Applicative' (Writer ω) where
  pure a := { runWriter := (a, MyMonoid.mempty) }
  seq wf wa := 
    let (f, w)  := wf.runWriter
    let (a, w') := wa.runWriter
    { runWriter := (f a, MyMonoid.mappend w w') }

-- Reader instance
structure Reader (ε α : Type) where
  runReader : ε → α

instance : Functor (Reader ε) where
  map f r := { runReader := fun e => f (r.runReader e) }

instance : Applicative' (Reader ε) where
  pure a := { runReader := fun _ => a }
  seq rf ra := { runReader := fun e => (rf.runReader e) (ra.runReader e) }

-- State instance
structure State (σ α : Type) where
  runState : σ → α × σ

instance : Functor (State σ) where
  map f s := { runState := fun σ₀ => 
    let (a, σ₁) := s.runState σ₀
    (f a, σ₁) }

instance : Applicative' (State σ) where
  pure a := { runState := fun s => (a, s) }
  seq sf sa := { runState := fun s₀ =>
    let (f, s₁) := sf.runState s₀
    let (a, s₂) := sa.runState s₁
    (f a, s₂) }

-- ZipList instance
structure ZipList (α : Type) where
  unZip : List α

instance : Functor ZipList where
  map f z := { unZip := z.unZip.map f }

partial def repeat' {α : Type} (a : α) : List α :=
  a :: repeat' a

def zipWith' {α β γ : Type} (f : α → β → γ) : List α → List β → List γ
  | [], _       => []
  | _, []       => []
  | a::as, b::bs => f a b :: zipWith' f as bs

instance : Applicative' ZipList where
  pure a := { unZip := repeat' a }
  seq zf za := { unZip := zipWith' (fun f a => f a) zf.unZip za.unZip }

-- List instance
instance : Applicative' List where
  pure a := [a]
  seq fs as := (fs.map (fun f => as.map f)).join

-- Continuation instance
structure Cont (ρ α : Type) where
  runCont : (α → ρ) → ρ

instance : Functor (Cont ρ) where
  map f c := { runCont := fun k => c.runCont (k ∘ f) }

instance : Applicative' (Cont ρ) where
  pure a := { runCont := fun k => k a }
  seq kf ka := { runCont := fun k =>
    kf.runCont (fun f =>
    ka.runCont (fun a => k (f a))) }

-- Composition of Applicatives
structure Compose (G F : Type → Type) (α : Type) where
  val : G (F α)

instance [Functor G] [Functor F] : Functor (Compose G F) where
  map h c := { val := Functor.map (Functor.map h) c.val }

instance [Functor G] [Functor F] [Applicative' G] [Applicative' F] : Applicative' (Compose G F) where
  pure x := { val := Applicative'.pure (Applicative'.pure x) }
  seq cff cfa := { val := Functor.map (Applicative'.seq) cff.val <*> cfa.val }

end DaoFP.Applicatives
