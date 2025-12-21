namespace DaoFP.FreeMonads

-- Free Monad definition
inductive Free (F : Type → Type) (α : Type) where
  | Pure : α → Free F α
  | Bind : F (Free F α) → Free F α

instance [Functor F] : Functor (Free F) where
  map f
    | Free.Pure a => Free.Pure (f a)
    | Free.Bind x => Free.Bind (Functor.map (Functor.map f) x)

instance [Functor F] : Applicative (Free F) where
  pure := Free.Pure
  seq ff fa := match ff with
    | Free.Pure f => Functor.map f fa
    | Free.Bind x => Free.Bind (Functor.map (fun c => Applicative.seq c fa) x)

instance [Functor F] : Monad (Free F) where
  bind m k := match m with
    | Free.Pure a => k a
    | Free.Bind x => Free.Bind (Functor.map (fun m' => Monad.bind m' k) x)

-- Mcata: folding a Free Monad structure
-- Haskell: type MAlg f g a = (a -> g a, f (g a) -> g a)
def mcata {F : Type → Type} [Functor F] {G : Type → Type} (l : {α : Type} → α → G α) (r : {α : Type} → F (G α) → G α) {α : Type} : Free F α → G α
  | Free.Pure a => l a
  | Free.Bind x => r (Functor.map (mcata l r) x)

-- Stack Calculator Example
inductive StackF (κ : Type) where
  | Push : Int → κ → StackF κ
  | Top  : (Int → κ) → StackF κ
  | Pop  : κ → StackF κ
  | Add  : κ → StackF κ

instance : Functor StackF where
  map f
    | StackF.Push n k => StackF.Push n (f k)
    | StackF.Top g    => StackF.Top (f ∘ g)
    | StackF.Pop k    => StackF.Pop (f k)
    | StackF.Add k    => StackF.Add (f k)

abbrev FreeStack := Free StackF

def liftF {F : Type → Type} [Functor F] {α : Type} (fa : F α) : Free F α :=
  Free.Bind (Functor.map Free.Pure fa)

def push (n : Int) : FreeStack Unit := liftF (StackF.Push n ())
def pop : FreeStack Unit := liftF (StackF.Pop ())
def top : FreeStack Int := liftF (StackF.Top id)
def add : FreeStack Unit := liftF (StackF.Add ())

def calc : FreeStack Int := do
  push 3
  push 4
  add
  let x ← top
  pop
  pure x

-- Stack Action (interpreter)
def StackAction (α : Type) := List Int → (List Int × α)

def runAlg_l {α : Type} : α → StackAction α :=
  fun a ns => (ns, a)

def runAlg_r {α : Type} : StackF (StackAction α) → StackAction α
  | StackF.Pop k    => fun ns => k (ns.tail)
  | StackF.Top ik   => fun ns => (ik ns.head!) ns
  | StackF.Push n k => fun ns => k (n :: ns)
  | StackF.Add k    => fun ns => 
    match ns with
    | n1 :: n2 :: ns' => k ((n1 + n2) :: ns')
    | _ => ([], panic! "Stack underflow")

def run {α : Type} (prog : FreeStack α) : List Int × α :=
  mcata runAlg_l runAlg_r prog []

-- Exercises
inductive Rose (α : Type) where
  | Leaf : α → Rose α
  | Node : List (Rose α) → Rose α

def roseToFree {α : Type} : Rose α → Free List α
  | Rose.Leaf a      => Free.Pure a
  | Rose.Node roses  => Free.Bind (roses.map roseToFree)

def freeToRose {α : Type} : Free List α → Rose α
  | Free.Pure a      => Rose.Leaf a
  | Free.Bind roses  => Rose.Node (roses.map freeToRose)

end DaoFP.FreeMonads
