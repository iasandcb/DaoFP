namespace DaoFP.KanExtensions

-- Left Kan extension of f along p
structure Lan (P F : Type → Type) (β : Type) where
  {ε : Type}
  f : P ε → β
  val : F ε

instance : Functor (Lan P F) where
  map g l := { f := g ∘ l.f, val := l.val }

def unitLan {P F : Type → Type} {ε : Type} (fe : F ε) : Lan P F (P ε) :=
  { f := id, val := fe }

-- Universal property
def sigma {P F G : Type → Type} [Functor G] (alpha : ∀ {ε}, F ε → G (P ε)) : ∀ {β}, Lan P F β → G β :=
  fun l => Functor.map l.f (alpha l.val)

-- Density Comonad (Lan F F)
structure Density (F : Type → Type) (α : Type) where
  {δ : Type}
  f : F δ → α
  val : F δ

instance : Functor (Density F) where
  map g d := { f := g ∘ d.f, val := d.val }

instance : Comonad (Density F) where
  extract d := d.f d.val
  extend k d := { f := fun fd' => k { f := d.f, val := fd' }, val := d.val }

-- Right Kan extension of f along p
structure Ran (P F : Type → Type) (β : Type) where
  run : ∀ {ε : Type}, (β → P ε) → F ε

instance : Functor (Ran P F) where
  map g r := { run := fun k => r.run (k ∘ g) }

def counitRan {P F : Type → Type} {ε : Type} (r : Ran P F (P ε)) : F ε :=
  r.run id

def sigmaRan {P F G : Type → Type} [Functor G] (alpha : ∀ {ε}, G (P ε) → F ε) : ∀ {β}, G β → Ran P F β :=
  fun {β} gb => { run := fun {ε} k => alpha (Functor.map k gb) }

-- Codensity Monad (Ran F F)
structure Codensity (F : Type → Type) (α : Type) where
  run : ∀ {δ : Type}, (α → F δ) → F δ

instance : Functor (Codensity F) where
  map h c := { run := fun k => c.run (k ∘ h) }

instance : Applicative (Codensity F) where
  pure x := { run := fun k => k x }
  seq cf ca := { run := fun k => cf.run (fun f => ca.run (fun a => k (f a))) }

instance : Monad (Codensity F) where
  bind c f := { run := fun k => c.run (fun a => (f a).run k) }

end DaoFP.KanExtensions
