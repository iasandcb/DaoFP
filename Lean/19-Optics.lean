namespace DaoFP.Optics

class Profunctor (P : Type → Type → Type) where
  dimap : {α β σ τ : Type} → (σ → α) → (β → τ) → P α β → P σ τ

class Profunctor P ⇒ Cartesian P where
  alpha : {α β γ : Type} → P α β → P (γ × α) (γ × β)

class Profunctor P ⇒ Cocartesian P where
  alpha_prime : {α β γ : Type} → P α β → P (Sum γ α) (Sum γ β)

-- Existential Lens
structure LensE (σ τ α β : Type) where
  {γ : Type}
  from : σ → γ × α
  to   : γ × β → τ

-- van Laarhoven / Profunctor Lens
def LensP (σ τ α β : Type) := ∀ {P : Type → Type → Type}, [Profunctor P] → [Cartesian P] → P α β → P σ τ

def toLensP {σ τ α β : Type} (l : LensE σ τ α β) : LensP σ τ α β :=
  fun p pc p_ab => Profunctor.dimap l.from l.to (Cartesian.alpha p_ab)

-- FlipLens to extract functions from LensP
structure FlipLens (α β σ τ : Type) where
  get : σ → α
  set : σ → β → τ

instance : Profunctor (FlipLens α β) where
  dimap f g l := {
    get := l.get ∘ f,
    set := fun s b => g (l.set (f s) b)
  }

instance : Cartesian (FlipLens α β) where
  alpha l := {
    get := l.get ∘ Prod.snd,
    set := fun (c, s) b => (c, l.set s b)
  }

def fromLensP {σ τ α β : Type} (lp : LensP σ τ α β) : (σ → α) × (σ → β → τ) :=
  let initial : FlipLens α β α τ := { get := id, set := fun _ b => b }
  let res := lp initial
  (res.get, res.set)

-- Existential Prism
structure PrismE (σ τ α β : Type) where
  {γ : Type}
  from' : σ → Sum γ α
  to'   : Sum γ β → τ

def toMatch {σ τ α β : Type} (p : PrismE σ τ α β) : σ → Sum τ α :=
  fun s => match p.from' s with
    | Sum.inl c => Sum.inl (p.to' (Sum.inl c))
    | Sum.inr a => Sum.inr a

def toBuild {σ τ α β : Type} (p : PrismE σ τ α β) : β → τ :=
  fun b => p.to' (Sum.inr b)

end DaoFP.Optics
