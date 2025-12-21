namespace DaoFP.Arrows

class Profunctor (P : Type → Type → Type) where
  dimap : {α β σ τ : Type} → (σ → α) → (β → τ) → P α β → P σ τ

class PreArrow (P : Type → Type → Type) [Profunctor P] where
  compose : {α β γ : Type} → P α β → P β γ → P α γ
  arr     : {α β : Type} → (α → β) → P α β

infixr:5 " >>> " => PreArrow.compose

class Arrow (P : Type → Type → Type) [PreArrow P] where
  first : {α β γ : Type} → P α β → P (α × γ) (β × γ)

-- Function type is the standard Arrow
instance : Profunctor (fun α β => α → β) where
  dimap f g h := g ∘ h ∘ f

instance : PreArrow (fun α β => α → β) where
  compose f g := g ∘ f
  arr f       := f

instance : Arrow (fun α β => α → β) where
  first f := fun (a, c) => (f a, c)

end DaoFP.Arrows
