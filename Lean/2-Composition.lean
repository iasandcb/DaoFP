namespace DaoFP.Composition

def postCompWith {α β ξ : Type} (f : α → β) : (ξ → α) → (ξ → β) :=
  fun h => f ∘ h

def preCompWith {α β ξ : Type} (f : α → β) : (β → ξ) → (α → ξ) :=
  fun h => h ∘ f

def injectBool (b : Bool) : Int :=
  if b then 1 else 0

end DaoFP.Composition
