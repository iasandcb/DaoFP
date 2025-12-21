namespace DaoFP.Lenses

-- Existential Lens (Costate Comonad Coalgebra)
structure LensE (σ τ α β : Type) where
  {γ : Type}
  l : σ → γ × α
  r : γ × β → τ

def toGet {σ τ α β : Type} (lens : LensE σ τ α β) : σ → α :=
  fun s => (lens.l s).2

def toSet {σ τ α β : Type} (lens : LensE σ τ α β) : σ → β → τ :=
  fun s b => lens.r ((lens.l s).1, b)

def prodLens {γ α β : Type} : LensE (γ × α) (γ × β) α β :=
  { γ := γ, l := id, r := id }

-- Commutativity/Associativity helpers
def assoc {α β γ : Type} : (α × β) × γ → α × (β × γ)
  | ((a, b), c) => (a, (b, c))

def assoc_inv {α β γ : Type} : α × (β × γ) → (α × β) × γ
  | (a, (b, c)) => ((a, b), c)

-- Lens composition
def compLens {α β α' β' σ τ : Type} (l2 : LensE α β α' β') (l1 : LensE σ τ α β) : LensE σ τ α' β' :=
  {
    γ := l1.γ × l2.γ,
    l := fun s => 
      let (c, a) := l1.l s
      let (c', a') := l2.l a
      ((c, c'), a'),
    r := fun ((c, c'), b') =>
      let b := l2.r (c', b')
      l1.r (c, b)
  }

-- Example usage
def l3 : LensE (String × (Bool × Int)) (String × (Bool × Char)) Int Char :=
  compLens prodLens prodLens

def example_val : String × (Bool × Int) := ("Outer", (True, 42))

def test_get := toGet l3 example_val
def test_set := toSet l3 example_val 'z'

end DaoFP.Lenses
