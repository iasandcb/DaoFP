namespace DaoFP.Adjunctions

-- Standard Adjunction definition via unit and counit
class Adjunction (L R : Type → Type) [Functor L] [Functor R] where
  unit {α : Type}   : α → R (L α)
  counit {α : Type} : L (R α) → α

-- Alternative Adjunction definition via hom-set isomorphism
class AdjunctionHom (L R : Type → Type) [Functor L] [Functor R] where
  ltor {α β : Type} : (L α → β) → (α → R β)
  rtol {α β : Type} : (α → R β) → (L α → β)

-- Example: Product-Exponential Adjunction
-- Haskell names: L r x = (x, r), R r x = r -> x
structure LAdj (ρ α : Type) where
  val : α × ρ

structure RAdj (ρ α : Type) where
  val : ρ → α

instance : Functor (LAdj ρ) where
  map f p := { val := (f p.val.1, p.val.2) }

instance : Functor (RAdj ρ) where
  map f g := { val := fun r => f (g.val r) }

instance : Adjunction (LAdj ρ) (RAdj ρ) where
  unit x   := { val := fun r => { val := (x, r) } }
  counit p := p.val.1.val p.val.2

-- Triangle identities (as functions)
def triangle {ρ α : Type} (x : LAdj ρ α) : LAdj ρ α :=
  Adjunction.counit (Functor.map Adjunction.unit x)

def triangle_prime {ρ α : Type} (x : RAdj ρ α) : RAdj ρ α :=
  Functor.map Adjunction.counit (Adjunction.unit x)

-- Testing the triangle identities
def test_val : LAdj Char Int := { val := (2, 'a') }
def test_result := triangle test_val

def test_prime (n : Int) : Int :=
  let f_adj : RAdj Int Int := { val := fun x => x * x }
  let res := triangle_prime f_adj
  res.val n

end DaoFP.Adjunctions
