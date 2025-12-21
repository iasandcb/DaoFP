namespace DaoFP.MonoidalFunctors

-- Monoidal Functor class: unit and combination
class Monoidal (F : Type → Type) where
  unit    : F Unit
  combine : {α β : Type} → F α → F β → F (α × β)

infixl:4 " >*< " => Monoidal.combine

instance : Monoidal Option where
  unit := some ()
  combine
    | some a, some b => some (a, b)
    | _, _           => none

-- Reassociating triples
def reassoc {α β γ : Type} : (α × β) × γ → α × β × γ
  | ((a, b), c) => (a, b, c)

-- Running three functions in parallel (conceptually)
def run3 {F : Type → Type} [Functor F] [Monoidal F] {χ ψ ζ α β γ : Type}
  (f1 : χ → F α) (f2 : ψ → F β) (f3 : ζ → F γ) : (χ × ψ × ζ) → F (α × β × γ) :=
  fun (x, y, z) =>
    let fab  := f1 x >*< f2 y
    let fabc := fab >*< f3 z
    Functor.map reassoc fabc

-- Applicative can be derived from Monoidal + Functor
def pure_from_monoidal {F : Type → Type} [Functor F] [Monoidal F] {α : Type} (a : α) : F α :=
  Functor.map (fun _ => a) Monoidal.unit

def seq_from_monoidal {F : Type → Type} [Functor F] [Monoidal F] {α β : Type} 
  (ff : F (α → β)) (fa : F α) : F β :=
  Functor.map (fun (f, a) => f a) (ff >*< fa)

-- Functor strength
def strength {F : Type → Type} [Functor F] {ε α : Type} (pair : ε × F α) : F (ε × α) :=
  let (e, as) := pair
  Functor.map (fun a => (e, a)) as

-- Exercise: Monoidal instance for List (ZipList style)
partial def zip_unit : List Unit := () :: zip_unit

def zip_combine {α β : Type} : List α → List β → List (α × β)
  | [], _ => []
  | _, [] => []
  | a :: as, b :: bs => (a, b) :: zip_combine as bs

instance : Monoidal List where
  unit := zip_unit
  combine := zip_combine

end DaoFP.MonoidalFunctors
