namespace DaoFP.Tannaka

-- Cayley Representation (DLists)
def DList (α : Type) := List α → List α

def rep {α : Type} (as : List α) : DList α :=
  fun xs => as ++ xs

def unRep {α : Type} (f : DList α) : List α :=
  f []

def rev {α : Type} : List α → DList α
  | []      => rep []
  | a :: as => (rev as) ∘ (rep [a])

def fastReverse {α : Type} (as : List α) : List α :=
  unRep (rev as)

-- Tannaka Reconstruction
structure Identity (α : Type) where
  val : α

instance : Functor Identity where
  map f i := { val := f i.val }

def toTannaka {α β : Type} (g : α → β) : ∀ {F : Type → Type} [Functor F], F α → F β :=
  fun {F} _ fa => Functor.map g fa

def fromTannaka {α β : Type} (G : ∀ {F : Type → Type}, [Functor F] → F α → F β) : α → β :=
  fun a => (G (Identity.mk a)).val

def Getter (α β : Type) := ∀ {F : Type → Type}, [Functor F] → F α → F β

-- Example
def boolToStr := toTannaka (fun (b : Bool) => if b then "True" else "False")

def test_tannaka : String :=
  fromTannaka boolToStr false

end DaoFP.Tannaka
