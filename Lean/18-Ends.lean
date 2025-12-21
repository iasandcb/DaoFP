namespace DaoFP.Ends

-- Ends and Coends in Lean
-- An End is a polymorphic function p x x
def End (P : Type → Type → Type) := ∀ {χ : Type}, P χ χ

-- A Coend is an existential type (represented as a structure in Lean 4)
structure Coend (P : Type → Type → Type) where
  {χ : Type}
  val : P χ χ

-- Yoneda using Ends
def Yo (F : Type → Type) (α χ ψ : Type) := (α → χ) → F ψ

def yoneda {F : Type → Type} [Functor F] {α : Type} (e : End (Yo F α)) : F α :=
  e id

def yoneda_inv {F : Type → Type} [Functor F] {α : Type} (fa : F α) : End (Yo F α) :=
  fun h => Functor.map h fa

-- Coyoneda using Coends
structure CoY (F : Type → Type) (α χ ψ : Type) where
  f : χ → α
  fx : F ψ -- In the Coend context, chi = psi = x

def coyoneda {F : Type → Type} [Functor F] {α : Type} (c : Coend (fun χ ψ => CoY F α χ ψ)) : F α :=
  Functor.map c.val.f c.val.fx

def coyoneda_inv {F : Type → Type} [Functor F] {α : Type} (fa : F α) : Coend (fun χ ψ => CoY F α χ ψ) :=
  { χ := α, val := { f := id, fx := fa } }

-- Day Convolution
structure Day (F G : Type → Type) (χ : Type) where
  {α β : Type}
  f : (α × β) → χ
  fa : F α
  gb : G β

instance : Functor (Day F G) where
  map h d := { f := h ∘ d.f, fa := d.fa, gb := d.gb }

def assoc {F G H : Type → Type} {χ : Type} (d : Day F (Day G H) χ) : Day (Day F G) H χ :=
  let inner := d.gb
  {
    α := α × β, -- New combined state for Day F G
    β := H.β,
    f := fun ((a, b), d_val) => d.f (a, inner.f (b, d_val)),
    fa := { f := id, fa := d.fa, gb := inner.fa },
    gb := inner.gb
  }
where
  α := F.α
  β := F.β

end DaoFP.Ends
