namespace DaoFP.DayAdjunction

structure Day (F G : Type → Type) (α : Type) where
  {χ ψ : Type}
  f : (χ × ψ) → α
  fx : F χ
  gy : G ψ

def DayHom (G H : Type → Type) (α : Type) := ∀ {β : Type}, G β → H (α × β)

def ltor {F G H : Type → Type} (day_h : ∀ {α : Type}, Day F G α → H α) : ∀ {α : Type}, F α → DayHom G H α :=
  fun {α} fa {β} gb => day_h { f := id, fx := fa, gy := gb }

def rtol {F G H : Type → Type} [Functor H] (f_hom : ∀ {α : Type}, F α → DayHom G H α) : ∀ {α : Type}, Day F G α → H α :=
  fun {α} d => Functor.map d.f (f_hom d.fx d.gy)

end DaoFP.DayAdjunction
