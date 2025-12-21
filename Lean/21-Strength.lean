namespace DaoFP.Strength

def strength {F : Type → Type} [Functor F] {α β : Type} (pair : α × F β) : F (α × β) :=
  Functor.map (fun b => (pair.1, b)) pair.2

def coeval {α β : Type} (a : α) : β → α × β :=
  fun b => (a, b)

def strength_prime {F : Type → Type} [Functor F] {α β : Type} (pair : α × F β) : F (α × β) :=
  let (a, f_val) := pair
  Functor.map (coeval a) f_val

end DaoFP.Strength
