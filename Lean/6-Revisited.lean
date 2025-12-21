namespace DaoFP.FunctionTypesRevisited

-- Universal property of sum
def mapOut {α β γ : Type} : (α → γ) × (β → γ) → (Sum α β → γ)
  | (f, g) => fun aorb => match aorb with
    | Sum.inl a => f a
    | Sum.inr b => g b

def either {α β γ : Type} (f : α → γ) (g : β → γ) : Sum α β → γ
  | Sum.inl a => f a
  | Sum.inr b => g b

def unEither {α β γ : Type} (h : Sum α β → γ) : (α → γ) × (β → γ) :=
  (fun a => h (Sum.inl a), fun b => h (Sum.inr b))

-- Universal property of product
def mapIn {α β γ : Type} : (γ → α) × (γ → β) → (γ → α × β)
  | (f, g) => fun c => (f c, g c)

-- &&& operator (often called fork or fanout)
def fork_op {α β γ : Type} (f : γ → α) (g : γ → β) : γ → α × β :=
  fun c => (f c, g c)

infixr:70 " &&& " => fork_op

def fork {α β γ : Type} (h : γ → α × β) : (γ → α) × (γ → β) :=
  (fun c => (h c).1, fun c => (h c).2)

-- Functoriality of sum
def bimapSum {α α' β β' : Type} (f : α → α') (g : β → β') : Sum α β → Sum α' β'
  | Sum.inl a => Sum.inl (f a)
  | Sum.inr b => Sum.inr (g b)

-- Functoriality of product
def bimapProd {α α' β β' : Type} (f : α → α') (g : β → β') : α × β → α' × β'
  | (a, b) => (f a, g b)

-- Functoriality of function type (dimap)
def dimap {α α' β β' : Type} (f : α' → α) (g : β → β') (h : α → β) : α' → β' :=
  fun a' => g (h (f a'))

-- Distributivity
def dist {α β γ : Type} : Sum (β × α) (γ × α) → (Sum β γ) × α
  | Sum.inl (b, a) => (Sum.inl b, a)
  | Sum.inr (c, a) => (Sum.inr c, a)

def undist {α β γ : Type} : (Sum β γ) × α → Sum (β × α) (γ × α)
  | (Sum.inl b, a) => Sum.inl (b, a)
  | (Sum.inr c, a) => Sum.inr (c, a)

-- Exercises: 2 * a = a + a
def toSum {α : Type} : Bool × α → Sum α α
  | (true, a)  => Sum.inl a
  | (false, a) => Sum.inr a

def fromSum {α : Type} : Sum α α → Bool × α
  | Sum.inl a => (true, a)
  | Sum.inr a => (false, a)

end DaoFP.FunctionTypesRevisited
