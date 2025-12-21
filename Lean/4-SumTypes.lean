namespace DaoFP.SumTypes

-- Bool' with constructors taking Unit
inductive Bool' where
  | true'  : Unit → Bool'
  | false' : Unit → Bool'

-- standard Bool-like definition
inductive Bool'' where
  | true'' : Bool''
  | false'' : Bool''

def x_plain : Bool := true

abbrev A := Int

def x : A := 5
def y : A := 7
def z : A := 11

def h (b : Bool) : A :=
  if b then x else y

def not (b : Bool) : Bool :=
  if b then false else true

inductive RGB where
  | Red   : RGB
  | Green : RGB
  | Blue  : RGB

def c : RGB := RGB.Blue

def h1 : RGB → A
  | .Red   => x
  | .Green => y
  | .Blue  => z

def h2 : Bool → A
  | true  => x
  | false => y

def h3 (c : RGB) : A :=
  match c with
  | .Red   => x
  | .Green => y
  | .Blue  => z

def h4 (b : Bool) : A :=
  match b with
  | true  => x
  | false => y

def c_char : Char := 'a'

def yesno (c : Char) : Bool :=
  match c with
  | 'y' => true
  | 'Y' => true
  | _   => false

inductive Either (α β : Type) where
  | Left  : α → Either α β
  | Right : β → Either α β

-- Using sorry instead of undefined for unimplemented placeholders
def f {α γ : Type} : α → γ := sorry
def g {β γ : Type} : β → γ := sorry

def h5 {α β γ : Type} : Either α β → γ
  | .Left a  => f a
  | .Right b => g b

def h6 {α β γ : Type} (e : Either α β) : γ :=
  match e with
  | .Left a  => f a
  | .Right b => g b

inductive Maybe' (α : Type) where
  | nothing' : Unit → Maybe' α
  | just'    : α → Maybe' α

inductive Maybe (α : Type) where
  | nothing : Maybe α
  | just    : α → Maybe α

inductive Void : Type

def absurd {α : Type} (v : Void) : α :=
  nomatch v

def f' : Either Unit Void → Unit
  | .Left () => ()
  | .Right v => nomatch v

def f_1 : Unit → Either Unit Void
  | () => Either.Left ()

-- Exercises

def from_either {α : Type} : Either α Void → α
  | .Left a  => a
  | .Right v => nomatch v

def to_either {α : Type} (x : α) : Either α Void :=
  Either.Left x

def sym {α β : Type} : Either α β → Either β α
  | .Left a  => .Right a
  | .Right b => .Left b

-- Placeholders for exercises
def f1 {α ξ : Type} : α → ξ := sorry
def f2 {β ξ : Type} : β → ξ := sorry
def f3 {γ ξ : Type} : γ → ξ := sorry

def h7 {α β γ ξ : Type} : Either (Either α β) γ → ξ
  | .Left (.Left a)  => f1 a
  | .Left (.Right b) => f2 b
  | .Right c         => f3 c

def h7' {α β γ ξ : Type} : Either α (Either β γ) → ξ
  | .Left a          => f1 a
  | .Right (.Left b)  => f2 b
  | .Right (.Right c) => f3 c

end DaoFP.SumTypes
