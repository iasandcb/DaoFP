namespace DaoFP.Parsers

structure Parser (α : Type) where
  parse : String → Option (α × String)

instance : Functor Parser where
  map f p := { parse := fun s => 
    match p.parse s with
    | some (a, s') => some (f a, s')
    | none         => none }

instance : Applicative Parser where
  pure a := { parse := fun s => some (a, s) }
  seq pf pa := { parse := fun s =>
    match pf.parse s with
    | some (f, s') => 
      match pa.parse s' with
      | some (a, s'') => some (f a, s'')
      | none          => none
    | none => none }

-- Applicative helper operators
def skipLeft {F : Type → Type} [Applicative F] {α β : Type} (p1 : F α) (p2 : F β) : F β :=
  (fun _ x => x) <$> p1 <*> p2

def skipRight {F : Type → Type} [Applicative F] {α β : Type} (p1 : F α) (p2 : F β) : F α :=
  (fun x _ => x) <$> p1 <*> p2

infixl:4 " *> " => skipLeft
infixl:4 " <* " => skipRight

-- Alternative class
class Alternative (F : Type → Type) [Applicative F] where
  empty : {α : Type} → F α
  orElse : {α : Type} → F α → F α → F α

infixl:3 " <|> " => Alternative.orElse

instance : Alternative Option where
  empty := none
  orElse
    | some a, _ => some a
    | none, r   => r

instance : Alternative Parser where
  empty := { parse := fun _ => none }
  orElse p1 p2 := { parse := fun s => p1.parse s <|> p2.parse s }

-- Basic parsers
def satisfy (p : Char → Bool) : Parser Char :=
  { parse := fun s => 
    match s.get? 0 with
    | some c => if p c then some (c, s.drop 1) else none
    | none   => none }

def char (c : Char) : Parser Char :=
  satisfy (· == c)

def seqA {F : Type → Type} [Applicative F] {α : Type} : List (F α) → F (List α)
  | [] => pure []
  | fa :: fas => (fun a as => a :: as) <$> fa <*> seqA fas

def string (s : String) : Parser String :=
  String.mk <$> seqA (s.toList.map char)

-- Combinators for repetitions
partial def many {α : Type} (p : Parser α) : Parser (List α) :=
  ((fun a as => a :: as) <$> p <*> many p) <|> pure []

partial def some {α : Type} (p : Parser α) : Parser (List α) :=
  (fun a as => a :: as) <$> p <*> many p

def digit : Parser Char :=
  satisfy Char.isDigit

def space : Parser Char :=
  char ' ' <|> char '\t'

def ss : Parser (List Char) :=
  many space

-- Lambda expression parser
inductive Expr where
  | Var    : Char → Expr
  | Lambda : Char → Expr → Expr
  | App    : Expr → Expr → Expr
  deriving Repr

def name : Parser Char :=
  satisfy Char.isLower

mutual
  partial def term : Parser Expr :=
    (Expr.Var <$> name <* ss) <|>
    (Expr.Lambda <$> (char '\\' *> name <* ss <* char '.' <* ss) <*> expr) <|>
    ({ parse := fun s => (char '(' *> ss *> expr <* char ')' <* ss).parse s })

  partial def expr : Parser Expr :=
    let foldl1 (f : α → α → α) : List α → α
      | a :: as => as.foldl f a
      | []      => panic! "empty list in foldl1"
    foldl1 Expr.App <$> some term
end

end DaoFP.Parsers
