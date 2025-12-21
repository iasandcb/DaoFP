namespace DaoFP

-- Void has no constructor
inductive Void : Type

-- Unique arrow from the initial Void to any type α
-- Since Void has no constructor, 
-- no element of Void can be passed to this function
def absurd {α : Type} (v : Void) : α :=
  nomatch v

-- Unique arrow from any type α to Unit -- the terminal type
-- In Lean, the terminal type is Unit and its only element is ()
def unit {α : Type} (_ : α) : Unit := ()

-- x is an element of the type Int
-- its value is 42
def x : Int := 42

-- Categorically it's equivalent to:
-- A function from the terminal type Unit to Int
def y : Unit → Int
  | () => 42

end DaoFP
