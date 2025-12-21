namespace DaoFP.Isomorphism

-- Type synonym
def MyTemperature := Int

-- Simple syntax (using structure)
structure Temperature' where
  val : Int

def toInt' (t : Temperature') : Int :=
  t.val

-- Record syntax (Lean 4 structures generate projections automatically)
structure Temperature where
  toInt : Int

-- Function composition in Lean ∘
-- Note: 'negate' for Int is '-' or 'Int.neg'
def invert (t : Temperature) : Temperature :=
  Temperature.mk (-(t.toInt))

-- Or using the composition style from Haskell
def invert' : Temperature → Temperature :=
  fun t => { toInt := -t.toInt }

end DaoFP.Isomorphism
