namespace DaoFP.FreeMonoids

class MyMonoid (M : Type) where
  mempty  : M
  mappend : M → M → M

instance : MyMonoid (List α) where
  mempty  := []
  mappend := List.append

-- foldMap implementation for Lists
def foldMap {α M : Type} [MyMonoid M] (f : α → M) : List α → M
  | []      => MyMonoid.mempty
  | a :: as => MyMonoid.mappend (f a) (foldMap f as)

-- Exercise: Monoid instances for Int addition and multiplication
structure IntPlus where
  unPlus : Int

instance : MyMonoid IntPlus where
  mempty      := { unPlus := 0 }
  mappend x y := { unPlus := x.unPlus + y.unPlus }

structure IntTimes where
  unTimes : Int

instance : MyMonoid IntTimes where
  mempty      := { unTimes := 1 }
  mappend x y := { unTimes := x.unTimes * y.unTimes }

def sumL (is : List Int) : Int :=
  (foldMap (fun i => IntPlus.mk i) is).unPlus

def multL (is : List Int) : Int :=
  (foldMap (fun i => IntTimes.mk i) is).unTimes

end DaoFP.FreeMonoids
