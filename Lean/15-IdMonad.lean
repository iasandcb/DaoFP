namespace DaoFP.IdMonad

structure Id (α : Type) where
  getId : α

instance : Functor Id where
  map f i := { getId := f i.getId }

instance : Applicative Id where
  pure a := { getId := a }
  seq if_ ia := { getId := if_.getId ia.getId }

instance : Monad Id where
  pure a := { getId := a }
  bind i k := k i.getId

end DaoFP.IdMonad
