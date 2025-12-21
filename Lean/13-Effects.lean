namespace DaoFP.Effects

structure Writer (ω α : Type) where
  runWriter : α × ω

structure Reader (ε α : Type) where
  runReader : ε → α

structure State (σ α : Type) where
  runState : σ → α × σ

structure Cont (ρ α : Type) where
  runCont : (α → ρ) → ρ

-- Exercise: Functor instance for Cont
instance : Functor (Cont ρ) where
  map f c := { runCont := fun k => c.runCont (k ∘ f) }

end DaoFP.Effects
