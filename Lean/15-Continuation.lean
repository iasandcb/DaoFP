namespace DaoFP.Continuations

structure Cont (ρ α : Type) where
  runCont : (α → ρ) → ρ

instance : Functor (Cont ρ) where
  map f c := { runCont := fun k => c.runCont (k ∘ f) }

instance : Applicative (Cont ρ) where
  pure a := { runCont := fun k => k a }
  seq cf ca := { runCont := fun k => cf.runCont (fun f => ca.runCont (fun a => k (f a))) }

instance : Monad (Cont ρ) where
  bind c f := { runCont := fun k => c.runCont (fun a => (f a).runCont k) }

-- Tree definitions
inductive Tree where
  | Leaf : String → Tree
  | Node : Tree → String → Tree → Tree

def example_tree : Tree := 
  Tree.Node (Tree.Leaf "leaf ") "root " (Tree.Node (Tree.Leaf "l1 ") "right " (Tree.Leaf "l2 "))

-- Direct recursion
def show1 : Tree → String
  | Tree.Leaf s     => s
  | Tree.Node l s r => show1 l ++ s ++ show1 r

-- Using Cont monad
def showk2 (t : Tree) : Cont ρ String :=
  match t with
  | Tree.Leaf s     => pure s
  | Tree.Node l s r => do
    let ls ← showk2 l
    let rs ← showk2 r
    pure (ls ++ s ++ rs)

def show2 (t : Tree) : String :=
  (showk2 t).runCont id

-- Direct CPS
def showk3 {ρ : Type} (t : Tree) (k : String → ρ) : ρ :=
  match t with
  | Tree.Leaf s     => k s
  | Tree.Node l s r =>
    showk3 l (fun ls => 
      showk3 r (fun rs => 
        k (ls ++ s ++ rs)))

def show3 (t : Tree) : String :=
  showk3 t id

-- Defunctionalized CPS
inductive Kont where
  | Done : Kont
  | Next : String → Tree → Kont → Kont
  | Conc : String → String → Kont → Kont

mutual
  def apply : Kont → String → String
    | Kont.Done,          s  => s
    | Kont.Next s rgt k,  ls => showk rgt (Kont.Conc ls s k)
    | Kont.Conc ls s k,   rs => apply k (ls ++ s ++ rs)

  def showk : Tree → Kont → String
    | Tree.Leaf s,     k => apply k s
    | Tree.Node l s r, k => showk l (Kont.Next s r k)
end

def showTree (t : Tree) : String :=
  showk t Kont.Done

end DaoFP.Continuations
