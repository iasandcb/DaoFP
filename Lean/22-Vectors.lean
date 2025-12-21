namespace DaoFP.Vectors

-- Natural numbers for indexing
inductive Nat where
  | Z : Nat
  | S : Nat → Nat

-- Dependent vectors
inductive Vec (α : Type) : Nat → Type where
  | VNil  : Vec α Nat.Z
  | VCons : {n : Nat} → α → Vec α n → Vec α (Nat.S n)

def headV {α : Type} {n : Nat} : Vec α (Nat.S n) → α
  | Vec.VCons a _ => a

def tailV {α : Type} {n : Nat} : Vec α (Nat.S n) → Vec α n
  | Vec.VCons _ v => v

def zipV {α β : Type} {n : Nat} : Vec α n → Vec β n → Vec (α × β) n
  | Vec.VNil,         Vec.VNil         => Vec.VNil
  | Vec.VCons a as, Vec.VCons b bs => Vec.VCons (a, b) (zipV as bs)

def sumV {n : Nat} : Vec Int n → Int
  | Vec.VNil       => 0
  | Vec.VCons i v => i + sumV v

-- Singleton Nat (to bridge between Type and Value levels in some cases)
inductive SNat : Nat → Type where
  | SZ : SNat Nat.Z
  | SS : {n : Nat} → SNat n → SNat (Nat.S n)

def replicateV {α : Type} {n : Nat} (x : α) : SNat n → Vec α n
  | SNat.SZ   => Vec.VNil
  | SNat.SS n => Vec.VCons x (replicateV x n)

-- Filter on vectors (returns a "sigma" type conceptually)
-- In Lean we can return a Sigma type: (n : Nat) × Vec α n
def filterV {α : Type} {n : Nat} (p : α → Bool) : Vec α n → (Σ m : Nat, Vec α m)
  | Vec.VNil => ⟨Nat.Z, Vec.VNil⟩
  | Vec.VCons a as => 
    let ⟨m, bs⟩ := filterV p as
    if p a then
      ⟨Nat.S m, Vec.VCons a bs⟩
    else
      ⟨m, bs⟩

def toList {α : Type} {n : Nat} : Vec α n → List α
  | Vec.VNil       => []
  | Vec.VCons a as => a :: toList as

-- Example usage
def v : Vec Int (Nat.S (Nat.S (Nat.S (Nat.S Nat.Z)))) :=
  Vec.VCons 2 (Vec.VCons (-2) (Vec.VCons 3 (Vec.VCons (-1) Vec.VNil)))

def test_vec : List Int :=
  let res := filterV (· > 0) v
  toList res.2

end DaoFP.Vectors
