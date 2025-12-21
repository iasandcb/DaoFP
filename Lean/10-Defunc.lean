namespace DaoFP.Defunctionalization

-- Continuation-Passing Style (CPS) sum
def sumK {ρ : Type} : List Int → (Int → ρ) → ρ
  | [], k      => k 0
  | i :: is, k => sumK is (fun s => k (i + s))

def sumList (as : List Int) : Int :=
  sumK as id

-- Defunctionalizing the continuation: Step 1
def more {ρ : Type} : (Int × (Int → ρ)) → Int → ρ
  | (i, k), s => k (i + s)

def done (i : Int) : Int := i

def sumK_prime {ρ : Type} : List Int → (Int → ρ) → ρ
  | [], k      => k 0
  | i :: is, k => sumK_prime is (more (i, k))

def sumList_prime (is : List Int) : Int :=
  sumK_prime is done

-- Defunctionalizing the continuation: Step 2 (Data-driven)
inductive Kont where
  | Done : Kont
  | More : Int → Kont → Kont

def apply_kont : Kont × Int → Int
  | (Kont.Done, i)     => i
  | (Kont.More i k, s) => apply_kont (k, i + s)

def sumK_double_prime : List Int → Kont → Int
  | [], k      => apply_kont (k, 0)
  | i :: is, k => sumK_double_prime is (Kont.More i k)

def sumList_double_prime (is : List Int) : Int :=
  sumK_double_prime is Kont.Done

end DaoFP.Defunctionalization
