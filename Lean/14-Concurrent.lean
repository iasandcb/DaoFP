namespace DaoFP.Concurrent

-- Mocking Concurrently to represent the concept in Lean
structure Concurrently (α : Type) where
  run : IO α

instance : Functor Concurrently where
  map f c := { run := f <$> c.run }

instance : Applicative Concurrently where
  pure a := { run := pure a }
  seq cf ca := { run := do
    -- In a real concurrent implementation, these would be spawned as Tasks
    let f ← cf.run
    let a ← ca.run
    pure (f a) }

def fileChars (path : String) : IO Int := do
  let content ← IO.FS.readFile path
  pure content.length

def f : Concurrently Int :=
  (fun m n => m + n) <$> { run := fileChars "Haskell/1-Types.hs" }
                     <*> { run := fileChars "Haskell/2-Composition.hs" }

-- Lean's do-notation is primarily monadic, but we can use applicative operators
def f_prime : Concurrently Int :=
  (fun m n => m + n) 
    <$> { run := fileChars "Haskell/1-Types.hs" } 
    <*> { run := fileChars "Haskell/2-Composition.hs" }

def prompt (str : String) : IO String := do
  IO.println str
  let input ← (← IO.getStdin).getLine
  pure input.trim

def greeting (s1 s2 : String) : String :=
  s!"Hi {s1} {s2}!"

def getNamesAndGreet : IO String :=
  greeting <$> prompt "First name: " <*> prompt "Last name: "

end DaoFP.Concurrent
