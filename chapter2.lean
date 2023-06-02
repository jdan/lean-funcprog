def main₁ : IO Unit := IO.println "Hello, world!"

-- lean --run chapter2.lean
-- Hello, world!

def main₂ : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  stdout.putStrLn "How would you like to be addressed?"
  -- Using an arrow means that the value of the expression is an IO action that
  -- should be executed, with the result of the action saved in the local
  -- variable.
  let input ← stdin.getLine
  let name := input.dropRightWhile Char.isWhitespace

  stdout.putStrLn s!"Hello, {name}!"

-- #eval "Hello!!!".dropRightWhile (· == '!')

def nTimes (action : IO Unit) : Nat → IO Unit
  | 0 => pure ()
  | n + 1 => do
    action
    nTimes action n

def main₃ := nTimes (IO.println "Hello, world!") 3

def main₄ : IO Unit := do
  (← IO.getStdout).putStrLn "Hello, world!!"

-- Watch out for execution order with this convenience!
def getNumA : IO Nat := do
  (← IO.getStdout).putStrLn "A"
  pure 5

def getNumB : IO Nat := do
  (← IO.getStdout).putStrLn "B"
  pure 6

def main₅ : IO Unit := do
  let a : Nat := if (← getNumA) == 5 then 0 else (← getNumB)
  (← IO.getStdout).putStrLn s!"Is {a}!"
-- A
-- B
-- Is 0!

def main := main₅