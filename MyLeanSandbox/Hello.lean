--def main : IO Unit :=
 -- IO.println "Hello, world!"

--IO Unit : Type
--IO : Type → Type

-- ? : IO α

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  stdout.putStrLn "How would you like to be addressed?"
  let input ← stdin.getLine
  let name := input.dropRightWhile Char.isWhitespace

  stdout.putStrLn s!"Hello, {name}!"
