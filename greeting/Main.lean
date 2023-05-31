import «Greeting»
import Greeting.«Smile»
-- Placing guillemets around a name, as in «Greeting», allow it to contain
-- spaces or other characters that are normally not allowed in Lean names, and
-- it allows reserved keywords such as if or def to be used as ordinary names by
-- writing «if» or «def».

def main : IO Unit :=
  IO.println s!"Hello, {hello}, with {expression}!"

-- lake build
-- ./build/bin/greeting
-- Hello, world, with a big smile!