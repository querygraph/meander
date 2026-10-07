import Arnold.TM.Defs
def main (args : List String) : IO Unit := do
  let N := (args.head? >>= String.toNat?).getD 20
  for n in List.range (N + 1) do
    IO.println s!"{n}\t{Arnold.TM.tmCount n}"
