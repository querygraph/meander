import Arnold.TM.Defs

/-- Print the number of ways a river can cross a road `n` times, for `n = 0, …, N`
(default `N = 30`). Each value is computed by `Arnold.TM.tmCount`, the transfer matrix, which
`Arnold.TM.tmCount_eq` proves equal to `Arnold.openMeanderCount`. -/
def main (args : List String) : IO Unit := do
  let N := (args.head? >>= String.toNat?).getD 30
  for n in List.range (N + 1) do
    IO.println s!"{n}\t{Arnold.TM.tmCount n}"
