import Arnold.Defs

/-- Print the number of ways a river can cross a road `n` times, for `n = 0, …, N`
(default `N = 16`). Each value is computed by `Arnold.meanderCount`, which is proved equal to
`Arnold.openMeanderCount`. -/
def main (args : List String) : IO Unit := do
  let N := (args.head? >>= String.toNat?).getD 16
  for n in List.range (N + 1) do
    IO.println s!"{n}\t{Arnold.meanderCount n}"
