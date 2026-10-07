import Arnold.TM.Main

/-!
# Certified values

All values come from the transfer matrix, which `Arnold.TM.tmCount_eq` and
`Arnold.TM.tmCountK_eq` prove equal to `openMeanderCount`. Closed meanders follow from
`closedMeanderCount_eq`.
-/

namespace Arnold

open TM

/-- Arnold's numbers for `n = 0, …, 13`, **checked by the Lean kernel**. -/
theorem openMeanderCount_values :
    (List.range 14).map openMeanderCount =
      [1, 1, 1, 2, 3, 8, 14, 42, 81, 262, 538, 1828, 3926, 13820] := by
  rw [show openMeanderCount = tmCountK from funext fun m => (tmCountK_eq m).symm]
  decide +kernel

/-- Closed meanders of orders `1, …, 7`, **checked by the Lean kernel** (via
`closed(n) = open(2n - 1)` and the table above). -/
theorem closedMeanderCount_values :
    (List.range' 1 7).map closedMeanderCount = [1, 2, 8, 42, 262, 1828, 13820] := by
  have hv : ∀ i, i < 14 → openMeanderCount i =
      ([1, 1, 1, 2, 3, 8, 14, 42, 81, 262, 538, 1828, 3926, 13820] : List ℕ).getD i 0 := by
    intro i hi
    have := congrArg (fun l => l.getD i 0) openMeanderCount_values
    simpa [List.getD_eq_getElem?_getD, hi] using this
  change [closedMeanderCount 1, closedMeanderCount 2, closedMeanderCount 3,
    closedMeanderCount 4, closedMeanderCount 5, closedMeanderCount 6, closedMeanderCount 7] = _
  rw [closedMeanderCount_eq 1 (by omega), closedMeanderCount_eq 2 (by omega),
    closedMeanderCount_eq 3 (by omega), closedMeanderCount_eq 4 (by omega),
    closedMeanderCount_eq 5 (by omega), closedMeanderCount_eq 6 (by omega),
    closedMeanderCount_eq 7 (by omega)]
  simp only [Nat.reduceMul, Nat.reduceSub]
  rw [hv 1 (by omega), hv 3 (by omega), hv 5 (by omega), hv 7 (by omega), hv 9 (by omega),
    hv 11 (by omega), hv 13 (by omega)]
  rfl

set_option linter.style.native false in
/-- Arnold's numbers for `n = 0, …, 24`. These are computed by the Lean interpreter
(`native_decide`), so they trust the compiler as well as the kernel. -/
theorem openMeanderCount_values_native :
    (List.range 25).map openMeanderCount =
      [1, 1, 1, 2, 3, 8, 14, 42, 81, 262, 538, 1828, 3926, 13820, 30694, 110954, 252939,
        933458, 2172830, 8152860, 19304190, 73424650, 176343390, 678390116, 1649008456] := by
  rw [show openMeanderCount = tmCount from funext fun m => (tmCount_eq m).symm]
  native_decide

end Arnold
