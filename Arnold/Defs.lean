/-!
# Core definitions

This file uses only core Lean (no Mathlib), so the search `meanderCount` can be compiled into
a fast standalone executable (see `Main.lean`). The problem statement in terms of permutations
is in `Arnold.Basic`, and the proof that the search is correct is in `Arnold.Fast`.
-/

namespace Arnold

/-- The chords `{a, b}` and `{c, d}` (with four distinct endpoints on a line) cross exactly
when one of `c`, `d` lies strictly between `a` and `b` and the other does not. -/
def Interleave (a b c d : Nat) : Prop :=
  ¬ ((min a b < c ∧ c < max a b) ↔ (min a b < d ∧ d < max a b))

instance (a b c d : Nat) : Decidable (Interleave a b c d) := by
  unfold Interleave; infer_instance

/-- Given the boundary points `P 0, P 1, …` visited by a river, with arc `k` joining `P k` to
`P (k+1)` and arcs alternating between the two half-planes: no two of the first `L` arcs on the
same side cross. -/
def NoCross (P : Nat → Nat) (L : Nat) : Prop :=
  ∀ k < L, ∀ j < k, j % 2 = k % 2 → ¬ Interleave (P j) (P (j + 1)) (P k) (P (k + 1))

instance (P : Nat → Nat) (L : Nat) : Decidable (NoCross P L) := by
  unfold NoCross; infer_instance

/-! ### The search -/

/-- Boundary point `k` of a river whose crossing order is the list `l`: the south end `n+1`,
then the entries of `l`, then the east end `n` (also used past the end of `l`). -/
def lpt (n : Nat) (l : List Nat) (k : Nat) : Nat :=
  if k = 0 then n + 1 else l.getD (k - 1) n

/-- Arc `t` (joining points `t` and `t+1`) crosses no earlier arc on the same side. -/
def StepOK (n : Nat) (q : List Nat) (t : Nat) : Prop :=
  ∀ j < t, j % 2 = t % 2 →
    ¬ Interleave (lpt n q j) (lpt n q (j + 1)) (lpt n q t) (lpt n q (t + 1))

instance (n : Nat) (q : List Nat) (t : Nat) : Decidable (StepOK n q t) := by
  unfold StepOK; infer_instance

/-! ### The parity test

Take an arc `j` that is already drawn, on side `s = j % 2`, with ends `a < b`. Every later
arc on side `s` has both ends strictly inside `(a, b)` or both outside, since it may not cross
arc `j`. So the side-`s` arc ends still to come inside `(a, b)` pair up, and there is an even
number of them. Those ends are: every unvisited bridge in `(a, b)` (each bridge eventually gets
one arc on each side); the current point, if the next arc is on side `s`; and the east end `n`,
if the final arc `n` is on side `s`. If the count is odd, the partial river cannot be finished.
`Arnold.parityOK_of_noCross` proves this. -/

/-- `x` lies strictly between the ends of arc `j` of the path `P`. -/
def inArc (P : Nat → Nat) (j x : Nat) : Bool :=
  decide (min (P j) (P (j + 1)) < x ∧ x < max (P j) (P (j + 1)))

/-- The number of arc ends still to come inside arc `j`, on its side of the road, when the path
`P` has drawn `t` arcs and the bridges in `r` are unvisited. -/
def futureEnds (n : Nat) (P : Nat → Nat) (t : Nat) (r : List Nat) (j : Nat) : Nat :=
  r.countP (inArc P j) + (if t % 2 = j % 2 ∧ inArc P j (P t) = true then 1 else 0) +
    (if n % 2 = j % 2 ∧ inArc P j n = true then 1 else 0)

/-- Every arc drawn so far encloses an even number of arc ends still to come. -/
def ParityOK (n : Nat) (q r : List Nat) : Prop :=
  ∀ j < q.length, futureEnds n (lpt n q) q.length r j % 2 = 0

instance (n : Nat) (q r : List Nat) : Decidable (ParityOK n q r) := by
  unfold ParityOK; infer_instance

/-- Depth-first search. `p` is the crossing order chosen so far, `rem` holds the unused bridges,
and `k = rem.length` is the recursion fuel. A bridge `x` is tried next only if the arc it
creates crosses no earlier arc and the parity test still passes. When `rem` is empty, the
final arc to the east is checked. -/
def dfs (n : Nat) : Nat → List Nat → List Nat → Nat
  | 0, p, _ => if StepOK n p p.length then 1 else 0
  | k + 1, p, rem => (rem.map fun x =>
      if StepOK n (p ++ [x]) p.length ∧ ParityOK n (p ++ [x]) (rem.erase x) then
        dfs n k (p ++ [x]) (rem.erase x)
      else 0).sum

/-! ### Compiled implementation

The compiler runs `dfs` through the array-based `dfsArr` below. `@[csimp]` makes it do that
only because `dfs_eq_dfsFast` proves the two functions equal, so the speed-up changes nothing
about what is computed. -/

/-- `allLt f t` checks `f j` for every `j < t`. -/
def allLt (f : Nat → Bool) : Nat → Bool
  | 0 => true
  | t + 1 => allLt f t && f t

theorem allLt_iff (f : Nat → Bool) (t : Nat) : allLt f t = true ↔ ∀ j < t, f j = true := by
  induction t with
  | zero => simp [allLt]
  | succ t ih =>
    simp only [allLt, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h, ht⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h' | rfl
      · exact h j h'
      · exact ht
    · intro h
      exact ⟨fun j hj => h j (by omega), h t (by omega)⟩

/-- `lpt` on an array, with constant-time lookup. -/
def apt (n : Nat) (a : Array Nat) (k : Nat) : Nat :=
  if k = 0 then n + 1 else a.getD (k - 1) n

/-- `StepOK` as a Boolean test on an array. -/
def stepOKb (n : Nat) (a : Array Nat) (t : Nat) : Bool :=
  let c := apt n a t
  let d := apt n a (t + 1)
  allLt (fun j => j % 2 != t % 2 || !decide (Interleave (apt n a j) (apt n a (j + 1)) c d)) t

/-- `ParityOK` as a Boolean test on an array. -/
def parityOKb (n : Nat) (a : Array Nat) (r : List Nat) : Bool :=
  allLt (fun j => futureEnds n (apt n a) a.size r j % 2 == 0) a.size

def dfsArr (n : Nat) : Nat → Array Nat → List Nat → Nat
  | 0, a, _ => if stepOKb n a a.size then 1 else 0
  | k + 1, a, rem => (rem.map fun x =>
      if stepOKb n (a.push x) a.size && parityOKb n (a.push x) (rem.erase x) then
        dfsArr n k (a.push x) (rem.erase x)
      else 0).sum

def dfsFast (n k : Nat) (p rem : List Nat) : Nat := dfsArr n k p.toArray rem

theorem apt_toArray (n : Nat) (p : List Nat) (k : Nat) : apt n p.toArray k = lpt n p k := by
  unfold apt lpt
  split
  · rfl
  · simp [Array.getD, List.getD_eq_getElem?_getD]
    split <;> simp_all

theorem stepOKb_toArray (n : Nat) (p : List Nat) (t : Nat) :
    stepOKb n p.toArray t = decide (StepOK n p t) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, stepOKb, allLt_iff]
  simp only [apt_toArray, Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true',
    decide_eq_false_iff_not, StepOK]
  constructor
  · intro h j hj hpar
    exact (h j hj).resolve_left (by simpa using hpar)
  · intro h j hj
    by_cases hpar : j % 2 = t % 2
    · exact Or.inr (h j hj hpar)
    · exact Or.inl hpar

theorem parityOKb_toArray (n : Nat) (p r : List Nat) :
    parityOKb n p.toArray r = decide (ParityOK n p r) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, parityOKb, allLt_iff,
    show apt n p.toArray = lpt n p from funext (apt_toArray n p), List.size_toArray]
  simp only [beq_iff_eq, ParityOK]

@[csimp] theorem dfs_eq_dfsFast : @dfs = @dfsFast := by
  funext n k
  induction k with
  | zero => funext p rem; simp [dfs, dfsFast, dfsArr, stepOKb_toArray]
  | succ k ih =>
    funext p rem
    simp only [dfs, dfsFast, dfsArr, List.size_toArray, List.push_toArray, stepOKb_toArray,
      parityOKb_toArray]
    congr 1
    apply List.map_congr_left
    intro x _
    by_cases h : StepOK n (p ++ [x]) p.length ∧ ParityOK n (p ++ [x]) (rem.erase x) <;>
      simp [h, ih, dfsFast]

/-- **Fast meander count**: the number of ways a river can cross a road `n` times.
(Declared after `dfs_eq_dfsFast`, so the compiled code uses the array version.) -/
def meanderCount (n : Nat) : Nat := dfs n n [] (List.range n)

end Arnold
