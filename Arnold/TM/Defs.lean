/-!
# The transfer matrix: definitions

This file uses only core Lean, so it compiles into the `meanders` executable.

Scan the points of the road from west to east: the bridges `0, …, m-1`, then the east end
`E = m` (one arc, on side `m % 2`), then the south end `S = m+1` (one arc, below). Each point
**opens** or **closes** its arc on each of its sides. Since arcs on one side never cross, the
arcs still open at a cut form a stack on each side, and a closing point always closes the top
one.

Between the cut and the west end, the river is cut into pieces, each joining two open arcs (or
an open arc and the east end). The state records, for each open arc, which other open arc (or
`E`) its piece leads to. Joining the two ends of one piece would close a loop, so the machine
rejects it. A whole river is accepted when, after `E`, only one arc is open: below the road,
with its piece leading to `E`, ready for `S` to close it.

`Arnold.TM.tmCount_eq` proves that `tmCount m` equals `openMeanderCount m`.
-/

namespace Arnold.TM

/-- A reference to an open arc: the east end `E`, or position `i` (counting from the bottom)
in the stack of side `σ` (`true` = above the road, `false` = below). -/
inductive Ref where
  | E
  | s (σ : Bool) (i : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- The state at a cut: for each open arc, in stack order, where its piece of river leads. -/
structure St where
  up : List Ref
  dn : List Ref
  deriving DecidableEq, Repr, Inhabited

namespace St

def stk (s : St) (σ : Bool) : List Ref := if σ then s.up else s.dn

def setStk (s : St) (σ : Bool) (l : List Ref) : St :=
  if σ then { s with up := l } else { s with dn := l }

def push (s : St) (σ : Bool) (r : Ref) : St := s.setStk σ (s.stk σ ++ [r])

def pop (s : St) (σ : Bool) : St := s.setStk σ (s.stk σ).dropLast

/-- Make the open arc `p` lead to `r`. -/
def setRef (s : St) : Ref → Ref → St
  | .E, _ => s
  | .s σ i, r => s.setStk σ ((s.stk σ).set i r)

end St

/-- Open an arc on side `σ` and close the top arc on side `!σ`: the new arc continues the closed
arc's piece. -/
def openClose (s : St) (σ : Bool) : Option St :=
  match (s.stk (!σ)).getLast? with
  | none => none
  | some p => some (((s.pop (!σ)).setRef p (.s σ (s.stk σ).length)).push σ p)

/-- Process point `x` with action `a = (above, below)` (`true` = open). Point `x = m` is the
east end, which uses only its side `m % 2` and reads `a.1`. -/
def step (m x : Nat) (s : St) (a : Bool × Bool) : Option St :=
  if x < m then
    match a with
    | (true, true) =>
      some ((s.push true (.s false (s.stk false).length)).push false
        (.s true (s.stk true).length))
    | (true, false) => openClose s true
    | (false, true) => openClose s false
    | (false, false) =>
      match (s.stk true).getLast?, (s.stk false).getLast? with
      | some pu, some pl =>
        if pu = .s false ((s.stk false).length - 1) then none
        else some ((((s.pop true).pop false).setRef pu pl).setRef pl pu)
      | _, _ => none
  else
    let e := m % 2 == 1
    if a.1 then some (s.push e .E)
    else
      match (s.stk e).getLast? with
      | none => none
      | some p => if p = .E then none else some ((s.pop e).setRef p .E)

/-- The actions available at point `x`: both sides free at a bridge, one side at `E`. -/
def acts (m x : Nat) : List (Bool × Bool) :=
  if x < m then [(true, true), (true, false), (false, true), (false, false)]
  else [(true, true), (false, false)]

def init : St := ⟨[], []⟩

/-- After `E`: one arc open, below the road, leading to `E`. Then `S` closes it. -/
def final : St := ⟨[], [.E]⟩

/-! ### Counting with merged states -/

def refCode : Ref → Nat
  | .E => 0
  | .s false i => 2 * i + 1
  | .s true i => 2 * i + 2

/-- A sort key for states. Any key works for correctness; a good one makes equal states adjacent. -/
def key (s : St) : List Nat := s.up.length :: (s.up.map refCode ++ s.dn.map refCode)

def lexLe : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: l, b :: l' => a < b || (a == b && lexLe l l')

/-- Add up the counts of adjacent equal states. -/
def mergeAdj : List (List Nat × St × Nat) → List (St × Nat)
  | [] => []
  | [(_, s, c)] => [(s, c)]
  | (k, s, c) :: (k', s', c') :: rest =>
    if s = s' then mergeAdj ((k, s, c + c') :: rest) else (s, c) :: mergeAdj ((k', s', c') :: rest)

/-- Sort by key and merge equal neighbours. -/
def compress (L : List (St × Nat)) : List (St × Nat) :=
  mergeAdj ((L.map fun sc => (key sc.1, sc.1, sc.2)).mergeSort fun a b => lexLe a.1 b.1)

/-- All successors of a layer at point `x`, keeping multiplicities. -/
def expand (m x : Nat) (L : List (St × Nat)) : List (St × Nat) :=
  L.flatMap fun sc => (acts m x).filterMap fun a => (step m x sc.1 a).map fun s' => (s', sc.2)

/-- The layer after processing points `0, …, k-1`. -/
def layer (m : Nat) : Nat → List (St × Nat)
  | 0 => [(init, 1)]
  | k + 1 => compress (expand m k (layer m k))

/-- **Transfer-matrix meander count.** -/
def tmCount (m : Nat) : Nat :=
  ((layer m (m + 1)).map fun sc => if sc.1 = final then sc.2 else 0).sum

end Arnold.TM
