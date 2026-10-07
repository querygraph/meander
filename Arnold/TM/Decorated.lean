import Arnold.TM.Count

/-!
# The decorated machine

To prove the transfer matrix right we run a richer machine alongside it. Each open arc also
remembers the point where it opened (`origin`) and the **actual piece of river** it leads into:
the list of points from its origin, through the points already scanned, to the origin of its
partner (or to the east end). The closed arcs are recorded too.

Forgetting the decorations gives back the transfer matrix exactly (`step_abs`). At the end, the
one remaining piece is the whole river.
-/

namespace Arnold.TM

/-- An open arc with its decorations. -/
structure Strand where
  ref : Ref
  origin : ℕ
  seg : List ℕ
  deriving Inhabited

/-- Decorated state: the stacks of open arcs, and the closed arcs `(left, right, side)`. -/
structure DSt where
  up : List Strand
  dn : List Strand
  arcs : List (ℕ × ℕ × Bool)

namespace DSt

def stk (D : DSt) (σ : Bool) : List Strand := if σ then D.up else D.dn

def setStk (D : DSt) (σ : Bool) (l : List Strand) : DSt :=
  if σ then { D with up := l } else { D with dn := l }

def push (D : DSt) (σ : Bool) (t : Strand) : DSt := D.setStk σ (D.stk σ ++ [t])

def pop (D : DSt) (σ : Bool) : DSt := D.setStk σ (D.stk σ).dropLast

def addArc (D : DSt) (a : ℕ × ℕ × Bool) : DSt := { D with arcs := a :: D.arcs }

/-- Make open arc `q` lead to `r`, extending its piece by `ext`. -/
def link (D : DSt) : Ref → Ref → List ℕ → DSt
  | .E, _, _ => D
  | .s σ i, r, ext =>
    D.setStk σ ((D.stk σ).set i ⟨r, ((D.stk σ).getD i default).origin,
      ((D.stk σ).getD i default).seg ++ ext⟩)

/-- Forget the decorations. -/
def abs (D : DSt) : St := ⟨D.up.map Strand.ref, D.dn.map Strand.ref⟩

/-- Look up an open arc. -/
def get? (D : DSt) : Ref → Option Strand
  | .E => none
  | .s σ i => (D.stk σ)[i]?

end DSt

/-- Decorated version of `openClose`. -/
def dOpenClose (D : DSt) (x : ℕ) (σ : Bool) : Option DSt :=
  match (D.stk (!σ)).getLast? with
  | none => none
  | some t => some ((((D.pop (!σ)).link t.ref (.s σ (D.stk σ).length) [x]).push σ
      ⟨t.ref, x, x :: t.seg⟩).addArc (t.origin, x, !σ))

/-- Decorated version of `step`. -/
def dstep (m x : ℕ) (D : DSt) (a : Bool × Bool) : Option DSt :=
  if x < m then
    match a with
    | (true, true) =>
      some ((D.push true ⟨.s false (D.stk false).length, x, [x]⟩).push false
        ⟨.s true (D.stk true).length, x, [x]⟩)
    | (true, false) => dOpenClose D x true
    | (false, true) => dOpenClose D x false
    | (false, false) =>
      match (D.stk true).getLast?, (D.stk false).getLast? with
      | some u, some l =>
        if u.ref = .s false ((D.stk false).length - 1) then none
        else some (((((D.pop true).pop false).link u.ref l.ref (x :: l.seg)).link l.ref u.ref
          (x :: u.seg)).addArc (u.origin, x, true) |>.addArc (l.origin, x, false))
      | _, _ => none
  else
    let e := m % 2 == 1
    if a.1 then some (D.push e ⟨.E, x, [x]⟩)
    else
      match (D.stk e).getLast? with
      | none => none
      | some t => if t.ref = .E then none
        else some (((D.pop e).link t.ref .E [x]).addArc (t.origin, x, e))

/-! ### Forgetting decorations -/

namespace DSt

@[simp] theorem abs_stk (D : DSt) (σ : Bool) : D.abs.stk σ = (D.stk σ).map Strand.ref := by
  cases σ <;> rfl

@[simp] theorem stk_setStk (D : DSt) (σ τ : Bool) (l : List Strand) :
    (D.setStk σ l).stk τ = if σ = τ then l else D.stk τ := by
  cases σ <;> cases τ <;> rfl

@[simp] theorem arcs_setStk (D : DSt) (σ : Bool) (l : List Strand) :
    (D.setStk σ l).arcs = D.arcs := by
  cases σ <;> rfl

theorem abs_setStk (D : DSt) (σ : Bool) (l : List Strand) :
    (D.setStk σ l).abs = D.abs.setStk σ (l.map Strand.ref) := by
  cases σ <;> rfl

theorem abs_push (D : DSt) (σ : Bool) (t : Strand) :
    (D.push σ t).abs = D.abs.push σ t.ref := by
  simp [push, St.push, abs_setStk]

theorem abs_pop (D : DSt) (σ : Bool) : (D.pop σ).abs = D.abs.pop σ := by
  simp [pop, St.pop, abs_setStk, List.map_dropLast]

theorem abs_addArc (D : DSt) (a : ℕ × ℕ × Bool) : (D.addArc a).abs = D.abs := rfl

theorem abs_link (D : DSt) (q r : Ref) (ext : List ℕ) :
    (D.link q r ext).abs = D.abs.setRef q r := by
  cases q with
  | E => rfl
  | s σ i => simp [link, St.setRef, abs_setStk, List.map_set]

end DSt

/-- The transfer matrix is the decorated machine with the decorations forgotten. -/
theorem step_abs (m x : ℕ) (D : DSt) (a : Bool × Bool) :
    step m x D.abs a = (dstep m x D a).map DSt.abs := by
  unfold step dstep
  split_ifs with hx
  · rcases a with ⟨_ | _, _ | _⟩
    · -- close both
      simp only [DSt.abs_stk, List.getLast?_map, List.length_map]
      cases hu : (D.stk true).getLast? <;> cases hl : (D.stk false).getLast? <;>
        simp only [Option.map_some, Option.map_none]
      rename_i u l
      split_ifs <;> simp [DSt.abs_link, DSt.abs_pop, DSt.abs_addArc]
    · -- close above, open below
      simp only [openClose, dOpenClose, DSt.abs_stk, List.getLast?_map, List.length_map]
      cases ht : (D.stk true).getLast? <;> simp [ht, DSt.abs_push, DSt.abs_link, DSt.abs_pop,
        DSt.abs_addArc]
    · simp only [openClose, dOpenClose, DSt.abs_stk, List.getLast?_map, List.length_map]
      cases ht : (D.stk false).getLast? <;> simp [ht, DSt.abs_push, DSt.abs_link, DSt.abs_pop,
        DSt.abs_addArc]
    · simp [DSt.abs_push]
  · simp [DSt.abs_push]
  · simp only [DSt.abs_stk, List.getLast?_map]
    cases ht : (D.stk (m % 2 == 1)).getLast? with
    | none => simp
    | some t =>
      simp only [Option.map_some]
      split_ifs <;> simp [DSt.abs_link, DSt.abs_pop, DSt.abs_addArc]

end Arnold.TM
