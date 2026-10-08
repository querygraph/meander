import Arnold.TM.Main

/-!
# Meet in the middle: every value from reusable layers

The transfer matrix processes the points of the road one at a time. A step at a bridge does not
depend on the number of crossings `m` at all: only the last point, the east end, does, and only
through the side `m % 2` of its arc. Two consequences make the computation reusable across `n`.

* The *forward layers* `flayer k`: the states after `k` bridges, with the number of action
  sequences reaching each, no pruning. They mention no target `n`, so one computation serves
  every `n ≥ k`.
* The *backward counts* `finish p r s`: the number of ways to finish from state `s` with `r` more
  bridges and then the east end on side `p`. They depend only on `p` and `r`.

`meet` proves that for every split `n = k + r`,
`openMeanderCount n = Σ_s (flayer k)(s) · finish (n % 2) r s`.
Every split gives the same value, so two splits check each other, and a value for `n + 1` needs
one more forward or backward layer, not a new sweep. The fast programs in `rust/` and `oxcaml/`
store these layers on disk and compute the backward layers by inverse transitions.
-/

set_option linter.deprecated false

namespace Arnold.TM

/-- The step at a bridge; `step m x` is this step whenever `x < m`. -/
def bstep (s : St) (a : Bool × Bool) : Option St := step 1 0 s a

/-- The actions at a bridge. -/
def bacts : List (Bool × Bool) := acts 1 0

/-- The step at the east end, whose arc is above the road (`p = true`) or below. -/
def estep (p : Bool) (s : St) (a : Bool × Bool) : Option St :=
  step (if p then 1 else 0) (if p then 1 else 0) s a

/-- The actions at the east end. -/
def eacts : List (Bool × Bool) := acts 0 0

theorem step_of_lt {m x : ℕ} (h : x < m) : step m x = bstep := by
  funext s a
  simp [bstep, step, h]

theorem acts_of_lt {m x : ℕ} (h : x < m) : acts m x = bacts := by
  simp [bacts, acts, h]

theorem step_self (m : ℕ) : step m m = estep (m % 2 == 1) := by
  funext s a
  unfold estep step
  cases m % 2 == 1 <;> simp

theorem acts_self (m : ℕ) : acts m m = eacts := by
  simp [eacts, acts]

/-- The number of ways to finish from `s` with `r` more bridges and then the east end on side
`p`: action sequences that drive `s` to `final`. -/
def finish (p : Bool) : ℕ → St → ℕ
  | 0, s => (eacts.map fun a =>
      match estep p s a with
      | none => 0
      | some s' => if s' = final then 1 else 0).sum
  | r + 1, s => (bacts.map fun a =>
      match bstep s a with
      | none => 0
      | some s' => finish p r s').sum

/-- The completions counted by `cntFrom` depend only on how many bridges remain and on the side
of the east end. -/
theorem cntFrom_eq_finish : ∀ (r x m : ℕ) (s : St), x + r = m →
    cntFrom m (r + 1) x s = finish (m % 2 == 1) r s := by
  intro r
  induction r with
  | zero =>
    intro x m s h
    obtain rfl : m = x := by omega
    rw [cntFrom_succ, acts_self, step_self]
    unfold finish
    congr 1
    apply List.map_congr_left
    intro a _
    cases estep (m % 2 == 1) s a with
    | none => rfl
    | some s' => simp [cntFrom_zero]
  | succ r ih =>
    intro x m s h
    rw [cntFrom_succ, acts_of_lt (by omega : x < m), step_of_lt (by omega : x < m)]
    unfold finish
    congr 1
    apply List.map_congr_left
    intro a _
    cases bstep s a with
    | none => rfl
    | some s' => exact ih (x + 1) m s' (by omega)

/-- All bridge successors of a layer, keeping multiplicities. -/
def fexpand (L : List (St × ℕ)) : List (St × ℕ) :=
  L.flatMap fun sc => bacts.filterMap fun a => (bstep sc.1 a).map fun s' => (s', sc.2)

/-- The forward layer after `k` bridges, merged by `comp` and not pruned: it mentions no target,
so it serves every `n ≥ k`. -/
def flayer (comp : List (St × ℕ) → List (St × ℕ)) : ℕ → List (St × ℕ)
  | 0 => [(init, 1)]
  | k + 1 => comp (fexpand (flayer comp k))

theorem fexpand_eq {m x : ℕ} (h : x < m) (L : List (St × ℕ)) : fexpand L = expand m x L := by
  unfold fexpand expand
  rw [acts_of_lt h, step_of_lt h]

theorem flayer_wsum (comp : List (St × ℕ) → List (St × ℕ))
    (hcomp : ∀ g L, wsum g (comp L) = wsum g L) (m : ℕ) : ∀ k ≤ m,
    wsum (cntFrom m (m + 1 - k) k) (flayer comp k) = cntFrom m (m + 1) 0 init := by
  intro k
  induction k with
  | zero => intro _; simp [flayer, wsum]
  | succ k ih =>
    intro hk
    rw [flayer, hcomp, fexpand_eq (by omega : k < m), show m + 1 - (k + 1) = m - k by omega,
      expand_wsum, show m - k + 1 = m + 1 - k by omega, ih (by omega)]

theorem cntFrom_init (m : ℕ) : cntFrom m (m + 1) 0 init = openMeanderCount m := by
  rw [← tmCountWith_eq compressK compressK_wsum m, tmCountWith_eq_countP compressK compressK_wsum m]
  rfl

/-- **Meet in the middle.** For every split `n = k + r`, the number of meanders with `n`
crossings is the forward layer after `k` bridges, weighted by the ways to finish with `r` more. -/
theorem meet (comp : List (St × ℕ) → List (St × ℕ))
    (hcomp : ∀ g L, wsum g (comp L) = wsum g L) (k r : ℕ) :
    openMeanderCount (k + r) = wsum (finish ((k + r) % 2 == 1) r) (flayer comp k) := by
  have h := flayer_wsum comp hcomp (k + r) k (by omega)
  rw [show k + r + 1 - k = r + 1 by omega] at h
  rw [← cntFrom_init, ← h]
  unfold wsum
  congr 1
  apply List.map_congr_left
  intro sc _
  rw [cntFrom_eq_finish r k (k + r) sc.1 rfl]

/-- Every split computes the same number: the splits check each other. -/
theorem meet_split (comp : List (St × ℕ) → List (St × ℕ))
    (hcomp : ∀ g L, wsum g (comp L) = wsum g L) {n k : ℕ} (hk : k ≤ n) :
    openMeanderCount n = wsum (finish (n % 2 == 1) (n - k)) (flayer comp k) := by
  have := meet comp hcomp k (n - k)
  rwa [show k + (n - k) = n by omega] at this

/-- A(0), …, A(10) from the balanced split `n = ⌈n/2⌉ + ⌊n/2⌋`, checked by the kernel. -/
theorem meet_values :
    (List.range 11).map
        (fun n => wsum (finish (n % 2 == 1) (n / 2)) (flayer compressK (n - n / 2))) =
      [1, 1, 1, 2, 3, 8, 14, 42, 81, 262, 538] := by
  decide +kernel

theorem openMeanderCount_values_meet :
    (List.range 11).map openMeanderCount = [1, 1, 1, 2, 3, 8, 14, 42, 81, 262, 538] := by
  rw [← meet_values]
  apply List.map_congr_left
  intro n _
  have h := meet_split compressK compressK_wsum (show n - n / 2 ≤ n by omega)
  rwa [show n - (n - n / 2) = n / 2 by omega] at h

end Arnold.TM
