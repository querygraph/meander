import Mathlib
import Arnold.Defs

/-!
# Arnold's meander problem

V. I. Arnold (1988): *in how many ways can a river cross a straight road `n` times?*

## Combinatorial model

The road is a horizontal line. Its `n` bridges (crossings) are labelled `0, …, n-1` from
west to east. The river comes in from infinity in the **south**, crosses the road `n` times,
and leaves to infinity in the **east**, never crossing itself. Two meanders are the same if
one can be deformed into the other without changing the crossings.

Such a curve is described by the order in which it visits the bridges: a permutation
`σ : Equiv.Perm (Fin n)`, where the river's `i`-th crossing is at bridge `σ i`. Between
crossings, the river runs along an arc in the lower half-plane, then the upper one, and so on
(it starts in the south, so the first arc is in the lower half-plane).

Compactify each half-plane to a disk. Its boundary is the road plus the point at infinity.
The two ends of the river touch infinity at two boundary points east of every bridge:
* `n`: the east end, where the river goes, and
* `n + 1`: the south end, where the river comes from.
(Going counterclockwise around the lower half-disk, the boundary passes the bridges, then
east, then south.) So the river's path is the sequence of boundary points
`n+1, σ 0, σ 1, …, σ (n-1), n`, and arc `k` joins points `k` and `k+1` of this sequence.
Even arcs lie in the lower half-plane and odd arcs in the upper one.

Jordan curve theory says the river has no self-intersections exactly when no two arcs in the
same half-plane cross, and two chords of a disk cross exactly when their endpoints alternate
around the boundary. `IsMeander` is that condition, and `openMeanderCount n` is the number of
permutations that satisfy it.

No closed formula for these numbers is known. Arnold's question is open, and the values are
known only by computer enumeration (OEIS A005316). This file states the problem precisely,
defines closed meanders (A005315), and proves general facts (at least one meander for every
`n`, and at most `n!`). See also:
* `Arnold.ClosedOpen`: `closed(n) = open(2n - 1)` for every `n ≥ 1`, via an explicit bijection;
* `Arnold.Fast`: a pruned search `meanderCount`, proved equal to `openMeanderCount`, and the
  values it certifies.
-/

namespace Arnold

/-! ### Open meanders (Arnold's river) -/

/-- The `k`-th boundary point on the river's path (`k = 0, …, n+1`): first the south end
`n+1`, then the bridges in the order the river crosses them, then the east end `n`. -/
def pathPt {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ) : ℕ :=
  if k = 0 then n + 1 else if h : k - 1 < n then (σ ⟨k - 1, h⟩ : ℕ) else n

/-- `σ` describes an open meander when no two arcs in the same half-plane cross.
Arc `k` (`k = 0, …, n`) joins `pathPt σ k` to `pathPt σ (k+1)`. -/
def IsMeander {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  NoCross (pathPt σ) (n + 1)

instance {n : ℕ} (σ : Equiv.Perm (Fin n)) : Decidable (IsMeander σ) := by
  unfold IsMeander; infer_instance

/-- **Arnold's number**: the number of ways a river can cross a straight road `n` times. -/
def openMeanderCount (n : ℕ) : ℕ :=
  Fintype.card {σ : Equiv.Perm (Fin n) // IsMeander σ}

/-! #### General facts -/

/-- The river that zig-zags straight east across bridges `0, 1, …, n-1` is a meander. -/
theorem isMeander_refl (n : ℕ) : IsMeander (Equiv.refl (Fin n)) := by
  intro k hk j hjk hpar
  have hpt : ∀ m : ℕ, 1 ≤ m → m ≤ n + 1 →
      pathPt (Equiv.refl (Fin n)) m = m - 1 := by
    intro m h1 h2
    unfold pathPt
    simp only [show m ≠ 0 by omega, ↓reduceIte]
    split_ifs with h
    · rfl
    · omega
  -- `k ≥ 2`, so arc `k` is the arc `(k-1, k)` between neighbouring points.
  have hk2 : 2 ≤ k := by omega
  rw [hpt (k + 1) (by omega) (by omega), hpt k (by omega) (by omega)]
  unfold Interleave
  by_cases hj0 : j = 0
  · -- Arc 0 is `(n+1, 0)`. It encloses every other lower arc.
    have h0 : pathPt (Equiv.refl (Fin n)) j = n + 1 := by simp [pathPt, hj0]
    rw [h0, hpt (j + 1) (by omega) (by omega)]
    omega
  · -- Arc `j` is `(j-1, j)`. No point lies strictly between its endpoints.
    rw [hpt j (by omega) (by omega), hpt (j + 1) (by omega) (by omega)]
    omega

/-- For every `n`, a river can cross the road `n` times. -/
theorem openMeanderCount_pos (n : ℕ) : 0 < openMeanderCount n :=
  Fintype.card_pos_iff.mpr ⟨⟨Equiv.refl _, isMeander_refl n⟩⟩

/-- There are at most `n!` meanders with `n` crossings, one per crossing order. -/
theorem openMeanderCount_le_factorial (n : ℕ) : openMeanderCount n ≤ n.factorial := by
  unfold openMeanderCount
  calc _ ≤ Fintype.card (Equiv.Perm (Fin n)) := Fintype.card_subtype_le _
    _ = n.factorial := by rw [Fintype.card_perm, Fintype.card_fin]

/-! #### Certified values (OEIS A005316) -/

theorem openMeanderCount_0 : openMeanderCount 0 = 1 := by decide
theorem openMeanderCount_1 : openMeanderCount 1 = 1 := by decide
theorem openMeanderCount_2 : openMeanderCount 2 = 1 := by decide
theorem openMeanderCount_3 : openMeanderCount 3 = 2 := by decide

/-! ### Closed meanders -/

/-- The `k`-th bridge (indices taken mod `2n`) visited by a closed river. -/
def closedPt {n : ℕ} (σ : Equiv.Perm (Fin (2 * n))) (k : ℕ) : ℕ :=
  if h : 0 < 2 * n then (σ ⟨k % (2 * n), Nat.mod_lt _ h⟩ : ℕ) else 0

/-- A **closed meander** of order `n` is a closed river crossing the road `2n` times. To count
each curve once, fix where it starts and which way it goes: start at the westmost bridge `0`
and leave it into the upper half-plane. The river then visits bridges `σ 0 = 0, σ 1, …`, and
arc `k` joins `σ k` to `σ (k+1 mod 2n)`. Even arcs are upper and odd arcs are lower. -/
def IsClosedMeander {n : ℕ} (σ : Equiv.Perm (Fin (2 * n))) : Prop :=
  (∀ h : 0 < 2 * n, σ ⟨0, h⟩ = ⟨0, h⟩) ∧ NoCross (closedPt σ) (2 * n)

instance {n : ℕ} (σ : Equiv.Perm (Fin (2 * n))) : Decidable (IsClosedMeander σ) := by
  unfold IsClosedMeander; infer_instance

/-- The number of closed meanders of order `n` (OEIS A005315). -/
def closedMeanderCount (n : ℕ) : ℕ :=
  Fintype.card {σ : Equiv.Perm (Fin (2 * n)) // IsClosedMeander σ}

end Arnold
