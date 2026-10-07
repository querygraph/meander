import Mathlib
import Arnold.TM.Defs

/-!
# The transfer matrix counts accepted action sequences

`tmCount m` processes all action sequences at once, layer by layer, merging equal states.
Here we prove it equals the number of action sequences (one action per point `0, …, m`) that
drive the machine from `init` to `final`. Merging is harmless: the number of accepted
continuations from a state depends only on the state.
-/

namespace Arnold.TM

/-- All action sequences for `f` consecutive points starting at `x`. -/
def sufWords (m : ℕ) : ℕ → ℕ → List (List (Bool × Bool))
  | 0, _ => [[]]
  | f + 1, x => (acts m x).flatMap fun a => (sufWords m f (x + 1)).map (a :: ·)

/-- Run the machine from state `s` at point `x` on an action sequence. -/
def runFrom (m : ℕ) : ℕ → St → List (Bool × Bool) → Option St
  | _, s, [] => some s
  | x, s, a :: w => (step m x s a).bind fun s' => runFrom m (x + 1) s' w

/-- The number of accepted continuations of length `f` from state `s` at point `x`. -/
def cntFrom (m f x : ℕ) (s : St) : ℕ :=
  (sufWords m f x).countP fun w => runFrom m x s w = some final

theorem cntFrom_zero (m x : ℕ) (s : St) : cntFrom m 0 x s = if s = final then 1 else 0 := by
  by_cases h : s = final <;> simp [cntFrom, sufWords, runFrom, h]

theorem cntFrom_succ (m f x : ℕ) (s : St) :
    cntFrom m (f + 1) x s = ((acts m x).map fun a =>
      match step m x s a with
      | none => 0
      | some s' => cntFrom m f (x + 1) s').sum := by
  unfold cntFrom
  rw [sufWords, List.countP_flatMap]
  congr 1
  apply List.map_congr_left
  intro a _
  simp only [Function.comp_apply, List.countP_map]
  cases h : step m x s a with
  | none => simp [Function.comp_def, runFrom, h]
  | some s' => simp [Function.comp_def, runFrom, h]

/-! ### Merging preserves weighted sums -/

/-- The weighted sum `Σ c * g s` of a layer. -/
def wsum (g : St → ℕ) (L : List (St × ℕ)) : ℕ := (L.map fun sc => sc.2 * g sc.1).sum

theorem mergeAdj_wsum (g : St → ℕ) (T : List (List ℕ × St × ℕ)) :
    wsum g (mergeAdj T) = (T.map fun t => t.2.2 * g t.2.1).sum := by
  induction T using mergeAdj.induct with
  | case1 => simp [mergeAdj, wsum]
  | case2 k s c => simp [mergeAdj, wsum]
  | case3 k c k' s' c' rest ih =>
    simp only [mergeAdj, ↓reduceIte, ih, List.map_cons, List.sum_cons]
    ring
  | case4 k s c k' s' c' rest hne ih =>
    simp only [mergeAdj, hne, ↓reduceIte, wsum, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]

theorem compress_wsum (g : St → ℕ) (L : List (St × ℕ)) : wsum g (compress L) = wsum g L := by
  unfold compress
  rw [mergeAdj_wsum, ((List.mergeSort_perm _ _).map _).sum_eq]
  simp [wsum, Function.comp_def]

theorem filterMap_wsum (m x c : ℕ) (s : St) (g : St → ℕ) (as : List (Bool × Bool)) :
    wsum g (as.filterMap fun a => (step m x s a).map fun s' => (s', c)) =
      c * (as.map fun a => match step m x s a with
        | none => 0
        | some s' => g s').sum := by
  induction as with
  | nil => simp [wsum]
  | cons a as ih =>
    cases h : step m x s a with
    | none => simp [h, ih]
    | some s' =>
      simp only [wsum, List.filterMap_cons, h, Option.map_some, List.map_cons, List.sum_cons,
        List.map, List.sum_cons] at ih ⊢
      rw [ih]
      ring

theorem expand_wsum (m x f : ℕ) (L : List (St × ℕ)) :
    wsum (cntFrom m f (x + 1)) (expand m x L) = wsum (cntFrom m (f + 1) x) L := by
  induction L with
  | nil => simp [expand, wsum]
  | cons sc L ih =>
    have h1 : expand m x (sc :: L) = ((acts m x).filterMap fun a =>
        (step m x sc.1 a).map fun s' => (s', sc.2)) ++ expand m x L := by
      simp [expand]
    rw [h1]
    simp only [wsum, List.map_append, List.sum_append] at ih ⊢
    rw [ih, ← wsum, filterMap_wsum]
    simp [cntFrom_succ]

/-- After `k` points, the layer's weighted count of accepted continuations is the total. -/
theorem layer_wsum (m : ℕ) : ∀ k ≤ m + 1,
    wsum (cntFrom m (m + 1 - k) k) (layer m k) = cntFrom m (m + 1) 0 init := by
  intro k
  induction k with
  | zero => intro _; simp [layer, wsum]
  | succ k ih =>
    intro hk
    rw [layer, compress_wsum, show m + 1 - (k + 1) = m - k by omega, expand_wsum,
      show m - k + 1 = m + 1 - k by omega, ih (by omega)]

/-- **The transfer matrix counts the accepted action sequences.** -/
theorem tmCount_eq_countP (m : ℕ) :
    tmCount m = (sufWords m (m + 1) 0).countP fun w => runFrom m 0 init w = some final := by
  have h := layer_wsum m (m + 1) le_rfl
  rw [Nat.sub_self] at h
  unfold tmCount
  rw [← cntFrom, ← h]
  unfold wsum
  congr 1
  apply List.map_congr_left
  intro sc _
  rw [cntFrom_zero]
  split <;> simp

end Arnold.TM
