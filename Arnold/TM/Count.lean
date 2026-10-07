import Mathlib
import Arnold.TM.Defs

/-!
# The transfer matrix counts accepted action sequences

`tmCount m` processes all action sequences at once, layer by layer, merging equal states.
Here we prove it equals the number of action sequences (one action per point `0, …, m`) that
drive the machine from `init` to `final`. Merging is harmless: the number of accepted
continuations from a state depends only on the state.
-/

set_option linter.deprecated false

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

/-! ### Dropping states that cannot be finished -/

theorem length_setRef (s : St) (p r : Ref) (σ : Bool) :
    ((s.setRef p r).stk σ).length = (s.stk σ).length := by
  cases p with
  | E => rfl
  | s τ i => cases τ <;> cases σ <;> simp [St.setRef, St.setStk, St.stk]

theorem stk_push_len (s : St) (σ τ : Bool) (r : Ref) :
    ((s.push σ r).stk τ).length = (s.stk τ).length + (if σ = τ then 1 else 0) := by
  cases σ <;> cases τ <;> simp [St.push, St.setStk, St.stk]

theorem stk_pop_len (s : St) (σ τ : Bool) :
    ((s.pop σ).stk τ).length = (s.stk τ).length - (if σ = τ then 1 else 0) := by
  cases σ <;> cases τ <;> simp [St.pop, St.setStk, St.stk]

theorem len_pos_of_getLast {l : List Ref} {p : Ref} (h : l.getLast? = some p) : 0 < l.length := by
  cases l with
  | nil => simp at h
  | cons _ _ => simp

/-- A step closes at most one open arc on each side, and only on the sides the point has. -/
theorem step_len {m x : ℕ} {s s' : St} {a : Bool × Bool} (h : step m x s a = some s')
    (σ : Bool) : (s.stk σ).length ≤
      (s'.stk σ).length + (if x < m ∨ (m % 2 == 1) = σ then 1 else 0) := by
  unfold step at h
  by_cases hx : x < m
  · rw [if_pos hx] at h
    simp only [hx, true_or, ↓reduceIte]
    rcases a with ⟨_ | _, _ | _⟩
    · simp only at h
      cases hu : (s.stk true).getLast? <;> cases hl : (s.stk false).getLast? <;>
        rw [hu, hl] at h <;> simp only [reduceCtorEq] at h
      split_ifs at h
      simp only [Option.some.injEq] at h
      subst h
      rw [length_setRef, length_setRef, stk_pop_len, stk_pop_len]
      cases σ <;> simp <;> omega
    · unfold openClose at h
      cases ht : (s.stk (!false)).getLast? <;> rw [ht] at h <;> simp only [reduceCtorEq,
        Option.some.injEq] at h
      subst h
      rw [stk_push_len, length_setRef, stk_pop_len]
      cases σ <;> simp <;> omega
    · unfold openClose at h
      cases ht : (s.stk (!true)).getLast? <;> rw [ht] at h <;> simp only [reduceCtorEq,
        Option.some.injEq] at h
      subst h
      rw [stk_push_len, length_setRef, stk_pop_len]
      cases σ <;> simp <;> omega
    · simp only [Option.some.injEq] at h
      subst h
      rw [stk_push_len, stk_push_len]
      omega
  · rw [if_neg hx] at h
    simp only [hx, false_or]
    dsimp only at h
    split_ifs at h with ha
    · simp only [Option.some.injEq] at h
      subst h
      rw [stk_push_len]
      split_ifs <;> omega
    · cases ht : (s.stk (m % 2 == 1)).getLast? with
      | none => rw [ht] at h; simp at h
      | some p =>
        rw [ht] at h
        simp only at h
        split_ifs at h
        simp only [Option.some.injEq] at h
        subst h
        rw [length_setRef, stk_pop_len]
        split_ifs <;> omega

theorem cap_succ (m k : ℕ) (hk : k ≤ m) (σ : Bool) :
    cap m k σ = cap m (k + 1) σ + (if k < m ∨ (m % 2 == 1) = σ then 1 else 0) := by
  unfold cap
  rcases Nat.lt_or_ge k m with h | h
  · simp only [hk, ↓reduceIte, show k + 1 ≤ m by omega, h, true_or]
    split_ifs <;> omega
  · have : k = m := by omega
    subst this
    simp only [le_refl, ↓reduceIte, Nat.sub_self, zero_add, show ¬ k + 1 ≤ k by omega,
      lt_irrefl, false_or]
    cases σ <;> cases (k % 2 == 1) <;> simp

/-- A state with accepted continuations is viable. -/
theorem viable_of_cnt (m : ℕ) : ∀ (f k : ℕ) (s : St), f + k = m + 1 →
    cntFrom m f k s ≠ 0 → viable m k s = true := by
  intro f
  induction f with
  | zero =>
    intro k s hk hc
    rw [cntFrom_zero] at hc
    split_ifs at hc with hs
    · subst hs
      simp [viable, cap, final, St.stk, show ¬ k ≤ m by omega]
    · exact absurd rfl hc
  | succ f ih =>
    intro k s hk hc
    rw [cntFrom_succ] at hc
    obtain ⟨n, hn, hn0⟩ := List.exists_mem_ne_zero_of_sum_ne_zero hc
    obtain ⟨a, _, rfl⟩ := List.mem_map.1 hn
    cases hst : step m k s a with
    | none => rw [hst] at hn0; exact absurd rfl hn0
    | some s' =>
      rw [hst] at hn0
      have hv := ih (k + 1) s' (by omega) hn0
      simp only [viable, Bool.and_eq_true, decide_eq_true_eq] at hv ⊢
      have h1 := step_len hst true
      have h2 := step_len hst false
      rw [cap_succ m k (by omega) true, cap_succ m k (by omega) false]
      omega

theorem filter_viable_wsum (m k : ℕ) (hk : k ≤ m + 1) (L : List (St × ℕ)) :
    wsum (cntFrom m (m + 1 - k) k) (L.filter fun sc => viable m k sc.1) =
      wsum (cntFrom m (m + 1 - k) k) L := by
  induction L with
  | nil => rfl
  | cons sc L ih =>
    by_cases hv : viable m k sc.1 = true
    · simp only [List.filter_cons, hv, ↓reduceIte, wsum, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
    · have h0 : cntFrom m (m + 1 - k) k sc.1 = 0 := by
        by_contra hc; exact hv (viable_of_cnt m _ k sc.1 (by omega) hc)
      simp only [List.filter_cons, hv, Bool.false_eq_true, ↓reduceIte, wsum, List.map_cons,
        List.sum_cons, h0, mul_zero, zero_add] at ih ⊢
      exact ih

theorem insertAdd_wsum (g : St → ℕ) (sc : St × ℕ) (L : List (St × ℕ)) :
    wsum g (insertAdd sc L) = sc.2 * g sc.1 + wsum g L := by
  induction L with
  | nil => simp [insertAdd, wsum]
  | cons tc L ih =>
    obtain ⟨t, c⟩ := tc
    by_cases h : t = sc.1
    · simp only [insertAdd, h, ↓reduceIte, wsum, List.map_cons, List.sum_cons]; ring
    · simp only [insertAdd, h, ↓reduceIte, wsum, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]; ring

theorem compressK_wsum (g : St → ℕ) (L : List (St × ℕ)) : wsum g (compressK L) = wsum g L := by
  induction L with
  | nil => rfl
  | cons sc L ih =>
    simp only [compressK, List.foldr_cons] at ih ⊢
    rw [insertAdd_wsum, ih]
    simp [wsum]

/-- After `k` points, the layer's weighted count of accepted continuations is the total. -/
theorem layer_wsum (comp : List (St × ℕ) → List (St × ℕ))
    (hcomp : ∀ g L, wsum g (comp L) = wsum g L) (m : ℕ) : ∀ k ≤ m + 1,
    wsum (cntFrom m (m + 1 - k) k) (layerWith comp m k) = cntFrom m (m + 1) 0 init := by
  intro k
  induction k with
  | zero => intro _; simp [layerWith, wsum]
  | succ k ih =>
    intro hk
    rw [layerWith, filter_viable_wsum m (k + 1) hk, hcomp,
      show m + 1 - (k + 1) = m - k by omega, expand_wsum,
      show m - k + 1 = m + 1 - k by omega, ih (by omega)]

/-- **The transfer matrix counts the accepted action sequences**, with any merge step that
keeps weighted sums. -/
theorem tmCountWith_eq_countP (comp : List (St × ℕ) → List (St × ℕ))
    (hcomp : ∀ g L, wsum g (comp L) = wsum g L) (m : ℕ) :
    tmCountWith comp m =
      (sufWords m (m + 1) 0).countP fun w => runFrom m 0 init w = some final := by
  have h := layer_wsum comp hcomp m (m + 1) le_rfl
  rw [Nat.sub_self] at h
  unfold tmCountWith
  rw [← cntFrom, ← h]
  unfold wsum
  congr 1
  apply List.map_congr_left
  intro sc _
  rw [cntFrom_zero]
  split <;> simp

end Arnold.TM
