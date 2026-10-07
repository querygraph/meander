import Arnold.Fast

/-!
# Meanders are bounded by Catalan numbers squared

A closed meander is two non-crossing perfect matchings of the bridges glued together: the arcs
above the road and the arcs below it. A non-crossing matching is determined by its Dyck word
(`U` where an arc opens, `D` where it closes), and there are `catalan n` Dyck words of
semilength `n`. So there are at most `catalan n ^ 2` closed meanders of order `n`.

We work with open meanders with `2n+1` crossings, which `closedMeanderCount_succ` identifies
with closed meanders of order `n+1`. Treat the two ends of the river as extra points to the
east of every bridge: the south end `S` below the road and the east end `E` above it. Then each
half-plane holds a non-crossing perfect matching of `2n+2` points, and the river can be read
back from the two matchings. Each step goes to the partner of the current point on the side
where the river is.

The proof has three parts:
1. `NCMatching.eq_of_pattern`: a non-crossing matching is determined by its `U`/`D` pattern.
   For an opener `x` with partner `y`, the arcs inside `(x, y)` are balanced, and every prefix
   of `(x, y)` has at least as many openers as closers. This pins `y` down from the pattern.
2. `mkMatching`: the arcs on one side of a river form a non-crossing matching.
3. `openMeanderCount_le_catalan_sq`: the map from a river to its pair of Dyck words is
   injective.
-/

namespace Arnold

open Equiv DyckStep

/-! ### Non-crossing perfect matchings -/

/-- A non-crossing perfect matching of the points `0, …, N-1`, given by the partner map. -/
structure NCMatching (N : ℕ) where
  /-- The partner of each point. -/
  m : ℕ → ℕ
  m_lt : ∀ a < N, m a < N
  m_m : ∀ a < N, m (m a) = a
  m_ne : ∀ a < N, m a ≠ a
  nc : ∀ a < N, ∀ b < N, ¬ Interleave a (m a) b (m b)

namespace NCMatching

variable {N : ℕ} (M : NCMatching N)

/-- `+1` if `i` opens its arc (`U`), `-1` if it closes it (`D`). -/
def sgn (i : ℕ) : ℤ := if i < M.m i then 1 else -1

/-- The number of arcs opened minus the number closed strictly between `x` and `z`. -/
def bal (x z : ℕ) : ℤ := ∑ i ∈ Finset.Ico (x + 1) z, M.sgn i

theorem bal_split {x z w : ℕ} (hxz : x < z) (hzw : z < w) :
    M.bal x w = M.bal x z + M.sgn z + M.bal z w := by
  unfold bal
  rw [← Finset.sum_Ico_consecutive _ (show x + 1 ≤ z by omega) hzw.le,
    Finset.sum_eq_sum_Ico_succ_bot hzw]
  ring

theorem bal_succ {x z : ℕ} (hxz : x < z) : M.bal x (z + 1) = M.bal x z + M.sgn z := by
  unfold bal
  rw [Finset.sum_Ico_succ_top (by omega)]

theorem sum_sgn (S : Finset ℕ) :
    ∑ i ∈ S, M.sgn i =
      ((S.filter fun i => i < M.m i).card : ℤ) - (S.filter fun i => ¬ i < M.m i).card := by
  simp [sgn, Finset.sum_ite, sub_eq_add_neg]

/-- Each closer in `S` is matched to an opener in `S`, so `S` has no more closers than
openers. -/
theorem closers_le_openers (S : Finset ℕ) (hS : ∀ c ∈ S, c < N)
    (hcl : ∀ c ∈ S, M.m c < c → M.m c ∈ S) :
    (S.filter fun i => ¬ i < M.m i).card ≤ (S.filter fun i => i < M.m i).card := by
  apply Finset.card_le_card_of_injOn M.m
  · intro c hc
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hc ⊢
    have hne := M.m_ne c (hS c hc.1)
    have hlt : M.m c < c := by omega
    exact ⟨hcl c hc.1 hlt, by rw [M.m_m c (hS c hc.1)]; exact hlt⟩
  · intro a ha b hb hab
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha hb
    have := congrArg M.m hab
    rwa [M.m_m a (hS a ha.1), M.m_m b (hS b hb.1)] at this

/-- Each opener in `S` is matched to a closer in `S`. -/
theorem openers_le_closers (S : Finset ℕ) (hS : ∀ c ∈ S, c < N)
    (hop : ∀ c ∈ S, c < M.m c → M.m c ∈ S) :
    (S.filter fun i => i < M.m i).card ≤ (S.filter fun i => ¬ i < M.m i).card := by
  apply Finset.card_le_card_of_injOn M.m
  · intro c hc
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hc ⊢
    exact ⟨hop c hc.1 hc.2, by rw [M.m_m c (hS c hc.1)]; omega⟩
  · intro a ha b hb hab
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha hb
    have := congrArg M.m hab
    rwa [M.m_m a (hS a ha.1), M.m_m b (hS b hb.1)] at this

/-- Points strictly inside the arc `(x, y)` are matched strictly inside it. -/
theorem inside {x : ℕ} (hx : x < N) (hxo : x < M.m x) {c : ℕ} (hc1 : x < c)
    (hc2 : c < M.m x) : x < M.m c ∧ M.m c < M.m x := by
  have hcN : c < N := by have := M.m_lt x hx; omega
  have h1 := M.nc x hx c hcN
  have h4 := M.m_ne c hcN
  have h5 : M.m c ≠ x := fun h => by
    have := congrArg M.m h
    rw [M.m_m c hcN] at this
    omega
  have h6 : M.m c ≠ M.m x := fun h => by
    have := congrArg M.m h
    rw [M.m_m c hcN, M.m_m x hx] at this
    omega
  unfold Interleave at h1
  omega

/-- For an opener `x` with partner `y`: the arcs strictly between them are balanced, and no
prefix of `(x, y)` closes more arcs than it opens. -/
theorem bal_opener {x : ℕ} (hx : x < N) (hxo : x < M.m x) :
    M.bal x (M.m x) = 0 ∧ ∀ z, x < z → z ≤ M.m x → 0 ≤ M.bal x z := by
  have hy := M.m_lt x hx
  have key : ∀ z, z ≤ M.m x →
      (Finset.Ico (x + 1) z |>.filter fun i => ¬ i < M.m i).card ≤
        (Finset.Ico (x + 1) z |>.filter fun i => i < M.m i).card := by
    intro z hz
    apply M.closers_le_openers
    · intro c hc
      rw [Finset.mem_Ico] at hc
      omega
    · intro c hc hlt
      rw [Finset.mem_Ico] at hc ⊢
      have := M.inside hx hxo (c := c) (by omega) (by omega)
      omega
  refine ⟨?_, fun z _ hz => ?_⟩
  · unfold bal
    rw [sum_sgn]
    have := M.openers_le_closers (Finset.Ico (x + 1) (M.m x))
      (fun c hc => by rw [Finset.mem_Ico] at hc; omega)
      (fun c hc hlt => by
        rw [Finset.mem_Ico] at hc ⊢
        have := M.inside hx hxo (c := c) (by omega) (by omega)
        omega)
    have := key (M.m x) le_rfl
    omega
  · unfold bal
    rw [sum_sgn]
    have := key z hz
    omega

/-! #### A matching is determined by its pattern -/

section Unique

variable {M} {M' : NCMatching N} (h : ∀ i < N, (i < M.m i ↔ i < M'.m i))
include h

theorem sgn_eq {i : ℕ} (hi : i < N) : M.sgn i = M'.sgn i := by
  unfold sgn
  by_cases h1 : i < M.m i
  · simp [h1, (h i hi).1 h1]
  · simp [h1, show ¬ i < M'.m i from fun h2 => h1 ((h i hi).2 h2)]

theorem bal_eq {x z : ℕ} (hz : z ≤ N) : M.bal x z = M'.bal x z := by
  unfold bal
  refine Finset.sum_congr rfl fun i hi => sgn_eq h ?_
  rw [Finset.mem_Ico] at hi
  omega

/-- An opener's partner in `M` cannot come before its partner in `M'`. -/
theorem opener_not_lt {x : ℕ} (hx : x < N) (hxo : x < M.m x) : ¬ M.m x < M'.m x := by
  intro hlt
  have hxo' : x < M'.m x := (h x hx).1 hxo
  have hy' := M'.m_lt x hx
  have hyN := M.m_lt x hx
  have hb := (M'.bal_opener hx hxo').2 (M.m x + 1) (by omega) (by omega)
  rw [bal_succ _ hxo, ← bal_eq h (by omega), (M.bal_opener hx hxo).1, ← sgn_eq h hyN] at hb
  have : M.sgn (M.m x) = -1 := by
    have hmm := M.m_m x hx
    simp only [sgn, hmm, show ¬ M.m x < x by omega, ↓reduceIte]
  omega

/-- A closer's partner in `M` cannot come before its partner in `M'`. -/
theorem closer_not_lt {x : ℕ} (hx : x < N) (hxc : ¬ x < M.m x) : ¬ M.m x < M'.m x := by
  intro hlt
  have hxc' : ¬ x < M'.m x := fun h' => hxc ((h x hx).2 h')
  have hne := M.m_ne x hx
  have hne' := M'.m_ne x hx
  have hyN := M.m_lt x hx
  have hy'N := M'.m_lt x hx
  -- `y = M.m x` opens the arc `(y, x)` in `M`; `y' = M'.m x` opens `(y', x)` in `M'`.
  have hMy : M.m (M.m x) = x := M.m_m x hx
  have hMy' : M'.m (M'.m x) = x := M'.m_m x hx
  have hyo : M.m x < M.m (M.m x) := by rw [hMy]; omega
  have hy'o : M'.m x < M'.m (M'.m x) := by rw [hMy']; omega
  have h1 := (M.bal_opener hyN hyo).1
  have h2 := (M.bal_opener hyN hyo).2 (M'.m x) (by omega) (by rw [hMy]; omega)
  have h3 := (M'.bal_opener hy'N hy'o).1
  rw [hMy] at h1
  rw [hMy', ← bal_eq h hx.le] at h3
  rw [bal_split M hlt (show M'.m x < x by omega), h3] at h1
  have : M.sgn (M'.m x) = 1 := by
    rw [sgn_eq h hy'N]
    simp [sgn, hy'o]
  omega

end Unique

/-- **Two non-crossing matchings with the same pattern of openers and closers are equal.** -/
theorem eq_of_pattern {M M' : NCMatching N} (h : ∀ i < N, (i < M.m i ↔ i < M'.m i)) :
    ∀ x < N, M.m x = M'.m x := by
  intro x hx
  have h' : ∀ i < N, (i < M'.m i ↔ i < M.m i) := fun i hi => (h i hi).symm
  by_cases hxo : x < M.m x
  · have := opener_not_lt h hx hxo
    have := opener_not_lt h' hx ((h x hx).1 hxo)
    omega
  · have := closer_not_lt h hx hxo
    have := closer_not_lt h' hx (fun h2 => hxo ((h x hx).2 h2))
    omega

/-! #### Dyck words -/

theorem count_range_map (p : ℕ → Prop) [DecidablePred p] (k : ℕ) :
    ((List.range k).map fun i => if p i then U else D).count U =
        ((Finset.range k).filter p).card ∧
      ((List.range k).map fun i => if p i then U else D).count D =
        ((Finset.range k).filter fun i => ¬ p i).card := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.count_append, List.count_append, ih.1, ih.2,
      Finset.range_add_one, Finset.filter_insert, Finset.filter_insert]
    by_cases hk : p k <;> simp [hk, Finset.card_insert_of_notMem]

/-- The Dyck word of a matching: `U` at each opener, `D` at each closer. -/
def toDyck (M : NCMatching N) : DyckWord where
  toList := (List.range N).map fun i => if i < M.m i then U else D
  count_U_eq_count_D := by
    rw [(count_range_map _ N).1, (count_range_map _ N).2]
    refine le_antisymm (M.openers_le_closers _ (fun c hc => ?_) (fun c hc _ => ?_))
      (M.closers_le_openers _ (fun c hc => ?_) (fun c hc _ => ?_)) <;>
    simp only [Finset.mem_range] at hc ⊢
    · exact hc
    · exact M.m_lt c hc
    · exact hc
    · exact M.m_lt c hc
  count_D_le_count_U i := by
    rw [← List.map_take, List.take_range, (count_range_map _ _).1, (count_range_map _ _).2]
    apply M.closers_le_openers
    · intro c hc
      rw [Finset.mem_range] at hc
      omega
    · intro c hc hlt
      rw [Finset.mem_range] at hc ⊢
      omega

theorem semilength_toDyck {n : ℕ} (M : NCMatching (2 * n)) : M.toDyck.semilength = n := by
  have := M.toDyck.two_mul_semilength_eq_length
  rw [show M.toDyck.toList.length = 2 * n by simp [toDyck]] at this
  omega

theorem pattern_of_toDyck_eq {M M' : NCMatching N} (hw : M.toDyck = M'.toDyck) :
    ∀ i < N, (i < M.m i ↔ i < M'.m i) := by
  intro i hi
  have := congrArg (fun p : DyckWord => p.toList[i]?) hw
  simp only [toDyck, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.some.injEq] at this
  by_cases h1 : i < M.m i <;> by_cases h2 : i < M'.m i
  · exact iff_of_true h1 h2
  · simp [h1, h2] at this
  · simp [h1, h2] at this
  · exact iff_of_false h1 h2

end NCMatching

/-! ### The arcs on one side of a river -/

/-- Partner of `v` along a path `Q lo, Q (lo+1), …` whose arcs `(Q j, Q (j+1))` with
`j ≡ lo (mod 2)` lie on one side; `pos` locates each point on the path. -/
def ofPath (lo : ℕ) (Q pos : ℕ → ℕ) (v : ℕ) : ℕ :=
  if pos v % 2 = lo % 2 then Q (pos v + 1) else Q (pos v - 1)

section MkMatching

variable {N lo : ℕ} {Q pos : ℕ → ℕ} (hN : N % 2 = 0)
  (hQ : ∀ i, lo ≤ i → i < lo + N → Q i < N ∧ pos (Q i) = i)
  (hpos : ∀ v < N, lo ≤ pos v ∧ pos v < lo + N ∧ Q (pos v) = v)

include hN hpos in
theorem arc_of {a : ℕ} (ha : a < N) : ∃ j, lo ≤ j ∧ j + 1 < lo + N ∧ j % 2 = lo % 2 ∧
    ((a = Q j ∧ ofPath lo Q pos a = Q (j + 1)) ∨ (a = Q (j + 1) ∧ ofPath lo Q pos a = Q j)) := by
  obtain ⟨h1, h2, h3⟩ := hpos a ha
  unfold ofPath
  split_ifs with hp
  · exact ⟨pos a, h1, by omega, hp, Or.inl ⟨h3.symm, rfl⟩⟩
  · refine ⟨pos a - 1, by omega, by omega, by omega, Or.inr ⟨?_, rfl⟩⟩
    rw [show pos a - 1 + 1 = pos a by omega, h3]

/-- The arcs on one side of a non-self-crossing path form a non-crossing perfect matching. -/
def mkMatching
    (hnc : ∀ k, lo ≤ k → k + 1 < lo + N → ∀ j, lo ≤ j → j < k → j % 2 = lo % 2 →
      k % 2 = lo % 2 → ¬ Interleave (Q j) (Q (j + 1)) (Q k) (Q (k + 1))) :
    NCMatching N where
  m := ofPath lo Q pos
  m_lt := by
    intro v hv
    obtain ⟨h1, h2, _⟩ := hpos v hv
    unfold ofPath
    split_ifs with hp
    · exact (hQ _ (by omega) (by omega)).1
    · exact (hQ _ (by omega) (by omega)).1
  m_m := by
    intro v hv
    obtain ⟨h1, h2, h3⟩ := hpos v hv
    by_cases hp : pos v % 2 = lo % 2
    · have hk := hQ (pos v + 1) (by omega) (by omega)
      simp only [ofPath, hp, ↓reduceIte, hk.2, show ¬ ((pos v + 1) % 2 = lo % 2) by omega,
        Nat.add_sub_cancel, h3]
    · have hk := hQ (pos v - 1) (by omega) (by omega)
      simp only [ofPath, hp, ↓reduceIte, hk.2, show (pos v - 1) % 2 = lo % 2 by omega,
        show pos v - 1 + 1 = pos v by omega, h3]
  m_ne := by
    intro v hv heq
    obtain ⟨h1, h2, h3⟩ := hpos v hv
    unfold ofPath at heq
    split_ifs at heq with hp
    · have := congrArg pos heq
      rw [(hQ _ (by omega) (by omega)).2] at this
      omega
    · have := congrArg pos heq
      rw [(hQ _ (by omega) (by omega)).2] at this
      omega
  nc := by
    intro a ha b hb
    obtain ⟨ja, hja1, hja2, hja3, hA⟩ := arc_of hN hpos ha
    obtain ⟨jb, hjb1, hjb2, hjb3, hB⟩ := arc_of hN hpos hb
    have hinj : ∀ i i', lo ≤ i → i < lo + N → lo ≤ i' → i' < lo + N → i ≠ i' → Q i ≠ Q i' :=
      fun i i' h1 h2 h3 h4 hne heq =>
        hne (by rw [← (hQ i h1 h2).2, ← (hQ i' h3 h4).2, heq])
    have d0 := hinj ja (ja + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
    have d0' := hinj jb (jb + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
    generalize ofPath lo Q pos a = x at hA
    generalize ofPath lo Q pos b = y at hB
    rcases lt_trichotomy ja jb with hlt | heq | hgt
    · have hc := hnc jb hjb1 hjb2 ja hja1 hlt hja3 hjb3
      have d1 := hinj ja jb (by omega) (by omega) (by omega) (by omega) (by omega)
      have d2 := hinj ja (jb + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
      have d3 := hinj (ja + 1) jb (by omega) (by omega) (by omega) (by omega) (by omega)
      have d4 := hinj (ja + 1) (jb + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
      generalize Q ja = qa at *
      generalize Q (ja + 1) = qa' at *
      generalize Q jb = qb at *
      generalize Q (jb + 1) = qb' at *
      unfold Interleave at *
      omega
    · subst heq
      generalize Q ja = qa at *
      generalize Q (ja + 1) = qa' at *
      unfold Interleave
      omega
    · have hc := hnc ja hja1 hja2 jb hjb1 hgt hjb3 hja3
      have d1 := hinj ja jb (by omega) (by omega) (by omega) (by omega) (by omega)
      have d2 := hinj ja (jb + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
      have d3 := hinj (ja + 1) jb (by omega) (by omega) (by omega) (by omega) (by omega)
      have d4 := hinj (ja + 1) (jb + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
      generalize Q ja = qa at *
      generalize Q (ja + 1) = qa' at *
      generalize Q jb = qb at *
      generalize Q (jb + 1) = qb' at *
      unfold Interleave at *
      omega

theorem mkMatching_m_Q (hnc) {i : ℕ} (hi1 : lo ≤ i) (hi2 : i + 1 < lo + N)
    (hi3 : i % 2 = lo % 2) : (mkMatching hN hQ hpos hnc).m (Q i) = Q (i + 1) := by
  simp only [mkMatching, ofPath, (hQ i hi1 (by omega)).2, hi3, ↓reduceIte]

end MkMatching

/-! ### The two matchings of an open meander with `2n+1` crossings -/

section OpenMeander

variable {n : ℕ} (τ : Perm (Fin (2 * n + 1)))

/-- The river's path with the south end relabelled from `2n+2` to `2n+1`. This keeps it east of
every bridge, and `2n+1` is free below the road, where the east end never goes. -/
def qpt (i : ℕ) : ℕ := if i = 0 then 2 * n + 1 else pathPt τ i

/-- Position of point `v` on the path: bridges by crossing order, and the extra point `2n+1`
at the start (`lo = 0`, the south end) or at the end (`lo = 1`, the east end). -/
def qpos (lo v : ℕ) : ℕ :=
  if h : v < 2 * n + 1 then (τ.symm ⟨v, h⟩ : ℕ) + 1 else if lo = 0 then 0 else 2 * n + 2

theorem qpt_bridge {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ 2 * n + 1) :
    qpt τ i = τ ⟨i - 1, by omega⟩ := by
  simp only [qpt, pathPt, show i ≠ 0 by omega, ↓reduceIte, show i - 1 < 2 * n + 1 by omega,
    ↓reduceDIte]

theorem qpt_spec (lo : ℕ) (hlo : lo ≤ 1) :
    ∀ i, lo ≤ i → i < lo + (2 * n + 2) → qpt τ i < 2 * n + 2 ∧ qpos τ lo (qpt τ i) = i := by
  intro i h1 h2
  by_cases hi0 : i = 0
  · subst hi0
    simp [qpt, qpos, show lo = 0 by omega]
  by_cases hiE : i = 2 * n + 2
  · subst hiE
    simp [qpt, pathPt, qpos, show lo ≠ 0 by omega]
  rw [qpt_bridge τ (by omega) (by omega)]
  refine ⟨by have := (τ ⟨i - 1, by omega⟩).isLt; omega, ?_⟩
  simp only [qpos, Fin.is_lt, ↓reduceDIte, Fin.eta, symm_apply_apply]
  omega

theorem qpos_spec (lo : ℕ) (hlo : lo ≤ 1) :
    ∀ v < 2 * n + 2, lo ≤ qpos τ lo v ∧ qpos τ lo v < lo + (2 * n + 2) ∧
      qpt τ (qpos τ lo v) = v := by
  intro v hv
  by_cases hb : v < 2 * n + 1
  · simp only [qpos, hb, ↓reduceDIte]
    have := (τ.symm ⟨v, hb⟩).isLt
    refine ⟨by omega, by omega, ?_⟩
    rw [qpt_bridge τ (by omega) (by omega)]
    simp
  · have hv' : v = 2 * n + 1 := by omega
    subst hv'
    rcases (show lo = 0 ∨ lo = 1 by omega) with rfl | rfl
    · simp [qpos, qpt]
    · simp [qpos, qpt, pathPt]

/-- Same-side arcs of the relabelled path do not cross. -/
theorem qpt_noCross (hτ : IsMeander τ) (lo : ℕ) (hlo : lo ≤ 1) :
    ∀ k, lo ≤ k → k + 1 < lo + (2 * n + 2) → ∀ j, lo ≤ j → j < k → j % 2 = lo % 2 →
      k % 2 = lo % 2 → ¬ Interleave (qpt τ j) (qpt τ (j + 1)) (qpt τ k) (qpt τ (k + 1)) := by
  intro k hk1 hk2 j hj1 hjk hj2 hk3
  have hc := hτ k (by omega) j hjk (by omega)
  have hP : ∀ i, 1 ≤ i → qpt τ i = pathPt τ i := fun i hi => by
    simp [qpt, show i ≠ 0 by omega]
  rw [hP (j + 1) (by omega), hP k (by omega), hP (k + 1) (by omega)]
  by_cases hj0 : j = 0
  · -- Below the road: the south end moves from `2n+2` to `2n+1`. The other endpoints are
    -- bridges `≤ 2n`, so nothing changes.
    subst hj0
    have e1 := pathPt_cases τ 1 (by omega)
    have e2 := pathPt_cases τ k (by omega)
    have e3 := pathPt_cases τ (k + 1) (by omega)
    have e0 : pathPt τ 0 = 2 * n + 2 := by simp [pathPt]
    simp only [qpt, ↓reduceIte, zero_add]
    rw [e0] at hc
    generalize pathPt τ 1 = b at *
    generalize pathPt τ k = c at *
    generalize pathPt τ (k + 1) = d at *
    unfold Interleave at *
    omega
  · rwa [hP j (by omega)]

/-- The arcs of the river below the road (`lo = 0`) or above it (`lo = 1`). -/
def sideMatching (hτ : IsMeander τ) (lo : ℕ) (hlo : lo ≤ 1) : NCMatching (2 * n + 2) :=
  mkMatching (by omega) (qpt_spec τ lo hlo) (qpos_spec τ lo hlo) (qpt_noCross τ hτ lo hlo)

theorem sideMatching_step (hτ : IsMeander τ) {i : ℕ} (hi : i ≤ 2 * n + 1) :
    (sideMatching τ hτ (i % 2) (by omega)).m (qpt τ i) = qpt τ (i + 1) :=
  mkMatching_m_Q _ _ _ _ (by omega) (by omega) (by omega)

/-- The pair of Dyck words of an open meander: the arcs below and above the road. -/
def dyckPair (τ : {τ : Perm (Fin (2 * n + 1)) // IsMeander τ}) :
    {p : DyckWord // p.semilength = n + 1} × {p : DyckWord // p.semilength = n + 1} :=
  (⟨(sideMatching τ.1 τ.2 0 (by omega)).toDyck, NCMatching.semilength_toDyck (n := n + 1) _⟩,
   ⟨(sideMatching τ.1 τ.2 1 (by omega)).toDyck, NCMatching.semilength_toDyck (n := n + 1) _⟩)

theorem dyckPair_injective : Function.Injective (dyckPair (n := n)) := by
  rintro ⟨τ, hτ⟩ ⟨τ', hτ'⟩ h
  simp only [dyckPair, Prod.mk.injEq, Subtype.mk.injEq] at h
  have hm : ∀ lo (hlo : lo ≤ 1), ∀ v < 2 * n + 2,
      (sideMatching τ hτ lo hlo).m v = (sideMatching τ' hτ' lo hlo).m v := by
    intro lo hlo
    rcases (show lo = 0 ∨ lo = 1 by omega) with rfl | rfl
    · exact NCMatching.eq_of_pattern (NCMatching.pattern_of_toDyck_eq h.1)
    · exact NCMatching.eq_of_pattern (NCMatching.pattern_of_toDyck_eq h.2)
  -- Follow the river: both paths take the same step each time.
  have hpath : ∀ i ≤ 2 * n + 2, qpt τ i = qpt τ' i := by
    intro i
    induction i with
    | zero => intro _; simp [qpt]
    | succ i ih =>
      intro hi
      rw [← sideMatching_step τ hτ (by omega), ← sideMatching_step τ' hτ' (by omega),
        ← ih (by omega)]
      exact hm _ _ _ ((qpt_spec τ (i % 2) (by omega) i (by omega) (by omega)).1)
  congr 1
  ext j
  have := hpath (j + 1) (by omega)
  rwa [qpt_bridge τ (by omega) (by omega), qpt_bridge τ' (by omega) (by omega)] at this

end OpenMeander

/-! ### The bounds -/

/-- **An open river with `2n+1` crossings: at most `catalan (n+1) ^ 2` of them.** -/
theorem openMeanderCount_le_catalan_sq (n : ℕ) :
    openMeanderCount (2 * n + 1) ≤ catalan (n + 1) ^ 2 := by
  unfold openMeanderCount
  calc _ ≤ Fintype.card ({p : DyckWord // p.semilength = n + 1} ×
        {p : DyckWord // p.semilength = n + 1}) :=
      Fintype.card_le_of_injective _ dyckPair_injective
    _ = catalan (n + 1) ^ 2 := by
      rw [Fintype.card_prod, DyckWord.card_dyckWord_semilength_eq_catalan, sq]

/-- **There are at most `catalan n ^ 2` closed meanders of order `n`.** -/
theorem closedMeanderCount_le_catalan_sq (n : ℕ) : closedMeanderCount n ≤ catalan n ^ 2 := by
  rcases n with _ | n
  · calc closedMeanderCount 0 ≤ Fintype.card (Perm (Fin (2 * 0))) := Fintype.card_subtype_le _
      _ = catalan 0 ^ 2 := by simp
  · rw [closedMeanderCount_succ]
    exact openMeanderCount_le_catalan_sq n

end Arnold
