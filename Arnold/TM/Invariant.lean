import Arnold.TM.Decorated
import Arnold.Defs

/-!
# The invariant of the decorated machine
-/

set_option linter.deprecated false

namespace Arnold.TM

open DSt

/-! ### Looking up open arcs after each operation -/

namespace DSt

theorem get?_s (D : DSt) (σ : Bool) (i : ℕ) : D.get? (.s σ i) = (D.stk σ)[i]? := rfl

@[simp] theorem get?_E (D : DSt) : D.get? .E = none := rfl

theorem get?_push (D : DSt) (σ : Bool) (t : Strand) (p : Ref) :
    (D.push σ t).get? p = if p = .s σ (D.stk σ).length then some t else D.get? p := by
  cases p with
  | E => simp
  | s τ i =>
    simp only [get?, push, stk_setStk, Ref.s.injEq]
    by_cases hστ : σ = τ
    · subst hστ
      simp only [↓reduceIte, true_and]
      rcases lt_trichotomy i (D.stk σ).length with h | h | h
      · rw [List.getElem?_append_left h, if_neg (by omega)]
      · subst h; simp
      · rw [if_neg (by omega), List.getElem?_eq_none (by simp; omega),
          List.getElem?_eq_none (by omega)]
    · simp [hστ, Ne.symm hστ]

theorem get?_pop (D : DSt) (σ : Bool) (p : Ref) :
    (D.pop σ).get? p = if p = .s σ ((D.stk σ).length - 1) then none else D.get? p := by
  cases p with
  | E => simp
  | s τ i =>
    simp only [get?, pop, stk_setStk, Ref.s.injEq]
    by_cases hστ : σ = τ
    · subst hστ
      simp only [↓reduceIte, true_and, List.getElem?_dropLast]
      split_ifs with h1 h2 h2 <;> first | rfl | omega | (rw [List.getElem?_eq_none (by omega)])
    · simp [hστ, Ne.symm hστ]

theorem get?_link (D : DSt) (q r : Ref) (ext : List ℕ) (p : Ref) :
    (D.link q r ext).get? p =
      (D.get? p).map fun t => if p = q then ⟨r, t.origin, t.seg ++ ext⟩ else t := by
  cases q with
  | E =>
    cases p with
    | E => simp
    | s τ i => simp [link]
  | s σ i =>
    cases p with
    | E => simp
    | s τ j =>
      simp only [get?, link, stk_setStk, Ref.s.injEq]
      by_cases hστ : σ = τ
      · subst hστ
        simp only [↓reduceIte, true_and, List.getElem?_set]
        by_cases hij : i = j
        · subst hij
          by_cases hi : i < (D.stk σ).length
          · simp [hi, List.getD_eq_getElem?_getD]
          · simp [hi]
        · simp [hij, Ne.symm hij]
      · simp [hστ, Ne.symm hστ]

@[simp] theorem get?_addArc (D : DSt) (a : ℕ × ℕ × Bool) (p : Ref) :
    (D.addArc a).get? p = D.get? p := rfl

@[simp] theorem arcs_push (D : DSt) (σ : Bool) (t : Strand) : (D.push σ t).arcs = D.arcs := by
  simp [push]

@[simp] theorem arcs_pop (D : DSt) (σ : Bool) : (D.pop σ).arcs = D.arcs := by simp [pop]

@[simp] theorem arcs_link (D : DSt) (q r : Ref) (ext : List ℕ) : (D.link q r ext).arcs = D.arcs := by
  cases q <;> simp [link]

@[simp] theorem arcs_addArc (D : DSt) (a : ℕ × ℕ × Bool) : (D.addArc a).arcs = a :: D.arcs := rfl

@[simp] theorem stk_push (D : DSt) (σ τ : Bool) (t : Strand) :
    (D.push σ t).stk τ = if σ = τ then D.stk τ ++ [t] else D.stk τ := by
  simp only [push, stk_setStk]; split_ifs with h <;> simp [h]

@[simp] theorem stk_pop (D : DSt) (σ τ : Bool) :
    (D.pop σ).stk τ = if σ = τ then (D.stk τ).dropLast else D.stk τ := by
  simp only [pop, stk_setStk]; split_ifs with h <;> simp [h]

@[simp] theorem stk_addArc (D : DSt) (a : ℕ × ℕ × Bool) (τ : Bool) : (D.addArc a).stk τ = D.stk τ := by
  cases τ <;> rfl

theorem stk_link (D : DSt) (q r : Ref) (ext : List ℕ) (τ : Bool) :
    ((D.link q r ext).stk τ).map Strand.origin = (D.stk τ).map Strand.origin := by
  cases q with
  | E => rfl
  | s σ i =>
    simp only [link, stk_setStk]
    split_ifs with h
    · subst h
      rw [List.map_set]
      by_cases hi : i < (D.stk σ).length
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
        rw [show (D.stk σ)[i].origin = ((D.stk σ).map Strand.origin)[i]'(by simpa) by simp,
          List.set_getElem_self]
      · rw [List.set_eq_of_length_le (by simp; omega)]
    · rfl

theorem length_stk_link (D : DSt) (q r : Ref) (ext : List ℕ) (τ : Bool) :
    ((D.link q r ext).stk τ).length = (D.stk τ).length := by
  have := congrArg List.length (stk_link D q r ext τ)
  simpa using this

theorem get?_top (D : DSt) (σ : Bool) (t : Strand) (h : (D.stk σ).getLast? = some t) :
    D.get? (.s σ ((D.stk σ).length - 1)) = some t ∧ 0 < (D.stk σ).length := by
  have hne : D.stk σ ≠ [] := by intro h'; simp [h'] at h
  have hl : 0 < (D.stk σ).length := List.length_pos_iff.2 hne
  refine ⟨?_, hl⟩
  rw [get?_s, List.getElem?_eq_getElem (by omega), ← List.getLast_eq_getElem hne]
  rw [List.getLast?_eq_some_getLast hne] at h
  simpa using h

end DSt

/-! ### The invariant -/

/-- Points `y` and `z` are joined by a recorded arc. -/
def Joined (A : List (ℕ × ℕ × Bool)) (y z : ℕ) : Prop := ∃ τ, (y, z, τ) ∈ A ∨ (z, y, τ) ∈ A

/-- All arc ends on side `σ` so far: origins of open arcs and both ends of closed ones. -/
def ends (D : DSt) (σ : Bool) : List ℕ :=
  (D.stk σ).map Strand.origin ++ D.arcs.flatMap fun a => if a.2.2 = σ then [a.1, a.2.1] else []

/-- Point `y` has an arc on side `σ` (bridges both, the east end one; `S` is never scanned). -/
def HasSide (m y : ℕ) (σ : Bool) : Prop := y < m ∨ (y = m ∧ σ = (m % 2 == 1))

/-- Whether point `y` opens its arc on side `σ`, according to the actions `w`. -/
def act (m : ℕ) (w : List (Bool × Bool)) (y : ℕ) (σ : Bool) : Bool :=
  if y < m then (if σ then (w.getD y (false, false)).1 else (w.getD y (false, false)).2)
  else (w.getD y (false, false)).1

/-- The invariant after scanning points `0, …, k-1` with actions `w`. -/
structure Inv (m k : ℕ) (w : List (Bool × Bool)) (D : DSt) : Prop where
  wlen : w.length = k
  ref_ne : ∀ p t, D.get? p = some t → t.ref ≠ p
  ref_ok : ∀ p t, D.get? p = some t → t.ref = .E ∨ ∃ t', D.get? t.ref = some t' ∧ t'.ref = p
  refE : ∀ p t, D.get? p = some t → t.ref = .E → m < k
  orig_lt : ∀ p t, D.get? p = some t → t.origin < k
  sorted : ∀ σ i j t t', D.get? (.s σ i) = some t → D.get? (.s σ j) = some t' → i < j →
    t.origin < t'.origin
  seg_nodup : ∀ p t, D.get? p = some t → t.seg.Nodup
  seg_head : ∀ p t, D.get? p = some t → t.seg.head? = some t.origin
  seg_lt : ∀ p t, D.get? p = some t → ∀ y ∈ t.seg, y < k
  seg_E : ∀ p t, D.get? p = some t → t.ref = .E → t.seg.getLast? = some m
  seg_rev : ∀ p t t', D.get? p = some t → D.get? t.ref = some t' → t'.seg = t.seg.reverse
  chain : ∀ p t, D.get? p = some t → t.seg.IsChain (Joined D.arcs)
  disj : ∀ p q t t', D.get? p = some t → D.get? q = some t' → q ≠ p → q ≠ t.ref →
    t.seg.Disjoint t'.seg
  cover : ∀ y < k, ∃ p t, D.get? p = some t ∧ y ∈ t.seg
  arc_lt : ∀ a b τ, (a, b, τ) ∈ D.arcs → a < b ∧ b < k
  nc : ∀ a b a' b' τ, (a, b, τ) ∈ D.arcs → (a', b', τ) ∈ D.arcs → ¬ Interleave a b a' b'
  nest : ∀ σ i t, D.get? (.s σ i) = some t → ∀ a b, (a, b, σ) ∈ D.arcs →
    ¬ (a ≤ t.origin ∧ t.origin < b)
  uniq : ∀ σ, (ends D σ).Nodup
  word : ∀ y < k, ∀ σ, HasSide m y σ →
    if act m w y σ then (∃ i t, D.get? (.s σ i) = some t ∧ t.origin = y) ∨ ∃ b, (y, b, σ) ∈ D.arcs
    else ∃ a, (a, y, σ) ∈ D.arcs

def DSt.empty : DSt := ⟨[], [], []⟩

@[simp] theorem DSt.get?_empty (p : Ref) : DSt.empty.get? p = none := by
  cases p with
  | E => rfl
  | s σ i => cases σ <;> rfl

@[simp] theorem DSt.stk_empty (σ : Bool) : DSt.empty.stk σ = [] := by cases σ <;> rfl

@[simp] theorem DSt.arcs_empty : DSt.empty.arcs = [] := rfl

theorem inv_init (m : ℕ) : Inv m 0 [] DSt.empty := by
  constructor <;> intros <;> simp_all [ends]

/-! ### Helpers -/

theorem act_append_lt (m : ℕ) (w : List (Bool × Bool)) (a : Bool × Bool) (y : ℕ) (σ : Bool)
    (hy : y < w.length) : act m (w ++ [a]) y σ = act m w y σ := by
  simp [act, List.getD_eq_getElem?_getD, List.getElem?_append_left hy]

theorem act_append_self (m : ℕ) (w : List (Bool × Bool)) (a : Bool × Bool) (σ : Bool) :
    act m (w ++ [a]) w.length σ =
      if w.length < m then (if σ then a.1 else a.2) else a.1 := by
  simp [act, List.getD_eq_getElem?_getD]

theorem Inv.ends_lt {m k w D} (h : Inv m k w D) (σ : Bool) : ∀ y ∈ ends D σ, y < k := by
  intro y hy
  simp only [ends, List.mem_append, List.mem_map, List.mem_flatMap] at hy
  rcases hy with ⟨t, ht, rfl⟩ | ⟨⟨a, b, τ⟩, hab, hy⟩
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
    exact h.orig_lt (.s σ i) _ (by simp [DSt.get?_s, hi])
  · have := h.arc_lt a b τ hab
    split_ifs at hy
    · simp at hy; omega
    · simp at hy

theorem nodup_mid {A B : List ℕ} {x : ℕ} (h : (A ++ B).Nodup) (hx : x ∉ A ++ B) :
    (A ++ [x] ++ B).Nodup := by
  have hp : (A ++ [x] ++ B).Perm (x :: (A ++ B)) := by
    simp [List.perm_middle]
  exact hp.nodup_iff.2 (List.nodup_cons.2 ⟨hx, h⟩)

theorem DSt.lt_of_get? {D : DSt} {σ : Bool} {i : ℕ} {t : Strand}
    (h : D.get? (.s σ i) = some t) : i < (D.stk σ).length := by
  rw [DSt.get?_s] at h
  by_contra hc
  rw [List.getElem?_eq_none (by omega)] at h
  simp at h

theorem Inv.noE {m k w D} (h : Inv m k w D) (hk : k ≤ m) :
    ∀ p t, D.get? p = some t → t.ref ≠ .E :=
  fun p t hp hE => by have := h.refE p t hp hE; omega

/-! ### Opening both sides at a bridge -/

theorem inv_TT {m x : ℕ} {w : List (Bool × Bool)} {D : DSt} (h : Inv m x w D) (hx : x < m) :
    Inv m (x + 1) (w ++ [(true, true)])
      ((D.push true ⟨.s false (D.stk false).length, x, [x]⟩).push false
        ⟨.s true (D.stk true).length, x, [x]⟩) := by
  set nU := (D.stk true).length with hnU
  set nD := (D.stk false).length with hnD
  set U : Strand := ⟨.s false nD, x, [x]⟩ with hU
  set L : Strand := ⟨.s true nU, x, [x]⟩ with hL
  set D' := (D.push true U).push false L with hD'
  have hg : ∀ p, D'.get? p =
      if p = .s false nD then some L else if p = .s true nU then some U else D.get? p := by
    intro p
    rw [hD', DSt.get?_push, DSt.get?_push]
    simp only [DSt.stk_push, Bool.true_eq_false, ↓reduceIte, ← hnU, ← hnD]
  have hU0 : D.get? (.s true nU) = none := by
    rw [DSt.get?_s]; exact List.getElem?_eq_none (by omega)
  have hL0 : D.get? (.s false nD) = none := by
    rw [DSt.get?_s]; exact List.getElem?_eq_none (by omega)
  have hold : ∀ q t, D.get? q = some t → D'.get? q = some t := by
    intro q t hq
    rw [hg]
    split_ifs with h1 h2
    · subst h1; rw [hL0] at hq; simp at hq
    · subst h2; rw [hU0] at hq; simp at hq
    · exact hq
  have hnew : ∀ p t, D'.get? p = some t →
      (p = .s false nD ∧ t = L) ∨ (p = .s true nU ∧ t = U) ∨ D.get? p = some t := by
    intro p t hp
    rw [hg] at hp
    split_ifs at hp with h1 h2
    · exact Or.inl ⟨h1, (Option.some.inj hp).symm⟩
    · exact Or.inr (Or.inl ⟨h2, (Option.some.inj hp).symm⟩)
    · exact Or.inr (Or.inr hp)
  have hLg : D'.get? (.s false nD) = some L := by rw [hg]; simp
  have hUg : D'.get? (.s true nU) = some U := by rw [hg]; simp
  have harcs : D'.arcs = D.arcs := by simp [hD']
  have hnoE := h.noE (by omega)
  constructor
  · simp [h.wlen]
  · intro p t hp
    rcases hnew p t hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hp
    · simp [hL]
    · simp [hU]
    · exact h.ref_ne p t hp
  · intro p t hp
    rcases hnew p t hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hp
    · exact Or.inr ⟨U, hUg, rfl⟩
    · exact Or.inr ⟨L, hLg, rfl⟩
    · rcases h.ref_ok p t hp with hE | ⟨t', ht', hr⟩
      · exact Or.inl hE
      · exact Or.inr ⟨t', hold _ _ ht', hr⟩
  · intro p t hp hE
    rcases hnew p t hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hp
    · simp [hL] at hE
    · simp [hU] at hE
    · exact absurd hE (hnoE p t hp)
  · intro p t hp
    rcases hnew p t hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hp
    · simp [hL]
    · simp [hU]
    · have := h.orig_lt p t hp; omega
  · intro σ i j t t' hi hj hij
    rcases hnew _ _ hi with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | hi'
    · -- `i` is the new top below; nothing lies above it
      simp only [Ref.s.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      rcases hnew _ _ hj with ⟨h2, rfl⟩ | ⟨h2, rfl⟩ | hj'
      · simp at h2; omega
      · simp at h2
      · have := DSt.lt_of_get? hj'; omega
    · simp only [Ref.s.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      rcases hnew _ _ hj with ⟨h2, rfl⟩ | ⟨h2, rfl⟩ | hj'
      · simp at h2
      · simp at h2; omega
      · have := DSt.lt_of_get? hj'; omega
    · rcases hnew _ _ hj with ⟨h2, rfl⟩ | ⟨h2, rfl⟩ | hj'
      · simp [hL]; exact h.orig_lt _ _ hi'
      · simp [hU]; exact h.orig_lt _ _ hi'
      · exact h.sorted σ i j t t' hi' hj' hij
  · intro p t hp
    rcases hnew p t hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hp
    · simp [hL]
    · simp [hU]
    · exact h.seg_nodup p t hp
  · intro p t hp
    rcases hnew p t hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hp
    · simp [hL]
    · simp [hU]
    · exact h.seg_head p t hp
  · intro p t hp y hy
    rcases hnew p t hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hp
    · simp [hL] at hy; omega
    · simp [hU] at hy; omega
    · have := h.seg_lt p t hp y hy; omega
  · intro p t hp hE
    rcases hnew p t hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hp
    · simp [hL] at hE
    · simp [hU] at hE
    · exact absurd hE (hnoE p t hp)
  · intro p t t' hp ht'
    rcases hnew p t hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hp
    · rw [hUg] at ht'; cases ht'; simp [hU, hL]
    · rw [hLg] at ht'; cases ht'; simp [hU, hL]
    · rcases h.ref_ok p t hp with hE | ⟨t2, ht2, _⟩
      · exact absurd hE (hnoE p t hp)
      · rw [hold _ _ ht2, Option.some.injEq] at ht'
        rw [← ht']
        exact h.seg_rev p t t2 hp ht2
  · intro p t hp
    rw [harcs]
    rcases hnew p t hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hp
    · simp [hL]
    · simp [hU]
    · exact h.chain p t hp
  · intro p q t t' hp hq hqp hqr
    have hxt : ∀ p t, D.get? p = some t → x ∉ t.seg := fun p t hp hx' => by
      have := h.seg_lt p t hp x hx'; omega
    rcases hnew p t hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hp' <;>
      rcases hnew q t' hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hq'
    · exact absurd rfl hqp
    · exact absurd rfl hqr
    · simpa [hL] using hxt _ _ hq'
    · exact absurd rfl hqr
    · exact absurd rfl hqp
    · simpa [hU] using hxt _ _ hq'
    · simpa [hL, List.disjoint_comm] using hxt _ _ hp'
    · simpa [hU, List.disjoint_comm] using hxt _ _ hp'
    · exact h.disj p q t t' hp' hq' hqp hqr
  · intro y hy
    by_cases hyx : y = x
    · exact ⟨_, _, hLg, by simp [hL, hyx]⟩
    · obtain ⟨p, t, hp, hyt⟩ := h.cover y (by omega)
      exact ⟨p, t, hold _ _ hp, hyt⟩
  · intro a b τ hab
    rw [harcs] at hab
    have := h.arc_lt a b τ hab; omega
  · intro a b a' b' τ h1 h2
    rw [harcs] at h1 h2
    exact h.nc a b a' b' τ h1 h2
  · intro σ i t hi a b hab
    rw [harcs] at hab
    rcases hnew _ _ hi with ⟨_, rfl⟩ | ⟨_, rfl⟩ | hi'
    · have := h.arc_lt a b _ hab; simp [hL]; omega
    · have := h.arc_lt a b _ hab; simp [hU]; omega
    · exact h.nest σ i t hi' a b hab
  · intro σ
    have hx' : x ∉ ends D σ := fun hx' => by have := h.ends_lt σ x hx'; omega
    have heq : ends D' σ = (D.stk σ).map Strand.origin ++ [x] ++
        D.arcs.flatMap fun a => if a.2.2 = σ then [a.1, a.2.1] else [] := by
      cases σ <;> simp [ends, hD', hU, hL]
    rw [heq]
    exact nodup_mid (h.uniq σ) hx'
  · intro y hy σ hs
    have hw := h.wlen
    by_cases hyx : y = x
    · have hyw : y = w.length := by omega
      rw [hyw, act_append_self, if_pos (show w.length < m by omega)]
      cases σ
      · exact Or.inl ⟨nD, L, hLg, by simp [hL]; omega⟩
      · exact Or.inl ⟨nU, U, hUg, by simp [hU]; omega⟩
    · rw [act_append_lt _ _ _ _ _ (by omega), harcs]
      have := h.word y (by omega) σ hs
      split_ifs at this ⊢
      · rcases this with ⟨i, t, hi, ho⟩ | hb
        · exact Or.inl ⟨i, t, hold _ _ hi, ho⟩
        · exact Or.inr hb
      · exact this

end Arnold.TM
