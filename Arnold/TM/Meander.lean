import Arnold.TM.Decode

/-!
# Meanders as paths: positions, neighbours, and the action sequence

For a river given by its crossing order `l` (a list meander), `lpt m l i` is the `i`-th point
on its path, `pos y` is the position of point `y`, and `nbr σ y` is the other end of `y`'s arc on
side `σ`. `encode m l` is the action sequence the river induces: each point opens its arc on a
side exactly when the other end lies to the east.
-/

set_option linter.deprecated false

namespace Arnold.TM

section

variable (m : ℕ) (l : List ℕ)

/-- The position of point `y` on the river's path. -/
def pos (y : ℕ) : ℕ := if y < m then l.idxOf y + 1 else if y = m then m + 1 else 0

/-- The other end of point `y`'s arc on side `σ`. -/
def nbr (σ : Bool) (y : ℕ) : ℕ :=
  if (pos m l y % 2 == 1) = σ then lpt m l (pos m l y + 1) else lpt m l (pos m l y - 1)

/-- Whether point `y` opens its arc on side `σ`. -/
def openAct (σ : Bool) (y : ℕ) : Bool := decide (y < nbr m l σ y)

/-- The action sequence of a river. -/
def encode : List (Bool × Bool) := (List.range (m + 1)).map fun y =>
  if y < m then (openAct m l true y, openAct m l false y)
  else (openAct m l (m % 2 == 1) m, openAct m l (m % 2 == 1) m)

/-- Point `y` has an arc on side `σ`: bridges both, `E = m` on side `m % 2`, `S = m+1` below. -/
def HasSideM (y : ℕ) (σ : Bool) : Prop :=
  y < m ∨ (y = m ∧ σ = (m % 2 == 1)) ∨ (y = m + 1 ∧ σ = false)

end

section Facts

variable {m : ℕ} {l : List ℕ} (hp : l.Perm (List.range m))
include hp

theorem lm_length : l.length = m := by simpa using hp.length_eq

theorem lm_nodup : l.Nodup := hp.nodup_iff.2 List.nodup_range

theorem lm_mem {y : ℕ} : y ∈ l ↔ y < m := by rw [hp.mem_iff, List.mem_range]

theorem lpt_zero' : lpt m l 0 = m + 1 := by simp [lpt]

theorem lpt_bridge {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ m) :
    lpt m l i = l[i - 1]'(by rw [lm_length hp]; omega) := by
  simp only [lpt, show i ≠ 0 by omega, ↓reduceIte, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by rw [lm_length hp]; omega)]
  rfl

theorem lpt_last : lpt m l (m + 1) = m := by
  simp [lpt, List.getD_eq_getElem?_getD, lm_length hp]

theorem lpt_bridge_lt {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ m) : lpt m l i < m := by
  rw [lpt_bridge hp h1 h2]; exact (lm_mem hp).1 (List.getElem_mem _)

theorem lpt_le {i : ℕ} (hi : i ≤ m + 1) : lpt m l i ≤ m + 1 := by
  rcases Nat.eq_zero_or_pos i with rfl | h0
  · simp [lpt_zero' hp]
  · rcases Nat.lt_or_ge m i with h | h
    · rw [show i = m + 1 by omega, lpt_last hp]; omega
    · have := lpt_bridge_lt hp h0 h; omega

theorem pos_lpt {i : ℕ} (hi : i ≤ m + 1) : pos m l (lpt m l i) = i := by
  rcases Nat.eq_zero_or_pos i with rfl | h0
  · simp [pos, lpt_zero' hp]
  rcases Nat.lt_or_ge m i with h | h
  · rw [show i = m + 1 by omega, lpt_last hp]; simp [pos]
  · have hb := lpt_bridge_lt hp h0 h
    simp only [pos, hb, ↓reduceIte]
    rw [lpt_bridge hp h0 h, List.Nodup.idxOf_getElem (lm_nodup hp)]
    omega

theorem pos_le {y : ℕ} (hy : y ≤ m + 1) : pos m l y ≤ m + 1 := by
  unfold pos
  split_ifs with h1 h2
  · have := List.idxOf_lt_length_of_mem ((lm_mem hp).2 h1); rw [lm_length hp] at this; omega
  · omega
  · omega

omit hp in
theorem bpar_add (i : ℕ) : ((i + 1) % 2 == 1) = !(i % 2 == 1) := by
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · have : (i + 1) % 2 = 1 := by omega
    simp [h, this]
  · have : (i + 1) % 2 = 0 := by omega
    simp [h, this]

omit hp in
theorem bpar_sub (i : ℕ) (hi : 1 ≤ i) : ((i - 1) % 2 == 1) = !(i % 2 == 1) := by
  have := bpar_add (i - 1)
  rw [show i - 1 + 1 = i by omega] at this
  rw [this]; simp

omit hp in
theorem bool_ne {a σ : Bool} (h : ¬ a = σ) : σ = !a := by cases a <;> cases σ <;> simp_all

theorem lpt_pos {y : ℕ} (hy : y ≤ m + 1) : lpt m l (pos m l y) = y := by
  unfold pos
  split_ifs with h1 h2
  · have hi := List.idxOf_lt_length_of_mem ((lm_mem hp).2 h1)
    rw [lm_length hp] at hi
    rw [lpt_bridge hp (by omega) (by omega)]
    simp
  · rw [h2, lpt_last hp]
  · rw [lpt_zero' hp]; omega

theorem lpt_inj {i j : ℕ} (hi : i ≤ m + 1) (hj : j ≤ m + 1) (h : lpt m l i = lpt m l j) :
    i = j := by
  rw [← pos_lpt hp hi, ← pos_lpt hp hj, h]

theorem nbr_lpt {i : ℕ} (hi : i ≤ m + 1) (σ : Bool) :
    nbr m l σ (lpt m l i) = if (i % 2 == 1) = σ then lpt m l (i + 1) else lpt m l (i - 1) := by
  simp [nbr, pos_lpt hp hi]

/-- The index of point `y`'s arc on side `σ`. -/
def arcIdx (m : ℕ) (l : List ℕ) (σ : Bool) (y : ℕ) : ℕ :=
  if (pos m l y % 2 == 1) = σ then pos m l y else pos m l y - 1

omit hp in
theorem parity_eq_iff (i : ℕ) (σ : Bool) : ((i % 2 == 1) = σ) ↔ (i % 2 = 1 ↔ σ = true) := by
  cases σ <;> simp

theorem arcIdx_spec {y : ℕ} {σ : Bool} (hs : HasSideM m y σ) :
    let j := arcIdx m l σ y
    j ≤ m ∧ (j % 2 == 1) = σ ∧
      ((y = lpt m l j ∧ nbr m l σ y = lpt m l (j + 1)) ∨
        (y = lpt m l (j + 1) ∧ nbr m l σ y = lpt m l j)) := by
  intro j
  have hy : y ≤ m + 1 := by rcases hs with h | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  have hpl := pos_le hp hy
  have hlp := lpt_pos hp hy
  set i := pos m l y with hi
  -- which points have which sides, by position
  have hside : (1 ≤ i ∧ i ≤ m) ∨ (i = m + 1 ∧ σ = (m % 2 == 1)) ∨ (i = 0 ∧ σ = false) := by
    rcases hs with h | ⟨h, hσ⟩ | ⟨h, hσ⟩
    · left
      have : i = l.idxOf y + 1 := by simp [hi, pos, h]
      have := List.idxOf_lt_length_of_mem ((lm_mem hp).2 h); rw [lm_length hp] at this
      omega
    · right; left; exact ⟨by simp [hi, pos, h], hσ⟩
    · right; right; exact ⟨by simp [hi, pos, h], hσ⟩
  simp only [j, arcIdx, ← hi, nbr]
  by_cases hpar : (i % 2 == 1) = σ
  · simp only [hpar, ↓reduceIte]
    refine ⟨?_, trivial, Or.inl ⟨hlp.symm, trivial⟩⟩
    rcases hside with h | ⟨h, hσ⟩ | ⟨h, hσ⟩
    · omega
    · exfalso; rw [h, hσ] at hpar; revert hpar
      rcases Nat.mod_two_eq_zero_or_one m with h2 | h2 <;> simp [h2, Nat.add_mod]
    · omega
  · simp only [hpar, ↓reduceIte]
    have hi1 : 1 ≤ i := by
      rcases hside with h | ⟨h, hσ⟩ | ⟨h, hσ⟩
      · omega
      · omega
      · exfalso; rw [h, hσ] at hpar; simp at hpar
    refine ⟨by omega, ?_, Or.inr ⟨by rw [show i - 1 + 1 = i by omega]; exact hlp.symm,
      by first | trivial | rfl⟩⟩
    rw [bpar_sub i hi1, bool_ne hpar]

theorem hasSide_of_arc {j : ℕ} (hj : j ≤ m) (k : ℕ) (hk : k = j ∨ k = j + 1) :
    HasSideM m (lpt m l k) (j % 2 == 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | h0
  · right; right; refine ⟨lpt_zero' hp, ?_⟩
    rcases hk with hk | hk <;> [subst hk; omega]; rfl
  · rcases Nat.lt_or_ge m k with h | h
    · right; left
      refine ⟨by rw [show k = m + 1 by omega, lpt_last hp], ?_⟩
      have : j = m := by omega
      rw [this]
    · left; exact lpt_bridge_lt hp h0 h

theorem nbr_hasSide {y : ℕ} {σ : Bool} (hs : HasSideM m y σ) :
    HasSideM m (nbr m l σ y) σ ∧ nbr m l σ (nbr m l σ y) = y ∧ nbr m l σ y ≠ y := by
  obtain ⟨hj, hσ, hc⟩ := arcIdx_spec hp hs
  set j := arcIdx m l σ y
  have hne : lpt m l j ≠ lpt m l (j + 1) := fun he => by
    have := lpt_inj hp (by omega) (by omega) he; omega
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨by rw [h2, ← hσ]; exact hasSide_of_arc hp hj _ (Or.inr rfl), ?_, ?_⟩
    · rw [h2, nbr_lpt hp (by omega)]
      have : ((j + 1) % 2 == 1) ≠ σ := by
        rw [← hσ]; rcases Nat.mod_two_eq_zero_or_one j with h | h <;> simp [h, Nat.add_mod]
      simp [this, h1]
    · rw [h2, h1]; exact Ne.symm hne
  · refine ⟨by rw [h2, ← hσ]; exact hasSide_of_arc hp hj _ (Or.inl rfl), ?_, ?_⟩
    · rw [h2, nbr_lpt hp (by omega), if_pos hσ, h1]
    · rw [h2, h1]; exact hne

/-- **Same-side arcs of a meander do not cross.** -/
theorem nbr_nc (hnc : NoCross (lpt m l) (m + 1)) {y y' : ℕ} {σ : Bool} (hs : HasSideM m y σ)
    (hs' : HasSideM m y' σ) (h1 : y' ≠ y) (h2 : y' ≠ nbr m l σ y) :
    ¬ Interleave y (nbr m l σ y) y' (nbr m l σ y') := by
  obtain ⟨hj, hσ, hc⟩ := arcIdx_spec hp hs
  obtain ⟨hj', hσ', hc'⟩ := arcIdx_spec hp hs'
  set j := arcIdx m l σ y
  set j' := arcIdx m l σ y'
  have hjj : j ≠ j' := by
    intro he
    rw [← he] at hc'
    rcases hc with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases hc' with ⟨b1, b2⟩ | ⟨b1, b2⟩
    · exact h1 (b1.trans a1.symm)
    · exact h2 (b1.trans a2.symm)
    · exact h2 (b1.trans a2.symm)
    · exact h1 (b1.trans a1.symm)
  have hpar : j % 2 = j' % 2 := by
    rw [← hσ'] at hσ
    rcases Nat.mod_two_eq_zero_or_one j with h | h <;>
      rcases Nat.mod_two_eq_zero_or_one j' with h' | h' <;> simp_all
  have key : ¬ Interleave (lpt m l j) (lpt m l (j + 1)) (lpt m l j') (lpt m l (j' + 1)) := by
    rcases Nat.lt_or_gt_of_ne hjj with hlt | hlt
    · exact hnc j' (by omega) j hlt hpar
    · have := hnc j (by omega) j' hlt hpar.symm
      intro hi
      apply this
      have hd1 : lpt m l j ≠ lpt m l j' := fun he => hjj (lpt_inj hp (by omega) (by omega) he)
      have hd2 : lpt m l j ≠ lpt m l (j' + 1) := fun he => by
        have := lpt_inj hp (by omega) (by omega) he
        omega
      have hd3 : lpt m l (j + 1) ≠ lpt m l j' := fun he => by
        have := lpt_inj hp (by omega) (by omega) he
        omega
      have hd4 : lpt m l (j + 1) ≠ lpt m l (j' + 1) := fun he => by
        have := lpt_inj hp (by omega) (by omega) he
        omega
      have hd5 : lpt m l j ≠ lpt m l (j + 1) := fun he => by
        have := lpt_inj hp (by omega) (by omega) he; omega
      have hd6 : lpt m l j' ≠ lpt m l (j' + 1) := fun he => by
        have := lpt_inj hp (by omega) (by omega) he; omega
      generalize lpt m l j = a at *
      generalize lpt m l (j + 1) = b at *
      generalize lpt m l j' = c at *
      generalize lpt m l (j' + 1) = d at *
      unfold Interleave at *
      omega
  rcases hc with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases hc' with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
    rw [a2, b2, a1, b1] <;>
    first
    | exact key
    | (rw [interleave_swap_left]; exact key)
    | (rw [interleave_swap_right]; exact key)
    | (rw [interleave_swap_left, interleave_swap_right]; exact key)

/-- Only the first bridge on the path is joined to the south end. -/
theorem nbr_eq_S {y : ℕ} {σ : Bool} (hs : HasSideM m y σ) (h : nbr m l σ y = m + 1) :
    σ = false ∧ y = lpt m l 1 := by
  obtain ⟨hj, hσ, hc⟩ := arcIdx_spec hp hs
  set j := arcIdx m l σ y
  have hS : m + 1 = lpt m l 0 := (lpt_zero' hp).symm
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h2, hS] at h; have := lpt_inj hp (by omega) (by omega) h; omega
  · rw [h2, hS] at h
    have hj0 := lpt_inj hp (by omega) (by omega) h
    rw [hj0] at hσ h1
    exact ⟨by simpa using hσ.symm, h1⟩

end Facts

end Arnold.TM
