import Arnold.TM.Meander

/-!
# Re-encoding a decoded run gives back its action sequence
-/

set_option linter.deprecated false

namespace Arnold.TM

open DSt

/-- Decode an action sequence: the crossing order of the river it builds. -/
def decode (m : ℕ) (w : List (Bool × Bool)) : List ℕ :=
  match druns m 0 DSt.empty w with
  | some D => (D.dn.headD default).seg.dropLast
  | none => []

theorem lpt_eq_getD {m : ℕ} {l : List ℕ} (hl : l.length = m) {i : ℕ} (hi : i ≤ m + 1) :
    lpt m l i = ((m + 1) :: (l ++ [m])).getD i 0 := by
  rcases Nat.eq_zero_or_pos i with rfl | h0
  · simp [lpt]
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    simp only [lpt, Nat.add_sub_cancel, Nat.add_one_ne_zero, ↓reduceIte, List.getD_cons_succ]
    rcases Nat.lt_or_ge k m with hk | hk
    · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show k < l.length by omega),
        List.getElem?_eq_getElem (show k < l.length by omega)]
    · have : k = m := by omega
      subst this
      simp [List.getD_eq_getElem?_getD, hl]

theorem hasSideM_of_hasSide {m y : ℕ} {σ : Bool} (h : HasSide m y σ) : HasSideM m y σ := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

/-- For an accepted run: the decoded river is a meander, and re-encoding it gives back the
action sequence. -/
theorem decode_spec {m : ℕ} {w : List (Bool × Bool)} (hw : w ∈ sufWords m (m + 1) 0)
    (hacc : runFrom m 0 init w = some final) :
    (decode m w).Perm (List.range m) ∧ NoCross (lpt m (decode m w)) (m + 1) ∧
      encode m (decode m w) = w := by
  obtain ⟨D, t, hr, hup, hdn, htE, h⟩ := decorated_of_accepted hw hacc
  have hdec : decode m w = t.seg.dropLast := by simp [decode, hr, hdn]
  rw [hdec]
  obtain ⟨hperm, hNC, hsplit, halt, hends⟩ := meander_of_final hup hdn htE h
  refine ⟨hperm, hNC, ?_⟩
  set l := t.seg.dropLast with hl
  set A := (t.origin, m + 1, false) :: D.arcs with hA
  have hlen := lm_length hperm
  have hg : D.get? (.s false 0) = some t := by simp [get?_s, stk, hdn]
  have honly : ∀ p T, D.get? p = some T → p = .s false 0 ∧ T = t := by
    intro p T hp
    cases p with
    | E => simp at hp
    | s σ i =>
      cases σ
      · simp only [get?_s, stk, Bool.false_eq_true, ↓reduceIte, hdn] at hp
        rcases i with _ | i
        · simp at hp; exact ⟨rfl, hp.symm⟩
        · simp at hp
      · simp [get?_s, stk, hup] at hp
  -- the river's arc at each point is an arc of `A`
  have hpath : ∀ y σ, HasSideM m y σ →
      (y, nbr m l σ y, σ) ∈ A ∨ (nbr m l σ y, y, σ) ∈ A := by
    intro y σ hs
    obtain ⟨hj, hσ, hc⟩ := arcIdx_spec hperm hs
    set j := arcIdx m l σ y
    have hside := halt j hj
    rw [hsplit, ← lpt_eq_getD hlen (show j ≤ m + 1 by omega),
      ← lpt_eq_getD hlen (show j + 1 ≤ m + 1 by omega), hσ] at hside
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2, h1] <;> rcases hside with hs' | hs'
    · exact Or.inl hs'
    · exact Or.inr hs'
    · exact Or.inr hs'
    · exact Or.inl hs'
  -- the action read at `y` on side `σ` is whether `y`'s arc goes east
  have hact : ∀ y < m + 1, ∀ σ, HasSide m y σ → openAct m l σ y = act m w y σ := by
    intro y hy σ hs
    have hsM := hasSideM_of_hasSide hs
    have hne := (nbr_hasSide hperm hsM).2.2
    have hwd := h.word y hy σ hs
    have hp := hpath y σ hsM
    unfold openAct
    split_ifs at hwd with hopen
    · rw [hopen]
      rcases hwd with ⟨i, T, hT, ho⟩ | ⟨b, hb⟩
      · obtain ⟨hpq, rfl⟩ := honly _ T hT
        simp only [Ref.s.injEq] at hpq
        obtain ⟨rfl, -⟩ := hpq
        have hS : (y, m + 1, false) ∈ A := by rw [← ho]; simp [hA]
        rcases hp with hp | hp
        · have := share hp hS (hends false) (by tauto)
          simp [this.2]; omega
        · have := share hp hS (hends false) (by tauto)
          exact absurd this.1 hne
      · have hb' : (y, b, σ) ∈ A := List.mem_cons_of_mem _ hb
        have hlt := h.arc_lt y b σ hb
        rcases hp with hp | hp
        · have := share hp hb' (hends σ) (by tauto)
          simp [this.2]; omega
        · have := share hp hb' (hends σ) (by tauto)
          exact absurd this.1 hne
    · rw [Bool.not_eq_true] at hopen
      rw [hopen]
      obtain ⟨a, ha⟩ := hwd
      have ha' : (a, y, σ) ∈ A := List.mem_cons_of_mem _ ha
      have hlt := h.arc_lt a y σ ha
      rcases hp with hp | hp
      · have := share hp ha' (hends σ) (by tauto)
        exact absurd this.2 hne
      · have := share hp ha' (hends σ) (by tauto)
        simp [this.1]; omega
  obtain ⟨hwlen, hacts⟩ := mem_sufWords m (m + 1) 0 w hw
  apply List.ext_getElem (by simp [encode, hwlen])
  intro y h1 h2
  simp only [encode, List.getElem_map, List.getElem_range]
  have hy : y < m + 1 := by simpa [encode] using h1
  have hwy : w.getD y (false, false) = w[y] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
  split_ifs with hym
  · rw [hact y hy true (Or.inl hym), hact y hy false (Or.inl hym)]
    simp only [act, hym, ↓reduceIte, hwy, Bool.false_eq_true]
  · have hye : y = m := by omega
    have hs : HasSide m m (m % 2 == 1) := Or.inr ⟨rfl, rfl⟩
    rw [hact m (by omega) _ hs]
    have hmem := hacts y h2
    simp only [zero_add, acts, show ¬ y < m from hym, ↓reduceIte, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    have hwm : w.getD m (false, false) = w[y] := by rw [← hye]; exact hwy
    simp only [act, lt_irrefl, ↓reduceIte, hwm]
    rcases hmem with hmem | hmem <;> rw [hmem]

end Arnold.TM
