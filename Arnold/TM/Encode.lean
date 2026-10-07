import Arnold.TM.EncodeAux

/-!
# Encoding: every meander's action sequence is accepted and decodes back to it
-/

set_option linter.deprecated false

namespace Arnold.TM

open DSt

/-- Along a meander's run: every recorded arc is an arc of the meander, and the open arcs on
each side are exactly those that cross the cut. -/
structure MI (m : ℕ) (l : List ℕ) (k : ℕ) (D : DSt) : Prop where
  arcs : ∀ a b τ, (a, b, τ) ∈ D.arcs → HasSideM m b τ ∧ a = nbr m l τ b
  stk : ∀ σ, (D.stk σ).map Strand.origin = stkF m l σ k

section

variable {m : ℕ} {l : List ℕ} (hp : l.Perm (List.range m)) (hnc : NoCross (lpt m l) (m + 1))
include hp hnc

/-- The top arc on a closing side is the one ending here. -/
theorem top_of_close {k : ℕ} {D : DSt} (hk : k ≤ m) (hM : MI m l k D) {σ : Bool}
    (hs : HasSideM m k σ) (hc : nbr m l σ k < k) :
    ∃ t, (D.stk σ).getLast? = some t ∧ t.origin = nbr m l σ k := by
  have h := (stkF_succ hp hnc hk σ).2.1 hs hc
  have hmap := hM.stk σ
  rw [h.1] at hmap
  have := congrArg List.getLast? hmap
  rw [List.getLast?_map, List.getLast?_concat] at this
  cases ht : (D.stk σ).getLast? with
  | none => rw [ht] at this; exact absurd this (by simp)
  | some t =>
    rw [ht] at this
    simp only [Option.map_some, Option.some.injEq] at this
    exact ⟨t, rfl, this⟩

omit hnc in
/-- **No loops.** At a bridge closing both sides, the two arcs being closed are not the two
ends of one piece: otherwise the piece, a stretch of the river between this bridge's two
neighbours, would have to pass through this bridge. -/
theorem no_cycle {k : ℕ} {ws : List (Bool × Bool)} {D : DSt} (hk : k < m)
    (hI : Inv m k ws D) (hM : MI m l k D) {u lo : Strand}
    (hu : (D.stk true).getLast? = some u) (hl : (D.stk false).getLast? = some lo)
    (huo : u.origin = nbr m l true k) (hlo : lo.origin = nbr m l false k) :
    u.ref ≠ .s false ((D.stk false).length - 1) := by
  intro hcyc
  obtain ⟨hug, _⟩ := DSt.get?_top D true u hu
  obtain ⟨hlg, _⟩ := DSt.get?_top D false lo hl
  have hrev : lo.seg = u.seg.reverse := hI.seg_rev _ u lo hug (by rw [hcyc]; exact hlg)
  have hhu := hI.seg_head _ u hug
  have hhl := hI.seg_head _ lo hlg
  have hlast : u.seg.getLast? = some lo.origin := by
    rw [← List.head?_reverse, ← hrev, hhl]
  -- positions along the piece move by one each step
  have hch : (u.seg.map (pos m l)).IsChain fun a b => a + 1 = b ∨ b + 1 = a := by
    rw [List.isChain_map]
    refine (hI.chain _ u hug).imp ?_
    rintro y z ⟨τ, hyz | hzy⟩
    · obtain ⟨hs, he⟩ := hM.arcs y z τ hyz
      rw [he]; rcases pos_nbr hp hs with h | h <;> omega
    · obtain ⟨hs, he⟩ := hM.arcs z y τ hzy
      rw [he]; rcases pos_nbr hp hs with h | h <;> omega
  have hks : ∀ σ, HasSideM m k σ := fun σ => Or.inl hk
  set i := pos m l k with hi
  have hki : lpt m l i = k := lpt_pos hp (by omega)
  have hi1 : 1 ≤ i ∧ i ≤ m := by
    have := pos_lpt hp (i := i) (by have := pos_le hp (y := k) (by omega); omega)
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · rw [h0, lpt_zero'] at hki; omega
    · refine ⟨h0, ?_⟩
      by_contra hc
      have : i = m + 1 := by have := pos_le hp (y := k) (by omega); omega
      rw [this, lpt_last hp] at hki; omega
  have hnb : ∀ σ, nbr m l σ k = if (i % 2 == 1) = σ then lpt m l (i + 1) else lpt m l (i - 1) := by
    intro σ; rw [← hki, nbr_lpt hp (by omega)]
  have hpu : pos m l u.origin = if (i % 2 == 1) = true then i + 1 else i - 1 := by
    rw [huo, hnb]; split_ifs <;> rw [pos_lpt hp (by omega)]
  have hpl : pos m l lo.origin = if (i % 2 == 1) = false then i + 1 else i - 1 := by
    rw [hlo, hnb]; split_ifs <;> rw [pos_lpt hp (by omega)]
  have hmem : i ∈ u.seg.map (pos m l) := by
    have hH : (u.seg.map (pos m l)).head? = some (pos m l u.origin) := by
      simp [List.head?_map, hhu]
    have hL : (u.seg.map (pos m l)).getLast? = some (pos m l lo.origin) := by
      simp [List.getLast?_map, hlast]
    by_cases hb : (i % 2 == 1) = true
    · have hb' : ¬ (i % 2 == 1) = false := by simp [hb]
      rw [if_pos hb] at hpu; rw [if_neg hb'] at hpl
      have hrev' : (u.seg.map (pos m l)).reverse.IsChain fun a b => a + 1 = b ∨ b + 1 = a := by
        rw [List.isChain_reverse]; exact hch.imp fun _ _ h => h.symm
      have := ivt_chain _ (pos m l lo.origin) (pos m l u.origin) i hrev'
        (by rw [List.head?_reverse, hL]) (by rw [List.getLast?_reverse, hH]) (by omega) (by omega)
      exact List.mem_reverse.1 this
    · have hb' : (i % 2 == 1) = false := by simpa using hb
      rw [if_neg hb] at hpu; rw [if_pos hb'] at hpl
      exact ivt_chain _ (pos m l u.origin) (pos m l lo.origin) i hch hH hL (by omega) (by omega)
  obtain ⟨y, hy, hyi⟩ := List.mem_map.1 hmem
  have hyk := hI.seg_lt _ u hug y hy
  have : y = k := by rw [← lpt_pos hp (y := y) (by omega), hyi, hki]
  omega

/-- One step of a meander's run. -/
theorem encode_step {k : ℕ} {ws : List (Bool × Bool)} {D : DSt} (hk : k ≤ m)
    (hI : Inv m k ws D) (hM : MI m l k D) :
    ∃ D', dstep m k D ((encode m l)[k]'(by simp [encode]; omega)) = some D' ∧
      MI m l (k + 1) D' := by
  have hentry : (encode m l)[k]'(by simp [encode]; omega) =
      if k < m then (openAct m l true k, openAct m l false k)
      else (openAct m l (m % 2 == 1) m, openAct m l (m % 2 == 1) m) := by
    simp [encode]
  rw [hentry]
  have hS := fun σ => stkF_succ hp hnc hk σ
  have hne : ∀ σ, HasSideM m k σ → nbr m l σ k ≠ k := fun σ hs => (nbr_hasSide hp hs).2.2
  -- what the stacks and arcs must become
  have hpush : ∀ σ, HasSideM m k σ → k < nbr m l σ k → ∀ (L : List Strand) (t : Strand),
      L.map Strand.origin = (D.stk σ).map Strand.origin → t.origin = k →
      (L ++ [t]).map Strand.origin = stkF m l σ (k + 1) := by
    intro σ hs hlt L t hL ht
    rw [List.map_append, hL, hM.stk σ, (hS σ).1 hs hlt]; simp [ht]
  have hpop : ∀ σ, HasSideM m k σ → nbr m l σ k < k → ∀ (L : List Strand),
      L.map Strand.origin = (D.stk σ).dropLast.map Strand.origin →
      L.map Strand.origin = stkF m l σ (k + 1) := by
    intro σ hs hlt L hL
    rw [hL, List.map_dropLast, hM.stk σ, ((hS σ).2.1 hs hlt).2]
  have hkeep : ∀ σ, ¬ HasSideM m k σ → ∀ (L : List Strand),
      L.map Strand.origin = (D.stk σ).map Strand.origin →
      L.map Strand.origin = stkF m l σ (k + 1) := by
    intro σ hs L hL
    rw [hL, hM.stk σ, (hS σ).2.2 hs]
  have harc : ∀ σ (t : Strand), HasSideM m k σ → t.origin = nbr m l σ k →
      ∀ a b τ, (a, b, τ) = (t.origin, k, σ) → HasSideM m b τ ∧ a = nbr m l τ b := by
    intro σ t hs ht a b τ he
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact ⟨hs, ht⟩
  by_cases hkm : k < m
  · rw [if_pos hkm]
    have hs : ∀ σ, HasSideM m k σ := fun σ => Or.inl hkm
    have hdir : ∀ σ, (openAct m l σ k = true ↔ k < nbr m l σ k) ∧
        (openAct m l σ k = false ↔ nbr m l σ k < k) := by
      intro σ
      have := hne σ (hs σ)
      refine ⟨by simp [openAct], ?_⟩
      unfold openAct
      rw [decide_eq_false_iff_not, not_lt]
      constructor <;> intro h <;> omega
    cases hT : openAct m l true k <;> cases hF : openAct m l false k
    · -- close both
      have hcT := (hdir true).2.1 hT
      have hcF := (hdir false).2.1 hF
      obtain ⟨u, hu, huo⟩ := top_of_close hp hnc hk hM (hs true) hcT
      obtain ⟨lo, hl, hlo⟩ := top_of_close hp hnc hk hM (hs false) hcF
      have hcyc := no_cycle hp hkm hI hM hu hl huo hlo
      simp only [dstep, if_pos hkm, hu, hl, hcyc, ↓reduceIte]
      refine ⟨_, rfl, ?_⟩
      constructor
      · intro a b τ hab
        simp only [arcs_addArc, arcs_link, arcs_pop, List.mem_cons] at hab
        rcases hab with he | he | hab
        · exact harc false lo (hs false) hlo a b τ he
        · exact harc true u (hs true) huo a b τ he
        · exact hM.arcs a b τ hab
      · intro σ
        apply hpop σ (hs σ) (by cases σ <;> assumption)
        simp only [stk_addArc]
        rw [stk_link, stk_link]
        cases σ <;> simp
    · -- close above, open below
      have hcT := (hdir true).2.1 hT
      have hoF := (hdir false).1.1 hF
      obtain ⟨u, hu, huo⟩ := top_of_close hp hnc hk hM (hs true) hcT
      simp only [dstep, if_pos hkm, dOpenClose, Bool.not_false, hu]
      refine ⟨_, rfl, ?_⟩
      constructor
      · intro a b τ hab
        simp only [arcs_addArc, arcs_push, arcs_link, arcs_pop, List.mem_cons] at hab
        rcases hab with he | hab
        · exact harc true u (hs true) huo a b τ (by simpa using he)
        · exact hM.arcs a b τ hab
      · intro σ
        cases σ
        · simp only [stk_addArc, stk_push, ↓reduceIte]
          apply hpush false (hs false) hoF
          · rw [stk_link]; simp
          · rfl
        · simp only [stk_addArc, stk_push, Bool.false_eq_true, ↓reduceIte]
          apply hpop true (hs true) hcT
          rw [stk_link]; simp [List.map_dropLast]
    · -- open above, close below
      have hoT := (hdir true).1.1 hT
      have hcF := (hdir false).2.1 hF
      obtain ⟨lo, hl, hlo⟩ := top_of_close hp hnc hk hM (hs false) hcF
      simp only [dstep, if_pos hkm, dOpenClose, Bool.not_true, hl]
      refine ⟨_, rfl, ?_⟩
      constructor
      · intro a b τ hab
        simp only [arcs_addArc, arcs_push, arcs_link, arcs_pop, List.mem_cons] at hab
        rcases hab with he | hab
        · exact harc false lo (hs false) hlo a b τ (by simpa using he)
        · exact hM.arcs a b τ hab
      · intro σ
        cases σ
        · simp only [stk_addArc, stk_push, Bool.true_eq_false, ↓reduceIte]
          apply hpop false (hs false) hcF
          rw [stk_link]; simp [List.map_dropLast]
        · simp only [stk_addArc, stk_push, ↓reduceIte]
          apply hpush true (hs true) hoT
          · rw [stk_link]; simp
          · rfl
    · -- open both
      have hoT := (hdir true).1.1 hT
      have hoF := (hdir false).1.1 hF
      simp only [dstep, if_pos hkm]
      refine ⟨_, rfl, ?_⟩
      constructor
      · intro a b τ hab
        simp only [arcs_push] at hab
        exact hM.arcs a b τ hab
      · intro σ
        cases σ
        · simp only [stk_push, Bool.true_eq_false, ↓reduceIte]
          exact hpush false (hs false) hoF _ _ (by simp) rfl
        · simp only [stk_push, Bool.false_eq_true, ↓reduceIte]
          exact hpush true (hs true) hoT _ _ (by simp) rfl
  · -- the east end
    rw [if_neg hkm]
    have hkm' : k = m := by omega
    set e := m % 2 == 1 with he
    have hse : HasSideM m k e := Or.inr (Or.inl ⟨hkm', rfl⟩)
    have hso : ∀ σ, σ ≠ e → ¬ HasSideM m k σ := by
      intro σ hσ hs
      rcases hs with h | ⟨_, h⟩ | ⟨h, _⟩
      · omega
      · exact hσ h
      · omega
    have hnee := hne e hse
    have hoa : openAct m l e m = openAct m l e k := congrArg (openAct m l e) hkm'.symm
    rw [hoa]
    by_cases ho : openAct m l e k = true
    · have hlt : k < nbr m l e k := by simpa [openAct] using ho
      simp only [dstep, if_neg hkm, ho, ↓reduceIte, ← he]
      refine ⟨_, rfl, ?_⟩
      constructor
      · intro a b τ hab; simp only [arcs_push] at hab; exact hM.arcs a b τ hab
      · intro σ
        by_cases hσ : σ = e
        · rw [hσ]
          simp only [stk_push, ↓reduceIte]
          exact hpush e hse hlt _ _ rfl rfl
        · simp only [stk_push, Ne.symm hσ, ↓reduceIte]
          exact hkeep σ (hso σ hσ) _ rfl
    · have hlt : nbr m l e k < k := by
        simp [openAct] at ho; omega
      obtain ⟨t, ht, hto⟩ := top_of_close hp hnc hk hM hse hlt
      obtain ⟨htg, _⟩ := DSt.get?_top D e t ht
      have htE : t.ref ≠ .E := hI.noE (by omega) _ t htg
      rw [Bool.not_eq_true] at ho
      simp only [dstep, if_neg hkm, ho, ← he, ht, htE, Bool.false_eq_true, ↓reduceIte]
      refine ⟨_, rfl, ?_⟩
      constructor
      · intro a b τ hab
        simp only [arcs_addArc, arcs_link, arcs_pop, List.mem_cons] at hab
        rcases hab with he' | hab
        · exact harc e t hse hto a b τ he'
        · exact hM.arcs a b τ hab
      · intro σ
        simp only [stk_addArc]
        by_cases hσ : σ = e
        · rw [hσ]
          apply hpop e hse hlt
          rw [stk_link]; simp [List.map_dropLast]
        · apply hkeep σ (hso σ hσ)
          rw [stk_link]; simp [Ne.symm hσ]

end

end Arnold.TM
