import Arnold.TM.Run
import Arnold.Fast

/-!
# Decoding: every accepted action sequence is a meander
-/

set_option linter.deprecated false

namespace Arnold.TM

open DSt

/-- Arc ends on side `σ` of an arc list. -/
def endsA (A : List (ℕ × ℕ × Bool)) (σ : Bool) : List ℕ :=
  A.flatMap fun a => if a.2.2 = σ then [a.1, a.2.1] else []

/-- `y` and `z` are joined by an arc of `A` on side `σ`. -/
def Side (A : List (ℕ × ℕ × Bool)) (y z : ℕ) (σ : Bool) : Prop := (y, z, σ) ∈ A ∨ (z, y, σ) ∈ A

/-- Two arcs on one side with a common end are the same arc. -/
theorem share {A : List (ℕ × ℕ × Bool)} {a b c d : ℕ} {τ : Bool} (h1 : (a, b, τ) ∈ A)
    (h2 : (c, d, τ) ∈ A) (hn : (endsA A τ).Nodup) (hs : a = c ∨ a = d ∨ b = c ∨ b = d) :
    a = c ∧ b = d := by
  by_contra hne
  have hne' : (a, b, τ) ≠ (c, d, τ) := fun he => by
    simp only [Prod.mk.injEq] at he; exact hne ⟨he.1, he.2.1⟩
  have hd := (List.nodup_flatMap.1 hn).2
  haveI : Std.Symm (Function.onFun List.Disjoint
      fun a : ℕ × ℕ × Bool => if a.2.2 = τ then [a.1, a.2.1] else []) :=
    ⟨fun _ _ h => List.Disjoint.symm h⟩
  have := hd.forall h1 h2 hne'
  simp only [Function.onFun, ↓reduceIte] at this
  rcases hs with rfl | rfl | rfl | rfl <;> simp [List.Disjoint] at this

theorem interleave_swap_left (a b c d : ℕ) : Interleave a b c d ↔ Interleave b a c d := by
  unfold Interleave; rw [min_comm, max_comm]

theorem interleave_swap_right (a b c d : ℕ) : Interleave a b c d ↔ Interleave a b d c := by
  unfold Interleave; tauto

theorem not_interleave_of_side {A : List (ℕ × ℕ × Bool)} {σ : Bool}
    (hnc : ∀ a b a' b', (a, b, σ) ∈ A → (a', b', σ) ∈ A → ¬ Interleave a b a' b')
    {y z y' z' : ℕ} (h1 : Side A y z σ) (h2 : Side A y' z' σ) : ¬ Interleave y z y' z' := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact hnc _ _ _ _ h1 h2
  · rw [interleave_swap_right]; exact hnc _ _ _ _ h1 h2
  · rw [interleave_swap_left]; exact hnc _ _ _ _ h1 h2
  · rw [interleave_swap_left, interleave_swap_right]; exact hnc _ _ _ _ h1 h2

/-- **Decoding.** The last piece of an accepted run, after the south end, is a meander. -/
theorem meander_of_final {m : ℕ} {w : List (Bool × Bool)} {D : DSt} {t : Strand}
    (hup : D.up = []) (hdn : D.dn = [t]) (htE : t.ref = .E) (h : Inv m (m + 1) w D) :
    t.seg.dropLast.Perm (List.range m) ∧ NoCross (lpt m t.seg.dropLast) (m + 1) ∧
      t.seg = t.seg.dropLast ++ [m] ∧
      (∀ i ≤ m, Side ((t.origin, m + 1, false) :: D.arcs) (((m + 1) :: t.seg).getD i 0)
        (((m + 1) :: t.seg).getD (i + 1) 0) (i % 2 == 1)) ∧
      ∀ σ, (endsA ((t.origin, m + 1, false) :: D.arcs) σ).Nodup := by
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
  set seg := t.seg with hseg
  have hcov : ∀ y < m + 1, y ∈ seg := by
    intro y hy
    obtain ⟨p, T, hp, hyT⟩ := h.cover y hy
    obtain ⟨_, rfl⟩ := honly p T hp
    exact hyT
  have hlt : ∀ y ∈ seg, y < m + 1 := h.seg_lt _ t hg
  have hnd : seg.Nodup := h.seg_nodup _ t hg
  have hlast : seg.getLast? = some m := h.seg_E _ t hg htE
  have hhead : seg.head? = some t.origin := h.seg_head _ t hg
  have hperm : seg.Perm (List.range (m + 1)) :=
    (List.perm_ext_iff_of_nodup hnd List.nodup_range).2 fun y => by
      simp only [List.mem_range]; exact ⟨hlt y, hcov y⟩
  have hlen : seg.length = m + 1 := by simpa using hperm.length_eq
  have hlen' : t.seg.length = m + 1 := hlen
  have hsplit : seg = seg.dropLast ++ [m] :=
    (List.dropLast_append_getLast? m hlast).symm
  have hτperm : seg.dropLast.Perm (List.range m) := by
    have : (seg.dropLast ++ [m]).Perm (List.range m ++ [m]) := by
      rw [← hsplit, ← List.range_succ]; exact hperm
    exact List.perm_append_right_iff _ |>.1 this
  -- the full path: south end, then the piece
  set q := (m + 1) :: seg with hq
  set Q : ℕ → ℕ := fun k => q.getD k 0 with hQ
  have hqlen : q.length = m + 2 := by simp [hq, hlen]
  have hqnd : q.Nodup := List.nodup_cons.2 ⟨fun hm => by have := hlt _ hm; omega, hnd⟩
  have hQinj : ∀ i j, i ≤ m + 1 → j ≤ m + 1 → Q i = Q j → i = j := by
    intro i j hi hj he
    simp only [hQ, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < q.length by omega),
      List.getElem?_eq_getElem (show j < q.length by omega), Option.getD_some] at he
    exact (hqnd.getElem_inj_iff).1 he
  -- arcs, with the south end's arc added
  set A := (t.origin, m + 1, false) :: D.arcs with hA
  have hJ : ∀ i ≤ m, Joined A (Q i) (Q (i + 1)) := by
    intro i hi
    rcases i with _ | i
    · refine ⟨false, Or.inr ?_⟩
      have h1 : Q 1 = t.origin := by
        simp only [hQ, hq, List.getD_cons_succ]
        cases hs : seg with
        | nil => rw [hs] at hhead; simp at hhead
        | cons y l => rw [hs] at hhead; simp at hhead; simp [hhead]
      have h0 : Q 0 = m + 1 := by simp [hQ, hq]
      rw [h0, h1]; simp [hA]
    · have hc := (List.isChain_iff_getElem.1 (h.chain _ t hg)) i (by omega)
      obtain ⟨τ, hτ⟩ := hc
      refine ⟨τ, ?_⟩
      have e1 : Q (i + 1) = seg[i]'(by omega) := by
        simp [hQ, hq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < seg.length by omega)]
      have e2 : Q (i + 1 + 1) = seg[i + 1]'(by omega) := by
        simp [hQ, hq, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (show i + 1 < seg.length by omega)]
      rw [e1, e2]
      rcases hτ with hτ | hτ
      · exact Or.inl (List.mem_cons_of_mem _ hτ)
      · exact Or.inr (List.mem_cons_of_mem _ hτ)
  have hends : ∀ σ, (endsA A σ).Nodup := by
    intro σ
    have hu := h.uniq σ
    have hlt' := h.ends_lt σ
    cases σ
    · simp only [ends, stk, Bool.false_eq_true, ↓reduceIte, hdn, List.map_cons,
        List.map_nil] at hu
      simp only [endsA, hA, List.flatMap_cons, ↓reduceIte]
      refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, (List.nodup_cons.1 hu).2⟩⟩
      · intro hm
        rcases List.mem_cons.1 hm with hm | hm
        · have := h.orig_lt _ t hg; omega
        · exact (List.nodup_cons.1 hu).1 (by simpa using hm)
      · intro hm
        have := hlt' (m + 1) (List.mem_append_right _ (by simpa using hm))
        omega
    · simp only [ends, stk, ↓reduceIte, hup, List.map_nil, List.nil_append] at hu
      simpa [endsA, hA] using hu
  have hncA : ∀ σ a b a' b', (a, b, σ) ∈ A → (a', b', σ) ∈ A → ¬ Interleave a b a' b' := by
    intro σ a b a' b' h1 h2
    have hS : ∀ a b, (a, b, false) ∈ D.arcs → ¬ Interleave t.origin (m + 1) a b ∧
        ¬ Interleave a b t.origin (m + 1) := by
      intro a b hab
      have hl := h.arc_lt a b false hab
      have hn := h.nest false 0 t hg a b hab
      unfold Interleave; omega
    simp only [hA, List.mem_cons, Prod.mk.injEq] at h1 h2
    rcases h1 with ⟨rfl, rfl, rfl⟩ | h1 <;> rcases h2 with ⟨rfl, rfl, h2'⟩ | h2
    · unfold Interleave; omega
    · exact (hS a' b' h2).1
    · subst h2'; exact (hS a b h1).2
    · exact h.nc a b a' b' σ h1 h2
  -- the sides of the path's arcs alternate, starting below
  have halt : ∀ i ≤ m, Side A (Q i) (Q (i + 1)) (i % 2 == 1) := by
    intro i
    induction i with
    | zero =>
      intro _
      obtain ⟨τ, hτ⟩ := hJ 0 (by omega)
      have h1 : Q 1 = t.origin := by
        simp only [hQ, hq, List.getD_cons_succ]
        cases hs : seg with
        | nil => rw [hs] at hhead; simp at hhead
        | cons y l => rw [hs] at hhead; simp at hhead; simp [hhead]
      have h0 : Q 0 = m + 1 := by simp [hQ, hq]
      right; rw [h0, h1]; simp [hA]
    | succ i ih =>
      intro hi
      have hprev := ih (by omega)
      obtain ⟨τ, hτ⟩ := hJ (i + 1) hi
      have hσ : τ = !(i % 2 == 1) := by
        by_contra hne
        have hτ' : τ = (i % 2 == 1) := by
          revert hne; generalize (i % 2 == 1) = b; cases τ <;> cases b <;> decide
        rw [hτ'] at hτ
        have hn := hends (i % 2 == 1)
        -- both arcs have the end `Q (i+1)`, so they coincide
        have key : Q i = Q (i + 1 + 1) ∨ Q (i + 1) = Q (i + 1 + 1) ∨ Q i = Q (i + 1) := by
          rcases hprev with hp | hp <;> rcases hτ with ht | ht
          · have := share hp ht hn (by tauto); tauto
          · have := share hp ht hn (by tauto); tauto
          · have := share hp ht hn (by tauto); tauto
          · have := share hp ht hn (by tauto); tauto
        rcases key with k | k | k
        · have := hQinj _ _ (by omega) (by omega) k; omega
        · have := hQinj _ _ (by omega) (by omega) k; omega
        · have := hQinj _ _ (by omega) (by omega) k; omega
      rw [hσ] at hτ
      have : (!(i % 2 == 1)) = ((i + 1) % 2 == 1) := by
        rcases Nat.mod_two_eq_zero_or_one i with h2 | h2 <;>
          simp [h2, Nat.add_mod]
      rw [this] at hτ
      rcases hτ with ht | ht
      · exact Or.inl ht
      · exact Or.inr ht
  -- the decoded river's points are the path's points
  have hlpt : ∀ k ≤ m + 1, lpt m seg.dropLast k = Q k := by
    intro k hk
    have hdl : seg.dropLast.length = m := by simp [hlen]
    unfold lpt
    split_ifs with hk0
    · simp [hk0, hQ, hq]
    · rcases Nat.lt_or_ge (k - 1) m with hkm | hkm
      · simp only [hQ, hq, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by simp; omega)]
        simp only [Option.getD_some, List.getElem_dropLast]
        rw [List.getElem_cons]; simp [show k ≠ 0 from hk0]
      · have hkm' : k = m + 1 := by omega
        subst hkm'
        simp only [Nat.add_sub_cancel, List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (show seg.dropLast.length ≤ m by omega), Option.getD_none]
        simp only [hQ, hq, List.getD_cons_succ]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
        simp only [Option.getD_some]
        have := List.getLast_eq_getElem (l := seg) (by intro he; simp [he] at hlen)
        rw [List.getLast?_eq_some_getLast (by intro he; simp [he] at hlen), Option.some.injEq,
          this] at hlast
        simpa [hlen] using hlast.symm
  have hNC : NoCross (lpt m seg.dropLast) (m + 1) := by
    rw [noCross_congr_pts hlpt]
    intro k hk j hjk hpar
    have hsj := halt j (by omega)
    have hsk := halt k (by omega)
    have hσ : (j % 2 == 1) = (k % 2 == 1) := by rw [hpar]
    rw [hσ] at hsj
    exact not_interleave_of_side (hncA _) hsj hsk
  exact ⟨hτperm, hNC, hsplit, halt, hends⟩

end Arnold.TM
