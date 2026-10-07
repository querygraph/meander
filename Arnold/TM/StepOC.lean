import Arnold.TM.Invariant

/-!
# Invariant: open one side, close the other
-/

set_option linter.deprecated false

namespace Arnold.TM

open DSt

theorem Joined.cons {A : List (ℕ × ℕ × Bool)} {y z : ℕ} (a : ℕ × ℕ × Bool) (h : Joined A y z) :
    Joined (a :: A) y z := by
  obtain ⟨τ, h | h⟩ := h
  · exact ⟨τ, Or.inl (List.mem_cons_of_mem _ h)⟩
  · exact ⟨τ, Or.inr (List.mem_cons_of_mem _ h)⟩

theorem chain_cons {A : List (ℕ × ℕ × Bool)} {l : List ℕ} (a : ℕ × ℕ × Bool)
    (h : l.IsChain (Joined A)) : l.IsChain (Joined (a :: A)) :=
  h.imp fun _ _ hj => hj.cons a

theorem getLast?_reverse_eq {l : List ℕ} {y : ℕ} (h : l.head? = some y) :
    l.reverse.getLast? = some y := by
  simpa [List.getLast?_reverse] using h

theorem ends_split (D : DSt) (σ : Bool) :
    ends D σ = (D.stk σ).map Strand.origin ++
      D.arcs.flatMap fun a => if a.2.2 = σ then [a.1, a.2.1] else [] := rfl

theorem inv_OC {m x : ℕ} {w : List (Bool × Bool)} {D D' : DSt} {σ : Bool} (h : Inv m x w D)
    (hx : x < m) (hD : dOpenClose D x σ = some D') :
    Inv m (x + 1) (w ++ [if σ then (true, false) else (false, true)]) D' := by
  unfold dOpenClose at hD
  cases htop : (D.stk (!σ)).getLast? with
  | none => rw [htop] at hD; simp at hD
  | some t =>
  rw [htop] at hD
  simp only [Option.some.injEq] at hD
  subst hD
  set c := !σ with hc
  have hcσ : c ≠ σ := by cases σ <;> simp [hc]
  set nσ := (D.stk σ).length with hnσ
  set tc := (D.stk c).length - 1 with htc
  obtain ⟨htg, hcpos⟩ := DSt.get?_top D c t htop
  rw [← htc] at htg
  set p := t.ref with hp
  have hnoE := h.noE (by omega)
  -- the partner `p` of the closed arc `t`
  obtain ⟨tp, hpg, hpref⟩ : ∃ tp, D.get? p = some tp ∧ tp.ref = .s c tc := by
    rcases h.ref_ok _ t htg with hE | h'
    · exact absurd hE (hnoE _ t htg)
    · exact h'
  have hpne : p ≠ .s c tc := h.ref_ne _ t htg
  have hpσ : p ≠ .s σ nσ := by
    intro he; rw [he] at hpg; have := DSt.lt_of_get? hpg; omega
  set U : Strand := ⟨p, x, x :: t.seg⟩ with hU
  set P' : Strand := ⟨.s σ nσ, tp.origin, tp.seg ++ [x]⟩ with hP'
  set D' := (((D.pop c).link p (.s σ nσ) [x]).push σ U).addArc (t.origin, x, c) with hD'
  have hlenσ : (((D.pop c).link p (.s σ nσ) [x]).stk σ).length = nσ := by
    rw [length_stk_link, stk_pop, if_neg hcσ]
  have hg : ∀ P, D'.get? P = if P = .s σ nσ then some U else
      (if P = .s c tc then none else D.get? P).map
        fun T => if P = p then ⟨.s σ nσ, T.origin, T.seg ++ [x]⟩ else T := by
    intro P
    rw [hD', get?_addArc, get?_push, hlenσ, get?_link, get?_pop]
  have hUg : D'.get? (.s σ nσ) = some U := by rw [hg]; simp
  have hPg : D'.get? p = some P' := by
    rw [hg, if_neg hpσ, if_neg hpne, hpg]; simp [hP']
  have hold : ∀ Q T, D.get? Q = some T → Q ≠ .s c tc → Q ≠ p → D'.get? Q = some T := by
    intro Q T hQ h1 h2
    have hQσ : Q ≠ .s σ nσ := by
      intro he; rw [he] at hQ; have := DSt.lt_of_get? hQ; omega
    rw [hg, if_neg hQσ, if_neg h1, hQ]; simp [h2]
  have hnew : ∀ P T, D'.get? P = some T →
      (P = .s σ nσ ∧ T = U) ∨ (P = p ∧ T = P') ∨
      (P ≠ .s σ nσ ∧ P ≠ .s c tc ∧ P ≠ p ∧ D.get? P = some T) := by
    intro P T hP
    rw [hg] at hP
    by_cases h1 : P = .s σ nσ
    · rw [if_pos h1] at hP; exact Or.inl ⟨h1, (Option.some.inj hP).symm⟩
    rw [if_neg h1] at hP
    by_cases h2 : P = .s c tc
    · rw [if_pos h2] at hP; simp at hP
    rw [if_neg h2] at hP
    by_cases h3 : P = p
    · rw [h3, hpg] at hP
      simp only [Option.map_some, ↓reduceIte, Option.some.injEq] at hP
      exact Or.inr (Or.inl ⟨h3, by rw [← hP]⟩)
    · rcases hD0 : D.get? P with _ | T0
      · rw [hD0] at hP; simp at hP
      · rw [hD0] at hP
        simp only [Option.map_some, h3, ↓reduceIte, Option.some.injEq] at hP
        exact Or.inr (Or.inr ⟨h1, h2, h3, by cases hP; rfl⟩)
  -- origins of surviving arcs do not change
  have horig : ∀ P T, D'.get? P = some T → P ≠ .s σ nσ →
      ∃ T0, D.get? P = some T0 ∧ T.origin = T0.origin ∧ P ≠ .s c tc := by
    intro P T hP hPσ
    rcases hnew P T hP with ⟨h1, _⟩ | ⟨rfl, rfl⟩ | ⟨_, h2, _, h3⟩
    · exact absurd h1 hPσ
    · exact ⟨tp, hpg, rfl, hpne⟩
    · exact ⟨T, h3, rfl, h2⟩
  have hseg_rev_t : tp.seg = t.seg.reverse := h.seg_rev _ t tp htg hpg
  have ht_head : t.seg.head? = some t.origin := h.seg_head _ t htg
  have hto : t.origin < x := h.orig_lt _ t htg
  have hxt : ∀ P T, D.get? P = some T → x ∉ T.seg := fun P T hP hx' => by
    have := h.seg_lt P T hP x hx'; omega
  have harcs : D'.arcs = (t.origin, x, c) :: D.arcs := by simp [hD']
  -- old strands other than `t` and `p` keep their partner
  have hrefold : ∀ P T, D.get? P = some T → P ≠ .s c tc → P ≠ p →
      T.ref = .E ∨ ∃ T', D'.get? T.ref = some T' ∧ D.get? T.ref = some T' ∧ T'.ref = P := by
    intro P T hP h1 h2
    rcases h.ref_ok P T hP with hE | ⟨T', hT', hr⟩
    · exact Or.inl hE
    · refine Or.inr ⟨T', hold _ _ hT' ?_ ?_, hT', hr⟩
      · intro he; rw [he] at hT'; rw [htg] at hT'; cases hT'
        exact h2 (by rw [hp]; exact hr.symm)
      · intro he; rw [he] at hT'; rw [hpg] at hT'; cases hT'
        exact h1 (by rw [← hr, hpref])
  constructor
  · simp [h.wlen]
  · intro P T hP
    rcases hnew P T hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨_, h2, h3, hP'⟩
    · simpa [hU] using hpσ
    · simpa [hP'] using Ne.symm hpσ
    · exact h.ref_ne P T hP'
  · intro P T hP
    rcases hnew P T hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨_, h2, h3, hP'⟩
    · exact Or.inr ⟨P', hPg, rfl⟩
    · exact Or.inr ⟨U, hUg, rfl⟩
    · rcases hrefold P T hP' h2 h3 with hE | ⟨T', hT', _, hr⟩
      · exact Or.inl hE
      · exact Or.inr ⟨T', hT', hr⟩
  · intro P T hP hE
    rcases hnew P T hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨_, _, _, hP'⟩
    · exact absurd hE (hnoE _ t htg)
    · simp [hP'] at hE
    · exact absurd hE (hnoE P T hP')
  · intro P T hP
    by_cases hPσ : P = .s σ nσ
    · subst hPσ; rw [hUg] at hP; cases hP; simp [hU]
    · obtain ⟨T0, hT0, ho, _⟩ := horig P T hP hPσ
      have := h.orig_lt P T0 hT0; omega
  · intro τ i j T T' hi hj hij
    by_cases hjσ : Ref.s τ j = .s σ nσ
    · simp only [Ref.s.injEq] at hjσ
      obtain ⟨rfl, rfl⟩ := hjσ
      rw [hUg] at hj; cases hj
      obtain ⟨T0, hT0, ho, _⟩ := horig _ T hi (by simp; omega)
      have := h.orig_lt _ T0 hT0; simp [hU]; omega
    · by_cases hiσ : Ref.s τ i = .s σ nσ
      · simp only [Ref.s.injEq] at hiσ
        obtain ⟨rfl, rfl⟩ := hiσ
        obtain ⟨T0, hT0, _, _⟩ := horig _ T' hj hjσ
        have := DSt.lt_of_get? hT0; omega
      · obtain ⟨T0, hT0, ho, _⟩ := horig _ T hi hiσ
        obtain ⟨T0', hT0', ho', _⟩ := horig _ T' hj hjσ
        rw [ho, ho']; exact h.sorted τ i j T0 T0' hT0 hT0' hij
  · intro P T hP
    rcases hnew P T hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨_, _, _, hP'⟩
    · exact List.nodup_cons.2 ⟨hxt _ t htg, h.seg_nodup _ t htg⟩
    · simp only [hP']
      exact (h.seg_nodup _ tp hpg).append (List.nodup_singleton x)
        (List.disjoint_singleton.2 (hxt _ tp hpg))
    · exact h.seg_nodup P T hP'
  · intro P T hP
    rcases hnew P T hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨_, _, _, hP'⟩
    · simp [hU]
    · have hh := h.seg_head _ tp hpg
      have hne : tp.seg ≠ [] := by intro he; simp [he] at hh
      simp [hP', List.head?_append, hh]
    · exact h.seg_head P T hP'
  · intro P T hP y hy
    rcases hnew P T hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨_, _, _, hP'⟩
    · simp only [hU, List.mem_cons] at hy
      rcases hy with rfl | hy
      · omega
      · have := h.seg_lt _ t htg y hy; omega
    · simp only [hP', List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | rfl
      · have := h.seg_lt _ tp hpg y hy; omega
      · omega
    · have := h.seg_lt P T hP' y hy; omega
  · intro P T hP hE
    rcases hnew P T hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨_, _, _, hP'⟩
    · exact absurd hE (hnoE _ t htg)
    · simp [hP'] at hE
    · exact absurd hE (hnoE P T hP')
  · intro P T T' hP hT'
    rcases hnew P T hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨_, h2, h3, hP'⟩
    · rw [hPg] at hT'; cases hT'; simp [hP', hU, hseg_rev_t]
    · rw [hUg] at hT'; cases hT'; simp [hP', hU, hseg_rev_t]
    · rcases hrefold P T hP' h2 h3 with hE | ⟨T2, hT2, hT2', _⟩
      · exact absurd hE (hnoE P T hP')
      · rw [hT2, Option.some.injEq] at hT'
        rw [← hT']
        exact h.seg_rev P T T2 hP' hT2'
  · intro P T hP
    rw [harcs]
    rcases hnew P T hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨_, _, _, hP'⟩
    · simp only [hU]
      have hc := chain_cons (t.origin, x, c) (h.chain _ t htg)
      cases hts : t.seg with
      | nil => simp
      | cons y l =>
        rw [hts] at hc ht_head
        simp only [List.head?_cons, Option.some.injEq] at ht_head
        rw [List.isChain_cons_cons]
        exact ⟨⟨c, Or.inr (by rw [ht_head]; simp)⟩, hc⟩
    · simp only [hP']
      refine (chain_cons (t.origin, x, c) (h.chain _ tp hpg)).append (by simp) ?_
      intro a ha b hb
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
      subst hb
      rw [hseg_rev_t, getLast?_reverse_eq ht_head] at ha
      simp only [Option.mem_def, Option.some.injEq] at ha
      subst ha
      exact ⟨c, Or.inl (by simp)⟩
    · exact chain_cons _ (h.chain P T hP')
  · intro P Q T T' hP hQ hQP hQr
    -- the pieces after the step, in terms of the old ones
    have key : ∀ P T, D'.get? P = some T → (P = .s σ nσ ∧ T.seg = x :: t.seg) ∨
        (P = p ∧ T.seg = tp.seg ++ [x]) ∨
        (P ≠ .s σ nσ ∧ P ≠ .s c tc ∧ P ≠ p ∧ D.get? P = some T) := by
      intro P T hP
      rcases hnew P T hP with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | h1
      · exact Or.inl ⟨h1, rfl⟩
      · exact Or.inr (Or.inl ⟨h1, rfl⟩)
      · exact Or.inr (Or.inr h1)
    have dt : ∀ Q T', D.get? Q = some T' → Q ≠ .s c tc → Q ≠ p → t.seg.Disjoint T'.seg :=
      fun Q T' hQ h1 h2 => h.disj _ Q t T' htg hQ h1 h2
    have dp : ∀ Q T', D.get? Q = some T' → Q ≠ .s c tc → Q ≠ p → tp.seg.Disjoint T'.seg :=
      fun Q T' hQ h1 h2 => h.disj p Q tp T' hpg hQ h2 (by rw [hpref]; exact h1)
    rcases key P T hP with ⟨rfl, hs⟩ | ⟨rfl, hs⟩ | ⟨h1, h2, h3, hP'⟩ <;>
      rcases key Q T' hQ with ⟨rfl, hs'⟩ | ⟨rfl, hs'⟩ | ⟨h1', h2', h3', hQ'⟩
    · exact absurd rfl hQP
    · rw [hUg] at hP; cases hP; exact absurd rfl hQr
    · rw [hs]
      exact List.disjoint_cons_left.2 ⟨hxt _ _ hQ', dt _ _ hQ' h2' h3'⟩
    · rw [hPg] at hP; cases hP; exact absurd rfl hQr
    · exact absurd rfl hQP
    · rw [hs]
      exact List.disjoint_append_left.2 ⟨dp _ _ hQ' h2' h3',
        List.singleton_disjoint.2 (hxt _ _ hQ')⟩
    · rw [hs']
      exact (List.disjoint_cons_left.2 ⟨hxt _ _ hP', dt _ _ hP' h2 h3⟩).symm
    · rw [hs']
      exact (List.disjoint_append_left.2 ⟨dp _ _ hP' h2 h3,
        List.singleton_disjoint.2 (hxt _ _ hP')⟩).symm
    · exact h.disj P Q T T' hP' hQ' hQP hQr
  · intro y hy
    by_cases hyx : y = x
    · exact ⟨_, _, hUg, by simp [hU, hyx]⟩
    · obtain ⟨P, T, hP, hyt⟩ := h.cover y (by omega)
      by_cases h1 : P = .s c tc
      · subst h1; rw [htg] at hP; cases hP
        exact ⟨_, _, hUg, by simp [hU, hyt]⟩
      · by_cases h2 : P = p
        · subst h2; rw [hpg] at hP; cases hP
          exact ⟨_, _, hPg, by simp [hP', hyt]⟩
        · exact ⟨P, T, hold P T hP h1 h2, hyt⟩
  · intro a b τ hab
    rw [harcs] at hab
    rcases List.mem_cons.1 hab with he | hab
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      omega
    · have := h.arc_lt a b τ hab; omega
  · intro a b a' b' τ h1 h2
    rw [harcs] at h1 h2
    have hnew_nc : ∀ a b, (a, b, c) ∈ D.arcs → ¬ Interleave t.origin x a b ∧
        ¬ Interleave a b t.origin x := by
      intro a b hab
      have hlt := h.arc_lt a b c hab
      have hn := h.nest c tc t htg a b hab
      unfold Interleave
      omega
    rcases List.mem_cons.1 h1 with he1 | h1' <;> rcases List.mem_cons.1 h2 with he2 | h2'
    · simp only [Prod.mk.injEq] at he1 he2
      obtain ⟨ha, hb, -⟩ := he1
      obtain ⟨ha', hb', -⟩ := he2
      rw [ha, hb, ha', hb']; unfold Interleave; omega
    · simp only [Prod.mk.injEq] at he1
      obtain ⟨ha, hb, hτ⟩ := he1
      rw [ha, hb]; rw [hτ] at h2'
      exact (hnew_nc a' b' h2').1
    · simp only [Prod.mk.injEq] at he2
      obtain ⟨ha, hb, hτ⟩ := he2
      rw [ha, hb]; rw [hτ] at h1'
      exact (hnew_nc a b h1').2
    · exact h.nc a b a' b' τ h1' h2'
  · intro τ i T hi a b hab
    rw [harcs] at hab
    by_cases hiσ : Ref.s τ i = .s σ nσ
    · simp only [Ref.s.injEq] at hiσ
      obtain ⟨rfl, rfl⟩ := hiσ
      rw [hUg] at hi; cases hi
      rcases List.mem_cons.1 hab with he | hab
      · simp only [Prod.mk.injEq] at he; exact absurd he.2.2.symm hcσ
      · have := h.arc_lt a b _ hab; simp [hU]; omega
    · obtain ⟨T0, hT0, ho, hne⟩ := horig _ T hi hiσ
      rw [ho]
      rcases List.mem_cons.1 hab with he | hab
      · simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl, rfl⟩ := he
        have hi' := DSt.lt_of_get? hT0
        have hit : i ≠ tc := fun he => hne (by rw [he])
        have := h.sorted c i tc T0 t hT0 htg (by omega)
        omega
      · exact h.nest τ i T0 hT0 a b hab
  · intro τ
    have hx' : x ∉ ends D τ := fun hx' => by have := h.ends_lt τ x hx'; omega
    have hl : D.stk c = (D.stk c).dropLast ++ [t] := (List.dropLast_append_getLast? t htop).symm
    have hsσ : (D'.stk σ).map Strand.origin = (D.stk σ).map Strand.origin ++ [x] := by
      simp [hD', stk_link, hcσ, hU]
    have hsc : (D'.stk c).map Strand.origin = (D.stk c).dropLast.map Strand.origin := by
      simp [hD', stk_link, Ne.symm hcσ, List.map_dropLast]
    by_cases hτ : τ = σ
    · rw [hτ] at hx' ⊢
      rw [ends_split, harcs, hsσ, List.flatMap_cons]
      simp only []
      rw [if_neg hcσ, List.nil_append]
      exact nodup_mid (h.uniq σ) hx'
    · have hτc : τ = c := by rw [hc]; revert hτ; cases τ <;> cases σ <;> decide
      rw [hτc] at hx' ⊢
      rw [ends_split, harcs, hsc, List.flatMap_cons]
      simp only []
      rw [if_pos trivial]
      have hu := h.uniq c
      rw [ends_split, hl] at hu
      simp only [List.map_append, List.map_singleton] at hu
      have heq : (D.stk c).dropLast.map Strand.origin ++ ([t.origin, x] ++
          D.arcs.flatMap fun a => if a.2.2 = c then [a.1, a.2.1] else []) =
          ((D.stk c).dropLast.map Strand.origin ++ [t.origin]) ++ x ::
            D.arcs.flatMap fun a => if a.2.2 = c then [a.1, a.2.1] else [] := by simp
      rw [heq]
      refine List.perm_middle.nodup_iff.2 (List.nodup_cons.2 ⟨fun hm => hx' ?_, hu⟩)
      rw [ends_split, hl]
      simpa using hm
  · intro y hy τ hs
    have hw := h.wlen
    rw [harcs]
    by_cases hyx : y = x
    · have hyw : y = w.length := by omega
      rw [hyw, act_append_self, if_pos (show w.length < m by omega)]
      have hact : (if τ then (if σ then (true, false) else (false, true)).1
          else (if σ then (true, false) else (false, true)).2) = (τ == σ) := by
        cases τ <;> cases σ <;> rfl
      rw [hact]
      by_cases hτ : τ = σ
      · rw [if_pos (by simp [hτ])]
        exact Or.inl ⟨nσ, U, by rw [hτ]; exact hUg, by simp [hU]; omega⟩
      · have hτc : τ = c := by rw [hc]; revert hτ; cases τ <;> cases σ <;> decide
        rw [if_neg (by simp [hτ])]
        exact ⟨t.origin, by rw [hτc, ← hyw, hyx]; simp⟩
    · rw [act_append_lt _ _ _ _ _ (by omega)]
      have := h.word y (by omega) τ hs
      split_ifs at this ⊢
      · rcases this with ⟨i, T, hi, ho⟩ | ⟨b, hb⟩
        · by_cases h1 : Ref.s τ i = .s c tc
          · rw [h1, htg] at hi; cases hi
            simp only [Ref.s.injEq] at h1
            exact Or.inr ⟨x, by rw [h1.1, ← ho]; simp⟩
          · by_cases h2 : Ref.s τ i = p
            · rw [h2, hpg] at hi; cases hi
              exact Or.inl ⟨i, P', by rw [h2]; exact hPg, by simp [hP', ho]⟩
            · exact Or.inl ⟨i, T, hold _ _ hi h1 h2, ho⟩
        · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb⟩
      · obtain ⟨a, ha⟩ := this
        exact ⟨a, List.mem_cons_of_mem _ ha⟩

end Arnold.TM
