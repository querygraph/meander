import Arnold.TM.StepFF

/-!
# Invariant: the east end
-/

set_option linter.deprecated false

namespace Arnold.TM

open DSt

/-- The east end opens its arc (it will be closed by `S`). -/
theorem inv_EO {m : ℕ} {w : List (Bool × Bool)} {D : DSt} {a : Bool × Bool} (h : Inv m m w D)
    (ha : a.1 = true) :
    Inv m (m + 1) (w ++ [a]) (D.push (m % 2 == 1) ⟨.E, m, [m]⟩) := by
  set e := m % 2 == 1 with he
  set ne := (D.stk e).length with hne
  set N : Strand := ⟨.E, m, [m]⟩ with hN
  set D' := D.push e N with hD'
  have hg : ∀ p, D'.get? p = if p = .s e ne then some N else D.get? p := by
    intro p; rw [hD', DSt.get?_push]
  have hN0 : D.get? (.s e ne) = none := by
    rw [DSt.get?_s]; exact List.getElem?_eq_none (by omega)
  have hold : ∀ q t, D.get? q = some t → D'.get? q = some t := by
    intro q t hq
    rw [hg]
    split_ifs with h1
    · subst h1; rw [hN0] at hq; simp at hq
    · exact hq
  have hnew : ∀ p t, D'.get? p = some t → (p = .s e ne ∧ t = N) ∨ D.get? p = some t := by
    intro p t hp
    rw [hg] at hp
    split_ifs at hp with h1
    · exact Or.inl ⟨h1, (Option.some.inj hp).symm⟩
    · exact Or.inr hp
  have hNg : D'.get? (.s e ne) = some N := by rw [hg]; simp
  have harcs : D'.arcs = D.arcs := by simp [hD']
  have hnoE := h.noE le_rfl
  constructor
  · simp [h.wlen]
  · intro p t hp
    rcases hnew p t hp with ⟨rfl, rfl⟩ | hp
    · simp [hN]
    · exact h.ref_ne p t hp
  · intro p t hp
    rcases hnew p t hp with ⟨rfl, rfl⟩ | hp
    · exact Or.inl rfl
    · rcases h.ref_ok p t hp with hE | ⟨t', ht', hr⟩
      · exact Or.inl hE
      · exact Or.inr ⟨t', hold _ _ ht', hr⟩
  · intro p t hp hE; omega
  · intro p t hp
    rcases hnew p t hp with ⟨rfl, rfl⟩ | hp
    · simp [hN]
    · have := h.orig_lt p t hp; omega
  · intro σ i j t t' hi hj hij
    rcases hnew _ _ hi with ⟨h1, rfl⟩ | hi'
    · simp only [Ref.s.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      rcases hnew _ _ hj with ⟨h2, rfl⟩ | hj'
      · simp at h2; omega
      · have := DSt.lt_of_get? hj'; omega
    · rcases hnew _ _ hj with ⟨h2, rfl⟩ | hj'
      · simpa [hN] using h.orig_lt _ _ hi'
      · exact h.sorted σ i j t t' hi' hj' hij
  · intro p t hp
    rcases hnew p t hp with ⟨rfl, rfl⟩ | hp
    · simp [hN]
    · exact h.seg_nodup p t hp
  · intro p t hp
    rcases hnew p t hp with ⟨rfl, rfl⟩ | hp
    · simp [hN]
    · exact h.seg_head p t hp
  · intro p t hp y hy
    rcases hnew p t hp with ⟨rfl, rfl⟩ | hp
    · simp [hN] at hy; omega
    · have := h.seg_lt p t hp y hy; omega
  · intro p t hp hE
    rcases hnew p t hp with ⟨rfl, rfl⟩ | hp
    · simp [hN]
    · exact absurd hE (hnoE p t hp)
  · intro p t t' hp ht'
    rcases hnew p t hp with ⟨rfl, rfl⟩ | hp
    · simp [hN] at ht'
    · rcases h.ref_ok p t hp with hE | ⟨t2, ht2, _⟩
      · exact absurd hE (hnoE p t hp)
      · rw [hold _ _ ht2, Option.some.injEq] at ht'
        rw [← ht']
        exact h.seg_rev p t t2 hp ht2
  · intro p t hp
    rw [harcs]
    rcases hnew p t hp with ⟨rfl, rfl⟩ | hp
    · simp [hN]
    · exact h.chain p t hp
  · intro p q t t' hp hq hqp hqr
    have hxt : ∀ p t, D.get? p = some t → m ∉ t.seg := fun p t hp hx' => by
      have := h.seg_lt p t hp m hx'; omega
    rcases hnew p t hp with ⟨rfl, rfl⟩ | hp' <;> rcases hnew q t' hq with ⟨rfl, rfl⟩ | hq'
    · exact absurd rfl hqp
    · simpa [hN] using hxt _ _ hq'
    · simpa [hN, List.disjoint_comm] using hxt _ _ hp'
    · exact h.disj p q t t' hp' hq' hqp hqr
  · intro y hy
    by_cases hyx : y = m
    · exact ⟨_, _, hNg, by simp [hN, hyx]⟩
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
    rcases hnew _ _ hi with ⟨_, rfl⟩ | hi'
    · have := h.arc_lt a b _ hab; simp [hN]; omega
    · exact h.nest σ i t hi' a b hab
  · intro σ
    have hx' : m ∉ ends D σ := fun hx' => by have := h.ends_lt σ m hx'; omega
    by_cases hσ : σ = e
    · have heq : ends D' σ = (D.stk σ).map Strand.origin ++ [m] ++
          D.arcs.flatMap fun a => if a.2.2 = σ then [a.1, a.2.1] else [] := by
        rw [hσ]; simp [ends, hD', hN]
      rw [heq]
      exact nodup_mid (h.uniq σ) hx'
    · have heq : ends D' σ = ends D σ := by
        simp [ends, hD', Ne.symm hσ]
      rw [heq]; exact h.uniq σ
  · intro y hy σ hs
    have hw := h.wlen
    by_cases hyx : y = m
    · have hyw : y = w.length := by omega
      have hσ : σ = e := by
        rcases hs with hs | ⟨_, hs⟩
        · omega
        · exact hs
      rw [hyw, act_append_self, if_neg (show ¬ w.length < m by omega), if_pos ha]
      exact Or.inl ⟨ne, N, by rw [hσ]; exact hNg, by simp [hN]; omega⟩
    · rw [act_append_lt _ _ _ _ _ (by omega), harcs]
      have := h.word y (by omega) σ hs
      split_ifs at this ⊢
      · rcases this with ⟨i, t, hi, ho⟩ | hb
        · exact Or.inl ⟨i, t, hold _ _ hi, ho⟩
        · exact Or.inr hb
      · exact this

/-- The east end closes the top arc on its side: that piece of river now ends at `E`. -/
theorem inv_EC {m : ℕ} {w : List (Bool × Bool)} {D : DSt} {a : Bool × Bool} {t : Strand}
    (h : Inv m m w D) (ha : a.1 = false) (htop : (D.stk (m % 2 == 1)).getLast? = some t)
    (htE : t.ref ≠ .E) :
    Inv m (m + 1) (w ++ [a])
      (((D.pop (m % 2 == 1)).link t.ref .E [m]).addArc (t.origin, m, m % 2 == 1)) := by
  set e := m % 2 == 1 with he
  set te := (D.stk e).length - 1 with hte
  obtain ⟨htg, hepos⟩ := DSt.get?_top D e t htop
  rw [← hte] at htg
  set p := t.ref with hp
  have hnoE := h.noE le_rfl
  obtain ⟨tp, hpg, hpref⟩ : ∃ tp, D.get? p = some tp ∧ tp.ref = .s e te := by
    rcases h.ref_ok _ t htg with hE | h'
    · exact absurd hE htE
    · exact h'
  have hpne : p ≠ .s e te := h.ref_ne _ t htg
  set P' : Strand := ⟨.E, tp.origin, tp.seg ++ [m]⟩ with hP'
  set D' := ((D.pop e).link p .E [m]).addArc (t.origin, m, e) with hD'
  have hg : ∀ P, D'.get? P = (if P = .s e te then none else D.get? P).map
      fun T => if P = p then ⟨.E, T.origin, T.seg ++ [m]⟩ else T := by
    intro P
    rw [hD', get?_addArc, get?_link, get?_pop]
  have hPg : D'.get? p = some P' := by
    rw [hg, if_neg hpne, hpg]; simp [hP']
  have hold : ∀ Q T, D.get? Q = some T → Q ≠ .s e te → Q ≠ p → D'.get? Q = some T := by
    intro Q T hQ h1 h2
    rw [hg, if_neg h1, hQ]; simp [h2]
  have hnew : ∀ P T, D'.get? P = some T → (P = p ∧ T = P') ∨
      (P ≠ .s e te ∧ P ≠ p ∧ D.get? P = some T) := by
    intro P T hP
    by_cases h3 : P = p
    · rw [h3, hPg] at hP; exact Or.inl ⟨h3, (Option.some.inj hP).symm⟩
    rw [hg] at hP
    by_cases h2 : P = .s e te
    · rw [if_pos h2] at hP; simp at hP
    · rw [if_neg h2] at hP
      rcases hD0 : D.get? P with _ | T0
      · rw [hD0] at hP; simp at hP
      · rw [hD0] at hP
        simp only [Option.map_some, h3, ↓reduceIte, Option.some.injEq] at hP
        exact Or.inr ⟨h2, h3, by cases hP; rfl⟩
  have horig : ∀ P T, D'.get? P = some T →
      ∃ T0, D.get? P = some T0 ∧ T.origin = T0.origin ∧ P ≠ .s e te := by
    intro P T hP
    rcases hnew P T hP with ⟨rfl, rfl⟩ | ⟨h2, _, h3⟩
    · exact ⟨tp, hpg, rfl, hpne⟩
    · exact ⟨T, h3, rfl, h2⟩
  have hseg_rev_t : tp.seg = t.seg.reverse := h.seg_rev _ t tp htg hpg
  have ht_head : t.seg.head? = some t.origin := h.seg_head _ t htg
  have hto : t.origin < m := h.orig_lt _ t htg
  have hxt : ∀ P T, D.get? P = some T → m ∉ T.seg := fun P T hP hx' => by
    have := h.seg_lt P T hP m hx'; omega
  have harcs : D'.arcs = (t.origin, m, e) :: D.arcs := by simp [hD']
  have hrefold : ∀ P T, D.get? P = some T → P ≠ .s e te → P ≠ p →
      T.ref = .E ∨ ∃ T', D'.get? T.ref = some T' ∧ D.get? T.ref = some T' ∧ T'.ref = P := by
    intro P T hP h1 h2
    rcases h.ref_ok P T hP with hE | ⟨T', hT', hr⟩
    · exact Or.inl hE
    · refine Or.inr ⟨T', hold _ _ hT' ?_ ?_, hT', hr⟩
      · intro he; rw [he, htg] at hT'; cases hT'
        exact h2 (by rw [hp]; exact hr.symm)
      · intro he; rw [he, hpg] at hT'; cases hT'
        exact h1 (by rw [← hr, hpref])
  constructor
  · simp [h.wlen]
  · intro P T hP
    rcases hnew P T hP with ⟨rfl, rfl⟩ | ⟨_, _, hP'⟩
    · simpa [hP'] using Ne.symm htE
    · exact h.ref_ne P T hP'
  · intro P T hP
    rcases hnew P T hP with ⟨rfl, rfl⟩ | ⟨h2, h3, hP'⟩
    · exact Or.inl rfl
    · rcases hrefold P T hP' h2 h3 with hE | ⟨T', hT', _, hr⟩
      · exact Or.inl hE
      · exact Or.inr ⟨T', hT', hr⟩
  · intro P T hP hE; omega
  · intro P T hP
    obtain ⟨T0, hT0, ho, _⟩ := horig P T hP
    have := h.orig_lt P T0 hT0; omega
  · intro τ i j T T' hi hj hij
    obtain ⟨T0, hT0, ho, _⟩ := horig _ T hi
    obtain ⟨T0', hT0', ho', _⟩ := horig _ T' hj
    rw [ho, ho']; exact h.sorted τ i j T0 T0' hT0 hT0' hij
  · intro P T hP
    rcases hnew P T hP with ⟨rfl, rfl⟩ | ⟨_, _, hP'⟩
    · simp only [hP']
      exact (h.seg_nodup _ tp hpg).append (List.nodup_singleton m)
        (List.disjoint_singleton.2 (hxt _ tp hpg))
    · exact h.seg_nodup P T hP'
  · intro P T hP
    rcases hnew P T hP with ⟨rfl, rfl⟩ | ⟨_, _, hP'⟩
    · have hh := h.seg_head _ tp hpg
      have hne : tp.seg ≠ [] := by intro he; simp [he] at hh
      simp [hP', List.head?_append, hh]
    · exact h.seg_head P T hP'
  · intro P T hP y hy
    rcases hnew P T hP with ⟨rfl, rfl⟩ | ⟨_, _, hP'⟩
    · simp only [hP', List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | rfl
      · have := h.seg_lt _ tp hpg y hy; omega
      · omega
    · have := h.seg_lt P T hP' y hy; omega
  · intro P T hP hE
    rcases hnew P T hP with ⟨rfl, rfl⟩ | ⟨_, _, hP'⟩
    · simp [hP']
    · exact absurd hE (hnoE P T hP')
  · intro P T T' hP hT'
    rcases hnew P T hP with ⟨rfl, rfl⟩ | ⟨h2, h3, hP'⟩
    · simp [hP'] at hT'
    · rcases hrefold P T hP' h2 h3 with hE | ⟨T2, hT2, hT2', _⟩
      · exact absurd hE (hnoE P T hP')
      · rw [hT2, Option.some.injEq] at hT'
        rw [← hT']
        exact h.seg_rev P T T2 hP' hT2'
  · intro P T hP
    rw [harcs]
    rcases hnew P T hP with ⟨rfl, rfl⟩ | ⟨_, _, hP'⟩
    · simp only [hP']
      refine (chain_cons (t.origin, m, e) (h.chain _ tp hpg)).append (by simp) ?_
      intro a ha b hb
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
      subst hb
      rw [hseg_rev_t, getLast?_reverse_eq ht_head] at ha
      simp only [Option.mem_def, Option.some.injEq] at ha
      subst ha
      exact ⟨e, Or.inl (by simp)⟩
    · exact chain_cons _ (h.chain P T hP')
  · intro P Q T T' hP hQ hQP hQr
    have dp : ∀ Q T', D.get? Q = some T' → Q ≠ .s e te → Q ≠ p → tp.seg.Disjoint T'.seg :=
      fun Q T' hQ h1 h2 => h.disj p Q tp T' hpg hQ h2 (by rw [hpref]; exact h1)
    rcases hnew P T hP with ⟨rfl, rfl⟩ | ⟨h1, h2, hPd⟩ <;>
      rcases hnew Q T' hQ with ⟨rfl, rfl⟩ | ⟨h1', h2', hQd⟩
    · exact absurd rfl hQP
    · simp only [hP']
      exact List.disjoint_append_left.2 ⟨dp _ _ hQd h1' h2',
        List.singleton_disjoint.2 (hxt _ _ hQd)⟩
    · simp only [hP']
      exact (List.disjoint_append_left.2 ⟨dp _ _ hPd h1 h2,
        List.singleton_disjoint.2 (hxt _ _ hPd)⟩).symm
    · exact h.disj P Q T T' hPd hQd hQP hQr
  · intro y hy
    by_cases hyx : y = m
    · exact ⟨_, _, hPg, by simp [hP', hyx]⟩
    · obtain ⟨P, T, hP, hyt⟩ := h.cover y (by omega)
      by_cases h1 : P = .s e te
      · rw [h1, htg] at hP; cases hP
        exact ⟨_, _, hPg, by simp [hP', hseg_rev_t, hyt]⟩
      · by_cases h2 : P = p
        · rw [h2, hpg] at hP; cases hP
          exact ⟨_, _, hPg, by simp [hP', hyt]⟩
        · exact ⟨P, T, hold P T hP h1 h2, hyt⟩
  · intro a b τ hab
    rw [harcs] at hab
    rcases List.mem_cons.1 hab with he' | hab
    · simp only [Prod.mk.injEq] at he'
      obtain ⟨rfl, rfl, rfl⟩ := he'
      omega
    · have := h.arc_lt a b τ hab; omega
  · intro a b a' b' τ h1 h2
    rw [harcs] at h1 h2
    have hnew_nc : ∀ a b, (a, b, e) ∈ D.arcs → ¬ Interleave t.origin m a b ∧
        ¬ Interleave a b t.origin m := by
      intro a b hab
      have hlt := h.arc_lt a b e hab
      have hn := h.nest e te t htg a b hab
      unfold Interleave
      omega
    rcases List.mem_cons.1 h1 with he1 | h1' <;> rcases List.mem_cons.1 h2 with he2 | h2'
    · simp only [Prod.mk.injEq] at he1 he2
      obtain ⟨ha1, hb1, -⟩ := he1
      obtain ⟨ha2, hb2, -⟩ := he2
      rw [ha1, hb1, ha2, hb2]; unfold Interleave; omega
    · simp only [Prod.mk.injEq] at he1
      obtain ⟨ha1, hb1, hτ⟩ := he1
      rw [ha1, hb1]; rw [hτ] at h2'
      exact (hnew_nc a' b' h2').1
    · simp only [Prod.mk.injEq] at he2
      obtain ⟨ha2, hb2, hτ⟩ := he2
      rw [ha2, hb2]; rw [hτ] at h1'
      exact (hnew_nc a b h1').2
    · exact h.nc a b a' b' τ h1' h2'
  · intro τ i T hi a b hab
    obtain ⟨T0, hT0, ho, hne⟩ := horig _ T hi
    rw [ho]
    rw [harcs] at hab
    rcases List.mem_cons.1 hab with he' | hab
    · simp only [Prod.mk.injEq] at he'
      obtain ⟨ha1, hb1, hτ⟩ := he'
      rw [ha1, hb1]
      rw [hτ] at hT0 hne
      have hi' := DSt.lt_of_get? hT0
      have hit : i ≠ te := fun he' => hne (by rw [he'])
      have := h.sorted e i te T0 t hT0 htg (by omega)
      omega
    · exact h.nest τ i T0 hT0 a b hab
  · intro τ
    have hx' : m ∉ ends D τ := fun hx' => by have := h.ends_lt τ m hx'; omega
    have hl : D.stk e = (D.stk e).dropLast ++ [t] := (List.dropLast_append_getLast? t htop).symm
    have hs : ∀ τ, (D'.stk τ).map Strand.origin =
        if τ = e then (D.stk e).dropLast.map Strand.origin else (D.stk τ).map Strand.origin := by
      intro τ
      simp only [hD', stk_addArc]
      rw [stk_link]
      by_cases hτ : τ = e
      · rw [hτ]; simp [List.map_dropLast]
      · simp [hτ, Ne.symm hτ]
    by_cases hτ : τ = e
    · rw [hτ] at hx' ⊢
      rw [ends_split, harcs, hs, if_pos rfl, List.flatMap_cons]
      simp only []
      rw [if_pos trivial]
      have hu := h.uniq e
      rw [ends_split, hl] at hu
      simp only [List.map_append, List.map_singleton] at hu
      refine nodup_close hu (fun hm => hx' ?_)
      rw [ends_split, hl]
      simpa using hm
    · rw [ends_split, harcs, hs, if_neg hτ, List.flatMap_cons]
      simp only []
      rw [if_neg (Ne.symm hτ), List.nil_append]
      exact h.uniq τ
  · intro y hy τ hs
    have hw := h.wlen
    rw [harcs]
    by_cases hyx : y = m
    · have hyw : y = w.length := by omega
      have hσ : τ = e := by
        rcases hs with hs | ⟨_, hs⟩
        · omega
        · exact hs
      rw [hyw, act_append_self, if_neg (show ¬ w.length < m by omega), ha]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨t.origin, by rw [hσ, ← hyw, hyx]; simp⟩
    · rw [act_append_lt _ _ _ _ _ (by omega)]
      have := h.word y (by omega) τ hs
      split_ifs at this ⊢
      · rcases this with ⟨i, T, hi, ho⟩ | ⟨b, hb⟩
        · by_cases h1 : Ref.s τ i = .s e te
          · rw [h1, htg] at hi; cases hi
            simp only [Ref.s.injEq] at h1
            exact Or.inr ⟨m, by rw [h1.1, ← ho]; simp⟩
          · by_cases h2 : Ref.s τ i = p
            · rw [h2, hpg] at hi; cases hi
              exact Or.inl ⟨i, P', by rw [h2]; exact hPg, by simp [hP', ho]⟩
            · exact Or.inl ⟨i, T, hold _ _ hi h1 h2, ho⟩
        · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb⟩
      · obtain ⟨a', ha'⟩ := this
        exact ⟨a', List.mem_cons_of_mem _ ha'⟩

end Arnold.TM
