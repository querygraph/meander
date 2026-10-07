import Arnold.TM.StepOC

/-!
# Invariant: close both sides (two pieces of river join)
-/

set_option linter.deprecated false

namespace Arnold.TM

open DSt

theorem nodup_close {A B : List ℕ} {o x : ℕ} (hu : (A ++ [o] ++ B).Nodup)
    (hx : x ∉ A ++ [o] ++ B) : (A ++ ([o, x] ++ B)).Nodup := by
  have heq : A ++ ([o, x] ++ B) = (A ++ [o]) ++ x :: B := by simp
  rw [heq]
  exact List.perm_middle.nodup_iff.2 (List.nodup_cons.2 ⟨hx, hu⟩)

theorem inv_FF {m x : ℕ} {w : List (Bool × Bool)} {D : DSt} {u l : Strand} (h : Inv m x w D)
    (hx : x < m) (hu : (D.stk true).getLast? = some u) (hl : (D.stk false).getLast? = some l)
    (hcyc : ¬ u.ref = .s false ((D.stk false).length - 1)) :
    Inv m (x + 1) (w ++ [(false, false)])
      (((((D.pop true).pop false).link u.ref l.ref (x :: l.seg)).link l.ref u.ref
        (x :: u.seg)).addArc (u.origin, x, true) |>.addArc (l.origin, x, false)) := by
  set tu := (D.stk true).length - 1 with htu
  set tl := (D.stk false).length - 1 with htl
  obtain ⟨hug, hupos⟩ := DSt.get?_top D true u hu
  obtain ⟨hlg, hlpos⟩ := DSt.get?_top D false l hl
  rw [← htu] at hug
  rw [← htl] at hlg
  set pu := u.ref with hpu
  set pl := l.ref with hpl
  have hnoE := h.noE (by omega)
  obtain ⟨tpu, hpug, hpuref⟩ : ∃ T, D.get? pu = some T ∧ T.ref = .s true tu := by
    rcases h.ref_ok _ u hug with hE | h'
    · exact absurd hE (hnoE _ u hug)
    · exact h'
  obtain ⟨tpl, hplg, hplref⟩ : ∃ T, D.get? pl = some T ∧ T.ref = .s false tl := by
    rcases h.ref_ok _ l hlg with hE | h'
    · exact absurd hE (hnoE _ l hlg)
    · exact h'
  have hpu_u : pu ≠ .s true tu := h.ref_ne _ u hug
  have hpl_l : pl ≠ .s false tl := h.ref_ne _ l hlg
  have hpu_l : pu ≠ .s false tl := hcyc
  have hpl_u : pl ≠ .s true tu := by
    intro he; rw [he] at hplg; rw [hug] at hplg; cases hplg
    exact hcyc (by rw [hpu, hplref])
  have hpu_pl : pu ≠ pl := by
    intro he; rw [he] at hpug; rw [hplg] at hpug; cases hpug
    rw [hpuref] at hplref; simp at hplref
  have hul : (Ref.s true tu) ≠ .s false tl := by simp
  set PU : Strand := ⟨pl, tpu.origin, tpu.seg ++ x :: l.seg⟩ with hPU
  set PL : Strand := ⟨pu, tpl.origin, tpl.seg ++ x :: u.seg⟩ with hPL
  set D' := (((((D.pop true).pop false).link pu pl (x :: l.seg)).link pl pu
    (x :: u.seg)).addArc (u.origin, x, true) |>.addArc (l.origin, x, false)) with hD'
  have hg : ∀ P, D'.get? P = if P = .s true tu ∨ P = .s false tl then none else
      (D.get? P).map fun T => if P = pu then ⟨pl, T.origin, T.seg ++ x :: l.seg⟩
        else if P = pl then ⟨pu, T.origin, T.seg ++ x :: u.seg⟩ else T := by
    intro P
    rw [hD', get?_addArc, get?_addArc, get?_link, get?_link, get?_pop, get?_pop]
    simp only [stk_pop, Bool.true_eq_false, ↓reduceIte, ← htl, ← htu]
    by_cases h1 : P = .s false tl
    · simp [h1]
    · by_cases h2 : P = .s true tu
      · simp [h2]
      · simp only [h1, h2, ↓reduceIte, or_self, Option.map_map]
        congr 1
        funext T
        by_cases h3 : P = pu
        · simp [h3, hpu_pl]
        · simp [h3]
  have hPUg : D'.get? pu = some PU := by
    rw [hg, if_neg (by tauto), hpug]; simp [hPU]
  have hPLg : D'.get? pl = some PL := by
    rw [hg, if_neg (by tauto), hplg]; simp [hPL, Ne.symm hpu_pl]
  have hold : ∀ Q T, D.get? Q = some T → Q ≠ .s true tu → Q ≠ .s false tl → Q ≠ pu → Q ≠ pl →
      D'.get? Q = some T := by
    intro Q T hQ h1 h2 h3 h4
    rw [hg, if_neg (by tauto), hQ]; simp [h3, h4]
  have hnew : ∀ P T, D'.get? P = some T → (P = pu ∧ T = PU) ∨ (P = pl ∧ T = PL) ∨
      (P ≠ .s true tu ∧ P ≠ .s false tl ∧ P ≠ pu ∧ P ≠ pl ∧ D.get? P = some T) := by
    intro P T hP
    by_cases h3 : P = pu
    · rw [h3, hPUg] at hP; exact Or.inl ⟨h3, (Option.some.inj hP).symm⟩
    by_cases h4 : P = pl
    · rw [h4, hPLg] at hP; exact Or.inr (Or.inl ⟨h4, (Option.some.inj hP).symm⟩)
    rw [hg] at hP
    by_cases h12 : P = .s true tu ∨ P = .s false tl
    · rw [if_pos h12] at hP; simp at hP
    · rw [if_neg h12] at hP
      rcases hD0 : D.get? P with _ | T0
      · rw [hD0] at hP; simp at hP
      · rw [hD0] at hP
        simp only [Option.map_some, h3, h4, ↓reduceIte, Option.some.injEq] at hP
        exact Or.inr (Or.inr ⟨fun e => h12 (Or.inl e), fun e => h12 (Or.inr e), h3, h4,
          by cases hP; rfl⟩)
  have horig : ∀ P T, D'.get? P = some T → ∃ T0, D.get? P = some T0 ∧ T.origin = T0.origin ∧
      P ≠ .s true tu ∧ P ≠ .s false tl := by
    intro P T hP
    rcases hnew P T hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨h1, h2, _, _, h5⟩
    · exact ⟨tpu, hpug, rfl, hpu_u, hpu_l⟩
    · exact ⟨tpl, hplg, rfl, hpl_u, hpl_l⟩
    · exact ⟨T, h5, rfl, h1, h2⟩
  have hrev_u : tpu.seg = u.seg.reverse := h.seg_rev _ u tpu hug hpug
  have hrev_l : tpl.seg = l.seg.reverse := h.seg_rev _ l tpl hlg hplg
  have hu_head : u.seg.head? = some u.origin := h.seg_head _ u hug
  have hl_head : l.seg.head? = some l.origin := h.seg_head _ l hlg
  have huo : u.origin < x := h.orig_lt _ u hug
  have hlo : l.origin < x := h.orig_lt _ l hlg
  have hxt : ∀ P T, D.get? P = some T → x ∉ T.seg := fun P T hP hx' => by
    have := h.seg_lt P T hP x hx'; omega
  have harcs : D'.arcs = (l.origin, x, false) :: (u.origin, x, true) :: D.arcs := by simp [hD']
  have hrefold : ∀ P T, D.get? P = some T → P ≠ .s true tu → P ≠ .s false tl → P ≠ pu →
      P ≠ pl → T.ref = .E ∨ ∃ T', D'.get? T.ref = some T' ∧ D.get? T.ref = some T' ∧
        T'.ref = P := by
    intro P T hP h1 h2 h3 h4
    rcases h.ref_ok P T hP with hE | ⟨T', hT', hr⟩
    · exact Or.inl hE
    · refine Or.inr ⟨T', hold _ _ hT' ?_ ?_ ?_ ?_, hT', hr⟩
      · intro he; rw [he, hug] at hT'; cases hT'; exact h3 (by rw [hpu]; exact hr.symm)
      · intro he; rw [he, hlg] at hT'; cases hT'; exact h4 (by rw [hpl]; exact hr.symm)
      · intro he; rw [he, hpug] at hT'; cases hT'; exact h1 (by rw [← hr, hpuref])
      · intro he; rw [he, hplg] at hT'; cases hT'; exact h2 (by rw [← hr, hplref])
  constructor
  · simp [h.wlen]
  · intro P T hP
    rcases hnew P T hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨_, _, _, _, hP'⟩
    · simpa [hPU] using Ne.symm hpu_pl
    · simpa [hPL] using hpu_pl
    · exact h.ref_ne P T hP'
  · intro P T hP
    rcases hnew P T hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨h1, h2, h3, h4, hP'⟩
    · exact Or.inr ⟨PL, hPLg, rfl⟩
    · exact Or.inr ⟨PU, hPUg, rfl⟩
    · rcases hrefold P T hP' h1 h2 h3 h4 with hE | ⟨T', hT', _, hr⟩
      · exact Or.inl hE
      · exact Or.inr ⟨T', hT', hr⟩
  · intro P T hP hE
    rcases hnew P T hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨_, _, _, _, hP'⟩
    · exact absurd hE (hnoE _ l hlg)
    · exact absurd hE (hnoE _ u hug)
    · exact absurd hE (hnoE P T hP')
  · intro P T hP
    obtain ⟨T0, hT0, ho, _⟩ := horig P T hP
    have := h.orig_lt P T0 hT0; omega
  · intro τ i j T T' hi hj hij
    obtain ⟨T0, hT0, ho, _⟩ := horig _ T hi
    obtain ⟨T0', hT0', ho', _⟩ := horig _ T' hj
    rw [ho, ho']; exact h.sorted τ i j T0 T0' hT0 hT0' hij
  · intro P T hP
    rcases hnew P T hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨_, _, _, _, hP'⟩
    · have hd : tpu.seg.Disjoint l.seg := h.disj _ _ tpu l hpug hlg (Ne.symm hpu_l)
        (by rw [hpuref]; exact Ne.symm hul)
      exact (h.seg_nodup _ _ hpug).append (List.nodup_cons.2 ⟨hxt _ _ hlg,
        h.seg_nodup _ _ hlg⟩) (List.disjoint_cons_right.2 ⟨hxt _ _ hpug, hd⟩)
    · have hd : tpl.seg.Disjoint u.seg := h.disj _ _ tpl u hplg hug (Ne.symm hpl_u)
        (by rw [hplref]; exact hul)
      exact (h.seg_nodup _ _ hplg).append (List.nodup_cons.2 ⟨hxt _ _ hug,
        h.seg_nodup _ _ hug⟩) (List.disjoint_cons_right.2 ⟨hxt _ _ hplg, hd⟩)
    · exact h.seg_nodup P T hP'
  · intro P T hP
    rcases hnew P T hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨_, _, _, _, hP'⟩
    · have hh := h.seg_head _ tpu hpug
      have hne : tpu.seg ≠ [] := by intro he; simp [he] at hh
      simp [hPU, List.head?_append, hh]
    · have hh := h.seg_head _ tpl hplg
      have hne : tpl.seg ≠ [] := by intro he; simp [he] at hh
      simp [hPL, List.head?_append, hh]
    · exact h.seg_head P T hP'
  · intro P T hP y hy
    rcases hnew P T hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨_, _, _, _, hP'⟩
    · simp only [hPU, List.mem_append, List.mem_cons] at hy
      rcases hy with hy | rfl | hy
      · have := h.seg_lt _ _ hpug y hy; omega
      · omega
      · have := h.seg_lt _ _ hlg y hy; omega
    · simp only [hPL, List.mem_append, List.mem_cons] at hy
      rcases hy with hy | rfl | hy
      · have := h.seg_lt _ _ hplg y hy; omega
      · omega
      · have := h.seg_lt _ _ hug y hy; omega
    · have := h.seg_lt P T hP' y hy; omega
  · intro P T hP hE
    rcases hnew P T hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨_, _, _, _, hP'⟩
    · exact absurd hE (hnoE _ l hlg)
    · exact absurd hE (hnoE _ u hug)
    · exact absurd hE (hnoE P T hP')
  · intro P T T' hP hT'
    rcases hnew P T hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨h1, h2, h3, h4, hP'⟩
    · rw [hPLg] at hT'; cases hT'; simp [hPL, hPU, hrev_u, hrev_l]
    · rw [hPUg] at hT'; cases hT'; simp [hPL, hPU, hrev_u, hrev_l]
    · rcases hrefold P T hP' h1 h2 h3 h4 with hE | ⟨T2, hT2, hT2', _⟩
      · exact absurd hE (hnoE P T hP')
      · rw [hT2, Option.some.injEq] at hT'
        rw [← hT']
        exact h.seg_rev P T T2 hP' hT2'
  · intro P T hP
    rw [harcs]
    have hj_u : Joined ((l.origin, x, false) :: (u.origin, x, true) :: D.arcs) u.origin x :=
      ⟨true, Or.inl (by simp)⟩
    have hj_l : Joined ((l.origin, x, false) :: (u.origin, x, true) :: D.arcs) x l.origin :=
      ⟨false, Or.inr (by simp)⟩
    have hj_u' : Joined ((l.origin, x, false) :: (u.origin, x, true) :: D.arcs) x u.origin :=
      ⟨true, Or.inr (by simp)⟩
    have hj_l' : Joined ((l.origin, x, false) :: (u.origin, x, true) :: D.arcs) l.origin x :=
      ⟨false, Or.inl (by simp)⟩
    have cc : ∀ P T, D.get? P = some T →
        T.seg.IsChain (Joined ((l.origin, x, false) :: (u.origin, x, true) :: D.arcs)) :=
      fun P T hP => chain_cons _ (chain_cons _ (h.chain P T hP))
    -- a piece ending at `a`, then `x`, then a piece starting at `b`
    have join : ∀ (A B : List ℕ) (a b : ℕ), A.getLast? = some a → B.head? = some b →
        A.IsChain (Joined ((l.origin, x, false) :: (u.origin, x, true) :: D.arcs)) →
        B.IsChain (Joined ((l.origin, x, false) :: (u.origin, x, true) :: D.arcs)) →
        Joined ((l.origin, x, false) :: (u.origin, x, true) :: D.arcs) a x →
        Joined ((l.origin, x, false) :: (u.origin, x, true) :: D.arcs) x b →
        (A ++ x :: B).IsChain (Joined ((l.origin, x, false) :: (u.origin, x, true) :: D.arcs)) := by
      intro A B a b hA hB cA cB ja jb
      refine cA.append ?_ ?_
      · cases B with
        | nil => simp
        | cons b' B =>
          simp only [List.head?_cons, Option.some.injEq] at hB
          subst hB; exact List.isChain_cons_cons.2 ⟨jb, cB⟩
      · intro a' ha' b' hb'
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb'
        subst hb'
        rw [hA] at ha'
        simp only [Option.mem_def, Option.some.injEq] at ha'
        subst ha'; exact ja
    rcases hnew P T hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨_, _, _, _, hP'⟩
    · exact join _ _ u.origin l.origin (by rw [hrev_u]; exact getLast?_reverse_eq hu_head)
        hl_head (cc _ _ hpug) (cc _ _ hlg) hj_u hj_l
    · exact join _ _ l.origin u.origin (by rw [hrev_l]; exact getLast?_reverse_eq hl_head)
        hu_head (cc _ _ hplg) (cc _ _ hug) hj_l' hj_u'
    · exact cc P T hP'
  · intro P Q T T' hP hQ hQP hQr
    have dd : ∀ Q T', D.get? Q = some T' → Q ≠ .s true tu → Q ≠ .s false tl → Q ≠ pu →
        Q ≠ pl → (tpu.seg ++ x :: l.seg).Disjoint T'.seg ∧
          (tpl.seg ++ x :: u.seg).Disjoint T'.seg := by
      intro Q T' hQ h1 h2 h3 h4
      have a1 := h.disj pu Q tpu T' hpug hQ h3 (by rw [hpuref]; exact h1)
      have a2 := h.disj _ Q l T' hlg hQ h2 h4
      have a3 := h.disj pl Q tpl T' hplg hQ h4 (by rw [hplref]; exact h2)
      have a4 := h.disj _ Q u T' hug hQ h1 h3
      exact ⟨List.disjoint_append_left.2 ⟨a1, List.disjoint_cons_left.2 ⟨hxt _ _ hQ, a2⟩⟩,
        List.disjoint_append_left.2 ⟨a3, List.disjoint_cons_left.2 ⟨hxt _ _ hQ, a4⟩⟩⟩
    rcases hnew P T hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨h1, h2, h3, h4, hP'⟩ <;>
      rcases hnew Q T' hQ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨h1', h2', h3', h4', hQ'⟩
    · exact absurd rfl hQP
    · exact absurd rfl hQr
    · exact (dd _ _ hQ' h1' h2' h3' h4').1
    · exact absurd rfl hQr
    · exact absurd rfl hQP
    · exact (dd _ _ hQ' h1' h2' h3' h4').2
    · exact (dd _ _ hP' h1 h2 h3 h4).1.symm
    · exact (dd _ _ hP' h1 h2 h3 h4).2.symm
    · exact h.disj P Q T T' hP' hQ' hQP hQr
  · intro y hy
    by_cases hyx : y = x
    · exact ⟨_, _, hPUg, by simp [hPU, hyx]⟩
    · obtain ⟨P, T, hP, hyt⟩ := h.cover y (by omega)
      by_cases e1 : P = .s true tu
      · rw [e1, hug] at hP; cases hP; exact ⟨_, _, hPLg, by simp [hPL, hyt]⟩
      by_cases e2 : P = .s false tl
      · rw [e2, hlg] at hP; cases hP; exact ⟨_, _, hPUg, by simp [hPU, hyt]⟩
      by_cases e3 : P = pu
      · rw [e3, hpug] at hP; cases hP; exact ⟨_, _, hPUg, by simp [hPU, hyt]⟩
      by_cases e4 : P = pl
      · rw [e4, hplg] at hP; cases hP; exact ⟨_, _, hPLg, by simp [hPL, hyt]⟩
      exact ⟨P, T, hold P T hP e1 e2 e3 e4, hyt⟩
  · intro a b τ hab
    rw [harcs] at hab
    simp only [List.mem_cons, Prod.mk.injEq] at hab
    rcases hab with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | hab
    · omega
    · omega
    · have := h.arc_lt a b τ hab; omega
  · intro a b a' b' τ h1 h2
    rw [harcs] at h1 h2
    have hn : ∀ (o : ℕ) (σ : Bool) (i : ℕ) (T : Strand), D.get? (.s σ i) = some T →
        T.origin = o → o < x → ∀ a b, (a, b, σ) ∈ D.arcs →
        ¬ Interleave o x a b ∧ ¬ Interleave a b o x := by
      intro o σ i T hT ho hox a b hab
      have hlt := h.arc_lt a b σ hab
      have hn := h.nest σ i T hT a b hab
      rw [ho] at hn
      unfold Interleave
      omega
    simp only [List.mem_cons, Prod.mk.injEq] at h1 h2
    rcases h1 with ⟨ha, hb, hτ⟩ | ⟨ha, hb, hτ⟩ | h1 <;>
      rcases h2 with ⟨ha', hb', hτ'⟩ | ⟨ha', hb', hτ'⟩ | h2
    · rw [ha, hb, ha', hb']; unfold Interleave; omega
    · rw [hτ] at hτ'; simp at hτ'
    · rw [ha, hb]; rw [hτ] at h2; exact (hn _ _ _ _ hlg rfl hlo a' b' h2).1
    · rw [hτ] at hτ'; simp at hτ'
    · rw [ha, hb, ha', hb']; unfold Interleave; omega
    · rw [ha, hb]; rw [hτ] at h2; exact (hn _ _ _ _ hug rfl huo a' b' h2).1
    · rw [ha', hb']; rw [hτ'] at h1; exact (hn _ _ _ _ hlg rfl hlo a b h1).2
    · rw [ha', hb']; rw [hτ'] at h1; exact (hn _ _ _ _ hug rfl huo a b h1).2
    · exact h.nc a b a' b' τ h1 h2
  · intro τ i T hi a b hab
    obtain ⟨T0, hT0, ho, hne1, hne2⟩ := horig _ T hi
    rw [ho]
    rw [harcs] at hab
    simp only [List.mem_cons, Prod.mk.injEq] at hab
    have hi' := DSt.lt_of_get? hT0
    rcases hab with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | hab
    · have hit : i ≠ tl := fun he => hne2 (by rw [he])
      have := h.sorted false i tl T0 l hT0 hlg (by omega)
      omega
    · have hit : i ≠ tu := fun he => hne1 (by rw [he])
      have := h.sorted true i tu T0 u hT0 hug (by omega)
      omega
    · exact h.nest τ i T0 hT0 a b hab
  · intro τ
    have hx' : x ∉ ends D τ := fun hx' => by have := h.ends_lt τ x hx'; omega
    have hsplit : ∀ σ (t : Strand), (D.stk σ).getLast? = some t →
        (D.stk σ).map Strand.origin = (D.stk σ).dropLast.map Strand.origin ++ [t.origin] := by
      intro σ t ht
      conv_lhs => rw [← List.dropLast_append_getLast? t ht]
      simp
    have hs : ∀ σ, (D'.stk σ).map Strand.origin = (D.stk σ).dropLast.map Strand.origin := by
      intro σ
      simp only [hD', stk_addArc]
      rw [stk_link, stk_link]
      cases σ <;> simp
    rw [ends_split, harcs, hs]
    simp only [List.flatMap_cons]
    cases τ
    · simp only [↓reduceIte, Bool.true_eq_false, List.nil_append]
      have hu0 := h.uniq false
      rw [ends_split, hsplit false l hl] at hu0
      refine nodup_close hu0 ?_
      rw [← hsplit false l hl]; exact hx'
    · simp only [↓reduceIte, Bool.false_eq_true, List.nil_append]
      have hu0 := h.uniq true
      rw [ends_split, hsplit true u hu] at hu0
      refine nodup_close hu0 ?_
      rw [← hsplit true u hu]; exact hx'
  · intro y hy τ hs
    have hw := h.wlen
    rw [harcs]
    by_cases hyx : y = x
    · have hyw : y = w.length := by omega
      rw [hyw, act_append_self, if_pos (show w.length < m by omega)]
      cases τ
      · exact ⟨l.origin, by rw [← hyw, hyx]; simp⟩
      · exact ⟨u.origin, by rw [← hyw, hyx]; simp⟩
    · rw [act_append_lt _ _ _ _ _ (by omega)]
      have := h.word y (by omega) τ hs
      split_ifs at this ⊢
      · rcases this with ⟨i, T, hi, ho⟩ | ⟨b, hb⟩
        · by_cases e1 : Ref.s τ i = .s true tu
          · rw [e1, hug] at hi; cases hi
            simp only [Ref.s.injEq] at e1
            exact Or.inr ⟨x, by rw [e1.1, ← ho]; simp⟩
          by_cases e2 : Ref.s τ i = .s false tl
          · rw [e2, hlg] at hi; cases hi
            simp only [Ref.s.injEq] at e2
            exact Or.inr ⟨x, by rw [e2.1, ← ho]; simp⟩
          by_cases e3 : Ref.s τ i = pu
          · rw [e3, hpug] at hi; cases hi
            exact Or.inl ⟨i, PU, by rw [e3]; exact hPUg, by simp [hPU, ho]⟩
          by_cases e4 : Ref.s τ i = pl
          · rw [e4, hplg] at hi; cases hi
            exact Or.inl ⟨i, PL, by rw [e4]; exact hPLg, by simp [hPL, ho]⟩
          exact Or.inl ⟨i, T, hold _ _ hi e1 e2 e3 e4, ho⟩
        · exact Or.inr ⟨b, by simp [hb]⟩
      · obtain ⟨a, ha⟩ := this
        exact ⟨a, by simp [ha]⟩

end Arnold.TM
