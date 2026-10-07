import Arnold.TM.Encode

/-!
# The transfer matrix counts meanders

`tmCount m` (layer-by-layer, merging equal states) equals `openMeanderCount m` for every `m`.
Accepted action sequences and meanders correspond one-to-one: `decode` sends an accepted
sequence to a meander, `encode` sends a meander back, and the two undo each other.
-/

set_option linter.deprecated false

namespace Arnold.TM

open DSt

theorem mem_sufWords_iff (m : ℕ) : ∀ (f x : ℕ) (ws : List (Bool × Bool)),
    ws ∈ sufWords m f x ↔ ws.length = f ∧ ∀ i (hi : i < ws.length), ws[i] ∈ acts m (x + i) := by
  intro f
  induction f with
  | zero =>
    intro x ws
    simp only [sufWords, List.mem_singleton]
    constructor
    · rintro rfl; simp
    · rintro ⟨h, -⟩; exact List.length_eq_zero_iff.1 h
  | succ f ih =>
    intro x ws
    simp only [sufWords, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨a, ha, ws', hws', rfl⟩
      obtain ⟨hl, hi⟩ := (ih (x + 1) ws').1 hws'
      refine ⟨by simp [hl], fun i hi' => ?_⟩
      cases i with
      | zero => simpa using ha
      | succ i =>
        simp only [List.getElem_cons_succ]
        have := hi i (by simp at hi'; omega)
        rwa [show x + 1 + i = x + (i + 1) by omega] at this
    · rintro ⟨hl, hi⟩
      cases ws with
      | nil => simp at hl
      | cons a ws' =>
        have h0 := hi 0 (by simp)
        simp only [List.getElem_cons_zero, add_zero] at h0
        refine ⟨a, h0, ws', (ih (x + 1) ws').2 ⟨by simp at hl; omega,
          fun i hi' => ?_⟩, rfl⟩
        have := hi (i + 1) (by simp; omega)
        simpa [show x + (i + 1) = x + 1 + i by omega] using this

theorem acts_nodup (m x : ℕ) : (acts m x).Nodup := by
  unfold acts; split_ifs <;> decide

theorem nodup_sufWords (m : ℕ) : ∀ f x, (sufWords m f x).Nodup := by
  intro f
  induction f with
  | zero => intro x; simp [sufWords]
  | succ f ih =>
    intro x
    refine List.nodup_flatMap.2 ⟨fun a _ => (ih (x + 1)).map List.cons_injective, ?_⟩
    refine (acts_nodup m x).imp fun {a b} hab => ?_
    intro w hw hw'
    simp only [List.mem_map] at hw hw'
    obtain ⟨_, _, rfl⟩ := hw
    obtain ⟨_, _, h⟩ := hw'
    exact hab (List.cons.inj h).1.symm

theorem encode_length {m : ℕ} {l : List ℕ} : (encode m l).length = m + 1 := by simp [encode]

section

variable {m : ℕ} {l : List ℕ} (hp : l.Perm (List.range m)) (hnc : NoCross (lpt m l) (m + 1))
include hp hnc

omit hp hnc in
theorem encode_mem_acts (k : ℕ) (hk : k < (encode m l).length) :
    (encode m l)[k] ∈ acts m k := by
  simp only [encode, List.getElem_map, List.getElem_range]
  unfold acts
  split_ifs with h1
  · rcases openAct m l true k <;> rcases openAct m l false k <;> simp
  · rcases openAct m l (m % 2 == 1) m <;> simp

theorem encode_run : ∀ k ≤ m + 1, ∃ D, druns m 0 DSt.empty ((encode m l).take k) = some D ∧
    Inv m k ((encode m l).take k) D ∧ MI m l k D := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨DSt.empty, by simp [druns], by simpa using inv_init m, ?_⟩
    constructor
    · intro a b τ hab; simp at hab
    · intro σ; simp [stkF]
  | succ k ih =>
    intro hk
    obtain ⟨D, hr, hI, hM⟩ := ih (by omega)
    have hklen : k < (encode m l).length := by rw [encode_length]; omega
    obtain ⟨D', hD', hM'⟩ := encode_step hp hnc (by omega) hI hM
    have htake : (encode m l).take (k + 1) = (encode m l).take k ++ [(encode m l)[k]] := by
      rw [List.take_succ, List.getElem?_eq_getElem hklen]; rfl
    have hlen : ((encode m l).take k).length = k := by simp; omega
    refine ⟨D', ?_, ?_, hM'⟩
    · rw [htake, druns_append, hr]
      simp [druns, hlen, hD']
    · rw [htake]
      exact inv_dstep hI (by omega) (encode_mem_acts k hklen) hD'

/-- **Encoding.** A meander's action sequence is accepted, and decodes back to the meander. -/
theorem encode_spec :
    encode m l ∈ sufWords m (m + 1) 0 ∧ runFrom m 0 init (encode m l) = some final ∧
      decode m (encode m l) = l := by
  have hlen : (encode m l).length = m + 1 := encode_length
  have hmem : encode m l ∈ sufWords m (m + 1) 0 :=
    (mem_sufWords_iff m _ _ _).2 ⟨hlen, fun i hi => by simpa using encode_mem_acts i hi⟩
  obtain ⟨D, hr, hI, hM⟩ := encode_run hp hnc (m + 1) le_rfl
  rw [List.take_of_length_le (by omega)] at hr hI
  -- the final state: nothing open above, one arc open below, from `lpt 1`
  have hup : D.up = [] := by
    have := hM.stk true
    have hF : stkF m l true (m + 1) = [] := by
      rw [List.eq_nil_iff_forall_not_mem]
      intro y hy
      obtain ⟨hy1, hys, hy2⟩ := mem_stkF.1 hy
      have := nbr_le hp hys
      have hS := nbr_eq_S hp hys (by omega)
      simp at hS
    rw [hF] at this
    simpa [stk] using this
  have hdn1 : D.dn.map Strand.origin = [lpt m l 1] := by
    have := hM.stk false
    simp only [stk, Bool.false_eq_true, ↓reduceIte] at this
    rw [this]
    have hside1 : HasSideM m (lpt m l 1) false := by
      have := hasSide_of_arc hp (j := 0) (by omega) 1 (Or.inr rfl)
      simpa using this
    have hn1 : nbr m l false (lpt m l 1) = m + 1 := by
      rw [nbr_lpt hp (by omega)]; simp [lpt_zero']
    have hnd : (stkF m l false (m + 1)).Nodup := List.nodup_range.filter _
    rw [← List.perm_singleton]
    refine (List.perm_ext_iff_of_nodup hnd (List.nodup_singleton _)).2 fun y => ?_
    rw [List.mem_singleton]
    refine ⟨?_, fun hy => hy ▸ mem_stkF.2 ⟨?_, hside1, by omega⟩⟩
    swap
    · have := (nbr_hasSide hp hside1).1
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0
        rw [List.eq_nil_of_length_eq_zero (lm_length hp)]
        simp [lpt]
      · have := lpt_bridge_lt hp (i := 1) le_rfl h0; omega
    · intro hy
      obtain ⟨hy1, hys, hy2⟩ := mem_stkF.1 hy
      exact (nbr_eq_S hp hys (by have := nbr_le hp hys; omega)).2
  obtain ⟨t, htdn⟩ : ∃ t, D.dn = [t] := by
    rcases hd : D.dn with _ | ⟨t, _ | ⟨t', r⟩⟩ <;> rw [hd] at hdn1 <;> simp at hdn1
    exact ⟨t, rfl⟩
  have hg : D.get? (.s false 0) = some t := by simp [get?_s, stk, htdn]
  have htE : t.ref = .E := by
    rcases hI.ref_ok _ t hg with hE | ⟨t', ht', _⟩
    · exact hE
    · exfalso
      have hne := hI.ref_ne _ t hg
      cases hr' : t.ref with
      | E => exact hne (by simp [hr'] at ht')
      | s σ i =>
        rw [hr'] at ht' hne
        cases σ
        · simp only [get?_s, stk, Bool.false_eq_true, ↓reduceIte, htdn] at ht'
          rcases i with _ | i
          · exact hne rfl
          · simp at ht'
        · simp [get?_s, stk, hup] at ht'
  have habs : D.abs = final := by simp [DSt.abs, final, hup, htdn, htE]
  refine ⟨hmem, ?_, ?_⟩
  · rw [← abs_empty, runFrom_abs, hr]; simp [habs]
  · -- the decoded river is the meander
    have hdec : decode m (encode m l) = t.seg.dropLast := by simp [decode, hr, htdn]
    rw [hdec]
    obtain ⟨hperm, _, hsplit, halt, _⟩ := meander_of_final hup htdn htE hI
    have hto : t.origin = lpt m l 1 := by simpa [htdn] using hdn1
    set A := (t.origin, m + 1, false) :: D.arcs with hA
    have hAm : ∀ a b τ, (a, b, τ) ∈ A → HasSideM m b τ ∧ a = nbr m l τ b := by
      intro a b τ hab
      rcases List.mem_cons.1 hab with he | hab
      · simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl, rfl⟩ := he
        refine ⟨Or.inr (Or.inr ⟨rfl, rfl⟩), ?_⟩
        rw [hto, ← lpt_zero', nbr_lpt hp (by omega)]; simp
      · exact hM.arcs a b τ hab
    set Q : ℕ → ℕ := fun i => ((m + 1) :: t.seg).getD i 0 with hQdef
    have hQ : ∀ i ≤ m + 1, Q i = lpt m l i := by
      intro i
      induction i with
      | zero => intro _; simp [hQdef, lpt_zero']
      | succ i ih =>
        intro hi
        have hs := halt i (by omega)
        have hQi := ih (by omega)
        have key : ∀ a b, (a, b, (i % 2 == 1)) ∈ A → (a = Q i ∧ b = Q (i + 1) ∨
            b = Q i ∧ a = Q (i + 1)) → Q (i + 1) = nbr m l (i % 2 == 1) (Q i) := by
          intro a b hab hor
          obtain ⟨hbs, hab'⟩ := hAm a b _ hab
          rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rw [hab', (nbr_hasSide hp hbs).2.1]
          · exact hab'
        have h1 : Q (i + 1) = nbr m l (i % 2 == 1) (Q i) := by
          rcases hs with hs | hs
          · exact key _ _ hs (Or.inl ⟨rfl, rfl⟩)
          · exact key _ _ hs (Or.inr ⟨rfl, rfl⟩)
        rw [h1, hQi, nbr_lpt hp (by omega)]; simp
    have hlseg : t.seg.length = m + 1 := by
      have := hperm.length_eq; simp at this
      have h2 := congrArg List.length hsplit; simp at h2; omega
    have hll : l.length = m := lm_length hp
    have hseg : t.seg = l ++ [m] := by
      apply List.ext_getElem (by simp [hlseg, hll])
      intro j h1 h2
      have e1 : t.seg[j] = Q (j + 1) := by
        simp [hQdef, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
      rw [e1, hQ (j + 1) (by omega), lpt_eq_getD hll (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
    rw [hseg, List.dropLast_concat]

end

theorem tmCountWith_eq (comp : List (St × ℕ) → List (St × ℕ))
    (hcomp : ∀ g L, wsum g (comp L) = wsum g L) (m : ℕ) :
    tmCountWith comp m = openMeanderCount m := by
  -- the spec as a count over lists
  have hspec : openMeanderCount m = (perms m (List.range m)).countP
      (fun s => decide (NoCross (lpt m s) (m + 1))) := by
    have h : openMeanderCount m =
        Fintype.card {σ : Equiv.Perm (Fin m) // NoCross (lpt m (toList σ)) (m + 1)} :=
      Fintype.card_congr (Equiv.subtypeEquivRight fun σ => by
        rw [IsMeander, show pathPt σ = lpt m (toList σ) from funext (pathPt_eq_lpt σ)])
    rw [h, card_eq_countP m (fun l => NoCross (lpt m l) (m + 1))]
  rw [tmCountWith_eq_countP comp hcomp, hspec, List.countP_eq_length_filter,
    List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup ((nodup_sufWords m _ _).filter _),
    ← List.toFinset_card_of_nodup ((nodup_perms _ _ List.nodup_range).filter _)]
  have hmp := mem_perms m (List.range m) (by simp)
  apply Finset.card_bij (fun w _ => decode m w)
  · intro w hw
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hw ⊢
    obtain ⟨hp, hnc, _⟩ := decode_spec hw.1 hw.2
    exact ⟨(hmp _).2 hp, hnc⟩
  · intro w1 hw1 w2 hw2 he
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hw1 hw2
    rw [← (decode_spec hw1.1 hw1.2).2.2, ← (decode_spec hw2.1 hw2.2).2.2]
    exact congrArg (encode m) he
  · intro l hl
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hl
    have hp := (hmp l).1 hl.1
    obtain ⟨hmem, hacc, hdec⟩ := encode_spec hp hl.2
    exact ⟨encode m l, by simp [hmem, hacc], hdec⟩

/-- **The transfer matrix counts Arnold's meanders**, for every `m`. -/
theorem tmCount_eq (m : ℕ) : tmCount m = openMeanderCount m :=
  tmCountWith_eq compress compress_wsum m

/-- The kernel-friendly version counts them too. -/
theorem tmCountK_eq (m : ℕ) : tmCountK m = openMeanderCount m :=
  tmCountWith_eq compressK compressK_wsum m

end Arnold.TM
