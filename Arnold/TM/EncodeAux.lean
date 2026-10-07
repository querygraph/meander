import Arnold.TM.EncodeDecode

/-!
# Auxiliary facts for running a meander's action sequence
-/

set_option linter.deprecated false

namespace Arnold.TM

open DSt

instance (m y : ℕ) (σ : Bool) : Decidable (HasSideM m y σ) := by
  unfold HasSideM; infer_instance

/-- The points scanned so far whose arc on side `σ` is still open at the cut `k`. -/
def stkF (m : ℕ) (l : List ℕ) (σ : Bool) (k : ℕ) : List ℕ :=
  (List.range k).filter fun y => decide (HasSideM m y σ ∧ k ≤ nbr m l σ y)

theorem mem_stkF {m : ℕ} {l : List ℕ} {σ : Bool} {k y : ℕ} :
    y ∈ stkF m l σ k ↔ y < k ∧ HasSideM m y σ ∧ k ≤ nbr m l σ y := by
  simp [stkF]

theorem druns_append (m : ℕ) : ∀ (ws ws' : List (Bool × Bool)) (x : ℕ) (D : DSt),
    druns m x D (ws ++ ws') = (druns m x D ws).bind fun D' => druns m (x + ws.length) D' ws'
  | [], ws', x, D => by simp [druns]
  | a :: ws, ws', x, D => by
    simp only [List.cons_append, druns]
    cases dstep m x D a with
    | none => rfl
    | some D1 =>
      simp only [Option.bind_some, List.length_cons]
      rw [druns_append m ws ws' (x + 1) D1]
      congr 1; funext D'; congr 1; omega

/-- A path of naturals moving by one each step passes every value in between. -/
theorem ivt_chain : ∀ (L : List ℕ) (a b c : ℕ),
    L.IsChain (fun x y => x + 1 = y ∨ y + 1 = x) → L.head? = some a → L.getLast? = some b →
    a < c → c < b → c ∈ L
  | [], _, _, _, _, ha, _, _, _ => by simp at ha
  | [x], a, b, c, _, ha, hb, hac, hcb => by simp at ha hb; omega
  | x :: y :: rest, a, b, c, hch, ha, hb, hac, hcb => by
    simp only [List.head?_cons, Option.some.injEq] at ha
    subst ha
    rw [List.isChain_cons_cons] at hch
    by_cases hyc : y = c
    · subst hyc; simp
    · have : y < c := by omega
      have := ivt_chain (y :: rest) y b c hch.2 rfl
        (by rw [List.getLast?_cons_cons] at hb; exact hb) this hcb
      exact List.mem_cons_of_mem _ this

section Facts

variable {m : ℕ} {l : List ℕ} (hp : l.Perm (List.range m)) (hnc : NoCross (lpt m l) (m + 1))
include hp

theorem pos_nbr {y : ℕ} {σ : Bool} (hs : HasSideM m y σ) :
    pos m l (nbr m l σ y) + 1 = pos m l y ∨ pos m l y + 1 = pos m l (nbr m l σ y) := by
  obtain ⟨hj, _, hc⟩ := arcIdx_spec hp hs
  generalize arcIdx m l σ y = j at hj hc
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2, h1, pos_lpt hp (by omega), pos_lpt hp (by omega)] <;>
    omega

omit hp in
theorem hasSideM_le {y : ℕ} {σ : Bool} (hs : HasSideM m y σ) : y ≤ m + 1 := by
  rcases hs with h | ⟨h, _⟩ | ⟨h, _⟩ <;> omega

theorem nbr_le {y : ℕ} {σ : Bool} (hs : HasSideM m y σ) : nbr m l σ y ≤ m + 1 :=
  hasSideM_le (nbr_hasSide hp hs).1

include hnc in
/-- If `k` closes its arc on side `σ`, the other end is the last open arc on that side. -/
theorem stkF_max {k : ℕ} {σ : Bool} (hks : HasSideM m k σ) (hz : nbr m l σ k < k) :
    ∀ y, y < k → HasSideM m y σ → k ≤ nbr m l σ y → y ≤ nbr m l σ k := by
  intro y hy hys hky
  by_contra hlt
  rw [not_le] at hlt
  set z := nbr m l σ k with hzdef
  have hzs : HasSideM m z σ := (nbr_hasSide hp hks).1
  have hzk : nbr m l σ z = k := (nbr_hasSide hp hks).2.1
  have hyk : nbr m l σ y ≠ k := by
    intro he
    have := (nbr_hasSide hp hys).2.1
    rw [he] at this
    omega
  have hc := nbr_nc hp hnc hzs hys (by omega) (by rw [hzk]; omega)
  rw [hzk] at hc
  apply hc
  unfold Interleave
  omega

include hnc in
theorem stkF_succ {k : ℕ} (hk : k ≤ m) (σ : Bool) :
    (HasSideM m k σ → k < nbr m l σ k → stkF m l σ (k + 1) = stkF m l σ k ++ [k]) ∧
    (HasSideM m k σ → nbr m l σ k < k →
      stkF m l σ k = (stkF m l σ k).dropLast ++ [nbr m l σ k] ∧
      stkF m l σ (k + 1) = (stkF m l σ k).dropLast) ∧
    (¬ HasSideM m k σ → stkF m l σ (k + 1) = stkF m l σ k) := by
  -- no earlier point has `k` as its other end, unless `k` closes
  have hno : ¬ (HasSideM m k σ ∧ nbr m l σ k < k) →
      ∀ y < k, HasSideM m y σ → nbr m l σ y ≠ k := by
    intro hn y hy hys he
    have h1 := (nbr_hasSide hp hys).1
    rw [he] at h1
    have h2 := (nbr_hasSide hp hys).2.1
    rw [he] at h2
    exact hn ⟨h1, by omega⟩
  have hsplit : stkF m l σ (k + 1) =
      ((List.range k).filter fun y => decide (HasSideM m y σ ∧ k + 1 ≤ nbr m l σ y)) ++
        (if HasSideM m k σ ∧ k + 1 ≤ nbr m l σ k then [k] else []) := by
    simp only [stkF, List.range_succ, List.filter_append, List.filter_cons, List.filter_nil]
    congr 1
    split_ifs with h1 h2 h2 <;> simp_all
  refine ⟨fun hs hlt => ?_, fun hs hlt => ?_, fun hs => ?_⟩
  · rw [hsplit, if_pos ⟨hs, by omega⟩]
    congr 1
    apply List.filter_congr
    intro y hy
    rw [List.mem_range] at hy
    have := hno (fun h => by omega) y hy
    by_cases hys : HasSideM m y σ
    · have := this hys; simp [hys]; omega
    · simp [hys]
  · set z := nbr m l σ k with hzdef
    have hzs : HasSideM m z σ := (nbr_hasSide hp hs).1
    have hzk : nbr m l σ z = k := (nbr_hasSide hp hs).2.1
    have hmax := stkF_max hp hnc hs hlt
    have hmem : z ∈ stkF m l σ k := by
      simp only [stkF, List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨hlt, hzs, by omega⟩
    have hsorted : (stkF m l σ k).Pairwise (· < ·) :=
      List.Pairwise.filter _ List.pairwise_lt_range
    have hne : stkF m l σ k ≠ [] := List.ne_nil_of_mem hmem
    have hlast : (stkF m l σ k).getLast? = some z := by
      rw [List.getLast?_eq_some_getLast hne, Option.some.injEq]
      have hlm := mem_stkF.1 (List.getLast_mem hne)
      have hle := hmax _ hlm.1 hlm.2.1 hlm.2.2
      have hsp := List.dropLast_append_getLast hne
      have hge : z ≤ (stkF m l σ k).getLast hne := by
        rw [← hsp] at hmem hsorted
        rw [List.pairwise_append] at hsorted
        rcases List.mem_append.1 hmem with h' | h'
        · exact (hsorted.2.2 z h' _ (List.mem_singleton_self _)).le
        · simp at h'; omega
      omega
    have h1 : stkF m l σ k = (stkF m l σ k).dropLast ++ [z] :=
      (List.dropLast_append_getLast? z hlast).symm
    refine ⟨h1, ?_⟩
    rw [hsplit, if_neg (fun h => by have := h.2; omega), List.append_nil]
    have hf : ((List.range k).filter fun y => decide (HasSideM m y σ ∧ k + 1 ≤ nbr m l σ y)) =
        (stkF m l σ k).filter fun y => y ≠ z := by
      rw [stkF, List.filter_filter]
      apply List.filter_congr
      intro y hy
      rw [List.mem_range] at hy
      by_cases hys : HasSideM m y σ
      · have hyz : nbr m l σ y = k ↔ y = z := by
          constructor
          · intro he; have := (nbr_hasSide hp hys).2.1; rw [he] at this; exact this.symm
          · intro he; rw [he, hzk]
        rw [Bool.eq_iff_iff]
        simp only [hys, true_and, Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · intro h'; exact ⟨fun he => by rw [hyz.2 he] at h'; omega, by omega⟩
        · rintro ⟨h', h''⟩
          have : nbr m l σ y ≠ k := fun he => h' (hyz.1 he)
          omega
      · simp [hys]
    rw [hf, h1, List.filter_append]
    have hnd : (stkF m l σ k).Nodup := hsorted.imp (fun h => Nat.ne_of_lt h)
    rw [h1] at hnd
    have hz' : z ∉ (stkF m l σ k).dropLast := by
      rw [← h1] at hnd
      intro hz''
      have := (List.nodup_append.1 (h1 ▸ hnd)).2.2 z hz'' z (List.mem_singleton_self _)
      exact this rfl
    have e1 : ([z].filter fun y => decide (y ≠ z)) = [] := by simp
    rw [e1, List.append_nil, List.filter_eq_self.2, List.dropLast_concat]
    intro y hy
    simp only [ne_eq, decide_eq_true_eq]
    exact fun he => hz' (he ▸ hy)
  · rw [hsplit, if_neg (fun h => hs h.1), List.append_nil]
    apply List.filter_congr
    intro y hy
    rw [List.mem_range] at hy
    have := hno (fun h => hs h.1) y hy
    by_cases hys : HasSideM m y σ
    · have := this hys; simp [hys]; omega
    · simp [hys]

end Facts

end Arnold.TM
