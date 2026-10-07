import Arnold.TM.StepE

/-!
# Running the decorated machine
-/

set_option linter.deprecated false

namespace Arnold.TM

open DSt

/-- Run the decorated machine from point `x`. -/
def druns (m : ℕ) : ℕ → DSt → List (Bool × Bool) → Option DSt
  | _, D, [] => some D
  | x, D, a :: ws => (dstep m x D a).bind fun D' => druns m (x + 1) D' ws

theorem runFrom_abs (m : ℕ) : ∀ (ws : List (Bool × Bool)) (x : ℕ) (D : DSt),
    runFrom m x D.abs ws = (druns m x D ws).map DSt.abs
  | [], x, D => rfl
  | a :: ws, x, D => by
    simp only [runFrom, druns, step_abs]
    cases dstep m x D a with
    | none => rfl
    | some D' => simp [runFrom_abs m ws (x + 1) D']

theorem abs_empty : DSt.empty.abs = init := rfl

/-- One step of the decorated machine keeps the invariant. -/
theorem inv_dstep {m x : ℕ} {w : List (Bool × Bool)} {D D' : DSt} {a : Bool × Bool}
    (h : Inv m x w D) (hx : x ≤ m) (ha : a ∈ acts m x) (hD : dstep m x D a = some D') :
    Inv m (x + 1) (w ++ [a]) D' := by
  unfold dstep at hD
  by_cases hxm : x < m
  · rw [if_pos hxm] at hD
    rcases a with ⟨_ | _, _ | _⟩
    · simp only at hD
      cases hu : (D.stk true).getLast? <;> cases hl : (D.stk false).getLast? <;>
        rw [hu, hl] at hD <;> simp only [reduceCtorEq] at hD
      rename_i u l
      split_ifs at hD with hcyc
      simp only [Option.some.injEq] at hD
      subst hD
      exact inv_FF h hxm hu hl hcyc
    · exact inv_OC (σ := false) h hxm hD
    · exact inv_OC (σ := true) h hxm hD
    · simp only [Option.some.injEq] at hD
      subst hD
      exact inv_TT h hxm
  · rw [if_neg hxm] at hD
    have hxe : x = m := by omega
    subst hxe
    dsimp only at hD
    by_cases ha1 : a.1 = true
    · rw [if_pos ha1, Option.some.injEq] at hD
      subst hD
      exact inv_EO h ha1
    · rw [if_neg ha1] at hD
      cases ht : (D.stk (x % 2 == 1)).getLast? with
      | none => rw [ht] at hD; simp at hD
      | some t =>
        rw [ht] at hD
        simp only at hD
        split_ifs at hD with htE
        simp only [Option.some.injEq] at hD
        subst hD
        exact inv_EC h (by simpa using ha1) ht htE

theorem mem_sufWords (m : ℕ) : ∀ (f x : ℕ) (ws : List (Bool × Bool)), ws ∈ sufWords m f x →
    ws.length = f ∧ ∀ i (hi : i < ws.length), ws[i] ∈ acts m (x + i)
  | 0, x, ws, h => by
    simp only [sufWords, List.mem_singleton] at h
    subst h; simp
  | f + 1, x, ws, h => by
    simp only [sufWords, List.mem_flatMap, List.mem_map] at h
    obtain ⟨a, ha, ws', hws', rfl⟩ := h
    obtain ⟨hl, hi⟩ := mem_sufWords m f (x + 1) ws' hws'
    refine ⟨by simp [hl], fun i hi' => ?_⟩
    cases i with
    | zero => simpa using ha
    | succ i =>
      simp only [List.getElem_cons_succ]
      have := hi i (by simp at hi'; omega)
      rwa [show x + 1 + i = x + (i + 1) by omega] at this

/-- The invariant holds along a whole run. -/
theorem inv_druns (m : ℕ) : ∀ (ws : List (Bool × Bool)) (x : ℕ) (w : List (Bool × Bool))
    (D D' : DSt), Inv m x w D → x + ws.length ≤ m + 1 →
    (∀ i (hi : i < ws.length), ws[i] ∈ acts m (x + i)) → druns m x D ws = some D' →
    Inv m (x + ws.length) (w ++ ws) D'
  | [], x, w, D, D', h, _, _, hr => by
    simp only [druns, Option.some.injEq] at hr
    subst hr; simpa using h
  | a :: ws, x, w, D, D', h, hlen, hacts, hr => by
    simp only [druns] at hr
    cases hs : dstep m x D a with
    | none => rw [hs] at hr; simp at hr
    | some D1 =>
      rw [hs] at hr
      simp only [Option.bind_some] at hr
      have h0 := hacts 0 (by simp)
      simp only [List.getElem_cons_zero, add_zero] at h0
      have h1 := inv_dstep h (by simp at hlen; omega) h0 hs
      have := inv_druns m ws (x + 1) (w ++ [a]) D1 D' h1 (by simp at hlen; omega)
        (fun i hi => by
          have := hacts (i + 1) (by simp; omega)
          simpa [show x + (i + 1) = x + 1 + i by omega] using this) hr
      simpa [show x + 1 + ws.length = x + (ws.length + 1) by omega] using this

/-- An accepted action sequence runs the decorated machine to a state satisfying the
invariant, with exactly one open arc: below the road, leading to `E`. -/
theorem decorated_of_accepted {m : ℕ} {w : List (Bool × Bool)} (hw : w ∈ sufWords m (m + 1) 0)
    (hacc : runFrom m 0 init w = some final) :
    ∃ D t, druns m 0 DSt.empty w = some D ∧ D.up = [] ∧ D.dn = [t] ∧ t.ref = .E ∧
      Inv m (m + 1) w D := by
  obtain ⟨hlen, hacts⟩ := mem_sufWords m (m + 1) 0 w hw
  rw [← abs_empty, runFrom_abs] at hacc
  cases hr : druns m 0 DSt.empty w with
  | none => rw [hr] at hacc; simp at hacc
  | some D =>
    rw [hr] at hacc
    simp only [Option.map_some, Option.some.injEq] at hacc
    have hinv := inv_druns m w 0 [] DSt.empty D (inv_init m) (by omega)
      (fun i hi => by simpa using hacts i hi) hr
    simp only [zero_add, List.nil_append, hlen] at hinv
    have hup : D.up.map Strand.ref = [] := congrArg St.up hacc
    have hdn : D.dn.map Strand.ref = [.E] := congrArg St.dn hacc
    rw [List.map_eq_nil_iff] at hup
    obtain ⟨t, ht⟩ : ∃ t, D.dn = [t] := by
      rcases hd : D.dn with _ | ⟨t, _ | ⟨t', l⟩⟩ <;> rw [hd] at hdn <;> simp at hdn
      exact ⟨t, rfl⟩
    rw [ht] at hdn
    exact ⟨D, t, rfl, hup, ht, by simpa using hdn, hinv⟩

end Arnold.TM
