import Arnold.Basic

/-!
# Closed meanders of order `n` are open meanders with `2n - 1` crossings

Take a closed meander with `2n` crossings, normalized to start at the westmost bridge `0` and
leave it into the upper half-plane. Delete that bridge: the two arcs at it now run off to
infinity in the west. Rotate the picture by 180°. The river now comes in from infinity in the
lower half-plane, crosses the road `2n - 1` times and leaves to the east, so it is an open
meander. Every step can be undone.

In coordinates, an open crossing order `τ` on `2n+1` bridges becomes the closed order
`0, 2n+1 - τ 0, 2n+1 - τ 1, …`, which is `Equiv.Perm.decomposeFin.symm (0, τ.trans Fin.revPerm)`.
-/

namespace Arnold

open Equiv

/-- Rotate an open meander with `2n+1` crossings by 180° and close it up through a new
westmost bridge `0`. -/
def closeUp {n : ℕ} (τ : Perm (Fin (2 * n + 1))) : Perm (Fin (2 * n + 1 + 1)) :=
  Perm.decomposeFin.symm (0, τ.trans Fin.revPerm)

/-- `NoCross` only depends on whether each pair of same-side arcs crosses. -/
theorem noCross_congr {P Q : ℕ → ℕ} {L : ℕ}
    (h : ∀ k < L, ∀ j < k, j % 2 = k % 2 →
      (Interleave (P j) (P (j + 1)) (P k) (P (k + 1)) ↔
        Interleave (Q j) (Q (j + 1)) (Q k) (Q (k + 1)))) :
    NoCross P L ↔ NoCross Q L :=
  forall₂_congr fun k hk => forall₂_congr fun j hj =>
    imp_congr_right fun hp => not_congr (h k hk j hj hp)

/-- The boundary points of an open meander with `2n+1` crossings: the south end `2n+2`, then
bridges `≤ 2n`, then the east end `2n+1`. -/
theorem pathPt_cases {n : ℕ} (τ : Perm (Fin (2 * n + 1))) (i : ℕ) (hi : i ≤ 2 * n + 2) :
    (i = 0 ∧ pathPt τ i = 2 * n + 2) ∨ (1 ≤ i ∧ i ≤ 2 * n + 1 ∧ pathPt τ i ≤ 2 * n) ∨
      (i = 2 * n + 2 ∧ pathPt τ i = 2 * n + 1) := by
  unfold pathPt
  split_ifs with h0 h1
  · omega
  · have := (τ ⟨i - 1, h1⟩).isLt
    omega
  · omega

/-- After the rotation, closed point `k` is the open point `k` reflected: `x ↦ 2n+1 - x`.
(Truncated subtraction sends the south end `2n+2` to the new bridge `0`.) -/
theorem closedPt_closeUp {n : ℕ} (τ : Perm (Fin (2 * n + 1))) (k : ℕ) (hk : k ≤ 2 * n + 2) :
    closedPt (n := n + 1) (closeUp τ) k = 2 * n + 1 - pathPt τ k := by
  unfold closedPt
  simp only [show 0 < 2 * (n + 1) by omega, ↓reduceDIte]
  by_cases hmid : 1 ≤ k ∧ k ≤ 2 * n + 1
  · have hidx : (⟨k % (2 * (n + 1)), Nat.mod_lt _ (by omega)⟩ : Fin (2 * n + 1 + 1)) =
        (⟨k - 1, by omega⟩ : Fin (2 * n + 1)).succ := by
      ext; simp only [Fin.val_succ]; rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [hidx]
    simp only [closeUp, Perm.decomposeFin_symm_apply_succ, swap_self, refl_apply,
      Equiv.trans_apply, Fin.revPerm_apply, Fin.val_succ, Fin.val_rev]
    unfold pathPt
    simp only [show k ≠ 0 by omega, show k - 1 < 2 * n + 1 by omega, ↓reduceIte, ↓reduceDIte]
    omega
  · have hidx : (⟨k % (2 * (n + 1)), Nat.mod_lt _ (by omega)⟩ : Fin (2 * n + 1 + 1)) = 0 := by
      ext; simp only [Fin.val_zero]
      rcases Nat.eq_zero_or_pos k with h | h
      · simp [h]
      · rw [show k = 2 * (n + 1) by omega, Nat.mod_self]
    rw [hidx]
    simp only [closeUp, Perm.decomposeFin_symm_apply_zero, Fin.val_zero]
    rcases pathPt_cases τ k hk with h | h | h <;> omega

/-- The rotated, closed-up river is a closed meander exactly when the original river is an open
meander. -/
theorem noCross_closeUp_iff {n : ℕ} (τ : Perm (Fin (2 * n + 1))) :
    NoCross (closedPt (n := n + 1) (closeUp τ)) (2 * (n + 1)) ↔ IsMeander τ := by
  unfold IsMeander
  refine noCross_congr fun k hk j hjk hpar => ?_
  rw [closedPt_closeUp τ j (by omega), closedPt_closeUp τ (j + 1) (by omega),
    closedPt_closeUp τ k (by omega), closedPt_closeUp τ (k + 1) (by omega)]
  have h1 := pathPt_cases τ j (by omega)
  have h2 := pathPt_cases τ (j + 1) (by omega)
  have h3 := pathPt_cases τ k (by omega)
  have h4 := pathPt_cases τ (k + 1) (by omega)
  generalize pathPt τ j = a at *
  generalize pathPt τ (j + 1) = b at *
  generalize pathPt τ k = c at *
  generalize pathPt τ (k + 1) = d at *
  unfold Interleave
  omega

theorem closeUp_zero {n : ℕ} (τ : Perm (Fin (2 * n + 1))) : closeUp τ 0 = 0 := by
  simp [closeUp]

theorem closeUp_injective {n : ℕ} : Function.Injective (closeUp (n := n)) := by
  intro τ τ' h
  have h' : τ.trans Fin.revPerm = τ'.trans Fin.revPerm := by
    have := congrArg (fun σ => (Perm.decomposeFin σ).2) h
    simpa [closeUp] using this
  exact Equiv.ext fun i => by simpa using congrArg (fun e => e i) h'

theorem closeUp_surjective {n : ℕ} (σ : Perm (Fin (2 * n + 1 + 1))) (h0 : σ 0 = 0) :
    ∃ τ, closeUp τ = σ := by
  obtain ⟨⟨p, e⟩, rfl⟩ := Perm.decomposeFin.symm.surjective σ
  rw [Perm.decomposeFin_symm_apply_zero] at h0
  subst h0
  refine ⟨e.trans Fin.revPerm, ?_⟩
  unfold closeUp
  congr
  ext i
  simp

/-- **Closed meanders of order `n+1` are open meanders with `2n+1` crossings.** -/
theorem closedMeanderCount_succ (n : ℕ) :
    closedMeanderCount (n + 1) = openMeanderCount (2 * n + 1) := by
  unfold closedMeanderCount openMeanderCount
  symm
  refine Fintype.card_of_bijective
    (f := fun τ => ⟨closeUp τ.1, fun _ => closeUp_zero τ.1,
      (noCross_closeUp_iff τ.1).2 τ.2⟩) ⟨?_, ?_⟩
  · intro τ τ' h
    exact Subtype.ext (closeUp_injective (congrArg Subtype.val h))
  · rintro ⟨σ, h0, hσ⟩
    obtain ⟨τ, rfl⟩ := closeUp_surjective σ (h0 (by omega))
    exact ⟨⟨τ, (noCross_closeUp_iff τ).1 hσ⟩, rfl⟩

/-- **Closed meanders of order `n` are open meanders with `2n-1` crossings** (`n ≥ 1`). -/
theorem closedMeanderCount_eq (n : ℕ) (hn : 1 ≤ n) :
    closedMeanderCount n = openMeanderCount (2 * n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [closedMeanderCount_succ]
  congr 1

end Arnold
