import PHP.RowDeletion
import Mathlib.Logic.Equiv.Fin.Basic

namespace PHP

open scoped BigOperators

def RowInvariant {m n : ℕ} (L : Word m n → ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin m)) (a : Word m n), L (fun j => (a j).map σ) = L a

/-- The reindexing of retained labels obtained by swapping the two missing rows. -/
def missingSwap {m : ℕ} (i i' : Fin (m+1)) : Equiv.Perm (Fin m) :=
  let e := Equiv.swap i i'
  let h : ∀ x, x ≠ i ↔ e x ≠ i' := fun x => by
    have hleft : e i = i' := Equiv.swap_apply_left i i'
    rw [← hleft]
    exact not_congr e.injective.eq_iff.symm
  (finSuccAboveEquiv i).trans ((e.subtypeEquiv h).trans (finSuccAboveEquiv i').symm)

theorem missingSwap_retained {m : ℕ} (i i' : Fin (m+1)) (p : Fin m) :
    i'.succAbove (missingSwap i i' p) = Equiv.swap i i' (i.succAbove p) := by
  unfold missingSwap
  let e := Equiv.swap i i'
  have h : ∀ x, x ≠ i ↔ e x ≠ i' := fun x => by
    have hleft : e i = i' := Equiv.swap_apply_left i i'
    rw [← hleft]
    exact not_congr e.injective.eq_iff.symm
  change ((finSuccAboveEquiv i') ((finSuccAboveEquiv i').symm
    (e.subtypeEquiv h (finSuccAboveEquiv i p)))).val = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem compatible_preimages {m n : ℕ} {L : Word m n → ℝ}
    (hinv : RowInvariant L) (i i' : Fin (m+1)) (a b : Word m n)
    (he : a.insertRow i = b.insertRow i') : L a = L b := by
  have hg : (fun j => (a j).map (missingSwap i i')) = b := by
    apply insertRow_injective i'
    funext j
    rw [← he]
    cases hj : a j with
    | none => simp [Word.insertRow, hj]
    | some p =>
      have hne : i.succAbove p ≠ i' := by
        intro h
        have ha : a.insertRow i j = some i' := by simp [Word.insertRow, hj, h]
        rw [he] at ha
        exact insertedRow_absent i' b j ha
      simp [Word.insertRow, hj, missingSwap_retained,
        Equiv.swap_apply_of_ne_of_ne (Fin.succAbove_ne i p) hne]
  rw [← hg, hinv]

/-- A symmetric small-board law defines a single weight compatible with every
one-row deletion. Patterns not represented by such a deletion receive zero. -/
noncomputable def liftSymmetric {m n : ℕ} (L : Word m n → ℝ)
    (a : Word (m+1) n) : ℝ := by
  classical
  exact if h : ∃ i, ∃ b : Word m n, b.insertRow i = a
    then L (Classical.choose (Classical.choose_spec h))
    else 0

theorem liftSymmetric_insert {m n : ℕ} {L : Word m n → ℝ}
    (hinv : RowInvariant L) (i : Fin (m+1)) (a : Word m n) :
    liftSymmetric L (a.insertRow i) = L a := by
  classical
  have h : ∃ i', ∃ b : Word m n, b.insertRow i' = a.insertRow i := ⟨i,a,rfl⟩
  unfold liftSymmetric
  rw [dif_pos h]
  exact compatible_preimages hinv _ i _ a
    (Classical.choose_spec (Classical.choose_spec h))

/-- The signed symmetric law gives a valid lower bound in the original,
unrestricted full-board primal model. -/
theorem symmetric_lower_bound {m n t : ℕ}
    (r : Refutation (@Plain (m+1) n) t) (L : Word m n → ℝ)
    (hinv : RowInvariant L)
    (hL : ∀ C : Cube m n, |∑ a, L a * eval C a.board| ≤ 1) :
    (∑ a, liftSymmetric L a) ≤ r.mass :=
  row_deletion_transfer r L _ hL (liftSymmetric_insert hinv)

end PHP
