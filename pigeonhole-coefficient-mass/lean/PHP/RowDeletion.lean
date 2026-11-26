import PHP.BoardBridge
import Mathlib.Data.Fin.SuccPred

/-! The exact restriction/transport step of the row-deletion lift.
This does not construct the symmetric law or count pattern multiplicities. -/
namespace PHP

open scoped BigOperators

def Word.insertRow {m n : ℕ} (i : Fin (m+1)) (a : Word m n) : Word (m+1) n :=
  fun j => (a j).map i.succAbove

def pullRow {m n : ℕ} (i : Fin (m+1)) (C : Cube (m+1) n) : Cube m n :=
  fun ij => C (i.succAbove ij.1, ij.2)

theorem insertedRow_absent {m n : ℕ} (i : Fin (m+1)) (a : Word m n) (j : Fin n) :
    a.insertRow i j ≠ some i := by
  cases h : a j with
  | none => simp [Word.insertRow, h]
  | some v => simp [Word.insertRow, h]

theorem on_retained_row {m n : ℕ} (i : Fin (m+1)) (a : Word m n)
    (p : Fin m) (j : Fin n) :
    (a.insertRow i).board (i.succAbove p,j) = a.board (p,j) := by
  cases h : a j with
  | none => simp [Word.board, Word.insertRow, h]
  | some v => simp [Word.board, Word.insertRow, h]

theorem holds_insertRow {m n : ℕ} (i : Fin (m+1)) (a : Word m n)
    (C : Cube (m+1) n) (he : ∀ j, C (i,j) = some false) :
    Holds C (a.insertRow i).board ↔ Holds (pullRow i C) a.board := by
  constructor
  · intro h ij b hb
    rw [← on_retained_row i a ij.1 ij.2]
    exact h _ b hb
  · intro h ij b hb
    obtain ⟨q,j⟩ := ij
    by_cases hh : q = i
    · subst q
      have hbf : b = false := Option.some.inj (hb.symm.trans (he j))
      rw [hbf]
      simp [Word.board, insertedRow_absent]
    · obtain ⟨p,hp⟩ := Fin.exists_succAbove_eq hh
      rw [← hp, on_retained_row]
      apply h (p,j) b
      simpa [pullRow, hp] using hb

theorem insertRow_injective {m n : ℕ} (i : Fin (m+1)) :
    Function.Injective (@Word.insertRow m n i) := by
  intro a b hab
  funext j
  have hj := congrFun hab j
  cases h₁ : a j <;> cases h₂ : b j <;>
    simp_all [Word.insertRow]

theorem exists_insertRow {m n : ℕ} (i : Fin (m+1)) (a : Word (m+1) n)
    (ha : ∀ j, a j ≠ some i) : ∃ b : Word m n, b.insertRow i = a := by
  classical
  have h : ∀ j, ∃ v : Option (Fin m), v.map i.succAbove = a j := by
    intro j
    cases hj : a j with
    | none => exact ⟨none,rfl⟩
    | some p =>
      have hp : p ≠ i := by simpa [hj] using ha j
      obtain ⟨v,hv⟩ := Fin.exists_succAbove_eq hp
      exact ⟨some v, by simp [hv]⟩
  choose b hb using h
  exact ⟨b, funext hb⟩

/-- All large-board source tests follow from the simultaneous restriction
identity for the candidate weight and a calibrated small-board law. -/
theorem row_deletion_transfer {m n t : ℕ}
    (r : Refutation (@Plain (m+1) n) t) (L : Word m n → ℝ)
    (W : Word (m+1) n → ℝ)
    (hL : ∀ C : Cube m n, |∑ a, L a * eval C a.board| ≤ 1)
    (hW : ∀ i (a : Word m n), W (a.insertRow i) = L a) :
    (∑ a, W a) ≤ r.mass := by
  classical
  apply plain_dual_words r W
  intro C hC
  obtain ⟨i, he⟩ := hC
  let absent : Word (m+1) n → Prop := fun a => ∀ j, a j ≠ some i
  have hz : ∀ a, ¬ absent a → eval C a.board = 0 := by
    intro a ha
    have hf : ¬ Holds C a.board :=
      fun h => ha (empty_row_forces_absence a he h)
    simp [eval, hf]
  have hsum : (∑ a : Word (m+1) n, W a * eval C a.board) =
      ∑ a ∈ Finset.univ.filter absent, W a * eval C a.board := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : absent a
    · exact (if_pos ha).symm
    · rw [if_neg ha, hz a ha, mul_zero]
  have hreindex :
      (∑ a : Word m n, L a * eval (pullRow i C) a.board) =
        ∑ a ∈ Finset.univ.filter absent, W a * eval C a.board := by
    apply Finset.sum_nbij (fun a => a.insertRow i)
    · intro a _
      simp [absent, insertedRow_absent]
    · exact (insertRow_injective i).injOn
    · intro a ha
      have h' : absent a := (Finset.mem_filter.mp ha).2
      obtain ⟨b,hb⟩ := exists_insertRow i a h'
      exact ⟨b, Finset.mem_univ _, hb⟩
    · intro a _
      rw [hW]
      simp only [eval, holds_insertRow i a C he]
  rw [hsum, ← hreindex]
  exact hL _

end PHP
