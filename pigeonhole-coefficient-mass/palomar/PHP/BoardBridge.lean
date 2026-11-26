module

public import Mathlib.Data.Fintype.Option
public import PHP.Model

@[expose] public section

/-! Column-capacity boards may support the plain-case dual, but the
refutation remains quantified over the entire Boolean cube. -/
namespace PHP

abbrev Word (m n : ℕ) := Fin n → Option (Fin m)

/-- A column has one occupant (or none). No bound is placed on the
number of times a row label occurs. -/
def Word.board {m n : ℕ} (a : Word m n) : Board m n := fun ij =>
  decide (a ij.2 = some ij.1)

theorem word_column_exclusive {m n : ℕ} (a : Word m n)
    {i i' : Fin m} {j : Fin n} (hi : a.board (i,j) = true)
    (hi' : a.board (i',j) = true) : i = i' := by
  have h₁ : a j = some i := of_decide_eq_true hi
  have h₂ : a j = some i' := of_decide_eq_true hi'
  exact Option.some.inj (h₁.symm.trans h₂)

theorem column_collision_not_holds {m n : ℕ} (a : Word m n)
    {C : Cube m n} (hc : ColumnCollision C) : ¬ Holds C a.board := by
  rintro hx
  obtain ⟨i, i', j, hne, h₁, h₂⟩ := hc
  exact hne (word_column_exclusive a (hx _ _ h₁) (hx _ _ h₂))

theorem empty_row_forces_absence {m n : ℕ} (a : Word m n)
    {C : Cube m n} {i : Fin m} (hc : ∀ j, C (i,j) = some false)
    (hx : Holds C a.board) : ∀ j, a j ≠ some i := by
  intro j hj
  have h := hx (i,j) false (hc j)
  simp [Word.board, hj] at h

theorem holds_word_iff_columns {m n : ℕ} (C : Cube m n) (a : Word m n) :
    Holds C a.board ↔ ∀ (j : Fin n) (i : Fin m) (b : Bool),
      C (i,j) = some b → decide (a j = some i) = b := by
  constructor
  · intro h j i b hb
    exact h (i,j) b hb
  · intro h ij b hb
    exact h ij.2 ij.1 b hb

/-- For a dual supported on words, only empty-row weakenings need to be
tested. Every collision weakening evaluates to zero on that support. -/
theorem plain_dual_words {m n t : ℕ} (r : Refutation (@Plain m n) t)
    (w : Word m n → ℝ)
    (h : ∀ C, EmptyRow C → |∑ a, w a * eval C a.board| ≤ 1) :
    (∑ a, w a) ≤ r.mass := by
  classical
  apply dual_bound_on r Word.board w
  intro C hC
  rcases hC with he | hc
  · exact h C he
  · have hz : ∀ a : Word m n, eval C a.board = 0 := by
      intro a
      simp [eval, column_collision_not_holds a hc]
    simp [hz]

end PHP
