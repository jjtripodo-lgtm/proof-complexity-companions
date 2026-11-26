module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Paper Definition 1: a term is a consistent literal cube on the entire Boolean board.
There are no row functionality assumptions on the evaluation domain. -/
namespace PHP

open scoped BigOperators

abbrev Cell (m n : ℕ) := Fin m × Fin n
abbrev Board (m n : ℕ) := Cell m n → Bool
abbrev Cube (m n : ℕ) := Cell m n → Option Bool

def Holds {m n : ℕ} (C : Cube m n) (x : Board m n) : Prop :=
  ∀ ij b, C ij = some b → x ij = b

noncomputable def eval {m n : ℕ} (C : Cube m n) (x : Board m n) : ℝ := by
  classical
  exact if Holds C x then 1 else 0

def EmptyRow {m n : ℕ} (C : Cube m n) : Prop :=
  ∃ i, ∀ j, C (i, j) = some false

def ColumnCollision {m n : ℕ} (C : Cube m n) : Prop :=
  ∃ i i' j, i ≠ i' ∧ C (i, j) = some true ∧ C (i', j) = some true

def RowCollision {m n : ℕ} (C : Cube m n) : Prop :=
  ∃ i j j', j ≠ j' ∧ C (i, j) = some true ∧ C (i, j') = some true

def Plain {m n : ℕ} (C : Cube m n) : Prop := EmptyRow C ∨ ColumnCollision C

def Functional {m n : ℕ} (C : Cube m n) : Prop := Plain C ∨ RowCollision C

structure Refutation {m n : ℕ} (Allowed : Cube m n → Prop) (t : ℕ) where
  cube : Fin t → Cube m n
  coeff : Fin t → ℝ
  legal : ∀ k, Allowed (cube k)
  identity : ∀ x : Board m n, (∑ k, coeff k * eval (cube k) x) = 1

noncomputable def Refutation.mass {m n t : ℕ} {A : Cube m n → Prop}
    (r : Refutation A t) : ℝ := ∑ k, |r.coeff k|

noncomputable def pairing {m n : ℕ} (w : Board m n → ℝ) (C : Cube m n) : ℝ :=
  ∑ x, w x * eval C x

/-- A dual may be supported on an arbitrary finite family of full boards;
the primal identity is still required on every Boolean board. -/
theorem dual_bound_on {m n t : ℕ} {A : Cube m n → Prop} (r : Refutation A t)
    {S : Type*} [Fintype S] (sample : S → Board m n) (w : S → ℝ)
    (hw : ∀ C, A C → |∑ u, w u * eval C (sample u)| ≤ 1) :
    (∑ u, w u) ≤ r.mass := by
  classical
  calc
    (∑ u, w u) = ∑ u, w u * ∑ k, r.coeff k * eval (r.cube k) (sample u) := by
      apply Finset.sum_congr rfl
      intro u _
      rw [r.identity (sample u), mul_one]
    _ = ∑ k, r.coeff k * ∑ u, w u * eval (r.cube k) (sample u) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ ≤ r.mass := by
      unfold Refutation.mass
      apply Finset.sum_le_sum
      intro k _
      calc
        _ ≤ |r.coeff k * ∑ u, w u * eval (r.cube k) (sample u)| := le_abs_self _
        _ = |r.coeff k| * |∑ u, w u * eval (r.cube k) (sample u)| := abs_mul _ _
        _ ≤ |r.coeff k| * 1 :=
          mul_le_mul_of_nonneg_left (hw _ (r.legal k)) (abs_nonneg _)
        _ = _ := mul_one _

/-- The signed dual lower bound on the literal coefficient mass of every finite
pointwise identity, with no relaxation of the board or coefficient domain. -/
theorem dual_bound {m n t : ℕ} {A : Cube m n → Prop} (r : Refutation A t)
    (w : Board m n → ℝ) (hw : ∀ C, A C → |pairing w C| ≤ 1) :
    (∑ x, w x) ≤ r.mass :=
  dual_bound_on r id w hw

end PHP
