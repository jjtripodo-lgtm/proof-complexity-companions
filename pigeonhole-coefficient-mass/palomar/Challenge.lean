module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.SpecialFunctions.Exp

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


/-- At twice as many pigeons as holes, plain real-coefficient weakening
refutations have exponential coefficient mass whereas the functional system
admits a polynomial-mass refutation. Pigeonhole terms are checked on every
Boolean board. -/
theorem paper_diagonal_separation (n : ℕ) (hn : 1 ≤ n) :
    (∀ t (r : Refutation (@Plain (2*n) n) t), Real.exp ((149/1000 : ℝ)*n-8) ≤ r.mass)
    ∧ (∃ (t : ℕ) (r : Refutation (@Functional (2*n) n) t), r.mass ≤ 16*(n:ℝ)^3) := by
  sorry

end PHP
