import PHP.CubeProduct
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace PHP

open scoped BigOperators

structure Combination (m n : ℕ) (I : Type) where
  cube : I → Cube m n
  coeff : I → ℝ

namespace Combination

variable {m n : ℕ} {I J : Type}

noncomputable def value [Fintype I] (C : Combination m n I) (x : Board m n) : ℝ :=
  ∑ i, C.coeff i * eval (C.cube i) x

noncomputable def cost [Fintype I] (C : Combination m n I) : ℝ :=
  ∑ i, |C.coeff i|

/-- Zero coefficient entries contribute nothing and need not have a source. -/
def legal (A : Cube m n → Prop) (C : Combination m n I) : Prop :=
  ∀ i, C.coeff i ≠ 0 → A (C.cube i)

noncomputable def prod (C : Combination m n I) (D : Combination m n J) :
    Combination m n (I × J) := by
  classical
  exact ⟨fun p => join (C.cube p.1) (D.cube p.2),
    fun p => if Compatible (C.cube p.1) (D.cube p.2)
      then C.coeff p.1 * D.coeff p.2 else 0⟩

theorem value_prod [Fintype I] [Fintype J] (C : Combination m n I)
    (D : Combination m n J) (x : Board m n) :
    (C.prod D).value x = C.value x * D.value x := by
  classical
  unfold value
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hE := eval_product (C.cube i) (D.cube j) x
  by_cases h : Compatible (C.cube i) (D.cube j)
  · simp [prod,h] at hE ⊢
    rw [show C.coeff i * eval (C.cube i) x * (D.coeff j * eval (D.cube j) x) =
      C.coeff i * D.coeff j * (eval (C.cube i) x * eval (D.cube j) x) by ring, hE]
  · simp only [prod,h,if_false,zero_mul] at hE ⊢
    rw [show C.coeff i * eval (C.cube i) x * (D.coeff j * eval (D.cube j) x) =
      C.coeff i * D.coeff j * (eval (C.cube i) x * eval (D.cube j) x) by ring, hE, mul_zero]

theorem cost_prod_le [Fintype I] [Fintype J] (C : Combination m n I)
    (D : Combination m n J) : (C.prod D).cost ≤ C.cost * D.cost := by
  classical
  unfold cost
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  by_cases h : Compatible (C.cube i) (D.cube j)
  · simp [prod,h,abs_mul]
  · simp only [prod,h,if_false,abs_zero]
    exact mul_nonneg (abs_nonneg _) (abs_nonneg _)

theorem legal_prod {A : Cube m n → Prop}
    (mono : ∀ {c d : Cube m n}, Extends d c → A c → A d)
    {C : Combination m n I} (hC : C.legal A) (D : Combination m n J) :
    (C.prod D).legal A := by
  classical
  rintro ⟨i,j⟩ h
  have hc : C.coeff i ≠ 0 := by
    intro hc
    simp [prod,hc] at h
  exact mono (join_extends_left _ _) (hC i hc)

/-- Turn an indexed certificate into the existing finite-list theorem
interface, dropping zero-weight entries before reindexing. -/
theorem refutation_of_value_one [Fintype I] {A : Cube m n → Prop}
    (C : Combination m n I) (hC : C.legal A) (h : ∀ x, C.value x = 1) :
    ∃ (t : ℕ) (r : Refutation A t), r.mass = C.cost := by
  classical
  let T := {i : I // C.coeff i ≠ 0}
  let e := (Fintype.equivFin T).symm
  let r : Refutation A (Fintype.card T) :=
    { cube := fun k => C.cube (e k)
      coeff := fun k => C.coeff (e k)
      legal := fun k => hC _ (e k).property
      identity := fun x => by
        have he := Fintype.sum_equiv e
          (fun k => C.coeff (e k) * eval (C.cube (e k)) x)
          (fun i : T => C.coeff i * eval (C.cube i) x) (by intro k; rfl)
        rw [he]
        rw [← Finset.sum_subtype (Finset.univ.filter (fun i : I => C.coeff i ≠ 0))
          (by simp : ∀ i : I, i ∈ Finset.univ.filter (fun i : I => C.coeff i ≠ 0) ↔ C.coeff i ≠ 0)
          (fun i => C.coeff i * eval (C.cube i) x), Finset.sum_filter]
        have hx := h x
        unfold value at hx
        rw [← hx]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : C.coeff i = 0 <;> simp [hi] }
  refine ⟨_,r,?_⟩
  unfold Refutation.mass cost
  change (∑ k, |C.coeff (e k)|) = _
  have he := Fintype.sum_equiv e (fun k => |C.coeff (e k)|)
    (fun i : T => |C.coeff i|) (by intro k; rfl)
  rw [he]
  rw [← Finset.sum_subtype (Finset.univ.filter (fun i : I => C.coeff i ≠ 0))
    (by simp : ∀ i : I, i ∈ Finset.univ.filter (fun i : I => C.coeff i ≠ 0) ↔ C.coeff i ≠ 0)
    (fun i => |C.coeff i|), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : C.coeff i = 0 <;> simp [hi]

end Combination

end PHP
