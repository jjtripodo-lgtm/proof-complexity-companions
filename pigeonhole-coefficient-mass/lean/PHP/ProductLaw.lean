import PHP.Model
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! The algebraic part of block calibration: signed rectangle pairings
tensorize and remain bounded under probability mixtures. -/
namespace PHP

open scoped BigOperators

theorem rectangle_product_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)]
    (f : ∀ i, β i → ℝ) (h : ∀ i, |∑ x, f i x| ≤ 1) :
    |∑ a : ∀ i, β i, ∏ i, f i (a i)| ≤ 1 := by
  classical
  rw [← Fintype.prod_sum, Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun i _ => h i)

theorem calibrated_mixture {ι : Type*} [Fintype ι]
    (p w : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (hw : ∀ i, |w i| ≤ 1) : |∑ i, p i * w i| ≤ 1 := by
  calc
    _ ≤ ∑ i, |p i * w i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, p i := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (hp i)]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hw i) (hp i)
    _ = _ := hs

end PHP
