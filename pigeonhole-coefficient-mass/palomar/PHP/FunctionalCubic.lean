module

public import PHP.FunctionalCharge
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace PHP

/-- For twice as many pigeons as holes, a finite real literal-cube
refutation with functionality has total absolute coefficient mass at most
`16 n³`. All Boolean boards are covered, including those with collisions
or pigeons appearing in several columns. -/
theorem functional_cubic (n : ℕ) (hn : 1 ≤ n) :
    ∃ (t : ℕ) (r : Refutation (@Functional (2*n) n) t),
      r.mass ≤ 16*(n : ℝ)^3 := by
  let C := charge (2*n) n
  let D := emptyInverse (2*n) n
  let K := C.prod D
  have hlegal : K.legal Functional :=
    Combination.legal_prod (fun h h' => functional_mono h h') (charge_legal _ _) _
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hid (x : Board (2*n) n) : K.value x = 1 := by
    have hpos : 0 < (n : ℝ) + ((vacancies x).card : ℝ) := by positivity
    unfold K C D
    rw [Combination.value_prod,charge_value,emptyInverse_value hn, Nat.cast_mul]
    have hz : (↑(2 : ℕ) : ℝ) * (n : ℝ) - (n : ℝ) + ((vacancies x).card : ℝ) =
        (n : ℝ) + ((vacancies x).card : ℝ) := by norm_num; ring
    rw [hz, mul_inv_cancel₀ hpos.ne']
  obtain ⟨t,r,h⟩ := Combination.refutation_of_value_one K hlegal hid
  have hC : C.cost ≤ 8*(n : ℝ)^3 := by
    have h₀ : (n : ℝ) ≤ (n : ℝ)^3 := by
      have hh : (1 : ℝ) ≤ (n : ℝ)^2 := one_le_pow₀ hnR
      nlinarith [mul_le_mul_of_nonneg_right hh (show 0 ≤ (n : ℝ) by positivity)]
    calc
      _ ≤ ((2*n : ℕ) : ℝ) + (n : ℝ)*((2*n : ℕ) : ℝ)*((2*n : ℕ) : ℝ) +
          ((2*n : ℕ) : ℝ)*n*n := charge_cost _ _
      _ ≤ _ := by push_cast; nlinarith
  have hD : D.cost ≤ 2 := emptyInverse_cost hn
  have hC0 : 0 ≤ C.cost := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hD0 : 0 ≤ D.cost := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨t,r,?_⟩
  rw [h]
  calc
    _ ≤ C.cost * D.cost := Combination.cost_prod_le C D
    _ ≤ (8*(n : ℝ)^3)*2 := mul_le_mul hC hD hD0 (by positivity)
    _ = _ := by ring

end PHP
