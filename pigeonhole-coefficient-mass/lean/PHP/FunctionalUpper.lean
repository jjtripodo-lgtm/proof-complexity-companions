import PHP.FunctionalCharge
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic

namespace PHP
open scoped BigOperators

noncomputable def emptyInverseFor (m n d : ℕ) : Combination m n (Finset (Fin n)) :=
  ⟨emptyColumns, fun J => ∫ u : ℝ in 0..1, u^(d-1) * (u-1)^J.card⟩

theorem emptyInverseFor_value {m n d : ℕ} (hd : 1 ≤ d) (x : Board m n) :
    (emptyInverseFor m n d).value x = ((d : ℝ) + ((vacancies x).card : ℝ))⁻¹ := by
  classical
  let f (J : Finset (Fin n)) (u : ℝ) :=
    (u^(d-1) * (u-1)^J.card) * eval (emptyColumns J) x
  have hf (J : Finset (Fin n)) : Continuous (f J) := by unfold f; fun_prop
  have hsum (u : ℝ) :
      (∑ J : Finset (Fin n), f J u) = u ^ (d-1+(vacancies x).card) := by
    unfold f
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, pow_add]
    congr 1
    rw [← all_vacancy_product x u]
    rw [show (∏ j : Fin n, (1 + (u-1)*vacancyBit x j)) =
        ∏ j : Fin n, ((u-1)*vacancyBit x j + 1) by simp only [add_comm]]
    rw [Fintype.prod_add]
    apply Finset.sum_congr rfl
    intro J _
    simp [eval_emptyColumns, Finset.prod_mul_distrib]
  calc
    _ = ∑ J : Finset (Fin n), ∫ u : ℝ in 0..1, f J u := by
      unfold Combination.value
      apply Finset.sum_congr rfl
      intro J _
      simp [emptyInverseFor, f, intervalIntegral.integral_mul_const]
    _ = ∫ u : ℝ in 0..1, ∑ J : Finset (Fin n), f J u :=
      (intervalIntegral.integral_finset_sum (fun J _ => (hf J).intervalIntegrable _ _)).symm
    _ = ∫ u : ℝ in 0..1, u ^ (d-1+(vacancies x).card) := by simp_rw [hsum]
    _ = _ := by
      rw [integral_unit_powNat]
      have hnat : d - 1 + (vacancies x).card + 1 = d + (vacancies x).card := by omega
      have hnat' : ((d - 1 + (vacancies x).card : ℕ) : ℝ) + 1 =
          (d : ℝ) + (vacancies x).card := by exact_mod_cast hnat
      rw [hnat']

theorem emptyInverseFor_cost {m n d : ℕ} :
    (emptyInverseFor m n d).cost = functionalIntegral d n := by
  classical
  let f (J : Finset (Fin n)) (u : ℝ) := u^(d-1) * (1-u)^J.card
  have hf (J : Finset (Fin n)) : Continuous (f J) := by unfold f; fun_prop
  have he (J : Finset (Fin n)) :
      |(emptyInverseFor m n d).coeff J| = ∫ u : ℝ in 0..1, f J u := by
    have hp : 0 ≤ ∫ u : ℝ in 0..1, f J u :=
      intervalIntegral.integral_nonneg (by norm_num) (fun u hu => by
        have h' : 0 ≤ 1-u := sub_nonneg.mpr hu.2
        exact mul_nonneg (pow_nonneg hu.1 _) (pow_nonneg h' _))
    have hf' (u : ℝ) : u^(d-1) * (u-1)^J.card = (-1 : ℝ)^J.card * f J u := by
      unfold f
      rw [show u-1 = (-1)*(1-u) by ring, mul_pow]
      ring
    change |∫ u : ℝ in 0..1, u^(d-1) * (u-1)^J.card| = _
    simp_rw [hf']
    rw [intervalIntegral.integral_const_mul, abs_mul, abs_of_nonneg hp, abs_pow]
    simp
  have hsum (u : ℝ) :
      (∑ J : Finset (Fin n), f J u) = u^(d-1) * (2-u)^n := by
    unfold f
    rw [← Finset.mul_sum]
    congr 1
    have h := Fintype.prod_add (fun _ : Fin n => 1-u) (fun _ => (1 : ℝ))
    simpa [show 1-u+1 = 2-u by ring] using h.symm
  calc
    _ = ∑ J : Finset (Fin n), ∫ u : ℝ in 0..1, f J u := by
      unfold Combination.cost
      simp_rw [he]
    _ = ∫ u : ℝ in 0..1, ∑ J : Finset (Fin n), f J u :=
      (intervalIntegral.integral_finset_sum (fun J _ => (hf J).intervalIntegrable _ _)).symm
    _ = functionalIntegral d n := by simp_rw [hsum]; rfl


private theorem ordered_pair_cost (r : ℕ) :
    (∑ b : Fin r, ∑ a : Fin r, if a < b then (1:ℝ) else 0) = (r:ℝ)*(r-1)/2 := by
  classical
  have h (b : Fin r) : (∑ a : Fin r, if a < b then (1:ℝ) else 0) = (b.val:ℝ) := by
    rw [Finset.sum_boole]
    have h' : (Finset.univ.filter (· < b)) = Finset.Iio b := by ext a; simp
    rw [h',Fin.card_Iio]
  simp_rw [h]
  clear h
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Fin.sum_univ_castSucc]
    change (∑ i : Fin r, (i.val:ℝ)) + (r:ℝ) = _
    push_cast
    rw [ih]
    ring

theorem charge_cost_exact (m n : ℕ) :
    (charge m n).cost =
      (m:ℝ)+(n:ℝ)*((m:ℝ)*(m-1)/2)+(m:ℝ)*((n:ℝ)*(n-1)/2) := by
  classical
  have h1 {r : ℕ} (a b : Fin r) :
      |if a < b then (-1:ℝ) else 0| = if a < b then (1:ℝ) else 0 := by
    by_cases h : a < b <;> simp [h]
  have h2 {r : ℕ} (a b : Fin r) :
      |if a < b then (1:ℝ) else 0| = if a < b then (1:ℝ) else 0 := by
    by_cases h : a < b <;> simp [h]
  unfold Combination.cost
  simp only [ChargeIndex,Fintype.sum_sum_type,Fintype.sum_prod_type,charge,abs_one,h1,h2]
  have h (r : ℕ) : (∑ a : Fin r, ∑ b : Fin r, if a < b then (1:ℝ) else 0) = (r:ℝ)*(r-1)/2 := by
    rw [Finset.sum_comm,ordered_pair_cost]
  simp only [h,Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Fintype.card_fin,mul_one]
  ring

/-- The all-surplus paper upper: a finite certificate on the entire original
Boolean board, using only plain sources and within-row pairs. -/
theorem functional_general_upper {m n : ℕ} (hm : n < m) :
    ∃ (s : ℕ) (r : Refutation (@Functional m n) s),
      r.mass ≤ ((m:ℝ)+(n:ℝ)*((m:ℝ)*(m-1)/2)+(m:ℝ)*((n:ℝ)*(n-1)/2)) *
        functionalIntegral (m-n) n := by
  let C := charge m n
  let D := emptyInverseFor m n (m-n)
  have hd : 1 ≤ m-n := by omega
  have hdn : 1 ≤ ((m-n : ℕ):ℝ) := by exact_mod_cast hd
  have hl := Combination.legal_prod (fun h h' => functional_mono h h') (charge_legal m n) D
  have hv (x : Board m n) : (C.prod D).value x = 1 := by
    unfold C D
    rw [Combination.value_prod,charge_value,emptyInverseFor_value hd,Nat.cast_sub hm.le]
    have hgap : (n:ℝ) < m := by exact_mod_cast hm
    exact mul_inv_cancel₀ (by linarith [Nat.cast_nonneg (α:=ℝ) (vacancies x).card])
  obtain ⟨s,r,hr⟩ := Combination.refutation_of_value_one _ hl hv
  refine ⟨s,r,?_⟩
  rw [hr]
  exact (Combination.cost_prod_le C D).trans_eq (by unfold C D; rw [charge_cost_exact,emptyInverseFor_cost])

end PHP
