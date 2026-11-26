module

public import PHP.Combination
public import PHP.FunctionalEstimate
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace PHP

open scoped BigOperators

def vacant {m n : ℕ} (x : Board m n) (j : Fin n) : Prop :=
  ∀ i, x (i,j) = false

noncomputable def vacancies {m n : ℕ} (x : Board m n) : Finset (Fin n) := by
  classical exact Finset.univ.filter (vacant x)

def emptyColumns {m n : ℕ} (J : Finset (Fin n)) : Cube m n :=
  fun ij => if ij.2 ∈ J then some false else none

theorem holds_emptyColumns {m n : ℕ} (J : Finset (Fin n)) (x : Board m n) :
    Holds (emptyColumns J) x ↔ J ⊆ vacancies x := by
  classical
  constructor
  · intro h j hj
    simp only [vacancies, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i
    exact h (i,j) false (by simp [emptyColumns,hj])
  · intro h ij b hb
    by_cases hj : ij.2 ∈ J
    · have hh : vacant x ij.2 := (Finset.mem_filter.mp (h hj)).2
      have hf : b = false := by simpa [emptyColumns,hj,eq_comm] using hb
      exact (hh ij.1).trans hf.symm
    · simp [emptyColumns,hj] at hb

noncomputable def vacancyBit {m n : ℕ} (x : Board m n) (j : Fin n) : ℝ := by
  classical exact if j ∈ vacancies x then 1 else 0

theorem eval_emptyColumns {m n : ℕ} (J : Finset (Fin n)) (x : Board m n) :
    eval (emptyColumns J) x = ∏ j ∈ J, vacancyBit x j := by
  classical
  by_cases h : J ⊆ vacancies x
  · have hh := (holds_emptyColumns J x).mpr h
    unfold eval
    rw [if_pos hh]
    symm
    apply Finset.prod_eq_one
    intro j hj
    simp [vacancyBit,h hj]
  · have h' : ∃ j ∈ J, j ∉ vacancies x := by
      by_contra hn
      apply h
      intro j hj
      by_contra hu
      exact hn ⟨j,hj,hu⟩
    obtain ⟨j,hj,hn⟩ := h'
    have hz : vacancyBit x j = 0 := by simp [vacancyBit,hn]
    rw [show eval (emptyColumns J) x = 0 by
      simp [eval,holds_emptyColumns,h]]
    exact (Finset.prod_eq_zero hj hz).symm

theorem all_vacancy_product {m n : ℕ} (x : Board m n) (u : ℝ) :
    (∏ j : Fin n, (1 + (u-1)*vacancyBit x j)) = u ^ (vacancies x).card := by
  classical
  have he (j : Fin n) : 1 + (u-1)*vacancyBit x j =
      if j ∈ vacancies x then u else 1 := by
    by_cases h : j ∈ vacancies x <;> simp [vacancyBit,h]
  simp_rw [he, Finset.prod_ite]
  have hf : Finset.univ.filter (fun j => j ∈ vacancies x) = vacancies x := by
    ext j
    simp
  simp [hf]

noncomputable def emptyInverse (m n : ℕ) : Combination m n (Finset (Fin n)) :=
  ⟨emptyColumns, fun J => ∫ u : ℝ in 0..1, u^(n-1) * (u-1)^J.card⟩

theorem integral_unit_powNat (k : ℕ) :
    (∫ u : ℝ in 0..1, u^k) = ((k : ℝ) + 1)⁻¹ := by
  have hn : ((k : ℝ) + 1) ≠ 0 := (show 0 < (k : ℝ) + 1 by positivity).ne'
  have hf (x : ℝ) : HasDerivAt (fun u : ℝ => u ^ (k+1) / ((k : ℝ) + 1)) (x^k) x := by
    have h := (hasDerivAt_pow (k+1) x).div_const ((k : ℝ) + 1)
    convert h using 1
    push_cast
    field_simp
  have hc : Continuous (fun u : ℝ => u^k) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hf u)
    (hc.intervalIntegrable 0 1)]
  simp [pow_succ, one_div]

theorem emptyInverse_value {m n : ℕ} (hn : 1 ≤ n) (x : Board m n) :
    (emptyInverse m n).value x = ((n : ℝ) + ((vacancies x).card : ℝ))⁻¹ := by
  classical
  let f (J : Finset (Fin n)) (u : ℝ) :=
    (u^(n-1) * (u-1)^J.card) * eval (emptyColumns J) x
  have hf (J : Finset (Fin n)) : Continuous (f J) := by unfold f; fun_prop
  have hsum (u : ℝ) :
      (∑ J : Finset (Fin n), f J u) = u ^ (n-1+(vacancies x).card) := by
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
      simp [emptyInverse, f, intervalIntegral.integral_mul_const]
    _ = ∫ u : ℝ in 0..1, ∑ J : Finset (Fin n), f J u :=
      (intervalIntegral.integral_finset_sum (fun J _ => (hf J).intervalIntegrable _ _)).symm
    _ = ∫ u : ℝ in 0..1, u ^ (n-1+(vacancies x).card) := by simp_rw [hsum]
    _ = _ := by
      rw [integral_unit_powNat]
      have hnat : n - 1 + (vacancies x).card + 1 = n + (vacancies x).card := by omega
      have hnat' : ((n - 1 + (vacancies x).card : ℕ) : ℝ) + 1 =
          (n : ℝ) + (vacancies x).card := by exact_mod_cast hnat
      rw [hnat']

theorem emptyInverse_cost {m n : ℕ} (hn : 1 ≤ n) :
    (emptyInverse m n).cost ≤ 2 := by
  classical
  let f (J : Finset (Fin n)) (u : ℝ) := u^(n-1) * (1-u)^J.card
  have hf (J : Finset (Fin n)) : Continuous (f J) := by unfold f; fun_prop
  have he (J : Finset (Fin n)) :
      |(emptyInverse m n).coeff J| = ∫ u : ℝ in 0..1, f J u := by
    have hp : 0 ≤ ∫ u : ℝ in 0..1, f J u :=
      intervalIntegral.integral_nonneg (by norm_num) (fun u hu => by
        have h' : 0 ≤ 1-u := sub_nonneg.mpr hu.2
        exact mul_nonneg (pow_nonneg hu.1 _) (pow_nonneg h' _))
    have hf' (u : ℝ) : u^(n-1) * (u-1)^J.card = (-1 : ℝ)^J.card * f J u := by
      unfold f
      rw [show u-1 = (-1)*(1-u) by ring, mul_pow]
      ring
    change |∫ u : ℝ in 0..1, u^(n-1) * (u-1)^J.card| = _
    simp_rw [hf']
    rw [intervalIntegral.integral_const_mul, abs_mul, abs_of_nonneg hp, abs_pow]
    simp
  have hsum (u : ℝ) :
      (∑ J : Finset (Fin n), f J u) = u^(n-1) * (2-u)^n := by
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
    _ = functionalIntegral n n := by simp_rw [hsum]; rfl
    _ ≤ _ := functionalIntegral_diagonal n hn

end PHP
