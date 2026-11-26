import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace PHP
open Finset Polynomial
open scoped BigOperators

noncomputable def uniformWeight (b : ℕ) (t : ℝ) (i : ℕ) : ℝ :=
  (Lagrange.basis (range (b+1)) (fun j : ℕ => (j:ℝ)) i).eval t

theorem uniform_interp (b : ℕ) (t : ℝ) (P : ℝ[X]) (hP : P.natDegree ≤ b) :
    (∑ i ∈ range (b+1), uniformWeight b t i * P.eval (i:ℝ)) = P.eval t := by
  have hInj : Set.InjOn (fun i : ℕ => (i:ℝ)) (range (b+1) : Set ℕ) := by
    intro i _ j _ h
    change (i:ℝ) = (j:ℝ) at h
    exact_mod_cast h
  have hd : P.degree < (range (b+1)).card := by
    rw [Finset.card_range]
    exact P.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hP)
  conv_rhs => rw [Lagrange.eq_interpolate hInj hd]
  simp [uniformWeight,Lagrange.interpolate_apply,Polynomial.eval_finset_sum,Polynomial.eval_mul,mul_comm]

private theorem prod_abs_distance (b i : ℕ) (hi : i ≤ b) :
    (∏ j ∈ (range (b+1)).erase i, |(i:ℝ)-j|) = (i.factorial:ℝ)*((b-i).factorial:ℝ) := by
  let S := range i
  let T := Ico (i+1) (b+1)
  have hST : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro k hk hk'
    have h1 := Finset.mem_range.mp hk
    have h2 := (Finset.mem_Ico.mp hk').1
    omega
  have hU : (range (b+1)).erase i = S ∪ T := by
    ext j
    simp [S,T,Finset.mem_Ico,Finset.mem_erase,Finset.mem_range]
    omega
  rw [hU,Finset.prod_union hST]
  have hS : (∏ j ∈ S, |(i:ℝ)-j|) = (i.factorial:ℝ) := by
    have hp : (∏ j ∈ S, |(i:ℝ)-j|) = ∏ j ∈ range i, (((i-1-j:ℕ):ℝ)+1) := by
      apply Finset.prod_congr rfl
      intro j hj
      have hi' := Finset.mem_range.mp hj
      have h : (j:ℝ) ≤ i := by exact_mod_cast hi'.le
      rw [abs_of_nonneg (sub_nonneg.mpr h)]
      have he : i-1-j+1=i-j := by omega
      rw [←Nat.cast_sub hi'.le]
      have hh := congrArg (fun k : ℕ => (k:ℝ)) he
      simpa only [Nat.cast_add,Nat.cast_one] using hh.symm
    rw [hp,Finset.prod_range_reflect (fun j => (j:ℝ)+1) i,Nat.factorial_eq_prod_range_add_one,Nat.cast_prod]
    simp
  have hT : (∏ j ∈ T, |(i:ℝ)-j|) = ((b-i).factorial:ℝ) := by
    unfold T
    rw [Finset.prod_Ico_eq_prod_range]
    have he : b+1-(i+1) = b-i := by omega
    rw [he,Nat.factorial_eq_prod_range_add_one,Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro j _
    have hh : (i:ℝ) ≤ (i+1+j:ℕ) := by exact_mod_cast (show i ≤ i+1+j by omega)
    rw [abs_of_nonpos (sub_nonpos.mpr hh)]
    push_cast
    ring
  rw [hS,hT]

private theorem weight_point_bound {b i : ℕ} {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ b) (hi : i ≤ b) :
    |uniformWeight b t i| ≤ (b:ℝ)^b/((i.factorial:ℝ)*((b-i).factorial:ℝ)) := by
  classical
  simp only [uniformWeight,Lagrange.basis,Lagrange.basisDivisor,Polynomial.eval_prod,
    Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_C,Polynomial.eval_X,Finset.abs_prod,abs_mul]
  rw [Finset.prod_mul_distrib]
  simp only [abs_inv,Finset.prod_inv_distrib]
  rw [prod_abs_distance b i hi,mul_comm _ (∏ j ∈ (range (b+1)).erase i, |t-↑j|),div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hJ (j : ℕ) (hj : j ∈ (range (b+1)).erase i) : |t-(j:ℝ)| ≤ (b:ℝ) := by
    have hj' := Finset.mem_range.mp (Finset.mem_of_mem_erase hj)
    have hjb : (j:ℝ) ≤ b := by exact_mod_cast Nat.lt_succ_iff.mp hj'
    exact abs_le.mpr ⟨by linarith,by linarith [Nat.cast_nonneg (α:=ℝ) j]⟩
  have hcard : ((range (b+1)).erase i).card = b := by
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)),Finset.card_range]
    omega
  have h := Finset.prod_le_prod (fun _ _ => abs_nonneg _) hJ
  simpa [hcard] using h

/-- Equally spaced interpolation on its own interval has exponentially
bounded ordinary coefficient mass, with an absolute base. -/
theorem uniform_weight_budget {b : ℕ} {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ b) :
    (∑ i ∈ range (b+1), |uniformWeight b t i|) ≤ (8:ℝ)^b := by
  have hFact : 0 < (b.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos b
  have he := Real.pow_div_factorial_le_exp (b:ℝ) (Nat.cast_nonneg (α:=ℝ) b) b
  have hb (i : ℕ) (hi : i ∈ range (b+1)) :
      (b:ℝ)^b/((i.factorial:ℝ)*((b-i).factorial:ℝ)) =
        ((b:ℝ)^b/(b.factorial:ℝ))*(b.choose i:ℝ) := by
    have hi' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 : 0 < (i.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos i
    have h2 : 0 < ((b-i).factorial:ℝ) := by exact_mod_cast Nat.factorial_pos (b-i)
    have hf : (b.choose i:ℝ)*(i.factorial:ℝ)*((b-i).factorial:ℝ) = (b.factorial:ℝ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi'
    field_simp
    exact hf.symm.trans (by ring)
  have hsum : (∑ i ∈ range (b+1), (b.choose i:ℝ)) = (2:ℝ)^b := by exact_mod_cast Nat.sum_range_choose b
  calc
    _ ≤ ∑ i ∈ range (b+1), (b:ℝ)^b/((i.factorial:ℝ)*((b-i).factorial:ℝ)) :=
      Finset.sum_le_sum (fun i hi => weight_point_bound h0 h1 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
    _ = ((b:ℝ)^b/(b.factorial:ℝ))*(2:ℝ)^b := by rw [Finset.sum_congr rfl hb,←Finset.mul_sum,hsum]
    _ ≤ Real.exp (b:ℝ)*(2:ℝ)^b := mul_le_mul_of_nonneg_right he (by positivity)
    _ ≤ _ := by
      rw [←mul_one (b:ℝ),Real.exp_nat_mul,←mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith [Real.exp_one_lt_d9]) _

end PHP
