import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace PHP
open scoped BigOperators
open Polynomial Finset

noncomputable def cosNode (b : ℕ) (i : Fin (b+1)) : ℝ :=
  Real.cos ((i.val:ℝ)*Real.pi/b)

theorem cosNode_anti {b : ℕ} (hb : 0 < b) : StrictAnti (cosNode b) := by
  intro i j hij
  have hp : (0:ℝ) < b := by exact_mod_cast hb
  have h (k : Fin (b+1)) : (k.val:ℝ)*Real.pi/b ∈ Set.Icc 0 Real.pi := by
    refine ⟨by positivity,?_⟩
    have hk : (k.val:ℝ) ≤ b := by exact_mod_cast Nat.le_of_lt_succ k.isLt
    exact (div_le_iff₀ hp).2 (by nlinarith [Real.pi_pos])
  unfold cosNode
  apply Real.strictAntiOn_cos (h i) (h j)
  exact (div_lt_div_iff_of_pos_right hp).2
    (mul_lt_mul_of_pos_right (by exact_mod_cast hij) Real.pi_pos)

noncomputable def extWeight (b : ℕ) (x : ℝ) (i : Fin (b+1)) : ℝ :=
  (Lagrange.basis Finset.univ (cosNode b) i).eval x

theorem interp_polynomial {b : ℕ} (hb : 0 < b) (x : ℝ) (P : ℝ[X]) (hP : P.natDegree ≤ b) :
    (∑ i : Fin (b+1), extWeight b x i * P.eval (cosNode b i)) = P.eval x := by
  classical
  have hi : Set.InjOn (cosNode b) ↑(Finset.univ : Finset (Fin (b+1))) :=
    (cosNode_anti hb).injective.injOn
  have hd : P.degree < (Finset.univ : Finset (Fin (b+1))).card := by
    simp only [Finset.card_univ,Fintype.card_fin]
    exact P.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hP)
  conv_rhs => rw [Lagrange.eq_interpolate hi hd]
  simp [Lagrange.interpolate_apply, extWeight, Polynomial.eval_finset_sum,
    Polynomial.eval_mul, mul_comm]

theorem weight_sign {b : ℕ} (hb : 0 < b) {x : ℝ} (hx : 1 < x)
    (i : Fin (b+1)) : |extWeight b x i| = (-1:ℝ)^i.val * extWeight b x i := by
  classical
  have ha := cosNode_anti hb
  let f : Fin (b+1) → ℝ := fun j => (x-cosNode b j)/(cosNode b i-cosNode b j)
  have hw : extWeight b x i = ∏ j ∈ Finset.univ.erase i, f j := by
    simp [extWeight,Lagrange.basis,Lagrange.basisDivisor,f,div_eq_mul_inv,Polynomial.eval_prod,mul_comm]
  rw [hw,Finset.abs_prod]
  have hpos (j : Fin (b+1)) : 0 < x-cosNode b j :=
    sub_pos.mpr ((Real.cos_le_one _).trans_lt hx)
  have h (j : Fin (b+1)) (hj : j ∈ Finset.univ.erase i) :
      |f j| = (if j < i then (-1:ℝ) else 1) * f j := by
    by_cases hji : j < i
    · have hf : f j ≤ 0 := (div_neg_of_pos_of_neg (hpos j) (sub_neg.mpr (ha hji))).le
      simp [hji, abs_of_nonpos hf]
    · have hij : i < j := lt_of_le_of_ne (le_of_not_gt hji) (Ne.symm (Finset.mem_erase.mp hj).1)
      have hf : 0 ≤ f j := (div_pos (hpos j) (sub_pos.mpr (ha hij))).le
      simp [hji, abs_of_nonneg hf]
  rw [Finset.prod_congr rfl h,Finset.prod_mul_distrib]
  congr 1
  have hs : (Finset.univ.erase i).filter (· < i) = Finset.Iio i := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_erase,Finset.mem_univ,true_and,and_true,Finset.mem_Iio]
    exact ⟨And.right,fun h => ⟨ne_of_lt h,h⟩⟩
  rw [← Finset.prod_filter, hs, Finset.prod_const,Fin.card_Iio]

theorem cosNode_chebyshev {b : ℕ} (hb : 0 < b) (i : Fin (b+1)) :
    (Polynomial.Chebyshev.T ℝ (b:ℤ)).eval (cosNode b i) = (-1:ℝ)^i.val := by
  unfold cosNode
  rw [Polynomial.Chebyshev.T_real_cos]
  push_cast
  have hb' : (b:ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have he : (b:ℝ) * ((i.val:ℝ)*Real.pi/b) = (i.val:ℝ)*Real.pi := by field_simp
  rw [he]
  simpa using Real.cos_add_nat_mul_pi 0 i.val

theorem degree_chebyshev (b : ℕ) : (Polynomial.Chebyshev.T ℝ (b:ℤ)).natDegree ≤ b := by
  induction b using Nat.strong_induction_on with
  | h b IH =>
    rcases b with _ | _ | b
    · simp
    · simp
    · have h1 := IH (b+1) (by omega)
      have h0 := IH b (by omega)
      push_cast at h1 h0 ⊢
      rw [show (b:ℤ)+1+1 = b+2 by ring, Polynomial.Chebyshev.T_add_two]
      apply le_trans (natDegree_sub_le _ _)
      apply max_le
      · apply le_trans natDegree_mul_le
        have h : (2*X:ℝ[X]).natDegree ≤ 1 := by
          exact (natDegree_mul_le (p:=(2:ℝ[X])) (q:=X)).trans (by simp)
        omega
      · omega

theorem weight_sum_chebyshev {b : ℕ} (hb : 0 < b) {x : ℝ} (hx : 1 < x) :
    (∑ i : Fin (b+1), |extWeight b x i|) = (Polynomial.Chebyshev.T ℝ (b:ℤ)).eval x := by
  rw [← interp_polynomial hb x _ (degree_chebyshev b)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [weight_sign hb hx,cosNode_chebyshev hb,mul_comm]

/-- Parametrization with growth base a. The smallest Bernoulli node is
((a-1)/(a+1))², while the total signed mass is bounded by a^b. -/
noncomputable def extPoint (a : ℝ) : ℝ := (a+a⁻¹)/2
noncomputable def batchNode (b : ℕ) (a : ℝ) (i : Fin (b+1)) : ℝ :=
  1 - (1+cosNode b i)/(1+extPoint a)

theorem extPoint_gt {a : ℝ} (ha : 1 < a) : 1 < extPoint a := by
  unfold extPoint
  have hp : 0 < a := by linarith
  have hs : 0 < (a-1)^2 := sq_pos_of_ne_zero (by linarith)
  rw [lt_div_iff₀ (by norm_num : (0:ℝ)<2)]
  rw [one_mul]
  have hh : 0 < (a-1)^2 / a := div_pos hs hp
  have he : (a-1)^2/a = a+a⁻¹-2 := by field_simp; ring
  linarith

theorem batchNode_bounds {b : ℕ} {a : ℝ} (ha : 1 < a) (i : Fin (b+1)) :
    ((a-1)/(a+1))^2 ≤ batchNode b a i ∧ batchNode b a i ≤ 1 := by
  have hx := extPoint_gt ha
  have hp : 0 < 1+extPoint a := by linarith
  have he : ((a-1)/(a+1))^2 = 1-2/(1+extPoint a) := by
    unfold extPoint
    have hp : 0 < a := by linarith
    have hq : 0 < a+1 := by linarith
    field_simp
    <;> ring
  constructor
  · rw [he,batchNode]
    have hh : (1+cosNode b i)/(1+extPoint a) ≤ 2/(1+extPoint a) :=
      div_le_div_of_nonneg_right (by unfold cosNode; linarith [Real.cos_le_one ((i.val:ℝ)*Real.pi/b)]) hp.le
    linarith
  · unfold batchNode
    have hh : 0 ≤ 1+cosNode b i := by unfold cosNode; linarith [Real.neg_one_le_cos ((i.val:ℝ)*Real.pi/b)]
    linarith [div_nonneg hh hp.le]

theorem batch_interp_exact {b s : ℕ} (hb : 0 < b) (hs : s ≤ b)
    {a : ℝ} (ha : 1 < a) :
    (∑ i : Fin (b+1), extWeight b (extPoint a) i*(1-batchNode b a i)^s) = 1 := by
  let P : ℝ[X] := ((1+X)*C ((1+extPoint a)⁻¹))^s
  have hP : P.natDegree ≤ b := by
    apply le_trans (natDegree_pow_le (p:=((1+X)*C ((1+extPoint a)⁻¹):ℝ[X])) (n:=s))
    have hd : ((1+X)*C ((1+extPoint a)⁻¹)).natDegree ≤ 1 := by
      apply le_trans natDegree_mul_le
      simp only [natDegree_C,add_zero]
      exact (natDegree_add_le _ _).trans (by simp)
    simpa using (Nat.mul_le_mul_left s hd).trans (by simpa using hs)
  have hf := interp_polynomial hb (extPoint a) P hP
  have hx : 1+extPoint a ≠ 0 := by linarith [extPoint_gt ha]
  have hfx : P.eval (extPoint a) = 1 := by
    simp [P,hx]
  rw [hfx] at hf
  convert hf using 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simp [P,batchNode,div_eq_mul_inv]

theorem batch_weight_bound {b : ℕ} (hb : 0 < b) {a : ℝ} (ha : 1 < a) :
    (∑ i : Fin (b+1), |extWeight b (extPoint a) i|) ≤ a^b := by
  have hp : 0 < a := by linarith
  have hcos : Real.cosh (Real.log a) = extPoint a := by
    rw [Real.cosh_eq, Real.exp_neg, Real.exp_log hp]
    rfl
  have hcos' : Real.cosh ((b:ℝ)*Real.log a) ≤ a^b := by
    rw [Real.cosh_eq, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hp]
    have hle : (1:ℝ) ≤ a^b := one_le_pow₀ ha.le
    have hi : (a^b)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hle
    linarith
  rw [weight_sum_chebyshev hb (extPoint_gt ha), ← hcos, Polynomial.Chebyshev.T_real_cosh]
  simpa using hcos'

end PHP
