import PHP.BatchInterpolation
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.ExponentialBounds

namespace PHP
open Finset Polynomial
open scoped BigOperators

def NonnegativeCoeffs (P : ℝ[X]) : Prop := ∀ i, 0 ≤ P.coeff i

theorem NonnegativeCoeffs.mul {P Q : ℝ[X]} (hP : NonnegativeCoeffs P)
    (hQ : NonnegativeCoeffs Q) : NonnegativeCoeffs (P*Q) := by
  intro i
  rw [Polynomial.coeff_mul]
  exact Finset.sum_nonneg (fun ij _ => mul_nonneg (hP ij.1) (hQ ij.2))

theorem NonnegativeCoeffs.prod {α : Type*} (s : Finset α) (P : α → ℝ[X])
    (h : ∀ i ∈ s, NonnegativeCoeffs (P i)) : NonnegativeCoeffs (∏ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro i; simp only [Finset.prod_empty,coeff_one]; split_ifs <;> norm_num
  | insert i s hi IH =>
    rw [Finset.prod_insert hi]
    exact (h i (by simp)).mul (IH fun j hj => h j (by simp [hj]))

private noncomputable def posBasis (b : ℕ) (i : Fin (b+1)) : ℝ[X] :=
  ∏ j ∈ univ.erase i, C (|(cosNode b i-cosNode b j)⁻¹|) *
    (C (1-cosNode b j)+C 2*X)

private theorem posBasis_nonneg (b : ℕ) (i : Fin (b+1)) : NonnegativeCoeffs (posBasis b i) := by
  unfold posBasis
  apply NonnegativeCoeffs.prod
  intro j _
  intro k
  rw [Polynomial.coeff_C_mul,Polynomial.coeff_add,Polynomial.coeff_C,Polynomial.coeff_C_mul,Polynomial.coeff_X]
  have h : 0 ≤ 1-cosNode b j := sub_nonneg.mpr (Real.cos_le_one _)
  split_ifs <;> positivity

private theorem posBasis_eval {b : ℕ} (i : Fin (b+1)) {y : ℝ} (hy : 0 ≤ y) :
    (posBasis b i).eval y = |extWeight b (1+2*y) i| := by
  classical
  simp only [posBasis,extWeight,Lagrange.basis,Lagrange.basisDivisor,
    Polynomial.eval_prod,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_sub,
    Polynomial.eval_C,Polynomial.eval_X,Finset.abs_prod,abs_mul]
  apply Finset.prod_congr rfl
  intro j _
  rw [abs_of_nonneg (by unfold cosNode; linarith [Real.cos_le_one ((j.val:ℝ)*Real.pi/b)] :
    0 ≤ 1+2*y - cosNode b j)]
  ring

private noncomputable def shiftedNodeValue (P : ℝ[X]) (b : ℕ) (i : Fin (b+1)) : ℝ :=
  (-1:ℝ)^i.val * P.eval ((1+cosNode b i)/2)

private theorem taylor_interp {b : ℕ} (hb : 0 < b) {P : ℝ[X]} (hP : P.natDegree ≤ b) :
    Polynomial.taylor 1 P = ∑ i : Fin (b+1), C (shiftedNodeValue P b i) * posBasis b i := by
  classical
  let Q := P.comp ((X+C 1)*C (1/2:ℝ))
  have hQ : Q.natDegree ≤ b := by
    have h : ((X + C (1:ℝ))*C (1/2:ℝ)).natDegree ≤ 1 := by
      apply le_trans natDegree_mul_le
      simp only [natDegree_C, add_zero]
      exact (natDegree_add_le _ _).trans (by simp)
    have hc : Q.natDegree ≤ P.natDegree * ((X+C (1:ℝ))*C (1/2:ℝ)).natDegree :=
      natDegree_comp_le
    exact hc.trans ((Nat.mul_le_mul_left _ h).trans (by simpa using hP))
  apply Polynomial.eq_of_infinite_eval_eq
  refine (Set.Ioi_infinite (0:ℝ)).mono ?_
  intro y hy
  have hy0 : 0 < y := hy
  have hw := interp_polynomial hb (1+2*y) Q hQ
  have hEval (x : ℝ) : Q.eval x = P.eval ((1+x)/2) := by
    simp [Q,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_add,div_eq_mul_inv,add_comm]
  have hE : (1+(1+2*y))/2 = y+1 := by ring
  rw [Set.mem_setOf_eq,Polynomial.taylor_apply,Polynomial.eval_comp]
  simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C]
  simp_rw [hEval,hE] at hw
  rw [←hw,Polynomial.eval_finset_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Polynomial.eval_mul,Polynomial.eval_C,shiftedNodeValue,
    posBasis_eval i hy0.le,weight_sign hb (show 1<1+2*y by linarith)]
  have hs : ((-1:ℝ)^i.val)^2 = 1 := by
    rw [←pow_mul,Nat.mul_comm,pow_mul]
    norm_num
  calc
    _ = (((-1:ℝ)^i.val)^2)*extWeight b (1+2*y) i * P.eval ((1+cosNode b i)/2) := by rw [hs,one_mul]
    _ = _ := by ring

private noncomputable def posSum (b : ℕ) : ℝ[X] :=
  ∑ i : Fin (b+1), posBasis b i

private theorem posSum_nonneg (b : ℕ) : NonnegativeCoeffs (posSum b) := by
  intro k
  simp only [posSum,Polynomial.finset_sum_coeff]
  exact Finset.sum_nonneg (fun i _ => posBasis_nonneg b i k)

private theorem coeff_domination {P : ℝ[X]} {b : ℕ} (hb : 0 < b) (hP : P.natDegree ≤ b)
    (hBound : ∀ x ∈ Set.Icc (0:ℝ) 1, |P.eval x| ≤ 1) (k : ℕ) :
    |(Polynomial.taylor 1 P).coeff k| ≤ (posSum b).coeff k := by
  rw [taylor_interp hb hP,posSum,Polynomial.finset_sum_coeff,Polynomial.finset_sum_coeff]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [Polynomial.coeff_C_mul,abs_mul,abs_of_nonneg (posBasis_nonneg b i k)]
  have ha : |shiftedNodeValue P b i| ≤ 1 := by
    rw [shiftedNodeValue,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]
    apply hBound
    exact ⟨by unfold cosNode; linarith [Real.neg_one_le_cos ((i.val:ℝ)*Real.pi/b)],
      by unfold cosNode; linarith [Real.cos_le_one ((i.val:ℝ)*Real.pi/b)]⟩
  simpa using mul_le_mul_of_nonneg_right ha (posBasis_nonneg b i k)

private theorem posSum_endpoint {b : ℕ} (hb : 0 < b) :
    let y₀ := (extPoint (1+(b:ℝ)⁻¹)-1)/2
    1/(8*(b:ℝ)^2) ≤ y₀ ∧ 0 < y₀ ∧ (posSum b).eval y₀ ≤ 4 := by
  dsimp only
  let a := 1+(b:ℝ)⁻¹
  let y₀ := (extPoint a-1)/2
  have hb0 : 0 < (b:ℝ) := by exact_mod_cast hb
  have hb1 : 1 ≤ (b:ℝ) := by exact_mod_cast hb
  have ha : 1 < a := by dsimp [a]; linarith [inv_pos.mpr hb0]
  have h0 : 0 < y₀ := by dsimp [y₀]; linarith [extPoint_gt ha]
  have hx : 1+2*y₀ = extPoint a := by dsimp [y₀]; ring
  have hY : y₀ = 1/(4*(b:ℝ)*((b:ℝ)+1)) := by
    unfold y₀ extPoint a
    field_simp
    <;> ring
  have hY' : 1/(8*(b:ℝ)^2) ≤ y₀ := by
    rw [hY]
    exact one_div_le_one_div_of_le (by positivity)
      (by nlinarith [mul_nonneg hb0.le (show 0 ≤ (b:ℝ)-1 by linarith)])
  refine ⟨hY',h0,?_⟩
  change (posSum b).eval y₀ ≤ 4
  simp only [posSum,Polynomial.eval_finset_sum]
  rw [show (∑ i : Fin (b+1), (posBasis b i).eval y₀) =
      ∑ i : Fin (b+1), |extWeight b (extPoint a) i| by
    apply Finset.sum_congr rfl
    intro i _
    rw [posBasis_eval i h0.le,hx]]
  apply (batch_weight_bound hb ha).trans
  calc
    a^b ≤ (Real.exp ((b:ℝ)⁻¹))^b := pow_le_pow_left₀ (by linarith) (by
      dsimp [a]; rw [add_comm]; exact Real.add_one_le_exp _) _
    _ = Real.exp 1 := by rw [←Real.exp_nat_mul,mul_inv_cancel₀ hb0.ne']
    _ ≤ _ := by linarith [Real.exp_one_lt_d9]

/-- Endpoint Taylor control using coefficientwise positivity of the
absolute Lagrange factors. This avoids a separate Markov inequality. -/
theorem extrapolate_quadratic {b : ℕ} (hb : 0 < b) {P : ℝ[X]} (hP : P.natDegree ≤ b)
    (hBound : ∀ x ∈ Set.Icc (0:ℝ) 1, |P.eval x| ≤ 1)
    {y : ℝ} (hy : 0 ≤ y) (hy' : y ≤ 1/(8*(b:ℝ)^2)) :
    |P.eval (1+y)-P.eval 1-y*P.derivative.eval 1| ≤ 256*((b:ℝ)^2*y)^2 := by
  let y₀ := (extPoint (1+(b:ℝ)⁻¹)-1)/2
  obtain ⟨hbase,hy₀,hEval⟩ := posSum_endpoint hb
  change 1/(8*(b:ℝ)^2) ≤ y₀ at hbase
  change 0 < y₀ at hy₀
  change (posSum b).eval y₀ ≤ 4 at hEval
  let Q := Polynomial.taylor 1 P
  let S := posSum b
  let d := max 2 (max Q.natDegree S.natDegree)
  have hd : 2 ≤ d := le_max_left _ _
  have hQd : Q.natDegree < d+1 := ((le_max_left _ _).trans (le_max_right 2 _)).trans_lt (Nat.lt_succ_self _)
  have hSd : S.natDegree < d+1 := ((le_max_right _ _).trans (le_max_right 2 _)).trans_lt (Nat.lt_succ_self _)
  have hE : Q.eval y = P.eval (1+y) := by
    simp [Q,Polynomial.taylor_apply,Polynomial.eval_comp,add_comm]
  have hp0 : Q.coeff 0 = P.eval 1 := by simp [Q]
  have hp1 : Q.coeff 1 = P.derivative.eval 1 := by simp [Q]
  have he : Q.eval y - Q.coeff 0 - y*Q.coeff 1 =
      ∑ i ∈ Ico 2 (d+1), Q.coeff i*y^i := by
    rw [Polynomial.eval_eq_sum_range' hQd]
    have hs : range (d+1) \ range 2 = Ico 2 (d+1) := by ext i; simp; omega
    have hz := Finset.sum_sdiff (Finset.range_mono (by omega : 2 ≤ d+1))
      (f:=fun i => Q.coeff i*y^i)
    rw [hs] at hz
    have hh : (∑ i ∈ range 2, Q.coeff i*y^i) = Q.coeff 0 + Q.coeff 1*y := by
      norm_num [Finset.sum_range_succ]
    rw [hh] at hz
    linarith
  rw [←hE,←hp0,←hp1,he]
  have hratio : 0 ≤ y/y₀ ∧ y/y₀ ≤ 1 := ⟨div_nonneg hy hy₀.le,
    (div_le_iff₀ hy₀).mpr (by simpa using hy'.trans hbase)⟩
  have hcomp (i : ℕ) (hi : i ∈ Ico 2 (d+1)) : y^i ≤ (y/y₀)^2*y₀^i := by
    have h₂ := Finset.mem_Ico.mp hi
    have h := pow_le_pow_of_le_one hratio.1 hratio.2 h₂.1
    have h' := mul_le_mul_of_nonneg_right h (pow_nonneg hy₀.le i)
    rw [div_pow,div_mul_cancel₀ _ (pow_ne_zero _ hy₀.ne')] at h'
    exact h'
  calc
    _ ≤ ∑ i ∈ Ico 2 (d+1), |Q.coeff i*y^i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Ico 2 (d+1), (y/y₀)^2*(S.coeff i*y₀^i) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul,abs_of_nonneg (pow_nonneg hy _)]
      have hc := coeff_domination hb hP hBound i
      exact (mul_le_mul hc (hcomp i hi) (pow_nonneg hy _) (posSum_nonneg b i)).trans_eq (by ring)
    _ ≤ (y/y₀)^2 * S.eval y₀ := by
      rw [←Finset.mul_sum,Polynomial.eval_eq_sum_range' hSd]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        exact Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2
      · intro j _ _
        exact mul_nonneg (posSum_nonneg b j) (pow_nonneg hy₀.le _)
    _ ≤ (y/y₀)^2*4 := mul_le_mul_of_nonneg_left hEval (sq_nonneg _)
    _ ≤ _ := by
      have hb0 : (0:ℝ) < b := by exact_mod_cast hb
      have hr : y/y₀ ≤ 8*((b:ℝ)^2*y) := by
        have h := one_div_le_one_div_of_le (show 0 < 1/(8*(b:ℝ)^2) by positivity) hbase
        have h' := mul_le_mul_of_nonneg_left h hy
        simpa [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using h'
      have hh := pow_le_pow_left₀ hratio.1 hr 2
      nlinarith

end PHP
