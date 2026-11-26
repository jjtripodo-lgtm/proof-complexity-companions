import PHP.CoupledLabels
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.BigOperators.Field

namespace PHP
open Finset Polynomial
open scoped BigOperators

noncomputable def averageMaskAt {m n L : ℕ} (labels : Fin m → CoupledLabel L)
    (H : Finset (Fin n)) (z : ℕ) (x : Board m n) : ℝ :=
  (∑ J ∈ (univ : Finset (Fin L)).powersetCard z,
    bit (Inactive (coupledMask labels J) H x)) / (L.choose z:ℝ)

private theorem choose_disjoint {L z h : ℕ} (hz : z ≤ L) (hh : h ≤ L) :
    (L-h).choose z * L.choose h = (L-z).choose h * L.choose z := by
  by_cases hf : z+h ≤ L
  · have h1 := Nat.choose_mul (n:=L) (k:=z+h) (s:=h) hf (by omega)
    have h2 := Nat.choose_mul (n:=L) (k:=z+h) (s:=z) hf (by omega)
    have hsym := Nat.choose_symm (n:=z+h) (k:=z) (by omega)
    rw [show z+h-z=h by omega] at hsym h2
    rw [show z+h-h=z by omega, hsym] at h1
    exact (Nat.mul_comm _ _).trans (h1.symm.trans (h2.trans (Nat.mul_comm _ _)))
  · have h1 := Nat.choose_eq_zero_of_lt (n:=L-h) (k:=z) (by omega)
    have h2 := Nat.choose_eq_zero_of_lt (n:=L-z) (k:=h) (by omega)
    simp [h1,h2]

noncomputable def fallingPoly (h : ℕ) : ℝ[X] :=
  ∏ i ∈ range h, (X-C (i:ℝ))

private theorem fallingPoly_degree (h : ℕ) : (fallingPoly h).natDegree ≤ h := by
  unfold fallingPoly
  induction h with
  | zero => simp
  | succ h ih =>
    rw [Finset.prod_range_succ]
    exact natDegree_mul_le.trans (Nat.add_le_add ih ((natDegree_sub_le _ _).trans (by simp)))

private theorem fallingPoly_nat (x h : ℕ) :
    (fallingPoly h).eval (x:ℝ) = (x.descFactorial h:ℝ) := by
  rw [fallingPoly,Polynomial.eval_prod]
  simp only [Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
  by_cases hle : h ≤ x
  · have hprod : (∏ i ∈ range h, ((x:ℝ)-i)) = ∏ i ∈ range h, ((x-i:ℕ):ℝ) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact (Nat.cast_sub (by have ht := Finset.mem_range.mp hi; omega)).symm
    rw [hprod,←Nat.cast_prod]
    exact_mod_cast (Nat.descFactorial_eq_prod_range x h).symm
  · have hi : x ∈ range h := Finset.mem_range.mpr (by omega)
    rw [Finset.prod_eq_zero hi (sub_self (x:ℝ)),Nat.descFactorial_eq_zero_iff_lt.mpr (by omega),Nat.cast_zero]

noncomputable def avoidPoly (L h : ℕ) : ℝ[X] :=
  C ((L.descFactorial h:ℝ)⁻¹) * (fallingPoly h).comp (C (L:ℝ)-X)

theorem avoidPoly_degree (L h : ℕ) : (avoidPoly L h).natDegree ≤ h := by
  unfold avoidPoly
  apply (natDegree_C_mul_le _ _).trans
  apply natDegree_comp_le.trans
  have hL : (C (L:ℝ)-X).natDegree ≤ 1 := (natDegree_sub_le _ _).trans (by simp)
  exact (Nat.mul_le_mul (fallingPoly_degree h) hL).trans_eq (Nat.mul_one _)

theorem avoidPoly_eval {L h z : ℕ} (hz : z ≤ L) (hh : h ≤ L) :
    (avoidPoly L h).eval (z:ℝ) = ((L-h).choose z:ℝ)/(L.choose z:ℝ) := by
  rw [avoidPoly,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_comp,Polynomial.eval_sub,
    Polynomial.eval_C,Polynomial.eval_X,←Nat.cast_sub hz,fallingPoly_nat]
  rw [Nat.descFactorial_eq_factorial_mul_choose,Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  have hfac : 0 < (h.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos h
  have hp : 0 < (L.choose h:ℝ) := by exact_mod_cast Nat.choose_pos hh
  have hq : 0 < (L.choose z:ℝ) := by exact_mod_cast Nat.choose_pos hz
  have he : ((L-h).choose z:ℝ)*(L.choose h:ℝ) = ((L-z).choose h:ℝ)*(L.choose z:ℝ) := by
    exact_mod_cast choose_disjoint hz hh
  field_simp
  rw [←he,mul_comm]

private theorem avoid_subsets_card {L : ℕ} (A : Finset (Fin L)) (z : ℕ) :
    ((univ : Finset (Fin L)).powersetCard z |>.filter (fun J => J ⊆ A)).card =
      A.card.choose z := by
  classical
  have h : ((univ : Finset (Fin L)).powersetCard z |>.filter (fun J => J ⊆ A)) =
      A.powersetCard z := by
    ext J
    simp [Finset.mem_powersetCard,and_comm]
  rw [h,Finset.card_powersetCard]

/-- After conditioning on row labels, the uniform z-bin mask is a
polynomial in z whenever no more than b bins are active. -/
theorem conditioned_mask_formula {m n L : ℕ} (labels : Fin m → CoupledLabel L)
    (H : Finset (Fin n)) (x : Board m n) {z : ℕ} (hz : z ≤ L) :
    averageMaskAt labels H z x =
      bit (Inactive (prefixRows labels) H x) *
      (avoidPoly L (liveGroups (binRows labels) H univ x).card).eval (z:ℝ) := by
  classical
  let S := liveGroups (binRows labels) H (univ : Finset (Fin L)) x
  have hS : S.card ≤ L := by simpa using S.card_le_univ
  have hSum : (∑ J ∈ (univ : Finset (Fin L)).powersetCard z,
    bit (Inactive (coupledMask labels J) H x)) =
      bit (Inactive (prefixRows labels) H x)*((L-S.card).choose z:ℝ) := by
    simp_rw [coupledMask_inactive,bit_and,←Finset.mul_sum]
    congr 1
    have hs (J : Finset (Fin L)) : (∀ j ∈ J, Inactive (binRows labels j) H x) ↔ J ⊆ Sᶜ := by
      simp [S,liveGroups,Finset.subset_iff]
    simp_rw [hs]
    have he : (∑ J ∈ (univ : Finset (Fin L)).powersetCard z, bit (J ⊆ Sᶜ)) =
        (∑ J ∈ (univ : Finset (Fin L)).powersetCard z, if J ⊆ Sᶜ then (1:ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro J _
      by_cases hj : J ⊆ Sᶜ <;> simp [bit,hj]
    rw [he,Finset.sum_boole,avoid_subsets_card,S.card_compl,Fintype.card_fin]
  unfold averageMaskAt
  rw [hSum]
  change _ = bit (Inactive (prefixRows labels) H x)*(avoidPoly L S.card).eval (z:ℝ)
  rw [avoidPoly_eval hz hS]
  ring

/-- Average first over labels or first over z bins: both give the
original Bernoulli no-hit function at the grid node. -/
theorem average_mask_fubini {m n L : ℕ} (hL : 0 < L) (a s : ℝ)
    (H : Finset (Fin n)) (x : Board m n) {z : ℕ} (hz : z ≤ L) :
    (∑ labels : Fin m → CoupledLabel L,
      iidWeight (coupledWeight L a s) labels*averageMaskAt labels H z x) =
        (1-(a+s/L*(z:ℝ)))^(activeRows H x).card := by
  classical
  let U : Finset (Fin L) := univ
  unfold averageMaskAt
  simp_rw [←mul_div_assoc,←Finset.sum_div]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [expected_coupled_mask hL]
  have hh (J : Finset (Fin L)) (hJ : J ∈ U.powersetCard z) : J.card = z :=
    (Finset.mem_powersetCard.mp hJ).2
  rw [Finset.sum_congr rfl (fun J hJ => by rw [hh J hJ]),Finset.sum_const,
    nsmul_eq_mul,Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast (Nat.choose_pos hz).ne')

end PHP
