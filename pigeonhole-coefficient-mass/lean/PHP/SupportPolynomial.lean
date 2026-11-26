import PHP.GenericBlockMoment
import PHP.GroupSampling
import Mathlib.Algebra.Polynomial.Derivative

namespace PHP
open scoped BigOperators
open Finset Polynomial

noncomputable def supportPoly {s R : ℕ} (B : CalibratedBlock s R) : ℝ[X] :=
  ∑ w : TileWord s R, C (B.weight w)*X^(tileSupport w)

theorem supportPoly_natDegree {s R : ℕ} (B : CalibratedBlock s R) : (supportPoly B).natDegree ≤ s := by
  unfold supportPoly
  apply natDegree_sum_le_of_forall_le
  intro w _
  exact (natDegree_C_mul_X_pow_le _ _).trans (tileSupport_le w)

theorem supportPoly_eval {s R : ℕ} (B : CalibratedBlock s R) (x : ℝ) :
    (supportPoly B).eval x = ∑ w : TileWord s R, B.weight w*x^(tileSupport w) := by
  simp [supportPoly,Polynomial.eval_finset_sum,Polynomial.eval_mul,Polynomial.eval_pow]

@[simp] theorem supportPoly_one {s R : ℕ} (B : CalibratedBlock s R) :
    (supportPoly B).eval 1 = 1 := by simp [supportPoly_eval,B.total]

theorem supportPoly_deriv {s R : ℕ} (B : CalibratedBlock s R) :
    (supportPoly B).derivative.eval 1 = B.expectedSupport := by
  unfold supportPoly CalibratedBlock.expectedSupport
  rw [Polynomial.derivative_sum,Polynomial.eval_finset_sum]
  apply Finset.sum_congr rfl
  intro w _
  simp only [Polynomial.derivative_C_mul,Polynomial.derivative_X_pow,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_C,Polynomial.eval_X,one_pow,mul_one]

theorem supportPoly_reciprocal {s R : ℕ} (B : CalibratedBlock s R) {x : ℝ} (hx : x ≠ 0) :
    B.polynomial x = x^s*(supportPoly B).eval x⁻¹ := by
  rw [supportPoly_eval,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  have hs := tileSupport_le w
  rw [inv_pow, show x^s = x^(s-tileSupport w)*x^(tileSupport w) by rw [←pow_add,Nat.sub_add_cancel hs]]
  rw [show x^(s-tileSupport w)*x^(tileSupport w)*(B.weight w*(x^tileSupport w)⁻¹) =
      B.weight w*x^(s-tileSupport w)*(x^(tileSupport w)*(x^tileSupport w)⁻¹) by ring,
    mul_inv_cancel₀ (pow_ne_zero _ hx),mul_one]

private theorem prob_contains {ι : Type*} [DecidableEq ι] {U S : Finset ι} (hS : S ⊆ U) (p : ℝ) :
    (∑ J ∈ U.powerset, bernoulliWeight U J p * bit (S ⊆ J)) = p^S.card := by
  classical
  let f : ι → ℝ := fun i => if i ∈ S then 0 else (1-p)
  calc
    _ = ∑ J ∈ U.powerset, (∏ _i ∈ J, p) * ∏ i ∈ U\J, f i := by
      apply Finset.sum_congr rfl
      intro J hJ
      by_cases h : S ⊆ J
      · rw [show bit (S ⊆ J) = 1 by simp [bit,h],mul_one]
        unfold bernoulliWeight
        rw [Finset.prod_const]
        congr 1
        rw [←Finset.prod_const]
        apply Finset.prod_congr rfl
        intro i hi
        have h' : i ∉ S := fun hh => (Finset.mem_sdiff.mp hi).2 (h hh)
        simp [f,h']
      · have h' := Finset.not_subset.mp h
        obtain ⟨i,hi,hin⟩ := h'
        have hi' : i ∈ U\J := Finset.mem_sdiff.mpr ⟨hS hi,hin⟩
        rw [Finset.prod_eq_zero hi' (show f i = 0 from if_pos hi)]
        simp [bit,h]
    _ = ∏ i ∈ U, (p+f i) := (Finset.prod_add _ _ _).symm
    _ = _ := by
      rw [←Finset.prod_sdiff hS]
      have h1 : (∏ i ∈ U\S, (p+f i)) = 1 := by
        apply Finset.prod_eq_one
        intro i hi
        simp [f,(Finset.mem_sdiff.mp hi).2]
      have h2 : (∏ i ∈ S, (p+f i)) = p^S.card := by
        rw [←Finset.prod_const]
        apply Finset.prod_congr rfl
        intro i hi
        simp [f,hi]
      rw [h1,h2,one_mul]

private theorem tile_subset_iff {s R : ℕ} (w : TileWord s R) (J : Finset (Fin R)) :
    tileUsed w ⊆ J ↔ ∀ j, (w j).elim True (·∈J) := by
  constructor
  · intro h j
    cases hw : w j with
    | none => trivial
    | some i => exact h ((mem_tileUsed w i).mpr ⟨j,hw⟩)
  · intro h i hi
    obtain ⟨j,hj⟩ := (mem_tileUsed w i).mp hi
    simpa [hj] using h j

theorem supportPoly_abs_le_one {s R : ℕ} (B : CalibratedBlock s R)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) : |(supportPoly B).eval p| ≤ 1 := by
  classical
  let U : Finset (Fin R) := univ
  rw [supportPoly_eval]
  simp_rw [← show ∀ w : TileWord s R, (tileUsed w).card = tileSupport w from fun _ => rfl]
  simp_rw [←prob_contains (U:=U) (Finset.subset_univ (tileUsed _)) p]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have htest (J : Finset (Fin R)) :
      |∑ w : TileWord s R, B.weight w*bit (tileUsed w ⊆ J)| ≤ 1 := by
    have h := B.box_bound (fun _ x => x.elim True (·∈J)) (fun _ => Or.inr (Or.inr trivial))
    simp_rw [←tile_subset_iff] at h
    convert h using 2
    apply Finset.sum_congr rfl
    intro w _
    by_cases h' : tileUsed w ⊆ J <;> simp [bit,h']
  calc
    _ = ∑ J ∈ U.powerset, bernoulliWeight U J p * |∑ w : TileWord s R, B.weight w*bit (tileUsed w ⊆ J)| := by
      apply Finset.sum_congr rfl
      intro J hJ
      simp_rw [show ∀ w : TileWord s R,
        B.weight w*(bernoulliWeight U J p*bit (tileUsed w ⊆ J)) =
        bernoulliWeight U J p*(B.weight w*bit (tileUsed w ⊆ J)) from fun w => by ring,
        ←Finset.mul_sum,abs_mul,abs_of_nonneg (bernoulliWeight_nonneg U J hp hp')]
    _ ≤ ∑ J ∈ U.powerset, bernoulliWeight U J p := by
      apply Finset.sum_le_sum
      intro J _
      simpa using mul_le_mul_of_nonneg_left (htest J) (bernoulliWeight_nonneg U J hp hp')
    _ = 1 := bernoulli_total U p

end PHP
