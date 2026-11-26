import PHP.PhaseLetters
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators

namespace PHP.Phase

open scoped BigOperators

variable {R : ℕ}

noncomputable def opProduct : (s : ℕ) → (Fin s → Op R) → Op R
  | 0, _ => 1
  | s+1, A => A 0 * opProduct s (fun i => A i.succ)

theorem opProduct_zero_of {s : ℕ} (A : Fin s → Op R) (i : Fin s) (h : A i = 0) :
    opProduct s A = 0 := by
  induction s with
  | zero => exact i.elim0
  | succ s ih =>
    refine Fin.cases ?_ (fun i' => ?_) i h
    · intro h
      simp [opProduct,h]
    · intro h
      rw [opProduct, ih (fun j => A j.succ) i' h, mul_zero]

theorem product_contraction {s : ℕ} (A : Fin s → Op R)
    (h : ∀ i v, energy (A i v) ≤ energy v) (v : Vec R) :
    energy (opProduct s A v) ≤ energy v := by
  induction s generalizing v with
  | zero => simp [opProduct]
  | succ s ih =>
    rw [opProduct]
    exact (h 0 _).trans (ih (fun i => A i.succ) (fun i => h i.succ) v)

theorem product_fixes {s : ℕ} (A : Fin s → Op R) (v : Vec R)
    (h : ∀ i, A i v = v) : opProduct s A v = v := by
  induction s with
  | zero => simp [opProduct]
  | succ s ih =>
    rw [opProduct]
    change A 0 (opProduct s (fun i => A i.succ) v) = v
    rw [ih (fun i => A i.succ) (fun i => h i.succ), h]

/-- Ordered product distributes across its finite Cartesian domain without
commuting any pair of operators. -/
theorem sum_word_products {s : ℕ} {α : Type*} [Fintype α]
    (A : Fin s → α → Op R) :
    (∑ w : Fin s → α, opProduct s (fun i => A i (w i))) =
      opProduct s (fun i => ∑ a, A i a) := by
  classical
  induction s with
  | zero => simp [opProduct]
  | succ s ih =>
    let e : (Fin (s+1) → α) ≃ α × (Fin s → α) := (Fin.consEquiv (fun _ => α)).symm
    rw [Fintype.sum_equiv e _ (fun p => A 0 p.1 *
      opProduct s (fun i => A i.succ (p.2 i)))]
    · rw [opProduct,Fintype.sum_prod_type, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      change (∑ y : Fin s → α, A 0 a * opProduct s (fun i => A i.succ (y i))) = _
      rw [← Finset.mul_sum, ih]
    · intro w
      rfl

noncomputable def onesVec (R : ℕ) : Vec R := fun _ => 1

noncomputable def score (A : Op R) : ℝ := (avg (A (onesVec R))).re

theorem score_sum {I : Type*} [Fintype I] (A : I → Op R) :
    score (∑ i, A i) = ∑ i, score (A i) := by
  classical
  unfold score
  rw [LinearMap.sum_apply, avg]
  simp_rw [Finset.sum_apply]
  rw [Finset.sum_comm,Finset.mul_sum,Complex.re_sum]
  rfl

theorem score_zero (R : ℕ) : score (0 : Op R) = 0 := by
  simp [score,avg]

theorem energy_ones (R : ℕ) : energy (onesVec R) = (R : ℝ) := by
  simp [energy,onesVec]

noncomputable def nu {s : ℕ} (a : Fin s → Letter R) : ℝ :=
  score (opProduct s (fun i => letterOp (a i)))

theorem slot_product_test {s : ℕ} (P : Fin s → Letter R → Prop)
    (w : Fin s → Letter R) :
    (by classical exact (if ∀ i, P i (w i) then nu w else 0 : ℝ)) =
      score (opProduct s (fun i => selectOp (P i) (w i))) := by
  classical
  by_cases h : ∀ i, P i (w i)
  · simp [h,nu,selectOp]
  · have he : ∃ i, ¬ P i (w i) := by push_neg at h; exact h
    obtain ⟨i,hi⟩ := he
    have hz : selectOp (P i) (w i) = 0 := by simp [selectOp,hi]
    rw [if_neg h,opProduct_zero_of _ i hz,score_zero]

theorem nu_rectangle_identity {s : ℕ} (P : Fin s → Letter R → Prop) :
    (by classical exact ∑ w : Fin s → Letter R, if ∀ i, P i (w i) then nu w else 0) =
      score (opProduct s (fun i => boxOp (P i))) := by
  classical
  simp_rw [slot_product_test, ← score_sum, sum_word_products,boxOp]

theorem nu_rectangle {s : ℕ} (hR : 0 < R) (P : Fin s → Letter R → Prop)
    (hP : ∀ i, Allowed (P i)) :
    (by classical exact |∑ w : Fin s → Letter R, if ∀ i, P i (w i) then nu w else 0| ≤ 1) := by
  classical
  rw [nu_rectangle_identity]
  apply avg_re_bounded hR
  have h := product_contraction (fun i => boxOp (P i))
    (fun i => box_contraction hR _ (hP i)) (onesVec R)
  rwa [energy_ones] at h

theorem nu_total {s : ℕ} (hR : 0 < R) :
    (∑ w : Fin s → Letter R, nu w) = 1 := by
  classical
  have he := nu_rectangle_identity (s:=s) (fun _ => @full R)
  simp only [full_box_eq_rotation,full] at he
  have htrue : ∀ _i : Fin s, True := fun _ => trivial
  simp only [if_pos htrue] at he
  rw [he]
  unfold score
  rw [product_fixes (fun _ : Fin s => rotation R) (onesVec R)
    (fun _ => rotation_constant hR 1)]
  change (avg (fun _ : Fin R => (1 : ℂ))).re = 1
  rw [avg_constant hR]
  rfl

end PHP.Phase
