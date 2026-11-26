import PHP.PhaseCore
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Data.Fintype.Option

namespace PHP.Phase

open scoped BigOperators ComplexConjugate

variable {R : ℕ}

def Allowed (P : Letter R → Prop) : Prop :=
  (∀ a, ¬ P a) ∨ (∃ p : Fin R, ∀ a, P a ↔ a = some p) ∨ P none

noncomputable def selectOp (P : Letter R → Prop) (a : Letter R) : Op R := by
  classical
  exact if P a then letterOp a else 0

noncomputable def boxOp (P : Letter R → Prop) : Op R :=
  ∑ a, selectOp P a

noncomputable def boxCoeff (P : Letter R → Prop) (i : Fin R) : ℂ := by
  classical
  exact ∑ a, if P a then coefficient a i else 0

theorem boxOp_eq (P : Letter R → Prop) :
    boxOp P = (rotation R).comp (diagonal (boxCoeff P)) := by
  classical
  ext v i
  unfold boxOp
  rw [LinearMap.sum_apply]
  change (∑ a, selectOp P a v) i = (rotation R (diagonal (boxCoeff P) v)) i
  have he (a : Letter R) :
      selectOp P a v = rotation R (diagonal
        (fun j => if P a then coefficient a j else 0) v) := by
    by_cases h : P a
    · simp [selectOp,h,letterOp]
    · have hz : diagonal (fun _ : Fin R => (0 : ℂ)) v = 0 := by
        funext j
        change 0 * v j = 0
        exact zero_mul _
      simp [selectOp,h,hz]
  simp_rw [he, ← map_sum]
  apply congrArg (fun x : Vec R => rotation R x i)
  funext j
  change (∑ a, diagonal (fun j => if P a then coefficient a j else 0) v) j =
    boxCoeff P j * v j
  rw [Finset.sum_apply,boxCoeff,Finset.sum_mul]
  rfl

theorem eta_one_sub_normSq : Complex.normSq (1 - eta) = 1 := by
  rw [eta_one_sub, Complex.normSq_conj, eta_normSq]

theorem coefficient_normSq (a : Letter R) (i : Fin R) : Complex.normSq (coefficient a i) ≤ 1 := by
  classical
  cases a with
  | none => simp [coefficient,eta_normSq]
  | some p => by_cases h : i = p <;> simp [coefficient,h,eta_one_sub_normSq]

theorem boxCoeff_none (P : Letter R → Prop) (h : P none) (i : Fin R) :
    boxCoeff P i = (by classical exact if P (some i) then 1 else eta) := by
  classical
  unfold boxCoeff
  rw [Fintype.sum_option]
  simp only [if_pos h,coefficient]
  rw [Finset.sum_eq_single i]
  · by_cases hi : P (some i) <;> simp [hi]
  · intro j _ hj
    have hh : i ≠ j := Ne.symm hj
    simp [hh]
  · simp

theorem box_coeff_norm_sq (P : Letter R → Prop) (h : Allowed P) (i : Fin R) :
    Complex.normSq (boxCoeff P i) ≤ 1 := by
  classical
  rcases h with h | ⟨p,hp⟩ | h
  · simp [boxCoeff,h]
  · have he : boxCoeff P i = coefficient (some p) i := by
      unfold boxCoeff
      simp [hp]
    rw [he]
    exact coefficient_normSq _ _
  · rw [boxCoeff_none P h i]
    by_cases hp : P (some i) <;> simp [hp,eta_normSq]

theorem box_contraction (hR : 0 < R) (P : Letter R → Prop) (h : Allowed P)
    (v : Vec R) : energy (boxOp P v) ≤ energy v := by
  rw [boxOp_eq]
  change energy (rotation R (diagonal (boxCoeff P) v)) ≤ energy v
  rw [rotation_energy hR]
  exact diagonal_contraction (box_coeff_norm_sq P h) v

def full {R : ℕ} (_ : Letter R) : Prop := True

theorem full_box_eq_rotation (R : ℕ) : boxOp (@full R) = rotation R := by
  rw [boxOp_eq]
  ext v i
  have he : diagonal (boxCoeff (@full R)) v = v := by
    funext j
    change boxCoeff full j * v j = v j
    rw [boxCoeff_none full trivial j]
    simp [full]
  simp [he]

end PHP.Phase
