import Mathlib.Data.Complex.BigOperators
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace PHP.Phase

open scoped BigOperators ComplexConjugate

abbrev Vec (R : ℕ) := Fin R → ℂ
abbrev Op (R : ℕ) := Module.End ℂ (Vec R)
abbrev Letter (R : ℕ) := Option (Fin R)

noncomputable def eta : ℂ := ⟨1/2, Real.sqrt 3 / 2⟩

theorem eta_normSq : Complex.normSq eta = 1 := by
  have hs : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [eta,Complex.normSq_apply]
  nlinarith

theorem eta_one_sub : 1 - eta = conj eta := by
  apply Complex.ext <;> norm_num [eta]

theorem eta_mul_conj : eta * conj eta = 1 := by
  rw [Complex.mul_conj,eta_normSq]
  norm_num

noncomputable def avg {R : ℕ} (v : Vec R) : ℂ :=
  (R : ℂ)⁻¹ * ∑ i, v i

noncomputable def energy {R : ℕ} (v : Vec R) : ℝ :=
  ∑ i, Complex.normSq (v i)

theorem energy_nonneg {R : ℕ} (v : Vec R) : 0 ≤ energy v :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem avg_constant {R : ℕ} (hR : 0 < R) (z : ℂ) : avg (fun _ : Fin R => z) = z := by
  have hn : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  unfold avg
  simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Fintype.card_fin]
  rw [← mul_assoc,inv_mul_cancel₀ hn,one_mul]

theorem sum_center {R : ℕ} (hR : 0 < R) (v : Vec R) :
    (∑ i, (v i - avg v)) = 0 := by
  have hn : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Fintype.card_fin,avg]
  rw [← mul_assoc,mul_inv_cancel₀ hn,one_mul,sub_self]

theorem energy_centered {R : ℕ} (c : ℂ) (v : Vec R) (h : ∑ i, v i = 0) :
    energy (fun i => c + v i) = (R : ℝ)*Complex.normSq c + energy v := by
  have hcross : (∑ i, (c * conj (v i)).re) = 0 := by
    rw [← Complex.re_sum,← Finset.mul_sum,← map_sum,h,map_zero,mul_zero,Complex.zero_re]
  unfold energy
  simp only [Complex.normSq_add,Finset.sum_add_distrib,← Finset.mul_sum,hcross,
    mul_zero,add_zero,Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Fintype.card_fin]

theorem energy_variance {R : ℕ} (hR : 0 < R) (v : Vec R) :
    energy v = (R : ℝ)*Complex.normSq (avg v) +
      energy (fun i => v i - avg v) := by
  have h := energy_centered (avg v) (fun i => v i - avg v) (sum_center hR v)
  have he : (fun i : Fin R => avg v + (v i - avg v)) = v := by
    funext i
    ring
  rwa [he] at h

theorem avg_re_bounded {R : ℕ} (hR : 0 < R) (v : Vec R) (h : energy v ≤ R) :
    |(avg v).re| ≤ 1 := by
  have h0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hp := energy_variance hR v
  have he := energy_nonneg (fun i => v i - avg v)
  have hj : (R : ℝ)*Complex.normSq (avg v) ≤ (R : ℝ)*1 := by linarith
  have hs : Complex.normSq (avg v) ≤ 1 := le_of_mul_le_mul_left hj h0
  have hre := (Complex.re_sq_le_normSq (avg v)).trans hs
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

noncomputable def rotation (R : ℕ) : Op R where
  toFun v i := avg v + conj eta * (v i - avg v)
  map_add' v w := by
    ext i
    simp only [avg,Pi.add_apply,Finset.sum_add_distrib]
    ring
  map_smul' z v := by
    ext i
    simp only [avg,Pi.smul_apply,smul_eq_mul,← Finset.mul_sum,RingHom.id_apply]
    ring

theorem rotation_energy {R : ℕ} (hR : 0 < R) (v : Vec R) :
    energy (rotation R v) = energy v := by
  have hz : (∑ i : Fin R, conj eta*(v i-avg v)) = 0 := by
    rw [← Finset.mul_sum,sum_center hR v,mul_zero]
  have hv :
      energy (rotation R v) = (R : ℝ)*Complex.normSq (avg v) +
          energy (fun i => conj eta*(v i-avg v)) :=
    energy_centered _ _ hz
  rw [hv,energy_variance hR v]
  simp only [energy,Complex.normSq_mul,Complex.normSq_conj,eta_normSq,one_mul]

theorem rotation_constant {R : ℕ} (hR : 0 < R) (z : ℂ) :
    rotation R (fun _ => z) = fun _ => z := by
  funext i
  change avg (fun _ : Fin R => z) + conj eta * (z - avg (fun _ : Fin R => z)) = z
  rw [avg_constant hR z,sub_self,mul_zero,add_zero]

noncomputable def diagonal {R : ℕ} (c : Vec R) : Op R where
  toFun v i := c i * v i
  map_add' v w := by ext i; simp [mul_add]
  map_smul' z v := by ext i; simp [smul_eq_mul]; ring

noncomputable def coefficient {R : ℕ} (a : Letter R) (i : Fin R) : ℂ :=
  match a with
  | none => eta
  | some p => if i = p then 1-eta else 0

noncomputable def letterOp {R : ℕ} (a : Letter R) : Op R :=
  (rotation R).comp (diagonal (coefficient a))

theorem diagonal_contraction {R : ℕ} {c : Vec R} (h : ∀ i, Complex.normSq (c i) ≤ 1)
    (v : Vec R) : energy (diagonal c v) ≤ energy v := by
  unfold energy
  apply Finset.sum_le_sum
  intro i _
  change Complex.normSq (c i * v i) ≤ Complex.normSq (v i)
  rw [Complex.normSq_mul]
  simpa only [one_mul] using
    (mul_le_mul_of_nonneg_right (h i) (Complex.normSq_nonneg (v i)))

end PHP.Phase
