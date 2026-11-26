import PHP.GenericOccupancy
import PHP.EmptyColumns
import PHP.RowMonotonicity

namespace PHP
open scoped BigOperators

private theorem mass_transport_gen {a b n t : ℕ} (h : a = b)
    (r : Refutation (@Plain b n) t) :
    (h.symm ▸ r : Refutation (@Plain a n) t).mass = r.mass := by
  subst b
  rfl

theorem GenericLayout.reciprocal_integral {s R k m n : ℕ}
    (D : GenericLayout s R k m n) (B : CalibratedBlock s R) (hm : s*k ≤ m) :
    (∑ a : Word m n, D.smallLaw B a / (1 + omissions a)) =
      ∫ x : ℝ in 0..1, x^(m-s*k) * B.polynomial x^k := by
  classical
  let f (a : Word m n) (x : ℝ) := D.smallLaw B a * x^(GenericLayout.missingNat a)
  have hf (a : Word m n) : Continuous (f a) := by unfold f; fun_prop
  calc
    _ = ∑ a : Word m n, ∫ x : ℝ in 0..1, f a x := by
      apply Finset.sum_congr rfl
      intro a _
      unfold f
      rw [intervalIntegral.integral_const_mul, integral_unit_powNat,
        GenericLayout.omissions_eq_cast, add_comm 1, div_eq_mul_inv]
    _ = ∫ x : ℝ in 0..1, ∑ a : Word m n, f a x :=
      (intervalIntegral.integral_finset_sum (fun a _ => (hf a).intervalIntegrable _ _)).symm
    _ = _ := by unfold f; simp_rw [D.small_polynomial B hm]

theorem generic_plain_integral {s R k m n t : ℕ} (hm : 1 ≤ m)
    (B : CalibratedBlock s R) (hc : k*s ≤ n) (hr : k*R ≤ m-1) (he : s*k ≤ m-1)
    (r : Refutation (@Plain m n) t) :
    (m : ℝ) * (∫ x : ℝ in 0..1, x^(m-1-s*k) * B.polynomial x^k) ≤ r.mass := by
  let m' := m-1
  have hEq : m'+1=m := by dsimp [m']; omega
  let D : GenericLayout s R k m' n := GenericLayout.standard hc hr
  let r' : Refutation (@Plain (m'+1) n) t := hEq.symm ▸ r
  have hmass : r'.mass = r.mass := mass_transport_gen hEq r
  have h := symmetric_lower_bound r' (D.smallLaw B) (D.small_invariant B) (D.small_calibrated B)
  rw [lift_mass_by_omissions _ (D.small_invariant B),D.reciprocal_integral B he,hmass,hEq] at h
  exact h

end PHP
