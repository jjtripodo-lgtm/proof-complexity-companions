module

public import PHP.BlockOccupancy
public import PHP.ExponentialArithmetic
public import PHP.EmptyColumns
public import PHP.RowMonotonicity

@[expose] public section

namespace PHP

open scoped BigOperators

theorem BlockLayout.reciprocal_integral {k m n : ℕ}
    (D : BlockLayout k m n) (hm : 3*k ≤ m) :
    (∑ a : Word m n, D.smallLaw a / (1 + omissions a)) =
      ∫ x : ℝ in 0..1, x^(m-3*k) * blockPolynomial x^k := by
  classical
  let f (a : Word m n) (x : ℝ) := D.smallLaw a * x^(BlockLayout.missingNat a)
  have hf (a : Word m n) : Continuous (f a) := by unfold f; fun_prop
  calc
    _ = ∑ a : Word m n, ∫ x : ℝ in 0..1, f a x := by
      apply Finset.sum_congr rfl
      intro a _
      unfold f
      rw [intervalIntegral.integral_const_mul, integral_unit_powNat,
        BlockLayout.omissions_eq_cast, add_comm 1, div_eq_mul_inv]
    _ = ∫ x : ℝ in 0..1, ∑ a : Word m n, f a x :=
      (intervalIntegral.integral_finset_sum (fun a _ => (hf a).intervalIntegrable _ _)).symm
    _ = _ := by unfold f; simp_rw [D.small_polynomial hm]

private theorem mass_transport {a b n t : ℕ} (h : a = b)
    (r : Refutation (@Plain b n) t) :
    (h.symm ▸ r : Refutation (@Plain a n) t).mass = r.mass := by
  subst b
  rfl

/-- Verified calibrated disjoint-block certificate and its exact mass lower
bound for every full-board plain refutation with twice as many rows as holes. -/
theorem plain_diagonal_integral {n t : ℕ} (hn : 1 ≤ n)
    (r : Refutation (@Plain (2*n) n) t) :
    (2*(n : ℝ)) * (∫ x : ℝ in 0..1,
      x^(2*n-1-3*(2*((n-1)/6))) * blockPolynomial x^(2*((n-1)/6))) ≤ r.mass := by
  let m := 2*n-1
  let k := 2*((n-1)/6)
  have hm : m+1 = 2*n := by dsimp [m]; omega
  have hcols : k*3 ≤ n := by dsimp [k]; omega
  have hrows : k*6 ≤ m := by dsimp [k,m]; omega
  have hexp : 3*k ≤ m := by omega
  let D : BlockLayout k m n := BlockLayout.standard hcols hrows
  let r' : Refutation (@Plain (m+1) n) t := hm.symm ▸ r
  have hr : r'.mass = r.mass := mass_transport hm r
  have hb := symmetric_lower_bound r' D.smallLaw D.small_invariant D.small_calibrated
  rw [lift_mass_by_omissions _ D.small_invariant, D.reciprocal_integral hexp,
    hr, hm, Nat.cast_mul] at hb
  exact hb

theorem plain_diagonal_exponential {n t : ℕ} (hn : 1 ≤ n)
    (r : Refutation (@Plain (2*n) n) t) :
    (2 : ℝ)^((n-1)/6)/1000 ≤ r.mass :=
  (exponential_integral n hn).trans (plain_diagonal_integral hn r)

/-- Plain lower bound in the entire stated bounded-ratio window n<m≤2n. -/
theorem plain_exponential {m n t : ℕ} (hn : 1 ≤ n) (hm : m ≤ 2*n)
    (r : Refutation (@Plain m n) t) :
    (2 : ℝ)^((n-1)/6)/1000 ≤ r.mass := by
  let e := Fin.castLEEmb hm
  exact (plain_diagonal_exponential hn (r.addPlainRows e)).trans_eq (addPlainRows_preserves_mass e r)

end PHP
