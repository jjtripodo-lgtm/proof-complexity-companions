import PHP.DivergingRatio
import PHP.BoundedRatio

namespace PHP

open scoped BigOperators Topology
open Filter

theorem Refutation.one_le_mass {m n s : ℕ} {A : Cube m n → Prop}
    (r : Refutation A s) : 1 ≤ r.mass := by
  classical
  let x : Board m n := fun _ => false
  have hh := r.identity x
  unfold Refutation.mass
  calc
    1 = |∑ j, r.coeff j * eval (r.cube j) x| := by rw [hh,abs_one]
    _ ≤ ∑ j, |r.coeff j * eval (r.cube j) x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |r.coeff j| := by
      apply Finset.sum_le_sum
      intro i _
      by_cases h : Holds (r.cube i) x <;> simp [eval,h]

def plainMassSet (m n : ℕ) : Set ℝ :=
  { c | ∃ (s : ℕ) (r : Refutation (@Plain m n) s), c = r.mass }

noncomputable def optimalPlainMass (m n : ℕ) : ℝ := sInf (plainMassSet m n)

theorem plainMassSet_nonempty {m n : ℕ} (hm : n < m) : (plainMassSet m n).Nonempty := by
  obtain ⟨s,r,_⟩ := (plain_exponential_seed hm).refutation
  exact ⟨r.mass,s,r,rfl⟩

theorem plainMassSet_bddBelow (m n : ℕ) : BddBelow (plainMassSet m n) := by
  refine ⟨1,?_⟩
  rintro x ⟨s,r,rfl⟩
  exact r.one_le_mass

theorem optimal_plain_one_le {m n : ℕ} (h : n < m) : 1 ≤ optimalPlainMass m n :=
  le_csInf (plainMassSet_nonempty h) (by rintro x ⟨s,r,rfl⟩; exact r.one_le_mass)

theorem optimal_plain_le_certificate {m n s : ℕ} (r : Refutation (@Plain m n) s) :
    optimalPlainMass m n ≤ r.mass :=
  csInf_le (plainMassSet_bddBelow m n) ⟨s,r,rfl⟩

/-- The entire bounded-ratio lower half, stated at optimal mass. -/
theorem optimal_plain_exponential_bounded (C : ℝ) (hC : 1 < C) :
    ∃ a b : ℝ, 0 < a ∧ 1 < b ∧ ∀ {m n : ℕ}, 1 ≤ n → n < m → (m:ℝ) ≤ C*n →
      Real.exp (a*(n:ℝ)-b) ≤ optimalPlainMass m n := by
  obtain ⟨a,b,ha,hb,h⟩ := bounded_ratio_exponential_real C hC
  refine ⟨a,b,ha,hb,fun hn hmn hC' => le_csInf (plainMassSet_nonempty hmn) ?_⟩
  rintro x ⟨s,r,rfl⟩
  exact h hn hC' r

/-- The subexponential upper half along every sequence of diverging
pigeon-to-hole ratios and growing hole counts. -/
theorem optimal_plain_log_rate_zero (m n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (hRatio : Tendsto (fun i => (m i:ℝ)/(n i:ℝ)) atTop atTop) :
    Tendsto (fun i => Real.log (optimalPlainMass (m i) (n i))/(n i:ℝ)) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hN := hn.eventually_ge_atTop 1
    have hR := hRatio.eventually_ge_atTop 2
    filter_upwards [hN,hR] with i hni hri
    have hnR : 0 < (n i:ℝ) := by exact_mod_cast hni
    have h : 2*(n i:ℝ) ≤ m i := (le_div_iff₀ hnR).mp hri
    have hnm : n i < m i := by exact_mod_cast (show (n i:ℝ) < m i by linarith)
    have hz := Real.log_nonneg (optimal_plain_one_le hnm)
    exact ha.trans_le (div_nonneg hz hnR.le)
  · intro a ha
    obtain ⟨C,N,hCN⟩ := plain_diverging_ratio (a/2) (by positivity)
    have hN := hn.eventually_ge_atTop (max 1 N)
    have hR := hRatio.eventually_ge_atTop (C:ℝ)
    have hR' := hRatio.eventually_ge_atTop 2
    filter_upwards [hN,hR,hR'] with i hni hri hri'
    have hni1 : 1 ≤ n i := (le_max_left _ _).trans hni
    have hnR : 0 < (n i:ℝ) := by exact_mod_cast hni1
    have hC : C*n i ≤ m i := by exact_mod_cast (le_div_iff₀ hnR).mp hri
    obtain ⟨s,r,hr⟩ := hCN ((le_max_right _ _).trans hni) hC
    have h : 2*(n i:ℝ) ≤ m i := (le_div_iff₀ hnR).mp hri'
    have hnm : n i < m i := by exact_mod_cast (show (n i:ℝ) < m i by linarith)
    have hp : 0 < optimalPlainMass (m i) (n i) := zero_lt_one.trans_le (optimal_plain_one_le hnm)
    have hh := Real.log_le_log hp ((optimal_plain_le_certificate r).trans hr)
    rw [Real.log_exp] at hh
    apply (div_lt_iff₀ hnR).mpr
    nlinarith

end PHP
