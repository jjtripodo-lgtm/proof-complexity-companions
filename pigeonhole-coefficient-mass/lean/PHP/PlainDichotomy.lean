import PHP.PhaseDiagram

namespace PHP
open Filter
open scoped Topology

/-- In the original satisfiability-gap domain, subexponential mass occurs
if and only if the pigeon-to-hole ratio tends to infinity. -/
theorem plain_subexponential_iff (m n : ℕ → ℕ)
    (hn : Tendsto n atTop atTop) (hmn : ∀ᶠ i in atTop, n i < m i) :
    Tendsto (fun i => Real.log (optimalPlainMass (m i) (n i))/(n i:ℝ)) atTop (𝓝 0) ↔
      Tendsto (fun i => (m i:ℝ)/(n i:ℝ)) atTop atTop := by
  constructor
  · intro hz
    apply tendsto_atTop.mpr
    intro cap
    let C := max 2 cap
    have hC : 1 < C := by have h := le_max_left (2:ℝ) cap; dsimp [C]; linarith
    obtain ⟨a,b,ha,hb,h⟩ := optimal_plain_exponential_bounded C hC
    have he := hz.eventually (eventually_lt_nhds (show (0:ℝ) < a/2 by positivity))
    obtain ⟨N,hN⟩ := exists_nat_gt (max 1 (2*b/a))
    have hnEv := hn.eventually_ge_atTop N
    filter_upwards [he,hnEv,hmn] with i hi hni hmi
    have hn1' : 1 ≤ (n i:ℝ) := ((le_max_left _ _).trans hN.le).trans (by exact_mod_cast hni)
    have hn1 : 1 ≤ n i := by exact_mod_cast hn1'
    have hn0 : 0 < (n i:ℝ) := by linarith
    by_contra! hfail
    have hcap : (m i:ℝ) ≤ C*n i :=
      (div_le_iff₀ hn0).mp ((hfail.le : _ ≤ cap).trans (le_max_right _ _))
    have hh := Real.log_le_log (Real.exp_pos _) (h hn1 hmi hcap)
    rw [Real.log_exp] at hh
    have hrate := (div_lt_iff₀ hn0).mp hi
    have hbig : 2*b/a ≤ (n i:ℝ) := ((le_max_right _ _).trans hN.le).trans (by exact_mod_cast hni)
    have hcomp := (div_le_iff₀ ha).mp hbig
    nlinarith
  · exact optimal_plain_log_rate_zero m n hn

/-- The one-surplus bound supplies positive exponential upper order on
the original board simultaneously for all surplus ratios. -/
theorem optimal_plain_le_pow {m n : ℕ} (h : n < m) (hn : 1 ≤ n) :
    optimalPlainMass m n ≤ (512:ℝ)^n := by
  obtain ⟨s,r,hr⟩ := (plain_exponential_seed h).refutation
  apply (optimal_plain_le_certificate r).trans (hr.trans ?_)
  have he : (2:ℝ)^(n+1) ≤ 2^(8*n) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hm : (2:ℝ)^(8*n+1) ≤ 2^(9*n) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  rw [pow_succ,pow_mul (2:ℝ) 9 n,show (2:ℝ)^9 = 512 by norm_num] at hm
  linarith

end PHP
