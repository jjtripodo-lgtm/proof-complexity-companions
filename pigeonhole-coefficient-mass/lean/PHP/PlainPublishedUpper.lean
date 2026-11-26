import PHP.PlainDichotomy
import PHP.UpperBase

namespace PHP

/-- Checks a finite certificate of the published one-surplus bound for
every surplus, without importing an external certificate. -/
theorem plain_published_upper {m n : ℕ} (hm : n < m) (hn : 1 ≤ n) :
    ∃ (s : ℕ) (r : Refutation (@Plain m n) s), r.mass ≤ 2^(5*(n+1)) := by
  obtain ⟨s,r,hr⟩ := (plain_exponential_seed_sharp hm).refutation
  refine ⟨s,r,hr.trans ?_⟩
  have h1 : (2:ℝ)^(n+1) ≤ 2^(5*n) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : (2:ℝ)^(5*n+1) ≤ 2^(5*(n+1)) := pow_le_pow_right₀ (by norm_num) (by omega)
  rw [pow_succ] at h2
  linarith

theorem optimal_plain_published_upper {m n : ℕ} (hm : n < m) (hn : 1 ≤ n) :
    optimalPlainMass m n ≤ 2^(5*(n+1)) := by
  obtain ⟨_,r,hr⟩ := plain_published_upper hm hn
  exact (optimal_plain_le_certificate r).trans hr

end PHP
