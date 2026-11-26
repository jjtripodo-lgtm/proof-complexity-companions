import PHP.AmplificationIntegral
import PHP.PhaseDensity

namespace PHP

/-- The bounded-ratio half of the paper's phase diagram. The constants
depend only on the selected row-to-column ratio bound; the certificate
tests the original full Boolean board without functionality. -/
theorem bounded_ratio_exponential (C : ℕ) (hC : 1 ≤ C) :
    ∃ a b : ℝ, 0 < a ∧ 1 < b ∧
      ∀ {m n t : ℕ}, 1 ≤ n → m ≤ C*n → (r : Refutation (@Plain m n) t) →
        Real.exp (a*(n : ℝ)-b) ≤ r.mass := by
  obtain ⟨s,R,B,hs,hR,hh⟩ := Phase.density_block C hC
  exact bounded_ratio_bound_from_block B C hC hs hR hh

/-- Forms the same theorem with an arbitrary real ratio cap as in the
paper: an integral cap is only used by the certificate construction. -/
theorem bounded_ratio_exponential_real (C : ℝ) (hC : 1 < C) :
    ∃ a b : ℝ, 0 < a ∧ 1 < b ∧
      ∀ {m n t : ℕ}, 1 ≤ n → (m : ℝ) ≤ C*n → (r : Refutation (@Plain m n) t) →
        Real.exp (a*(n : ℝ)-b) ≤ r.mass := by
  obtain ⟨N,hN⟩ := exists_nat_gt C
  have hNN : 1 ≤ N := by exact_mod_cast (show (1 : ℝ) ≤ N by linarith)
  obtain ⟨a,b,ha,hb,h⟩ := bounded_ratio_exponential N hNN
  refine ⟨a,b,ha,hb,?_⟩
  intro m n t hn hm r
  have hm' : (m : ℝ) ≤ (N : ℝ)*(n : ℝ) :=
    hm.trans (mul_le_mul_of_nonneg_right hN.le (by positivity))
  exact h hn (by exact_mod_cast hm') r

end PHP
