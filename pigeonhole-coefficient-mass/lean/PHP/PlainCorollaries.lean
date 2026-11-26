import PHP.PlainPublishedUpper
import PHP.UniformLower
import PHP.FunctionalAsymptotics
import PHP.DiagonalSeparation

namespace PHP

/-- Uniform exponential order at every bounded positive surplus ratio. -/
theorem plain_exact_exponential_order (C : ℝ) (hC : 1 < C) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∃ N : ℕ,
      ∀ {m n : ℕ}, N ≤ n → n < m → (m:ℝ) ≤ C*n →
        Real.exp (a*(n:ℝ)) ≤ optimalPlainMass m n ∧
        optimalPlainMass m n ≤ Real.exp (b*(n:ℝ)) := by
  obtain ⟨a,b,ha,hb,h⟩ := optimal_plain_exponential_bounded C hC
  obtain ⟨N,hN⟩ := exists_nat_gt (max 1 (2*b/a))
  have hB : 0 < Real.log 512 := Real.log_pos (by norm_num)
  refine ⟨a/2,Real.log 512,by positivity,hB,N,?_⟩
  intro m n hn hmn hcap
  have hn' : 1 ≤ n := by
    exact_mod_cast (((le_max_left (1:ℝ) _).trans hN.le).trans (by exact_mod_cast hn) : (1:ℝ) ≤ n)
  have hl := h hn' hmn hcap
  have hh : 2*b/a ≤ (n:ℝ) := ((le_max_right _ _).trans hN.le).trans (by exact_mod_cast hn)
  have hhh := (div_le_iff₀ ha).mp hh
  refine ⟨(Real.exp_le_exp.mpr (by linarith : a/2*(n:ℝ) ≤ a*(n:ℝ)-b)).trans hl,?_⟩
  rw [mul_comm,Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ) < 512)]
  exact optimal_plain_le_pow hmn hn'

/-- Polynomial plain mass forces at least order n²/log n pigeons. -/
theorem plain_polynomial_mass_necessary (C : ℝ) (hC : 0 < C) (A : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ {m n : ℕ}, 2 ≤ n → n < m →
      optimalPlainMass m n ≤ C*(n:ℝ)^A →
      c*(n:ℝ)^2/Real.log n ≤ (m:ℝ) := by
  obtain ⟨α,hα,h⟩ := optimal_plain_all_ratio_lower
  let L := Real.log 2
  let K := 1+(A:ℝ)+|Real.log C|/L
  have hL : 0 < L := Real.log_pos (by norm_num)
  have hK : 0 < K := by unfold K; positivity
  refine ⟨α/K,div_pos hα hK,?_⟩
  intro m n hn hmn hpoly
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hmR : 0 < (m:ℝ) := by exact_mod_cast (show 0<m by omega)
  have hl := Real.log_le_log (zero_lt_one.trans_le (optimal_plain_one_le hmn)) hpoly
  rw [Real.log_mul hC.ne' (pow_ne_zero _ hnR.ne'),Real.log_pow] at hl
  have hln : L ≤ Real.log (n:ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hln0 : 0 < Real.log (n:ℝ) := hL.trans_le hln
  have hAbs : |Real.log C| ≤ (|Real.log C|/L)*Real.log (n:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hln (show 0 ≤ |Real.log C|/L by positivity)
    rwa [div_mul_cancel₀ _ hL.ne'] at hh
  have hlog : Real.log (optimalPlainMass m n) ≤ K*Real.log (n:ℝ) := by
    unfold K
    nlinarith [le_abs_self (Real.log C)]
  have hcore : α*((n:ℝ)^2/(m:ℝ)) ≤ K*Real.log (n:ℝ) := by
    have hh := h hn hmn
    nlinarith [mul_nonneg hα.le hln0.le]
  have he : α*(n:ℝ)^2 ≤ (K*Real.log (n:ℝ))*(m:ℝ) := by
    have hh := (div_le_iff₀ hmR).mp (show α*(n:ℝ)^2/(m:ℝ) ≤ K*Real.log (n:ℝ) by
      rw [mul_div_assoc]; exact hcore)
    exact hh
  apply (div_le_iff₀ hln0).mpr
  apply le_of_mul_le_mul_right _ hK
  have hEq : (α/K*(n:ℝ)^2)*K = α*(n:ℝ)^2 := by field_simp
  rw [hEq]
  exact he.trans_eq (by ring)

end PHP
