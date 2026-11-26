import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-! Polynomial estimate for the functional upper-bound mechanism. This file
bounds the integral only; it does not construct a refutation. -/
namespace PHP

noncomputable def functionalIntegral (d n : ℕ) : ℝ :=
  ∫ u : ℝ in 0..1, u^(d-1) * (2-u)^n

/-- At twice as many rows as columns, the integral is at most 2.
This substitute for the Gaussian estimate is enough to keep the upper mass
polynomial and avoids the Gaussian integral and the square-root bound. -/
theorem functionalIntegral_diagonal (n : ℕ) (hn : 1 ≤ n) :
    functionalIntegral n n ≤ 2 := by
  have hu : Continuous (fun u : ℝ => u^(n-1) * (2-u)^n) := by fun_prop
  have hc : Continuous (fun _ : ℝ => (2 : ℝ)) := continuous_const
  have h01 : (0 : ℝ) ≤ 1 := zero_le_one
  have hm := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) h01
    (hu.intervalIntegrable 0 1) (hc.intervalIntegrable 0 1)
    (fun u hu' => show u^(n-1) * (2-u)^n ≤ 2 by
      have h0 : 0 ≤ u := hu'.1
      have h1 : u ≤ 1 := hu'.2
      have h2 : 0 ≤ 2-u := by linarith
      have hprod : u * (2-u) ≤ 1 := by nlinarith [sq_nonneg (u-1)]
      have ep : (2-u)^n = (2-u)^(n-1) * (2-u) := by
        rw [← pow_succ]
        congr 1
        omega
      calc
        u^(n-1) * (2-u)^n = (u*(2-u))^(n-1) * (2-u) := by
          rw [ep, mul_pow, mul_assoc]
        _ ≤ 1 * (2-u) :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ (mul_nonneg h0 h2) hprod) h2
        _ ≤ 2 := by linarith)
  simpa [functionalIntegral] using hm

end PHP
