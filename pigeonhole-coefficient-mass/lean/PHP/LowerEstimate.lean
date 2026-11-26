import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace PHP

def blockPolynomial (x : ℝ) : ℝ := 20 - 30*x + 12*x^2 - x^3

theorem blockPolynomial_decreases {x y : ℝ} (hx : 0 ≤ x)
    (hxy : x ≤ y) (hy : y ≤ 1) : blockPolynomial y ≤ blockPolynomial x := by
  have hy0 : 0 ≤ y := hx.trans hxy
  have hx1 : x ≤ 1 := hxy.trans hy
  have hq : 0 ≤ 30 - 12*(x+y) + (x^2+x*y+y^2) := by
    nlinarith [mul_nonneg hx hy0, sq_nonneg x, sq_nonneg y]
  have hp := mul_nonneg (sub_nonneg.mpr hxy) hq
  have hid : blockPolynomial x - blockPolynomial y =
      (y-x)*(30 - 12*(x+y) + (x^2+x*y+y^2)) := by
    unfold blockPolynomial
    ring
  exact sub_nonneg.mp (hid.symm ▸ hp)

/-- The rational subinterval bound in the paper, separate from realizing its
integrand as the mass of a feasible signed dual. -/
theorem lower_interval_estimate (a k : ℕ) (hk : Even k) :
    (1/100 : ℝ) * (78/100 : ℝ)^a * (3296/1000 : ℝ)^k ≤
      ∫ x : ℝ in 0..1, x^a * blockPolynomial x^k := by
  let f : ℝ → ℝ := fun x => x^a * blockPolynomial x^k
  let D : ℝ := (78/100 : ℝ)^a * (3296/1000 : ℝ)^k
  have hf : Continuous f := by unfold f blockPolynomial; fun_prop
  have hc : Continuous fun _ : ℝ => D := continuous_const
  have hD : ∀ x ∈ Set.Icc (78/100 : ℝ) (79/100 : ℝ), D ≤ f x := by
    intro x hx
    have h0 : 0 ≤ x := (by norm_num : (0 : ℝ) ≤ 78/100).trans hx.1
    have hp : (3296/1000 : ℝ) ≤ blockPolynomial x :=
      (by norm_num [blockPolynomial] : (3296/1000 : ℝ) ≤ blockPolynomial (79/100)).trans
        (blockPolynomial_decreases h0 hx.2 (by norm_num))
    have hp0 : 0 ≤ blockPolynomial x := (by norm_num : (0 : ℝ) ≤ 3296/1000).trans hp
    exact mul_le_mul
      (pow_le_pow_left₀ (by norm_num) hx.1 _)
      (pow_le_pow_left₀ (by norm_num) hp _)
      (by positivity) (pow_nonneg h0 _)
  have hmono := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
    (by norm_num : (78/100 : ℝ) ≤ 79/100)
    (hc.intervalIntegrable _ _) (hf.intervalIntegrable _ _) hD
  have hleft : 0 ≤ ∫ x : ℝ in 0..(78/100), f x :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun x hx => mul_nonneg (pow_nonneg hx.1 _) (hk.pow_nonneg _))
  have hright : 0 ≤ ∫ x : ℝ in (79/100)..1, f x :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun x hx => mul_nonneg (pow_nonneg ((by norm_num : (0:ℝ) ≤ 79/100).trans hx.1) _)
        (hk.pow_nonneg _))
  have hjoin := intervalIntegral.integral_add_adjacent_intervals
    (μ := MeasureTheory.volume)
    (hf.intervalIntegrable 0 (78/100)) (hf.intervalIntegrable (78/100) (79/100))
  have hjoin' := intervalIntegral.integral_add_adjacent_intervals
    (μ := MeasureTheory.volume)
    (hf.intervalIntegrable 0 (79/100)) (hf.intervalIntegrable (79/100) 1)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  change (1/100 : ℝ) * (78/100)^a * (3296/1000)^k ≤ ∫ x : ℝ in 0..1, f x
  have hlen : (79/100 : ℝ) - 78/100 = 1/100 := by norm_num
  rw [hlen] at hmono
  change (1/100 : ℝ) * ((78/100)^a * (3296/1000)^k) ≤ _ at hmono
  rw [mul_assoc]
  linarith

end PHP
