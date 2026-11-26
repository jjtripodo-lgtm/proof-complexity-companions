import PHP.FunctionalUpper
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace PHP
open Set MeasureTheory
open scoped Interval

private theorem folded_integral (n : ℕ) (hn : 1 ≤ n) :
    functionalIntegral n n = ∫ v : ℝ in 0..1, (1+v)*(1-v^2)^(n-1) := by
  let f := fun u : ℝ => u^(n-1)*(2-u)^n
  have he := intervalIntegral.integral_comp_add_mul (a:=0) (b:=1) f
    (show (-1:ℝ) ≠ 0 by norm_num) 1
  norm_num at he
  simp only [intervalIntegral.integral_symm (a:=0) (b:=1),neg_neg] at he
  unfold functionalIntegral
  have h : (∫ x : ℝ in 0..1, f x) = ∫ x : ℝ in 0..1, f (1+-x) := by
    linarith
  change (∫ x : ℝ in 0..1, f x) = _
  rw [h]
  apply intervalIntegral.integral_congr
  intro x _
  change (1+ -x)^(n-1)*(2-(1+ -x))^n = (1+x)*(1-x^2)^(n-1)
  -- Only the second power uses the surplus factor.
  rw [show 2-(1+ -x) = 1+x by ring]
  have hh : (1+x)^n = (1+x)^(n-1)*(1+x) := by rw [←pow_succ, Nat.sub_add_cancel hn]
  rw [hh,show 1-x^2 = (1+ -x)*(1+x) by ring,mul_pow]
  ring

private theorem gaussian_first_slab {a : ℝ} (ha : 0 < a) :
    (∫ v : ℝ in 0..1, Real.exp (-a*v^2)) ≤ Real.sqrt Real.pi / (2*Real.sqrt a) := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  have hh := setIntegral_mono_set ((integrable_exp_neg_mul_sq ha).integrableOn)
    (ae_of_all _ fun x => (Real.exp_pos (-a*x^2)).le)
    (Filter.Eventually.of_forall (fun x (hx : x ∈ Ioc (0:ℝ) 1) => show x ∈ Ioi 0 from hx.1))
  apply hh.trans_eq
  change (∫ x : ℝ in Ioi 0, Real.exp (-a*x^2)) = _
  rw [integral_gaussian_Ioi,Real.sqrt_div Real.pi_pos.le]
  ring

private theorem gaussian_weighted_slab {a : ℝ} (ha : 0 < a) :
    (∫ v : ℝ in 0..1, v*Real.exp (-a*v^2)) ≤ 1/(2*a) := by
  have hD (x : ℝ) :
      HasDerivAt (fun v : ℝ => Real.exp (-a*v^2)/(-2*a))
        (x*Real.exp (-a*x^2)) x := by
    have hp := (hasDerivAt_pow 2 x).const_mul (-a)
    have hh := hp.exp.div_const (-2*a)
    convert hh using 1
    field_simp [ha.ne']
    <;> ring
  have hc : Continuous (fun v : ℝ => v*Real.exp (-a*v^2)) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hD x) (hc.intervalIntegrable 0 1)]
  have h : 0 ≤ Real.exp (-a*1^2)/(2*a) := by positivity
  have he : Real.exp (-a*1^2)/(-2*a) - Real.exp (-a*0^2)/(-2*a)
      = 1/(2*a) - Real.exp (-a*1^2)/(2*a) := by
    norm_num [ha.ne']
    field_simp
    <;> ring
  linarith

private theorem functional_diagonal_gaussian_integral (n : ℕ) (hn : 2 ≤ n) :
    functionalIntegral n n ≤
      Real.sqrt Real.pi/(2*Real.sqrt ((n:ℝ)-1)) + 1/(2*((n:ℝ)-1)) := by
  let a := (n:ℝ)-1
  have hN : (2:ℝ) ≤ n := by exact_mod_cast hn
  have ha : 0 < a := by dsimp [a]; linarith
  rw [folded_integral n (by omega)]
  have hf : Continuous (fun v : ℝ => (1+v)*(1-v^2)^(n-1)) := by fun_prop
  have hg : Continuous (fun v : ℝ => (1+v)*Real.exp (-a*v^2)) := by fun_prop
  have hmono := intervalIntegral.integral_mono_on (μ:=volume) (by norm_num : (0:ℝ) ≤ 1)
    (hf.intervalIntegrable 0 1) (hg.intervalIntegrable 0 1)
    (fun v hv => show (1+v)*(1-v^2)^(n-1) ≤ (1+v)*Real.exp (-a*v^2) by
      apply mul_le_mul_of_nonneg_left _ (by linarith [hv.1])
      have h0 : 0 ≤ 1-v^2 := by nlinarith [hv.1,hv.2,mul_nonneg hv.1 (sub_nonneg.mpr hv.2)]
      have hp : 1-v^2 ≤ Real.exp (-v^2) := by linarith [Real.add_one_le_exp (-v^2)]
      have h := pow_le_pow_left₀ h0 hp (n-1)
      rw [← Real.exp_nat_mul,Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_one] at h
      exact h.trans_eq (by dsimp [a]; congr 1; ring))
  apply hmono.trans
  have hsplit (v : ℝ) : (1+v)*Real.exp (-a*v^2) =
      Real.exp (-a*v^2)+v*Real.exp (-a*v^2) := by ring
  simp_rw [hsplit]
  rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) 0 1)
    (Continuous.intervalIntegrable (by fun_prop) 0 1)]
  exact add_le_add (gaussian_first_slab ha) (gaussian_weighted_slab ha)

/-- The exact displayed Gaussian coefficient bound in the manuscript. -/
theorem functional_diagonal_gaussian (n : ℕ) (hn : 2 ≤ n) :
    ∃ (s : ℕ) (r : Refutation (@Functional (2*n) n) s),
      r.mass ≤ 3*(n:ℝ)^3*
        (Real.sqrt Real.pi/(2*Real.sqrt ((n:ℝ)-1)) + 1/(2*((n:ℝ)-1))) := by
  obtain ⟨s,r,hr⟩ := functional_general_upper (show n < 2*n by omega)
  have hN : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hI := functional_diagonal_gaussian_integral n hn
  have h0 : 0 ≤ functionalIntegral n n := by rw [← emptyInverseFor_cost (m:=2*n)]; exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have he : 2*n-n = n := by omega
  rw [he] at hr
  refine ⟨s,r,hr.trans ?_⟩
  apply mul_le_mul _ hI h0 (by positivity)
  push_cast
  nlinarith [mul_nonneg (show (0:ℝ) ≤ n by positivity) (show 0 ≤ (n:ℝ)-1 by linarith)]

end PHP
