import PHP.FunctionalWindow
import PHP.OneHot

namespace PHP
open Filter
open scoped Topology

theorem optimal_functional_one_le {m n : ℕ} (hm : n < m) :
    1 ≤ optimalFunctionalMass m n := by
  obtain ⟨s,r,_⟩ := functional_general_upper hm
  apply le_csInf (show (functionalMassSet m n).Nonempty from ⟨r.mass,s,r,rfl⟩)
  rintro _ ⟨s',r',rfl⟩
  exact r'.one_le_mass

theorem functional_surplus_integral {m n : ℕ} (hm : 2*n < m) :
    functionalIntegral (m-n) n ≤ 1/((m:ℝ)-2*(n:ℝ)) := by
  let d := m-2*n
  have hd : 1 ≤ d := by unfold d; omega
  have he : m-n-1 = d-1+n := by unfold d; omega
  have hcm : Continuous (fun u : ℝ => u^(m-n-1)*(2-u)^n) := by fun_prop
  have hcd : Continuous (fun u : ℝ => u^(d-1)) := by fun_prop
  have h := intervalIntegral.integral_mono_on (μ:=MeasureTheory.volume) (by norm_num : (0:ℝ) ≤ 1)
    (hcm.intervalIntegrable 0 1) (hcd.intervalIntegrable 0 1)
    (fun u (hu : u ∈ Set.Icc (0:ℝ) 1) => show u^(m-n-1)*(2-u)^n ≤ u^(d-1) by
      rw [he,pow_add,mul_assoc,←mul_pow]
      have hp : 0 ≤ u*(2-u) := mul_nonneg hu.1 (by linarith [hu.2])
      have hp' : u*(2-u) ≤ 1 := by nlinarith [sq_nonneg (u-1)]
      have he' := mul_le_mul_of_nonneg_left (pow_le_one₀ (n:=n) hp hp') (pow_nonneg hu.1 (d-1))
      simpa only [mul_one] using he')
  change functionalIntegral (m-n) n ≤ (∫ u : ℝ in 0..1, u^(d-1)) at h
  apply h.trans_eq
  rw [integral_unit_powNat,Nat.cast_sub hd,Nat.cast_one,sub_add_cancel,one_div]
  unfold d
  rw [Nat.cast_sub hm.le,Nat.cast_mul]
  norm_num

theorem optimal_functional_surplus_upper {m n : ℕ} (hm : 2*n < m) :
    optimalFunctionalMass m n ≤ functionalChargeBudget m n/((m:ℝ)-2*(n:ℝ)) := by
  obtain ⟨s,r,hr⟩ := functional_general_upper (by omega : n < m)
  have h := mul_le_mul_of_nonneg_left (functional_surplus_integral hm) (functionalChargeBudget_nonneg m n)
  have hh := (functional_optimum_le r).trans (hr.trans h)
  simpa only [div_eq_mul_inv,one_mul] using hh

private theorem eventually_log_small (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    {c : ℝ} (hc : 0 < c) : ∀ᶠ i in atTop, Real.log (n i)/(n i:ℝ) < c := by
  have h : Tendsto (fun x : ℝ => Real.log x/x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  exact (h.comp (tendsto_natCast_atTop_atTop.comp hn)).eventually (eventually_lt_nhds hc)

private theorem eventually_log_large (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) :
    ∀ᶠ i in atTop, 1 ≤ Real.log (n i) := by
  exact (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hn)).eventually_ge_atTop 1

/-- An exact polynomial-versus-superpolynomial threshold for the
functional system. It is stated without assuming m = O(n); the side
m ≥ 2n is already controlled by row monotonicity. -/
theorem functional_polynomial_threshold (m n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (hmn : ∀ᶠ i in atTop, n i < m i) :
    (∃ (C : ℝ) (A : ℕ), 0 < C ∧ ∀ᶠ i in atTop,
      optimalFunctionalMass (m i) (n i) ≤ C*(n i:ℝ)^A) ↔
    (∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in atTop, ((2*n i-m i:ℕ):ℝ)^2 ≤ C*(n i:ℝ)*Real.log (n i)) := by
  classical
  let k := fun i => ((2*n i-m i:ℕ):ℝ)
  have hn4 : ∀ᶠ i in atTop, 4 ≤ n i := hn.eventually_ge_atTop 4
  have hLog := eventually_log_large n hn
  constructor
  · rintro ⟨C,A,hC,hPoly⟩
    let B := |Real.log C|+Real.log 2+(A:ℝ)
    have hB : 0 ≤ B := by
      have h := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
      dsimp [B]
      positivity
    refine ⟨4*B,by positivity,?_⟩
    filter_upwards [hPoly,hn4,hmn,hLog] with i hPi hni hmi hli
    have hn0 : 0 < (n i:ℝ) := by exact_mod_cast (show 0 < n i by omega)
    by_cases hh : m i ≤ 2*n i
    · have hc : k i = (2*n i:ℕ)-(m i:ℝ) := Nat.cast_sub hh
      obtain ⟨hlo,_⟩ := functional_window_simple hni hmi hh
      rw [←hc] at hlo
      have hlog := Real.log_le_log (zero_lt_one.trans_le (optimal_functional_one_le hmi)) hPi
      rw [Real.log_mul hC.ne' (pow_ne_zero _ hn0.ne'),Real.log_pow] at hlog
      have hm : Real.log C + (A:ℝ)*Real.log (n i) + Real.log 2 ≤ B*Real.log (n i) := by
        have hL : 0 ≤ |Real.log C|+Real.log 2 := by
          have h := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
          positivity
        have hh' := mul_le_mul_of_nonneg_left hli hL
        dsimp [B]
        nlinarith [le_abs_self (Real.log C)]
      change (k i)^2 ≤ 4*B*(n i:ℝ)*Real.log (n i)
      rw [show 4*B*(n i:ℝ)*Real.log (n i) = (B*Real.log (n i))*(4*(n i:ℝ)) by ring]
      apply (div_le_iff₀ (show 0 < 4*(n i:ℝ) by positivity)).mp
      calc
        _ ≤ Real.log (optimalFunctionalMass (m i) (n i))+Real.log 2 := by linarith
        _ ≤ _ := by nlinarith
    · have hz : k i = 0 := by dsimp [k]; rw [Nat.sub_eq_zero_of_le (by omega),Nat.cast_zero]
      change (k i)^2 ≤ _
      rw [hz,zero_pow (by decide : (2:ℕ) ≠ 0)]
      exact mul_nonneg (by positivity) (by linarith : 0 ≤ Real.log (n i))
  · rintro ⟨C,hC,hCbound⟩
    obtain ⟨A,hA⟩ := exists_nat_gt (max 3 (C/2+4))
    have hA3 : 3 ≤ A := by exact_mod_cast ((le_max_left _ _).trans hA.le : (3:ℝ) ≤ A)
    have hAC : C/2+4 ≤ (A:ℝ) := (le_max_right _ _).trans hA.le
    have hc : 0 < 1/(4*(C+1)) := by positivity
    have hSmall := eventually_log_small n hn hc
    refine ⟨24,A,by norm_num,?_⟩
    filter_upwards [hCbound,hn4,hmn,hLog,hSmall] with i hCᵢ hni hmi hli hsi
    have hn0 : 0 < (n i:ℝ) := by exact_mod_cast (show 0 < n i by omega)
    have hn1 : 1 ≤ (n i:ℝ) := by exact_mod_cast (show 1 ≤ n i by omega)
    by_cases hh : 2*n i ≤ m i
    · have h := functional_poly_above_two (by omega : 1 ≤ n i) hh
      exact h.trans (mul_le_mul (by norm_num) (pow_le_pow_right₀ hn1 hA3) (by positivity) (by norm_num))
    · have h2 : m i ≤ 2*n i := by omega
      have hk : k i = (2*n i:ℕ)-(m i:ℝ) := Nat.cast_sub h2
      have hki : 0 ≤ k i := by dsimp [k]; positivity
      change (k i)^2 ≤ _ at hCᵢ
      have hsmall := (div_lt_iff₀ hn0).mp hsi
      have hlog := (lt_div_iff₀ (show 0 < 4*(C+1) by positivity)).mp
        (show Real.log (n i)/(n i:ℝ) < 1/(4*(C+1)) from hsi)
      have hbound : C*(n i:ℝ)*Real.log (n i) ≤ ((n i:ℝ)/2)^2 := by
        have hhelp : C*Real.log (n i) ≤ (n i:ℝ)/4 := by
          have hhh := mul_nonneg (show 0 ≤ Real.log (n i) by linarith) (show (0:ℝ) ≤ 1 by norm_num)
          have he := mul_le_mul_of_nonneg_right hlog.le hn0.le
          have hcancel : Real.log (n i)/(n i:ℝ)*(4*(C+1))*(n i:ℝ) =
              Real.log (n i)*(4*(C+1)) := by field_simp
          rw [hcancel] at he
          nlinarith
        have hh := mul_le_mul_of_nonneg_right hhelp hn0.le
        nlinarith
      have hnear : k i ≤ (n i:ℝ)/2 :=
        (sq_le_sq₀ hki (by positivity)).mp (hCᵢ.trans hbound)
      obtain ⟨_,hU⟩ := functional_window_simple hni hmi h2
      rw [←hk] at hU
      have hu := hU hnear
      have hh : (k i)^2/(2*(n i:ℝ)) ≤ C/2*Real.log (n i) := by
        apply (div_le_iff₀ (by positivity : 0 < 2*(n i:ℝ))).mpr
        convert hCᵢ using 1
        ring
      have hL : Real.log (optimalFunctionalMass (m i) (n i)) ≤ Real.log (24*(n i:ℝ)^A) := by
        rw [Real.log_mul (by norm_num : (24:ℝ) ≠ 0) (pow_ne_zero _ hn0.ne'),Real.log_pow]
        have h := mul_le_mul_of_nonneg_right hAC (show 0 ≤ Real.log (n i) by linarith)
        nlinarith
      exact (Real.log_le_log_iff (zero_lt_one.trans_le (optimal_functional_one_le hmi)) (by positivity)).mp hL

end PHP
