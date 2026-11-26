import PHP.PaperRate

namespace PHP
open scoped BigOperators

private theorem sharpened_interval_estimate (a k : ℕ) (hk : Even k) :
    (1/50000 : ℝ) * (78151/100000 : ℝ)^a * (3406219/1000000 : ℝ)^k ≤
      ∫ x : ℝ in 0..1, x^a * blockPolynomial x^k := by
  let f : ℝ → ℝ := fun x => x^a * blockPolynomial x^k
  let D : ℝ := (78151/100000 : ℝ)^a * (3406219/1000000 : ℝ)^k
  have hf : Continuous f := by unfold f blockPolynomial; fun_prop
  have hc : Continuous fun _ : ℝ => D := continuous_const
  have hD : ∀ x ∈ Set.Icc (78151/100000 : ℝ) (78153/100000 : ℝ), D ≤ f x := by
    intro x hx
    have h0 : 0 ≤ x := (by norm_num : (0 : ℝ) ≤ 78151/100000).trans hx.1
    have hp : (3406219/1000000 : ℝ) ≤ blockPolynomial x :=
      (by norm_num [blockPolynomial] : (3406219/1000000 : ℝ) ≤ blockPolynomial (78153/100000)).trans
        (blockPolynomial_decreases h0 hx.2 (by norm_num))
    have hp0 : 0 ≤ blockPolynomial x := (by norm_num : (0 : ℝ) ≤ 3406219/1000000).trans hp
    exact mul_le_mul
      (pow_le_pow_left₀ (by norm_num) hx.1 _)
      (pow_le_pow_left₀ (by norm_num) hp _)
      (by positivity) (pow_nonneg h0 _)
  have hmono := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
    (by norm_num : (78151/100000 : ℝ) ≤ 78153/100000)
    (hc.intervalIntegrable _ _) (hf.intervalIntegrable _ _) hD
  have hleft : 0 ≤ ∫ x : ℝ in 0..(78151/100000), f x :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun x hx => mul_nonneg (pow_nonneg hx.1 _) (hk.pow_nonneg _))
  have hright : 0 ≤ ∫ x : ℝ in (78153/100000)..1, f x :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun x hx => mul_nonneg (pow_nonneg ((by norm_num : (0:ℝ) ≤ 78153/100000).trans hx.1) _)
        (hk.pow_nonneg _))
  have hjoin := intervalIntegral.integral_add_adjacent_intervals
    (μ := MeasureTheory.volume)
    (hf.intervalIntegrable 0 (78151/100000)) (hf.intervalIntegrable (78151/100000) (78153/100000))
  have hjoin' := intervalIntegral.integral_add_adjacent_intervals
    (μ := MeasureTheory.volume)
    (hf.intervalIntegrable 0 (78153/100000)) (hf.intervalIntegrable (78153/100000) 1)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  change (1/50000 : ℝ) * (78151/100000)^a * (3406219/1000000)^k ≤ ∫ x : ℝ in 0..1, f x
  have hlen : (78153/100000 : ℝ) - 78151/100000 = 1/50000 := by norm_num
  rw [hlen] at hmono
  change (1/50000 : ℝ) * ((78151/100000)^a * (3406219/1000000)^k) ≤ _ at hmono
  rw [mul_assoc]
  linarith


private theorem saddle_exp_step : Real.exp (972/1000) ≤ (78151/100000 : ℝ)^6 * (3406219/1000000 : ℝ)^2 := by
  have h := Real.exp_bound' (x := (972/1000 : ℝ)) (n := 11)
    (by norm_num) (by norm_num) (by decide)
  refine h.trans ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

private theorem saddle_exp_slack : Real.exp (-14) ≤ (1/1000000 : ℝ) := by
  have hlo : (27/10 : ℝ) ≤ Real.exp 1 :=
    (by norm_num : (27/10 : ℝ) ≤ 2.7182818283).trans Real.exp_one_gt_d9.le
  have hpow : (1000000 : ℝ) ≤ Real.exp 14 := by
    rw [show (14 : ℝ) = ((14 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
    exact (by norm_num : (1000000 : ℝ) ≤ (27/10 : ℝ)^14).trans
      (pow_le_pow_left₀ (by norm_num) hlo 14)
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1000000) hpow

/-- A narrower interval near the exact saddle sharpens the coefficient.
The certificate itself is the same rational six-label witness. -/
theorem saddle_rate_integral (n : ℕ) (hn : 1 ≤ n) :
    Real.exp ((162/1000 : ℝ)*n - 15) ≤
    (2*(n : ℝ)) * (∫ x : ℝ in 0..1,
      x^(2*n-1-3*(2*((n-1)/6))) * blockPolynomial x^(2*((n-1)/6))) := by
  let q := (n-1)/6
  let r := (n-1)%6
  let B : ℝ := (78151/100000 : ℝ)^6 * (3406219/1000000 : ℝ)^2
  have hB : 0 ≤ B := by unfold B; norm_num
  have hr : r < 6 := Nat.mod_lt _ (by decide)
  have hnr : n = 6*q + r + 1 := by
    have := Nat.mod_add_div (n-1) 6
    dsimp [q,r]
    omega
  have hnrR : (n : ℝ) = 6*(q : ℝ) + (r : ℝ) + 1 := by exact_mod_cast hnr
  have rR : (r : ℝ) ≤ 5 := by exact_mod_cast (show r ≤ 5 by omega)
  have he : 2*n-1-3*(2*q) = 6*q + (2*r+1) := by omega
  have hk : Even (2*q) := ⟨q,by omega⟩
  have hint := sharpened_interval_estimate (2*n-1-3*(2*q)) (2*q) hk
  have hrpow : (78151/100000 : ℝ)^11 ≤ (78151/100000 : ℝ)^(2*r+1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hbase : (Real.exp (972/1000))^q ≤ B^q :=
    pow_le_pow_left₀ (Real.exp_pos _).le saddle_exp_step q
  have hsmall : Real.exp ((162/1000 : ℝ)*((r : ℝ)+1)-15) ≤ 1/1000000 :=
    (Real.exp_le_exp.mpr (by linarith : (162/1000 : ℝ)*((r : ℝ)+1)-15 ≤ -14)).trans saddle_exp_slack
  have hexp : Real.exp ((162/1000 : ℝ)*n - 15) =
      (Real.exp (972/1000))^q * Real.exp ((162/1000 : ℝ)*((r : ℝ)+1)-15) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    rw [hnrR]
    ring
  rw [he,pow_add,pow_mul,pow_mul] at hint
  have hrewrite :
      (1/50000 : ℝ) * (((78151/100000 : ℝ)^6)^q * (78151/100000 : ℝ)^(2*r+1)) *
          ((3406219/1000000 : ℝ)^2)^q =
      (1/50000 : ℝ) * (78151/100000 : ℝ)^(2*r+1) * B^q := by
    unfold B
    rw [mul_pow]
    ring
  rw [hrewrite] at hint
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hc : (1/1000000 : ℝ) ≤ (2*(n : ℝ)) * ((1/50000 : ℝ) * (78151/100000 : ℝ)^(2*r+1)) := by
    calc
      _ ≤ (2 : ℝ) * ((1/50000 : ℝ) * (78151/100000 : ℝ)^11) := by norm_num
      _ ≤ 2 * (1/50000 * (78151/100000 : ℝ)^(2*r+1)) := by gcongr
      _ ≤ _ := by gcongr; linarith
  calc
    _ ≤ B^q * (1/1000000 : ℝ) := by
      rw [hexp]
      exact mul_le_mul hbase hsmall (Real.exp_pos _).le (pow_nonneg hB _)
    _ ≤ (2*(n : ℝ)) * ((1/50000 : ℝ) * (78151/100000 : ℝ)^(2*r+1)) * B^q := by
      rw [mul_comm (B^q)]
      exact mul_le_mul_of_nonneg_right hc (pow_nonneg hB _)
    _ ≤ _ := by
      rw [mul_assoc, show (n-1)/6 = q from rfl, he]
      exact mul_le_mul_of_nonneg_left hint (by positivity)

/-- A stronger explicit rate in the same model and entire manuscript range.
For n < m ≤ 2 n, the result is asymptotically stronger than 0.149n−8. -/
theorem plain_sharpened_rate {m n t : ℕ} (hn : 1 ≤ n) (hm : m ≤ 2*n)
    (r : Refutation (@Plain m n) t) :
    Real.exp ((162/1000 : ℝ)*n - 15) ≤ r.mass := by
  let e := Fin.castLEEmb hm
  have hr := (saddle_rate_integral n hn).trans (plain_diagonal_integral hn (r.addPlainRows e))
  simpa only [addPlainRows_preserves_mass] using hr


end PHP
