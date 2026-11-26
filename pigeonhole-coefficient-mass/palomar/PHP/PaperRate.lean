module

public import PHP.PlainWitness
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

namespace PHP

open scoped BigOperators

private theorem exp_step : Real.exp (894/1000) ≤ (78/100 : ℝ)^6 * (3296/1000 : ℝ)^2 := by
  have h := Real.exp_bound' (x := (894/1000 : ℝ)) (n := 7)
    (by norm_num) (by norm_num) (by decide)
  refine h.trans ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

private theorem exp_slack : Real.exp (-7) ≤ (1/1000 : ℝ) := by
  have hlo : (27/10 : ℝ) ≤ Real.exp 1 :=
    (by norm_num : (27/10 : ℝ) ≤ 2.7182818283).trans Real.exp_one_gt_d9.le
  have hpow : (1000 : ℝ) ≤ Real.exp 7 := by
    rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
    exact (by norm_num : (1000 : ℝ) ≤ (27/10 : ℝ)^7).trans
      (pow_le_pow_left₀ (by norm_num) hlo 7)
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1000) hpow

/-- Exact printed constant. A rational exponential step and a separate
seven-unit slack bound avoid computing logarithms. -/
theorem paper_rate_integral (n : ℕ) (hn : 1 ≤ n) :
    Real.exp ((149/1000 : ℝ)*n - 8) ≤
    (2*(n : ℝ)) * (∫ x : ℝ in 0..1,
      x^(2*n-1-3*(2*((n-1)/6))) * blockPolynomial x^(2*((n-1)/6))) := by
  let q := (n-1)/6
  let r := (n-1)%6
  let B : ℝ := (78/100 : ℝ)^6 * (3296/1000 : ℝ)^2
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
  have hint := lower_interval_estimate (2*n-1-3*(2*q)) (2*q) hk
  have hrpow : (78/100 : ℝ)^11 ≤ (78/100 : ℝ)^(2*r+1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hbase : (Real.exp (894/1000))^q ≤ B^q :=
    pow_le_pow_left₀ (Real.exp_pos _).le exp_step q
  have hsmall : Real.exp ((149/1000 : ℝ)*((r : ℝ)+1)-8) ≤ 1/1000 :=
    (Real.exp_le_exp.mpr (by linarith : (149/1000 : ℝ)*((r : ℝ)+1)-8 ≤ -7)).trans exp_slack
  have hexp : Real.exp ((149/1000 : ℝ)*n - 8) =
      (Real.exp (894/1000))^q * Real.exp ((149/1000 : ℝ)*((r : ℝ)+1)-8) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    rw [hnrR]
    ring
  rw [he,pow_add,pow_mul,pow_mul] at hint
  have hrewrite :
      (1/100 : ℝ) * (((78/100 : ℝ)^6)^q * (78/100 : ℝ)^(2*r+1)) *
          ((3296/1000 : ℝ)^2)^q =
      (1/100 : ℝ) * (78/100 : ℝ)^(2*r+1) * B^q := by
    unfold B
    rw [mul_pow]
    ring
  rw [hrewrite] at hint
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hc : (1/1000 : ℝ) ≤ (2*(n : ℝ)) * ((1/100 : ℝ) * (78/100 : ℝ)^(2*r+1)) := by
    calc
      _ ≤ (2 : ℝ) * ((1/100 : ℝ) * (78/100 : ℝ)^11) := by norm_num
      _ ≤ 2 * (1/100 * (78/100 : ℝ)^(2*r+1)) := by gcongr
      _ ≤ _ := by gcongr; linarith
  calc
    _ ≤ B^q * (1/1000 : ℝ) := by
      rw [hexp]
      exact mul_le_mul hbase hsmall (Real.exp_pos _).le (pow_nonneg hB _)
    _ ≤ (2*(n : ℝ)) * ((1/100 : ℝ) * (78/100 : ℝ)^(2*r+1)) * B^q := by
      rw [mul_comm (B^q)]
      exact mul_le_mul_of_nonneg_right hc (pow_nonneg hB _)
    _ ≤ _ := by
      rw [mul_assoc, show (n-1)/6 = q from rfl, he]
      exact mul_le_mul_of_nonneg_left hint (by positivity)

/-- The manuscript's theorem with its exact constant and the full Boolean
primal domain, for every finite legal plain refutation in the stated range. -/
theorem plain_paper_rate {m n t : ℕ} (hn : 1 ≤ n) (hm : m ≤ 2*n)
    (r : Refutation (@Plain m n) t) :
    Real.exp ((149/1000 : ℝ)*n - 8) ≤ r.mass := by
  let e := Fin.castLEEmb hm
  have hr := (paper_rate_integral n hn).trans (plain_diagonal_integral hn (r.addPlainRows e))
  simpa only [addPlainRows_preserves_mass] using hr

end PHP
