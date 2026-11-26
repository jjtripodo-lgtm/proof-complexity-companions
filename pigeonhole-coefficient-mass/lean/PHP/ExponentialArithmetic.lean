import PHP.LowerEstimate

namespace PHP

/-- A rational exponential lower estimate after taking the largest feasible even
number of blocks. This avoids logarithm certificates when only the qualitative
exponential-versus-polynomial distinction is needed. -/
theorem exponential_integral (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℝ)^((n-1)/6) / 1000 ≤
      (2*(n : ℝ)) * (∫ x : ℝ in 0..1,
        x^(2*n-1-3*(2*((n-1)/6))) * blockPolynomial x^(2*((n-1)/6))) := by
  let q := (n-1)/6
  let r := (n-1)%6
  have hr : r < 6 := Nat.mod_lt _ (by decide)
  have hnr : n = 6*q + r + 1 := by
    have := Nat.mod_add_div (n-1) 6
    dsimp [q,r]
    omega
  have he : 2*n-1-3*(2*q) = 6*q + (2*r+1) := by omega
  have hk : Even (2*q) := ⟨q, by omega⟩
  have hint := lower_interval_estimate (2*n-1-3*(2*q)) (2*q) hk
  have hrpow : (78/100 : ℝ)^11 ≤ (78/100 : ℝ)^(2*r+1) := by
    apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
    omega
  have hbase : (2 : ℝ)^q ≤ ((78/100 : ℝ)^6 * (3296/1000 : ℝ)^2)^q :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  rw [he, pow_add, pow_mul, pow_mul] at hint
  have hrewrite :
      (1/100 : ℝ) * (((78/100 : ℝ)^6)^q * (78/100 : ℝ)^(2*r+1)) *
          ((3296/1000 : ℝ)^2)^q =
      (1/100 : ℝ) * (78/100 : ℝ)^(2*r+1) *
          (((78/100 : ℝ)^6) * ((3296/1000 : ℝ)^2))^q := by
    rw [mul_pow]
    ring
  rw [hrewrite] at hint
  have hcoeff : (1/1000 : ℝ) ≤
      (2*(n : ℝ)) * ((1/100 : ℝ) * (78/100 : ℝ)^(2*r+1)) := by
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    calc
      _ ≤ (2 : ℝ) * ((1/100 : ℝ) * (78/100 : ℝ)^11) := by norm_num
      _ ≤ 2 * (1/100 * (78/100 : ℝ)^(2*r+1)) := by gcongr
      _ ≤ _ := by gcongr; linarith
  have hnm : 0 ≤ (2*(n : ℝ)) := by positivity
  change (2 : ℝ)^q / 1000 ≤ _
  calc
    _ = (1/1000 : ℝ) * (2 : ℝ)^q := by ring
    _ ≤ (2*(n : ℝ)) * ((1/100 : ℝ) * (78/100 : ℝ)^(2*r+1)) *
        (((78/100 : ℝ)^6) * ((3296/1000 : ℝ)^2))^q :=
      mul_le_mul hcoeff hbase (by positivity) (by positivity)
    _ ≤ _ := by
      rw [mul_assoc, show (n-1)/6 = q from rfl, he]
      exact mul_le_mul_of_nonneg_left hint hnm

end PHP
