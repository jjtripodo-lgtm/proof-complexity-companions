import PHP.MaskContraction
import PHP.UpperIteration

namespace PHP

private theorem rate_stage_parameters {t k b : ℕ} (ht : 0 < t) (hb : 0 < b) (hkb : b ≤ k) :
    let a := growthBase t
    let d := rowMultiplier t
    1 < a ∧ a ≤ 2 ∧ 2 ≤ d ∧
      (k:ℝ) - ((a-1)/(a+1))^2 * (↑(d*k):ℝ)/2 ≤ -(b:ℝ)-1 := by
  dsimp only
  have ht' : 0 < (t:ℝ) := by exact_mod_cast ht
  have ht1 : 1 ≤ (t:ℝ) := by exact_mod_cast ht
  refine ⟨?_,?_,?_,?_⟩
  · unfold growthBase
    linarith [inv_pos.mpr ht']
  · unfold growthBase
    linarith [inv_le_one_of_one_le₀ ht1]
  · unfold rowMultiplier
    nlinarith
  · have hbase : (growthBase t-1)/(growthBase t+1) = (2*(t:ℝ)+1)⁻¹ := by
      unfold growthBase
      have h : 0 < (t:ℝ)⁻¹ := inv_pos.mpr ht'
      have h1 : 0 < 1+(t:ℝ)⁻¹+1 := by positivity
      have h2 : 0 < 2*(t:ℝ)+1 := by positivity
      field_simp
      ring
    rw [hbase]
    simp only [rowMultiplier,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one]
    have he : ((2*(t:ℝ)+1)⁻¹)^2 * ((8*(2*(t:ℝ)+1)^2)*(k:ℝ))/2 = 4*k := by
      have hh : 0 < 2*(t:ℝ)+1 := by positivity
      field_simp
      <;> ring
    rw [he]
    have hB : (1:ℝ) ≤ b := by exact_mod_cast hb
    have hK : (b:ℝ) ≤ k := by exact_mod_cast hkb
    linarith

private theorem seed_small {n b : ℕ} (hb : 0 < b) (hn : n ≤ b) :
    (2:ℝ)^(8*n)+2^(n+1)-1 ≤ 512^b := by
  have h1 := pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num) (show 8*n ≤ 8*b by omega)
  have h2 := pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num) (show n+1 ≤ 8*b by omega)
  have h3 := pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num) (show 8*b+1 ≤ 9*b by omega)
  rw [pow_succ,pow_mul (2:ℝ) 9 b,show (2:ℝ)^9 = 512 by norm_num] at h3
  linarith

private theorem precise_mass_iteration {t b n₀ : ℕ} (ht : 0 < t) (hb : 0 < b)
    (hbn : b ≤ n₀+1) :
    let d := rowMultiplier t
    let a := growthBase t
    let P := 8*((n₀+1:ℕ):ℝ)^2*(d:ℝ)^(2*t)*(8192:ℝ)^b
    ∀ i ≤ t, ∀ n ≤ (i+1)*b, n ≤ n₀ →
      BoundedCombination (@Plain ((n₀+1)*d^i) n) (fun _ => 1) ((4*a^b)^i*(5*P)) := by
  dsimp only
  let d := rowMultiplier t
  let a := growthBase t
  let P := 8*((n₀+1:ℕ):ℝ)^2*(d:ℝ)^(2*t)*(8192:ℝ)^b
  obtain ⟨ha,ha2,hd,_⟩ := rate_stage_parameters (k:=b) ht hb (show b ≤ b from le_rfl)
  change 1 < a at ha
  change a ≤ 2 at ha2
  change 2 ≤ d at hd
  have hd1 : 1 ≤ d := by omega
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd1
  have hN : (1:ℝ) ≤ ((n₀+1:ℕ):ℝ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n₀))
  have hPre : 1 ≤ 8*((n₀+1:ℕ):ℝ)^2*(d:ℝ)^(2*t) := by
    have hN' := one_le_pow₀ (n:=2) hN
    have hD := one_le_pow₀ (n:=2*t) hdR
    exact one_le_mul_of_one_le_of_one_le (by linarith) hD
  have hP : (512:ℝ)^b ≤ P := by
    calc
      _ ≤ (8192:ℝ)^b := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ ≤ _ := le_mul_of_one_le_left (by positivity) hPre
  have hp : 1 ≤ P := (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 512)).trans hP
  have hA : 1 ≤ a^b := one_le_pow₀ ha.le
  have hc : 1 ≤ 4*a^b := by linarith
  have hc' (i : ℕ) : 5*P ≤ (4*a^b)^i*(5*P) :=
    le_mul_of_one_le_left (by linarith) (one_le_pow₀ hc)
  have hdval (i : ℕ) : 1 ≤ d^i := one_le_pow₀ hd1
  have hm (i n : ℕ) (hn : n ≤ n₀) : n < (n₀+1)*d^i :=
    (Nat.lt_succ_of_le hn).trans_le (Nat.le_mul_of_pos_right _ (by have := hdval i; omega))
  intro i
  induction i with
  | zero =>
    intro hi n hn hn0
    exact (plain_exponential_seed (hm 0 n hn0)).cost_mono (by
      simp only [pow_zero,one_mul]
      have hh := (seed_small hb (by simpa using hn)).trans hP
      linarith)
  | succ i IH =>
    intro hi n hn hn0
    by_cases hnb : n ≤ b
    · exact (plain_exponential_seed (hm _ _ hn0)).cost_mono (by
        have hh := (seed_small hb hnb).trans hP
        exact hh.trans ((by linarith : P ≤ 5*P).trans (hc' _)))
    let B := (4*a^b)^i*(5*P)
    let k := (n₀+1)*d^i
    let m := (n₀+1)*d^(i+1)
    have hmk : m = d*k := by unfold m k; rw [pow_succ]; ring
    have hk : b ≤ k := hbn.trans (Nat.le_mul_of_pos_right _ (by have := hdval i; omega))
    have hmN : n < m := hm _ _ hn0
    have hsub := IH (by omega : i ≤ t) (n-b) (by
      have h : (i+1+1)*b = (i+1)*b+b := by ring
      omega) (by omega)
    obtain ⟨_,_,_,htail⟩ := rate_stage_parameters ht hb hk
    rw [←show m = rowMultiplier t*k from hmk] at htail
    have hStep := sharp_sampled_step (m:=m) (n:=n) (k:=k) hb (by omega) hmN ha ha2 htail hsub
    apply hStep.cost_mono
    change 2*(a^b*B+(1+a^b)*coupledConstant m b)+1 ≤ (4*a^b)^(i+1)*(5*P)
    have hCap : coupledConstant m b ≤ P := by
      have hM : (0:ℝ) ≤ m := by positivity
      have hMax : (m:ℝ) ≤ ((n₀+1:ℕ):ℝ)*(d:ℝ)^t := by
        unfold m
        push_cast
        apply mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hdR hi) (by positivity)
      have hM2 : (m:ℝ)*((m:ℝ)-1) ≤ (((n₀+1:ℕ):ℝ)*(d:ℝ)^t)^2 := by
        have h1 := pow_le_pow_left₀ hM hMax 2
        nlinarith
      have h := mul_le_mul_of_nonneg_left hM2 (show 0 ≤ 8*(8:ℝ)^b*2^(10*b) by positivity)
      unfold coupledConstant
      refine h.trans_eq ?_
      have he : (8:ℝ)^b*2^(10*b) = (8192:ℝ)^b := by
        rw [pow_mul (2:ℝ) 10 b,←mul_pow,show (8:ℝ)*2^10=8192 by norm_num]
      rw [mul_assoc (8:ℝ),he,mul_pow,←pow_mul]
      unfold P
      rw [Nat.mul_comm t 2]
      ring
    have hB : 5*P ≤ B := hc' i
    have hCap' := mul_le_mul_of_nonneg_left hCap (show 0 ≤ 1+a^b by linarith)
    have hBB := mul_le_mul_of_nonneg_left hB (show 0 ≤ a^b by linarith)
    have he : (4*a^b)^(i+1)*(5*P) = 4*a^b*B := by rw [pow_succ]; dsimp [B]; ring
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_right hA (show 0 ≤ P by linarith)]

/-- An explicit uniform bound giving log T = O(n/t + t log t + log n)
under a surplus row budget (n+1) d^t, with d = 8(2t+1)^2. -/
theorem plain_sharp_upper_explicit {m n t : ℕ} (ht : 0 < t)
    (hm : (n+1)*rowMultiplier t^t ≤ m) :
    ∃ (s : ℕ) (r : Refutation (@Plain m n) s),
      r.mass ≤ 40*((n+1:ℕ):ℝ)^2*(4*(rowMultiplier t:ℝ)^2)^t*(32768:ℝ)^(n/t+1) := by
  let d := rowMultiplier t
  let b := n/t+1
  have hb : 0 < b := Nat.zero_lt_succ _
  have hbn : b ≤ n+1 := Nat.succ_le_succ (Nat.div_le_self n t)
  have hn : n ≤ (t+1)*b := by
    have he : n % t + t*(n/t) = n := Nat.mod_add_div n t
    have hlt : n % t < t := Nat.mod_lt n ht
    have hh : t*b = t*(n/t)+t := by dsimp [b]; ring
    calc
      n ≤ t*b := by omega
      _ ≤ (t+1)*b := Nat.mul_le_mul_right _ (by omega)
  have h := precise_mass_iteration (n₀:=n) ht hb hbn t le_rfl n hn le_rfl
  obtain ⟨s,r,hr⟩ := h.refutation
  refine ⟨s,r.addPlainRows (Fin.castLEEmb hm),?_⟩
  rw [addPlainRows_preserves_mass]
  apply hr.trans
  have ht0 : (0:ℝ) < t := by exact_mod_cast ht
  have h1 : (growthBase t)^t ≤ 4 := by
    calc
      _ ≤ (Real.exp ((t:ℝ)⁻¹))^t := pow_le_pow_left₀ (by unfold growthBase; positivity)
        (by simpa [growthBase,add_comm] using Real.add_one_le_exp ((t:ℝ)⁻¹)) _
      _ = Real.exp 1 := by rw [←Real.exp_nat_mul,mul_inv_cancel₀ ht0.ne']
      _ ≤ _ := by linarith [Real.exp_one_lt_d9]
  have he : (((growthBase t)^b)^t) ≤ (4:ℝ)^b := by
    rw [←pow_mul,mul_comm b t,pow_mul]
    exact pow_le_pow_left₀ (by unfold growthBase; positivity) h1 _
  change (4*growthBase t^b)^t*(5*(8*((n+1:ℕ):ℝ)^2*(d:ℝ)^(2*t)*(8192:ℝ)^b)) ≤
    40*((n+1:ℕ):ℝ)^2*(4*(d:ℝ)^2)^t*(32768:ℝ)^b
  rw [mul_pow]
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by positivity : (0:ℝ) ≤ 4^t))
    (show 0 ≤ 5*(8*((n+1:ℕ):ℝ)^2*(d:ℝ)^(2*t)*(8192:ℝ)^b) by positivity)
  refine h.trans_eq ?_
  rw [mul_pow,←pow_mul,show (32768:ℝ)=4*8192 by norm_num,mul_pow]
  ring

end PHP
