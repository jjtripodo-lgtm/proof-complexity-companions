import PHP.SampledStep
import PHP.RowMonotonicity
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.Complex.ExponentialBounds

namespace PHP
open Finset
open scoped BigOperators

private theorem choose_linear_bound {d b : ℕ} (hd : 2 ≤ d) (hb : 0 < b) :
    ((b*d).choose (b+1):ℝ) ≤ (4*(d:ℝ))^(b+1) := by
  have hden : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  let r := b*d
  have hr : b+1 ≤ r := by dsimp [r]; nlinarith
  have hterm : (d:ℝ)⁻¹^(b+1) * 1^(r-(b+1)) * (r.choose (b+1):ℝ)
      ≤ ((d:ℝ)⁻¹+1)^r := by
    rw [add_pow]
    apply Finset.single_le_sum (f:=fun j => (d:ℝ)⁻¹^j * 1^(r-j) * (r.choose j:ℝ))
    · intro i hi
      positivity
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hr)
  have he : (d:ℝ)⁻¹+1 ≤ Real.exp ((d:ℝ)⁻¹) := Real.add_one_le_exp _
  have hh : ((d:ℝ)⁻¹+1)^r ≤ (4:ℝ)^b := by
    calc
      _ ≤ (Real.exp ((d:ℝ)⁻¹))^r := pow_le_pow_left₀ (by positivity) he _
      _ = Real.exp (b:ℝ) := by
        rw [←Real.exp_nat_mul]
        congr 1
        simp [r,hden.ne']
      _ = (Real.exp 1)^b := by rw [← mul_one (b:ℝ),Real.exp_nat_mul]
      _ ≤ _ := pow_le_pow_left₀ (by positivity) (by linarith [Real.exp_one_lt_d9]) _
  simp only [one_pow,mul_one,inv_pow] at hterm
  have ht : (r.choose (b+1):ℝ) ≤ (4:ℝ)^b * (d:ℝ)^(b+1) := by
    apply (div_le_iff₀ (by positivity : (0:ℝ) < (d:ℝ)^(b+1))).mp
    simpa [div_eq_mul_inv,mul_comm] using hterm.trans hh
  apply ht.trans
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Nat.le_succ _)) (by positivity)

noncomputable def growthBase (t : ℕ) : ℝ := 1+(t:ℝ)⁻¹

def rowMultiplier (t : ℕ) : ℕ := 8*(2*t+1)^2

noncomputable def collisionBase (t : ℕ) : ℝ := (4*(rowMultiplier t:ℝ))^2*256

private theorem growth_params {t b : ℕ} (ht : 0 < t) (hb : 0 < b) :
    let a := growthBase t
    let d := rowMultiplier t
    1 < a ∧ a ≤ 2 ∧ 2 ≤ d ∧
      (b:ℝ) - ((a-1)/(a+1))^2 * (↑(b*d):ℝ)/2 ≤ -(b:ℝ)-1 := by
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
    have he : ((2*(t:ℝ)+1)⁻¹)^2 * ((b:ℝ)*(8*(2*(t:ℝ)+1)^2))/2 = 4*b := by
      have hh : 0 < 2*(t:ℝ)+1 := by positivity
      field_simp
      <;> ring
    rw [he]
    have hB : (1:ℝ) ≤ b := by exact_mod_cast hb
    linarith

private theorem collision_base_large (t : ℕ) : (512:ℝ) ≤ collisionBase t := by
  have h : (8:ℝ) ≤ rowMultiplier t := by
    exact_mod_cast (show 8 ≤ rowMultiplier t by
      unfold rowMultiplier
      exact Nat.le_mul_of_pos_right _ (by positivity))
  unfold collisionBase
  nlinarith [sq_nonneg ((rowMultiplier t:ℝ)-8)]

private theorem seed_le_b {n b : ℕ} (hb : 0 < b) (hn : n ≤ b) :
    (2:ℝ)^(8*n)+2^(n+1)-1 ≤ 512^b := by
  have h1 := pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num) (show 8*n ≤ 8*b by omega)
  have h2 := pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num) (show n+1 ≤ 8*b by omega)
  have h3 := pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num) (show 8*b+1 ≤ 9*b by omega)
  rw [pow_succ, pow_mul (2:ℝ) 9 b, show (2:ℝ)^9 = 512 by norm_num] at h3
  linarith

/-- An explicit, finite certificate bound after b-column elimination.
The iteration is on the original board and uses no limit of certificates. -/
theorem plain_batch_iteration {t b : ℕ} (ht : 0 < t) (hb : 0 < b) :
    let d := rowMultiplier t
    let a := growthBase t
    let P := (d:ℝ)^(2*t)*(collisionBase t)^b
    ∀ i ≤ t, ∀ n ≤ (i+1)*b,
      BoundedCombination (@Plain (b*d^(i+1)) n) (fun _ => 1) ((4*a^b)^i*(5*P)) := by
  dsimp only
  let d := rowMultiplier t
  let a := growthBase t
  let P := (d:ℝ)^(2*t)*(collisionBase t)^b
  obtain ⟨ha,ha2,hd,htail⟩ := growth_params ht hb
  change 1 < a at ha
  change a ≤ 2 at ha2
  change 2 ≤ d at hd
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hP : (512:ℝ)^b ≤ P := by
    calc
      _ ≤ (collisionBase t)^b := pow_le_pow_left₀ (by norm_num) (collision_base_large t) _
      _ ≤ _ := le_mul_of_one_le_left (pow_nonneg ((by norm_num : (0:ℝ) ≤ 512).trans (collision_base_large t)) _) (one_le_pow₀ hd1)
  have hp : 1 ≤ P := (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 512)).trans hP
  have hA : 1 ≤ a^b := one_le_pow₀ ha.le
  have hc : 1 ≤ 4*a^b := by linarith
  have hc' (i : ℕ) : 5*P ≤ (4*a^b)^i*(5*P) :=
    le_mul_of_one_le_left (by linarith) (one_le_pow₀ hc)
  have hm {i n : ℕ} (hin : n ≤ (i+1)*b) : n < b*d^(i+1) := by
    have hpow : i+1 < d^(i+1) :=
      Nat.lt_pow_self (by omega)
    have h := Nat.mul_lt_mul_of_pos_right hpow hb
    rw [mul_comm (d^(i+1)) b] at h
    exact hin.trans_lt h
  intro i
  induction i with
  | zero =>
    intro hi n hn
    exact (plain_exponential_seed (hm hn)).cost_mono (by
      simp only [pow_zero,one_mul]
      have hh := (seed_le_b hb (by simpa using hn)).trans hP
      linarith)
  | succ i IH =>
    intro hi n hn
    by_cases hnb : n ≤ b
    · exact (plain_exponential_seed (hm hn)).cost_mono (by
        have hh := (seed_le_b hb hnb).trans hP
        exact hh.trans ((by linarith : P ≤ 5*P).trans (hc' _)))
    let B := (4*a^b)^i*(5*P)
    have hsub := IH (by omega : i ≤ t) (n-b) (by
      have h : (i+1+1)*b = (i+1)*b+b := by ring
      omega)
    have hstep := sampled_block_step (r:=b*d) (K:=d^(i+1)) (k:=b) (n:=n) hb
      (by omega) (by simpa [pow_succ,mul_left_comm,mul_assoc,mul_comm] using hm hn)
      ha ha2 htail hsub
    have hr : b*d*d^(i+1) = b*d^(i+1+1) := by rw [pow_succ]; ring
    rw [hr] at hstep
    apply hstep.cost_mono
    change 2*(a^b*B+(1+a^b)*(( (b*d).choose (b+1):ℝ)*(((d^(i+1):ℕ):ℝ)^2*2^(8*b))))+1
      ≤ (4*a^b)^(i+1)*(5*P)
    have hcap : (((b*d).choose (b+1):ℝ)*(((d^(i+1):ℕ):ℝ)^2*2^(8*b))) ≤ P := by
      push_cast
      have hh : (4*(d:ℝ))^(b+1) ≤ (4*(d:ℝ))^(2*b) :=
        pow_le_pow_right₀ (by linarith) (by omega)
      have hj : ((d:ℝ)^(i+1))^2 ≤ (d:ℝ)^(2*t) := by
        rw [← pow_mul]
        exact pow_le_pow_right₀ hd1 (by omega)
      have hk := mul_le_mul ((choose_linear_bound hd hb).trans hh)
        (mul_le_mul_of_nonneg_right hj (show (0:ℝ) ≤ 2^(8*b) by positivity)) (by positivity) (by positivity)
      rw [pow_mul (4*(d:ℝ)) 2 b,pow_mul (2:ℝ) 8 b] at hk
      rw [show (2:ℝ)^8 = 256 by norm_num] at hk
      rw [pow_mul (2:ℝ) 8 b, show (2:ℝ)^8 = 256 by norm_num]
      dsimp [P,collisionBase]
      change _ ≤ (d:ℝ)^(2*t)*((4*(d:ℝ))^2*256)^b
      rw [mul_pow]
      exact hk.trans_eq (by ac_rfl)
    have hB : 5*P ≤ B := hc' i
    have hcap' : 0 ≤ (((b*d).choose (b+1):ℝ)*(((d^(i+1):ℕ):ℝ)^2*2^(8*b))) := by positivity
    have hp2 := mul_le_mul_of_nonneg_left hcap (show 0 ≤ 1+a^b by linarith)
    have hs := mul_le_mul_of_nonneg_left hB (show 0 ≤ a^b by linarith)
    have hr' : (4*a^b)^(i+1)*(5*P) = 4*a^b*B := by rw [pow_succ]; dsimp [B]; ring
    rw [hr']
    nlinarith [mul_le_mul_of_nonneg_right hA (show 0 ≤ P by linarith)]

end PHP
