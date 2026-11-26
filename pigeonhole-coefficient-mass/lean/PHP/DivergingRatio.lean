import PHP.UpperIteration
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace PHP
open Filter
open scoped Topology

noncomputable def finalBase (t : ℕ) : ℝ := 4*collisionBase t
noncomputable def finalPrefactor (t : ℕ) : ℝ :=
  5 * (rowMultiplier t:ℝ)^(2*t) * (4:ℝ)^t

private theorem final_base_one (t : ℕ) : 1 ≤ finalBase t := by
  have h : (1:ℝ) ≤ rowMultiplier t := by
    exact_mod_cast (show 1 ≤ rowMultiplier t by
      unfold rowMultiplier
      exact (by decide : 1 ≤ 8).trans (Nat.le_mul_of_pos_right _ (by positivity)))
  unfold finalBase collisionBase
  nlinarith [sq_nonneg ((rowMultiplier t:ℝ)-1)]

private theorem final_prefactor_pos (t : ℕ) : 0 < finalPrefactor t := by
  have h : (0:ℝ) < rowMultiplier t := by
    exact_mod_cast (show 0 < rowMultiplier t by unfold rowMultiplier; positivity)
  unfold finalPrefactor
  positivity

theorem plain_batch_explicit {m n t : ℕ} (ht : 0 < t)
    (hm : (n/t+1)*rowMultiplier t^(t+1) ≤ m) :
    ∃ (s : ℕ) (r : Refutation (@Plain m n) s),
      r.mass ≤ finalPrefactor t * (finalBase t)^(n/t+1) := by
  let b := n/t+1
  have hb : 0 < b := Nat.zero_lt_succ _
  have hn : n ≤ (t+1)*b := by
    have he : n % t + t*(n/t) = n := Nat.mod_add_div n t
    have hlt : n % t < t := Nat.mod_lt n ht
    have hh : t*b = t*(n/t)+t := by dsimp [b]; ring
    calc
      n ≤ t*b := by omega
      _ ≤ (t+1)*b := Nat.mul_le_mul_right _ (by omega)
  have h := plain_batch_iteration ht hb t le_rfl n hn
  obtain ⟨s,r,hr⟩ := h.refutation
  refine ⟨s,r.addPlainRows (Fin.castLEEmb hm),?_⟩
  rw [addPlainRows_preserves_mass]
  apply hr.trans
  have ht0 : (0:ℝ) < t := by exact_mod_cast ht
  have h1 : (growthBase t)^t ≤ 4 := by
    calc
      _ ≤ (Real.exp ((t:ℝ)⁻¹))^t := pow_le_pow_left₀ (by unfold growthBase; positivity)
        (by simpa [growthBase,add_comm] using Real.add_one_le_exp ((t:ℝ)⁻¹)) _
      _ = Real.exp 1 := by rw [← Real.exp_nat_mul, mul_inv_cancel₀ ht0.ne']
      _ ≤ _ := by linarith [Real.exp_one_lt_d9]
  have he : (((growthBase t)^b)^t) ≤ (4:ℝ)^b := by
    rw [←pow_mul, mul_comm b t,pow_mul]
    exact pow_le_pow_left₀ (by unfold growthBase; positivity) h1 _
  have ha : 0 ≤ (collisionBase t)^b := by
    unfold collisionBase
    positivity
  change (4*growthBase t^b)^t*(5*((rowMultiplier t:ℝ)^(2*t)*collisionBase t^b)) ≤
    finalPrefactor t * finalBase t^b
  unfold finalPrefactor finalBase
  rw [mul_pow,mul_pow]
  calc
    _ ≤ (4:ℝ)^t*4^b*(5*((rowMultiplier t:ℝ)^(2*t)*collisionBase t^b)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by positivity)) (by positivity)
    _ = _ := by ring

private theorem final_base_polynomial {t : ℕ} (ht : 0 < t) :
    finalBase t ≤ 100000000 * (t:ℝ)^4 := by
  have h1 : (1:ℝ) ≤ t := by exact_mod_cast ht
  have h : (2*(t:ℝ)+1)^2 ≤ (3*(t:ℝ))^2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have hs : ((2*(t:ℝ)+1)^2)^2 ≤ ((3*(t:ℝ))^2)^2 :=
    pow_le_pow_left₀ (by positivity) h _
  unfold finalBase collisionBase rowMultiplier
  push_cast
  have hg : (t:ℝ)^4 ≥ 0 := by positivity
  have hl : (4*(8*(2*(t:ℝ)+1)^2))^2 = 1024*((2*(t:ℝ)+1)^2)^2 := by ring
  rw [hl]
  have hr : ((3*(t:ℝ))^2)^2 = 81*(t:ℝ)^4 := by ring
  rw [hr] at hs
  linarith

private theorem tune_block_parameter {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℕ, 0 < t ∧ Real.log (finalBase t) ≤ ε*(t:ℝ)/2 := by
  have h : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have he : ∀ᶠ x : ℝ in atTop, Real.log x / x < ε/16 :=
    h.eventually (eventually_lt_nhds (by positivity : (0:ℝ) < ε/16))
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  let C := Real.log 100000000
  obtain ⟨t,ht⟩ := exists_nat_gt (max 1 (max N (4*C/ε)))
  have ht1 : (1:ℝ) < t := (le_max_left _ _).trans_lt ht
  have ht0 : 0 < t := by exact_mod_cast (show (0:ℝ) < t by linarith)
  have htN : N ≤ t := ((le_max_left _ _).trans (le_max_right _ _)).trans ht.le
  have htC : 4*C/ε ≤ t := ((le_max_right _ _).trans (le_max_right _ _)).trans ht.le
  have hl := (div_lt_iff₀ (show (0:ℝ) < t by linarith)).mp (hN t htN)
  have hc := (div_le_iff₀ hε).mp htC
  refine ⟨t,ht0,?_⟩
  have hpoly := Real.log_le_log (show 0 < finalBase t from zero_lt_one.trans_le (final_base_one t))
    (final_base_polynomial ht0)
  rw [Real.log_mul (by norm_num : (100000000:ℝ) ≠ 0)
    (by positivity : (t:ℝ)^4 ≠ 0), Real.log_pow] at hpoly
  change _ ≤ C+4*Real.log (t:ℝ) at hpoly
  linarith

/-- For any desired linear log-mass rate, a sufficiently large constant
surplus ratio already suffices; this implies the manuscript's o(n) direction
along every sequence with m/n → ∞. -/
theorem plain_diverging_ratio (ε : ℝ) (hε : 0 < ε) :
    ∃ C N : ℕ, ∀ {m n : ℕ}, N ≤ n → C*n ≤ m →
      ∃ (s : ℕ) (r : Refutation (@Plain m n) s), r.mass ≤ Real.exp (ε*n) := by
  obtain ⟨t,ht,hTune⟩ := tune_block_parameter hε
  let d := rowMultiplier t
  let P := finalPrefactor t
  let B := finalBase t
  have hB : 1 ≤ B := final_base_one t
  have hp : 0 < P := final_prefactor_pos t
  have hLog : 0 ≤ Real.log B := Real.log_nonneg hB
  let L := Real.log P + Real.log B
  obtain ⟨N,hN⟩ := exists_nat_gt (max 1 (2*L/ε))
  refine ⟨2*d^(t+1),N,?_⟩
  intro m n hn hm
  have hN1 : (1:ℝ) ≤ N := (le_max_left _ _).trans hN.le
  have hn1 : 1 ≤ n := by
    exact_mod_cast hN1.trans (by exact_mod_cast hn : (N:ℝ) ≤ n)
  have hb : n/t+1 ≤ 2*n := by
    have h := Nat.div_le_self n t
    omega
  have hmw : (n/t+1)*d^(t+1) ≤ m := by
    have h := Nat.mul_le_mul_right (d^(t+1)) hb
    exact h.trans (by convert hm using 1 <;> ring)
  obtain ⟨s,r,hr⟩ := plain_batch_explicit ht hmw
  refine ⟨s,r,hr.trans ?_⟩
  change P*B^(n/t+1) ≤ Real.exp (ε*n)
  have hεn : L ≤ ε*(n:ℝ)/2 := by
    have h : 2*L/ε ≤ (n:ℝ) := ((le_max_right _ _).trans hN.le).trans (by exact_mod_cast hn)
    have h := (div_le_iff₀ hε).mp h
    linarith
  have htR : (0:ℝ) < t := by exact_mod_cast ht
  have hb' : ((n/t+1:ℕ):ℝ) ≤ (n:ℝ)/t+1 := by
    simp only [Nat.cast_add,Nat.cast_one]
    apply add_le_add_right
    rw [le_div_iff₀ htR]
    exact_mod_cast Nat.div_mul_le_self n t
  have hprod := mul_le_mul_of_nonneg_right hb' hLog
  have hT := mul_le_mul_of_nonneg_left hTune (show (0:ℝ) ≤ (n:ℝ)/t by positivity)
  have hmul : (n:ℝ)/t*(ε*t/2) = ε*n/2 := by field_simp
  rw [hmul] at hT
  have hlogbound : Real.log P + ((n/t+1:ℕ):ℝ)*Real.log B ≤ ε*n := by
    change Real.log B ≤ ε*(t:ℝ)/2 at hTune
    change (n:ℝ)/t*Real.log B ≤ ε*n/2 at hT
    dsimp [L] at hεn
    linarith
  have he := Real.exp_le_exp.mpr hlogbound
  rw [Real.exp_add,Real.exp_log hp,Real.exp_nat_mul,Real.exp_log (zero_lt_one.trans_le hB)] at he
  exact he

end PHP
