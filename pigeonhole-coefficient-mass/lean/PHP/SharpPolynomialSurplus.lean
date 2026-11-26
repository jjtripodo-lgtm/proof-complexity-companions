import PHP.SharpIteration
import PHP.PhaseDiagram
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring

namespace PHP
open Filter
open scoped Topology

private theorem rowMultiplier_log_le {t : ℕ} (ht : 1 ≤ t) :
    Real.log (rowMultiplier t:ℝ) ≤ Real.log 72 + 2*Real.log (t:ℝ) := by
  have hT : 1 ≤ (t:ℝ) := by exact_mod_cast ht
  have ht' : 0 < (t:ℝ) := by linarith
  have hd : 0 < (rowMultiplier t:ℝ) := by
    exact_mod_cast (show 0 < rowMultiplier t by unfold rowMultiplier; positivity)
  have hh : (rowMultiplier t:ℝ) ≤ 72*(t:ℝ)^2 := by
    unfold rowMultiplier
    push_cast
    have h := pow_le_pow_left₀ (show 0 ≤ 2*(t:ℝ)+1 by positivity)
      (show 2*(t:ℝ)+1 ≤ 3*(t:ℝ) by linarith) 2
    nlinarith
  have h := Real.log_le_log hd hh
  rw [Real.log_mul (by norm_num : (72:ℝ) ≠ 0) (pow_ne_zero _ ht'.ne'),Real.log_pow] at h
  exact h

theorem sharp_explicit_log {m n t : ℕ} (ht : 0 < t) (hnm : n < m)
    (hm : (n+1)*rowMultiplier t^t ≤ m) :
    Real.log (optimalPlainMass m n) ≤ Real.log 40 + 2*Real.log ((n+1:ℕ):ℝ) +
      (t:ℝ)*(Real.log 4+2*Real.log (rowMultiplier t:ℝ)) +
      ((n/t+1:ℕ):ℝ)*Real.log 32768 := by
  obtain ⟨s,r,hr⟩ := plain_sharp_upper_explicit ht hm
  have hopt := (optimal_plain_le_certificate r).trans hr
  have hlog := Real.log_le_log (zero_lt_one.trans_le (optimal_plain_one_le hnm)) hopt
  have hg : 0 < (rowMultiplier t:ℝ) := by
    exact_mod_cast (show 0 < rowMultiplier t by unfold rowMultiplier; positivity)
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num) (by positivity)] at hlog
  simp only [Real.log_pow] at hlog
  rw [Real.log_mul (by norm_num : (4:ℝ) ≠ 0) (by positivity),Real.log_pow] at hlog
  exact hlog

private theorem eventually_surplus_tuning (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧ 1 ≤ Real.log (Real.log (n:ℝ)) ∧ Real.log (n:ℝ) ≤
      (n:ℝ)*Real.log (Real.log (n:ℝ))/Real.log (n:ℝ) ∧
      ∃ t : ℕ, 0 < t ∧ (t:ℝ) ≤ Real.log (n:ℝ) ∧
        (t:ℝ)*Real.log (rowMultiplier t:ℝ) ≤ (ε/2)*Real.log (n:ℝ) ∧
        (t:ℝ)*Real.log (rowMultiplier t:ℝ) ≤ 3*Real.log (n:ℝ) ∧
        (n:ℝ)/(t:ℝ) ≤ (2/min 1 (ε/8))*
          ((n:ℝ)*Real.log (Real.log (n:ℝ))/Real.log (n:ℝ)) ∧
        (((n+1)*rowMultiplier t^t:ℕ):ℝ) ≤ (n:ℝ)^(1+ε) := by
  let c := min (1:ℝ) (ε/8)
  have hc : 0 < c := lt_min zero_lt_one (by positivity)
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcE : c ≤ ε/8 := min_le_right _ _
  have hcast : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog := Real.tendsto_log_atTop.comp hcast
  have hloglog := Real.tendsto_log_atTop.comp hlog
  have h1 := hlog.eventually_ge_atTop 1
  have h2 := hloglog.eventually_ge_atTop (max 1 (Real.log 72))
  have h3 := hlog.eventually_ge_atTop (4*Real.log 2/ε)
  have hLogDiv : Tendsto (fun x : ℝ => Real.log x/x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h4 := (hLogDiv.comp hlog).eventually (eventually_lt_nhds (show (0:ℝ)<c/2 by positivity))
  have h5' : Tendsto (fun x : ℝ => (Real.log x)^2/x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have h5 := (h5'.comp hcast).eventually (eventually_lt_nhds (show (0:ℝ)<1 by norm_num))
  filter_upwards [eventually_ge_atTop (2:ℕ),h1,h2,h3,h4,h5] with n hn hN hY hX hSmall hPow
  let X := Real.log (n:ℝ)
  let Y := Real.log X
  have hX1 : 1 ≤ X := hN
  have hX0 : 0 < X := by linarith
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hY
  have hY0 : 0 < Y := by linarith
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hPow' : X^2 ≤ (n:ℝ) := by
    change X^2/(n:ℝ) < 1 at hPow
    have h := (div_lt_iff₀ hnR).mp hPow
    linarith
  have hxy : X ≤ (n:ℝ)*Y/X := by
    apply (le_div_iff₀ hX0).mpr
    have h := mul_le_mul_of_nonneg_left hY1 hnR.le
    nlinarith
  refine ⟨hn,hY1,hxy,?_⟩
  let q := c*X/Y
  let t := ⌊q⌋₊
  have hq : 2 < q := by
    change Y/X < c/2 at hSmall
    have hh := (div_lt_iff₀ hX0).mp hSmall
    exact (lt_div_iff₀ hY0).mpr (by linarith)
  have ht0 : 0 < t := Nat.floor_pos.mpr (by linarith)
  have htR : 0 < (t:ℝ) := by exact_mod_cast ht0
  have hl : (t:ℝ) ≤ q := Nat.floor_le (by linarith)
  have hq' : q/2 ≤ (t:ℝ) := by
    have h := Nat.lt_floor_add_one q
    change q < (t:ℝ)+1 at h
    linarith
  have hTX : (t:ℝ) ≤ X := by
    apply hl.trans
    apply (div_le_iff₀ hY0).mpr
    have h1 := mul_le_mul_of_nonneg_right hc1 hX0.le
    have h2 := mul_le_mul_of_nonneg_left hY1 hX0.le
    linarith
  have hD : Real.log (rowMultiplier t:ℝ) ≤ 3*Y := by
    have h := rowMultiplier_log_le (by omega : 1 ≤ t)
    have hl := Real.log_le_log htR hTX
    change Real.log (t:ℝ) ≤ Y at hl
    have h72 : Real.log 72 ≤ Y := (le_max_right _ _).trans hY
    linarith
  have hTY : (t:ℝ)*Y ≤ c*X := by
    have hh := (le_div_iff₀ hY0).mp hl
    exact hh
  have htd : (t:ℝ)*Real.log (rowMultiplier t:ℝ) ≤ 3*c*X := by
    have h := mul_le_mul_of_nonneg_left hD htR.le
    linarith
  have htdE : (t:ℝ)*Real.log (rowMultiplier t:ℝ) ≤ ε/2*X := by
    have h := mul_le_mul_of_nonneg_right hcE hX0.le
    nlinarith [mul_nonneg hε.le hX0.le]
  have htdX : (t:ℝ)*Real.log (rowMultiplier t:ℝ) ≤ 3*X := by
    have h := mul_le_mul_of_nonneg_right hc1 hX0.le
    linarith
  have hRecip : (n:ℝ)/(t:ℝ) ≤ (2/c)*((n:ℝ)*Y/X) := by
    have hprod : c*X ≤ 2*(t:ℝ)*Y := by
      have h : c*X/Y ≤ 2*(t:ℝ) := by change q ≤ _; linarith
      exact (div_le_iff₀ hY0).mp h
    apply (div_le_iff₀ htR).mpr
    have he : 2/c*((n:ℝ)*Y/X)*(t:ℝ) = (n:ℝ)/(c*X)*(2*(t:ℝ)*Y) := by field_simp
    rw [he]
    exact (show (n:ℝ)/(c*X)*(c*X) = n by field_simp).ge.trans
      (mul_le_mul_of_nonneg_left hprod (by positivity))
  have hrow : (((n+1)*rowMultiplier t^t:ℕ):ℝ) ≤ (n:ℝ)^(1+ε) := by
    have hd0 : (0:ℝ) < rowMultiplier t := by
      exact_mod_cast (show 0 < rowMultiplier t by unfold rowMultiplier; positivity)
    have hz : 0 < (((n+1)*rowMultiplier t^t:ℕ):ℝ) := by
      push_cast
      positivity
    apply (Real.log_le_log_iff hz (Real.rpow_pos_of_pos hnR _)).mp
    push_cast
    rw [Real.log_mul (by positivity) (pow_ne_zero _ hd0.ne'),Real.log_pow,Real.log_rpow hnR]
    have hnr : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have he := Real.log_le_log (show 0 < (n:ℝ)+1 by positivity) (show (n:ℝ)+1 ≤ 2*(n:ℝ) by linarith)
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hnR.ne'] at he
    change 4*Real.log 2/ε ≤ X at hX
    have h := (div_le_iff₀ hε).mp hX
    change Real.log ((n:ℝ)+1) ≤ Real.log 2+X at he
    change Real.log ((n:ℝ)+1)+(t:ℝ)*Real.log (rowMultiplier t:ℝ) ≤ (1+ε)*X
    nlinarith [mul_nonneg hε.le hX0.le]
  exact ⟨t,ht0,hTX,htdE,htdX,hRecip,hrow⟩

/-- Exact quantitative upper in the paper's polynomial-surplus regime:
for fixed ε>0, log T is Oε(n log log n/log n), uniformly over all m≥n^(1+ε). -/
theorem plain_polynomial_surplus_log_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
      n < m → (n:ℝ)^(1+ε) ≤ (m:ℝ) →
      Real.log (optimalPlainMass m n) ≤
        K*((n:ℝ)*Real.log (Real.log (n:ℝ))/Real.log (n:ℝ)) := by
  let c := min (1:ℝ) (ε/8)
  let K := Real.log 40 + 2*Real.log 2 + Real.log 4 + 8 +
    Real.log 32768 + (2/c)*Real.log 32768
  have hc : 0 < c := lt_min zero_lt_one (by positivity)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hl40 : 0 < Real.log 40 := Real.log_pos (by norm_num)
  have hl32 : 0 < Real.log 32768 := Real.log_pos (by norm_num)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  have hX := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1
  filter_upwards [eventually_surplus_tuning ε hε,hX] with n h hX
  obtain ⟨hn,hY,hs, t,ht,htX,htD,htD',hRecip,hrow⟩ := h
  intro m hnm hm
  have hrow' : (n+1)*rowMultiplier t^t ≤ m := by exact_mod_cast hrow.trans hm
  have h := sharp_explicit_log ht hnm hrow'
  let X := Real.log (n:ℝ)
  let Y := Real.log X
  let S := (n:ℝ)*Y/X
  have hSX : X ≤ S := hs
  have hX1 : 1 ≤ X := hX
  have hS : 1 ≤ S := hX1.trans hSX
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have ht0 : 0 < (t:ℝ) := by exact_mod_cast ht
  have hln : Real.log ((n+1:ℕ):ℝ) ≤ Real.log 2+X := by
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have h := Real.log_le_log (show 0 < ((n+1:ℕ):ℝ) by positivity)
      (show ((n+1:ℕ):ℝ) ≤ 2*(n:ℝ) by push_cast; linarith)
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hn0.ne'] at h
    exact h
  have hdiv : ((n/t+1:ℕ):ℝ) ≤ (2/c)*S+1 := by
    have he : (↑(n/t:ℕ):ℝ) ≤ (n:ℝ)/t := (le_div_iff₀ ht0).mpr (by exact_mod_cast Nat.div_mul_le_self n t)
    have hrec : (n:ℝ)/t ≤ (2/c)*S := hRecip
    push_cast
    linarith
  have hLogT : (t:ℝ)*Real.log 4 ≤ Real.log 4 * S := by
    exact (mul_le_mul_of_nonneg_right (htX.trans hSX) hl4.le).trans_eq (by ring)
  have hDivLog := mul_le_mul_of_nonneg_right hdiv hl32.le
  have hConst := mul_le_mul_of_nonneg_left hS (show 0 ≤ Real.log 40+2*Real.log 2+Real.log 32768 by positivity)
  change _ ≤ K*S
  unfold K
  change (t:ℝ)*Real.log (rowMultiplier t:ℝ) ≤ 3*X at htD'
  nlinarith

end PHP
