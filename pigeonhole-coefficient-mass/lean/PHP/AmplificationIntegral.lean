import PHP.AmplificationWindow
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace PHP
open scoped BigOperators

theorem window_integral {s R : ℕ} (B : CalibratedBlock s R) (C q k : ℕ)
    (hk : Even k) (a b base : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hbase : 1 < base) (hw : ∀ x ∈ Set.Icc a b, base ≤ scoreEnvelope B C x) :
    (b-a) * a^q * base^k ≤
      ∫ x : ℝ in 0..1, x^(q+((C-1)*s)*k) * B.polynomial x^k := by
  let f : ℝ → ℝ := fun x => x^(q+((C-1)*s)*k) * B.polynomial x^k
  let D := a^q * base^k
  have hf : Continuous f := by unfold f CalibratedBlock.polynomial; fun_prop
  have hc : Continuous (fun _ : ℝ => D) := continuous_const
  have hD : ∀ x ∈ Set.Icc a b, D ≤ f x := by
    intro x hx
    have hx0 : 0 ≤ x := ha.le.trans hx.1
    have he : f x = x^q * scoreEnvelope B C x^k := by
      unfold f scoreEnvelope
      rw [pow_add,pow_mul,mul_pow]
      ring
    rw [he]
    apply mul_le_mul (pow_le_pow_left₀ ha.le hx.1 _)
      (pow_le_pow_left₀ (by linarith) (hw x hx) _)
      (by positivity) (pow_nonneg hx0 _)
  have hm := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hab.le
    (hc.intervalIntegrable _ _) (hf.intervalIntegrable _ _) hD
  have hl : 0 ≤ ∫ x : ℝ in 0..a, f x :=
    intervalIntegral.integral_nonneg ha.le
      (fun x hx => mul_nonneg (pow_nonneg hx.1 _) (hk.pow_nonneg _))
  have hr : 0 ≤ ∫ x : ℝ in b..1, f x :=
    intervalIntegral.integral_nonneg hb.le
      (fun x hx => mul_nonneg (pow_nonneg ((ha.le.trans hab.le).trans hx.1) _) (hk.pow_nonneg _))
  have hjoin := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hf.intervalIntegrable 0 a) (hf.intervalIntegrable a b)
  have hjoin' := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hf.intervalIntegrable 0 b) (hf.intervalIntegrable b 1)
  rw [intervalIntegral.integral_const,smul_eq_mul] at hm
  change (b-a)*a^q*base^k ≤ ∫ x : ℝ in 0..1, f x
  have hh : (b-a)*a^q*base^k = (b-a)*D := by unfold D; ring
  rw [hh]
  linarith

structure BlockBudget (C s R n : ℕ) where
  copies : ℕ
  slack : ℕ
  even_copies : Even copies
  column_fit : copies*s ≤ n
  row_fit : copies*R ≤ C*n-1
  column_slack : s*copies ≤ C*n-1
  exp_split : C*n-1-s*copies = slack + ((C-1)*s)*copies
  slack_bound : slack ≤ C*(2*s)
  cols_bound : n ≤ s*copies + 2*s

theorem chooseBlockBudget (C s R n : ℕ) (hC : 1 ≤ C) (hs : 0 < s)
    (hn : 1 ≤ n) (hR : R ≤ C*s) : Nonempty (BlockBudget C s R n) := by
  let d := (n-1)/(2*s)
  let u := (n-1)%(2*s)
  let k := 2*d
  let q := C*(u+1)-1
  have hu : u < 2*s := Nat.mod_lt _ (by positivity)
  have hdecomp : s*k + u + 1 = n := by
    have h := Nat.mod_add_div (n-1) (2*s)
    have he : (2*s)*d = s*k := by dsimp [k]; ring
    change u + (2*s)*d = n-1 at h
    rw [he] at h
    omega
  have hmul : C*n = C*(s*k) + C*(u+1) := by
    rw [← hdecomp]
    ring
  have hcp : 0 < C*(u+1) := by positivity
  have hC' : C = (C-1)+1 := by omega
  have hcoef : C*(s*k) = s*k + ((C-1)*s)*k := by
    nth_rewrite 1 [hC']
    ring
  have hcsk : s*k ≤ C*(s*k) := by omega
  have hks : k*s = s*k := Nat.mul_comm _ _
  refine ⟨⟨k,q,⟨d,by omega⟩,?_,?_,?_,?_,?_,?_⟩⟩
  · rw [hks]; omega
  · have h := Nat.mul_le_mul_left k hR
    have he : k*(C*s) = C*(s*k) := by ring
    omega
  · omega
  · unfold q
    omega
  · have h := Nat.mul_le_mul_left C (show u+1 ≤ 2*s by omega)
    unfold q
    omega
  · omega

/-- A calibrated block with positive density slack yields an explicit
exponential lower bound on the full Boolean primal up to that density. -/
theorem bounded_ratio_bound_from_block {s R : ℕ} (B : CalibratedBlock s R)
    (C : ℕ) (hC : 1 ≤ C) (hs : 0 < s) (hR : R ≤ C*s)
    (hh : (C : ℝ)*s < B.expectedSupport) :
    ∃ a b : ℝ, 0 < a ∧ 1 < b ∧
      ∀ {m n t : ℕ}, 1 ≤ n → m ≤ C*n → (r : Refutation (@Plain m n) t) →
        Real.exp (a*(n : ℝ)-b) ≤ r.mass := by
  obtain ⟨lo,hi,base,hlo,hli,hhi,hbase,hw⟩ := score_window B C hC hh
  let c : ℝ := (hi-lo)*lo^(C*(2*s))
  have hc : 0 < c := mul_pos (sub_pos.mpr hli) (pow_pos hlo _)
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
  have hlb : 0 < Real.log base := Real.log_pos hbase
  let rate := Real.log base / s
  let pad := max 2 (2*Real.log base - Real.log c)
  refine ⟨rate,pad,by unfold rate; positivity,by unfold pad; linarith [le_max_left (2 : ℝ) (2*Real.log base-Real.log c)],?_⟩
  intro m n t hn hm r
  obtain ⟨E⟩ := chooseBlockBudget C s R n hC hs hn hR
  obtain ⟨k,q,hke,hcol,hrow,hcs,hsp,hq,hnb⟩ := E
  let r' := r.addPlainRows (Fin.castLEEmb hm)
  have hmass : r'.mass = r.mass := addPlainRows_preserves_mass _ r
  have hCn : 1 ≤ C*n := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hplain := generic_plain_integral hCn B hcol hrow hcs r'
  have hwin := window_integral B C q k hke lo hi base hlo hli hhi hbase hw
  have hpow : lo^(C*(2*s)) ≤ lo^q := pow_le_pow_of_le_one hlo.le
    (show lo ≤ 1 by linarith) hq
  have hco : c * base^k ≤ (hi-lo)*lo^q*base^k := by
    unfold c
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (sub_nonneg.mpr hli.le)) (by positivity)
  have hpos : (0 : ℝ) ≤ c * base^k := by positivity
  have hCnR : (1 : ℝ) ≤ ((C*n : ℕ) : ℝ) := by exact_mod_cast hCn
  have hI : c * base^k ≤ r.mass := by
    rw [hsp] at hplain
    have hz := mul_le_mul_of_nonneg_left (hco.trans hwin)
      (show (0 : ℝ) ≤ ((C*n : ℕ) : ℝ) by positivity)
    rw [hmass] at hplain
    exact (le_mul_of_one_le_left hpos hCnR).trans (hz.trans hplain)
  have hnb' : (n : ℝ) ≤ (s : ℝ)*k + 2*s := by exact_mod_cast hnb
  have hl : rate*(n : ℝ) ≤ Real.log base*(k : ℝ) + 2*Real.log base := by
    have h := mul_le_mul_of_nonneg_left hnb' (show 0 ≤ rate by unfold rate; positivity)
    have he : rate*((s : ℝ)*k + 2*s) =
        Real.log base*(k : ℝ) + 2*Real.log base := by unfold rate; field_simp
    rwa [he] at h
  have hpad : 2*Real.log base - Real.log c ≤ pad := le_max_right _ _
  have hexp : Real.exp (rate*(n : ℝ)-pad) ≤ c * base^k := by
    have he : rate*(n : ℝ)-pad ≤ Real.log c + (k : ℝ)*Real.log base := by linarith
    refine (Real.exp_le_exp.mpr he).trans_eq ?_
    rw [Real.exp_add,Real.exp_log hc,Real.exp_nat_mul,Real.exp_log (by linarith)]
  exact hexp.trans hI

end PHP
