import PHP.UniformScore
import PHP.PhaseDiagram
import PHP.OneHot
import Mathlib.Algebra.Order.Floor.Semiring

namespace PHP
set_option maxHeartbeats 1300000

noncomputable def uniformRate : ℝ := Real.log uniformBase / 8
noncomputable def uniformPad : ℝ := 2*Real.log uniformBase-Real.log (uniformDelta/32)

theorem uniformRate_pos : 0 < uniformRate := by
  unfold uniformRate
  exact div_pos (Real.log_pos uniformBase_gt) (by norm_num)

theorem uniformPad_pos : 0 < uniformPad := by
  have h := Real.log_pos uniformBase_gt
  have h' := Real.log_neg (show 0 < uniformDelta/32 by norm_num [uniformDelta])
    (show uniformDelta/32 < 1 by norm_num [uniformDelta])
  unfold uniformPad
  linarith

/-- Uniform coefficient bound through the formerly nonquantitative
bounded-density construction. The rate deteriorates only as 1/C. -/
theorem plain_uniform_cap {C m n t : ℕ} (hC : 1 ≤ C) (hn : 1 ≤ n) (hm : m ≤ C*n)
    (r : Refutation (@Plain m n) t) :
    uniformRate*((n:ℝ)/C)-uniformPad ≤ Real.log r.mass := by
  let s := 8*C
  let R := 6*C^2
  let δ := uniformDelta
  let lo := 1-δ/(s:ℝ)^2
  let hi := 1-δ/(2*(s:ℝ)^2)
  let a := Real.log uniformBase
  have ha : 0 < a := Real.log_pos uniformBase_gt
  have hδ : 0 < δ := uniformDelta_pos
  have hδ1 : δ < 1 := by norm_num [δ,uniformDelta]
  have hs : 0 < s := by dsimp [s]; omega
  have hCp : (0:ℝ) < C := by exact_mod_cast hC
  have hCn : 1 ≤ C*n := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hCn0 : 0 ≤ ((C*n:ℕ):ℝ) := Nat.cast_nonneg _
  have hsR : 0 < (s:ℝ) := by exact_mod_cast hs
  have hsc : (s:ℝ) = 8*(C:ℝ) := by dsimp [s]; push_cast; rfl
  have hR : R ≤ C*s := by dsimp [R,s]; nlinarith
  obtain ⟨B,hB⟩ := Phase.density_block_margin C hC
  obtain ⟨hlo,hh,hhi,hlohalf,hscore⟩ := uniform_score_window hC B hB
  obtain ⟨E⟩ := chooseBlockBudget C s R n hC hs hn hR
  obtain ⟨k,q,hke,hcol,hrow,hcs,hsp,hq,hnb⟩ := E
  let r' := r.addPlainRows (Fin.castLEEmb hm)
  have hmass : r'.mass = r.mass := addPlainRows_preserves_mass _ r
  have hmain := generic_plain_integral hCn B hcol hrow hcs r'
  have hwin := window_integral B C q k hke lo hi uniformBase hlo hh hhi uniformBase_gt hscore
  rw [hsp,hmass] at hmain
  have hI := (mul_le_mul_of_nonneg_left hwin hCn0).trans hmain
  have hq0 : (1/2:ℝ) ≤ lo^q := by
    have h := one_add_mul_sub_le_pow (show -1 ≤ lo by linarith) q
    have hqR : (q:ℝ) ≤ (C:ℝ)*(2*(s:ℝ)) := by exact_mod_cast hq
    have hq' : (q:ℝ)*(1-lo) ≤ δ/4 := by
      have hh' : 0 ≤ 1-lo := by linarith
      calc
        _ ≤ (C:ℝ)*(2*(s:ℝ))*(1-lo) := mul_le_mul_of_nonneg_right hqR hh'
        _ = _ := by unfold lo; rw [hsc]; field_simp; ring
    calc
      _ ≤ 1+(q:ℝ)*(lo-1) := by nlinarith
      _ ≤ _ := h
  have hw : hi-lo = δ/(2*(s:ℝ)^2) := by unfold hi lo; field_simp; ring
  have hcu : (k:ℝ)/8 ≤ ((C*n:ℕ):ℝ)/(s:ℝ)^2 := by
    apply (le_div_iff₀ (sq_pos_of_ne_zero hsR.ne')).mpr
    have h := (mul_le_mul_of_nonneg_left (show (k:ℝ)*(s:ℝ) ≤ n by exact_mod_cast hcol)
      hCp.le)
    push_cast
    rw [hsc] at h ⊢
    nlinarith
  have hbeta : 0 < uniformBase := zero_lt_one.trans uniformBase_gt
  have hconst : 0 < δ/32 := by positivity
  have hc : Real.log (δ/32) ≤ 0 := Real.log_nonpos hconst.le (by linarith)
  have hnk : (n:ℝ) ≤ (s:ℝ)*k + 2*s := by exact_mod_cast hnb
  have hrate : uniformRate*((n:ℝ)/C) ≤ a*k + 2*a := by
    have h := mul_le_mul_of_nonneg_left hnk (show 0 ≤ a/(s:ℝ) by positivity)
    have hl : a/(s:ℝ)*(n:ℝ) = uniformRate*((n:ℝ)/C) := by
      unfold uniformRate a
      rw [hsc]
      field_simp
    have hr : a/(s:ℝ)*((s:ℝ)*k+2*s) = a*k+2*a := by field_simp
    rwa [hl,hr] at h
  by_cases hk : k = 0
  · have hL := Real.log_nonneg r.one_le_mass
    rw [hk,Nat.cast_zero,mul_zero,zero_add] at hrate
    change uniformRate*((n:ℝ)/C)-(2*a-Real.log (δ/32)) ≤ _
    linarith
  · have hk1 : (1:ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    have hprod : (δ/32)*uniformBase^k ≤ r.mass := by
      rw [hw] at hI
      have hF : (δ/32) ≤ ((C*n:ℕ):ℝ)*(δ/(2*(s:ℝ)^2))*lo^q := by
        have hG : (δ/32)*(k:ℝ) ≤ ((C*n:ℕ):ℝ)*(δ/(2*(s:ℝ)^2))*(1/2:ℝ) := by
          calc
            _ = (δ/4)*((k:ℝ)/8) := by ring
            _ ≤ (δ/4)*(((C*n:ℕ):ℝ)/(s:ℝ)^2) :=
              mul_le_mul_of_nonneg_left hcu (by positivity)
            _ = _ := by field_simp; ring
        have hG' := mul_le_mul_of_nonneg_left hq0
          (show 0 ≤ ((C*n:ℕ):ℝ)*(δ/(2*(s:ℝ)^2)) by positivity)
        exact (le_mul_of_one_le_right hconst.le hk1).trans (hG.trans hG')
      have hG := mul_le_mul_of_nonneg_right hF (pow_nonneg hbeta.le k)
      exact hG.trans (by linarith)
    have hL := Real.log_le_log (mul_pos hconst (pow_pos hbeta k)) hprod
    rw [Real.log_mul hconst.ne' (pow_ne_zero _ hbeta.ne'),Real.log_pow] at hL
    change uniformRate*((n:ℝ)/C)-(2*a-Real.log (δ/32)) ≤ _
    change Real.log (δ/32)+(k:ℝ)*a ≤ _ at hL
    linarith

/-- The manuscript's all-ratio lower on every literal-cube proof; the
constant is absolute and no hidden dependence on the surplus remains. -/
theorem plain_all_ratio_lower :
    ∃ α : ℝ, 0 < α ∧ ∀ {m n t : ℕ}, 2 ≤ n → n < m →
      ∀ r : Refutation (@Plain m n) t,
      α*((n:ℝ)^2/(m:ℝ)+Real.log n) ≤ Real.log r.mass := by
  let A := uniformRate/2
  let B := uniformPad
  let L := Real.log 2
  let D := (1+B/(2*L))/A + 1/2
  have hA : 0 < A := by unfold A; exact div_pos uniformRate_pos (by norm_num)
  have hB : 0 < B := uniformPad_pos
  have hL : 0 < L := Real.log_pos (by norm_num)
  have hD : 0 < D := by unfold D; positivity
  refine ⟨D⁻¹,inv_pos.mpr hD,?_⟩
  intro m n t hn hnm r
  let c := (m:ℝ)/n
  let C := ⌈c⌉₊
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hm0 : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hnmR : (n:ℝ) < m := by exact_mod_cast hnm
  have hpos : 1 < c := (lt_div_iff₀ hn0).mpr (by simpa using hnmR)
  have hC : 1 ≤ C := Nat.one_le_ceil_iff.mpr (by linarith)
  have hCr : 0 < (C:ℝ) := by exact_mod_cast hC
  have hceil : c ≤ (C:ℝ) := Nat.le_ceil c
  have hfit : m ≤ C*n := by
    have h := (div_le_iff₀ hn0).mp hceil
    exact_mod_cast h
  have hsmall : (C:ℝ) ≤ 2*c := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ c by positivity)
    change (C:ℝ) < c+1 at h
    linarith
  have hRate : (n:ℝ)^2/(2*(m:ℝ)) ≤ (n:ℝ)/C := by
    have he : (n:ℝ)^2/(2*(m:ℝ)) = (n:ℝ)/(2*c) := by unfold c; field_simp
    rw [he]
    exact div_le_div_of_nonneg_left hn0.le hCr hsmall
  have hCap := plain_uniform_cap hC (by omega : 1 ≤ n) hfit r
  have hLow : A*((n:ℝ)^2/(m:ℝ))-B ≤ Real.log r.mass := by
    have h := mul_le_mul_of_nonneg_left hRate uniformRate_pos.le
    have he : uniformRate*((n:ℝ)^2/(2*(m:ℝ))) = A*((n:ℝ)^2/(m:ℝ)) := by unfold A; ring
    rw [he] at h
    linarith
  have hone := plain_onehot_lower (by omega : 2 ≤ m) (by omega : 1 ≤ n) r
  have hlog := Real.log_le_log (pow_pos hn0 2) hone
  rw [Real.log_pow] at hlog
  norm_num at hlog
  have hlower : L ≤ Real.log (n:ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hpad : B ≤ (B/(2*L))*Real.log r.mass := by
    have h := mul_le_mul_of_nonneg_left (by linarith : 2*L ≤ Real.log r.mass)
      (show 0 ≤ B/(2*L) by positivity)
    have he : B/(2*L)*(2*L) = B := by field_simp
    rwa [he] at h
  have hfront : (n:ℝ)^2/(m:ℝ) ≤ ((1+B/(2*L))/A)*Real.log r.mass := by
    have h := (le_div_iff₀ hA).mpr (by linarith : (n:ℝ)^2/(m:ℝ)*A ≤ (1+B/(2*L))*Real.log r.mass)
    convert h using 1
    ring
  have he : (n:ℝ)^2/(m:ℝ)+Real.log n ≤ D*Real.log r.mass := by
    unfold D
    linarith
  exact (mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hD.le)).trans_eq (by
    rw [←mul_assoc,inv_mul_cancel₀ hD.ne',one_mul])


theorem optimal_plain_all_ratio_lower :
    ∃ α : ℝ, 0 < α ∧ ∀ {m n : ℕ}, 2 ≤ n → n < m →
      α*((n:ℝ)^2/(m:ℝ)+Real.log n) ≤ Real.log (optimalPlainMass m n) := by
  obtain ⟨α,hα,h⟩ := plain_all_ratio_lower
  refine ⟨α,hα,?_⟩
  intro m n hn hm
  let z := α*((n:ℝ)^2/(m:ℝ)+Real.log n)
  have hz : Real.exp z ≤ optimalPlainMass m n := by
    apply le_csInf (plainMassSet_nonempty hm)
    rintro _ ⟨s,r,rfl⟩
    exact (Real.exp_le_exp.mpr (h hn hm r)).trans_eq
      (Real.exp_log (zero_lt_one.trans_le r.one_le_mass))
  have hh := Real.log_le_log (Real.exp_pos z) hz
  rwa [Real.log_exp] at hh

end PHP
