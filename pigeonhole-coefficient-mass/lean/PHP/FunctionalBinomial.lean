import PHP.MatchingIntegral
import PHP.PhaseDiagram
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.Calculus.Deriv.Add

namespace PHP
open Finset
open scoped BigOperators
set_option maxHeartbeats 900000

private noncomputable def bernTerm (m j : ℕ) (x : ℝ) : ℝ :=
  (m.choose j:ℝ)*x^j*(1-x)^(m-j)

private theorem deriv_bern {m j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ m+1) (x : ℝ) :
    HasDerivAt (bernTerm (m+1) j)
      ((m+1:ℕ)*(bernTerm m (j-1) x-bernTerm m j x)) x := by
  have ha := hasDerivAt_pow j x
  have hneg : HasDerivAt (fun x : ℝ => 1-x) (-1) x := (hasDerivAt_id x).const_sub 1
  have hb := hneg.pow (m+1-j)
  have h := (ha.mul hb).const_mul (((m+1).choose j:ℕ):ℝ)
  convert h using 1
  · ext u
    simp [bernTerm,mul_assoc]
  have hs1 : ((m+1).choose j:ℝ)*(j:ℝ) = ((m+1:ℕ):ℝ)*(m.choose (j-1):ℝ) := by
    have h' := Nat.succ_mul_choose_eq m (j-1)
    rw [show (j-1).succ = j by omega] at h'
    exact_mod_cast h'.symm
  have hs2 : ((m+1).choose j:ℝ)*((m+1-j:ℕ):ℝ) = ((m+1:ℕ):ℝ)*(m.choose j:ℝ) := by
    exact_mod_cast (Nat.choose_mul_succ_eq m j).symm.trans (Nat.mul_comm _ _)
  have hsub1 : m-(j-1) = m+1-j := by omega
  have hsub2 : m+1-j-1 = m-j := by omega
  unfold bernTerm
  simp only [hsub1,hsub2]
  change ((m+1:ℕ):ℝ)*((m.choose (j-1):ℝ)*x^(j-1)*(1-x)^(m+1-j) -
      (m.choose j:ℝ)*x^j*(1-x)^(m-j)) = _
  have he : (((m+1).choose j:ℕ):ℝ) *
        ((j:ℝ)*x^(j-1)*(1-x)^(m+1-j) +
          x^j*(((m+1-j:ℕ):ℝ)*(1-x)^(m-j)*(-1))) =
        ((((m+1).choose j:ℕ):ℝ)*(j:ℝ))*x^(j-1)*(1-x)^(m+1-j) -
        ((((m+1).choose j:ℕ):ℝ)*((m+1-j:ℕ):ℝ))*x^j*(1-x)^(m-j) := by ring
  change _ = (((m+1).choose j:ℕ):ℝ) *
    ((j:ℝ)*x^(j-1)*(1-x)^(m+1-j) +
      x^j*(((m+1-j:ℕ):ℝ)*(1-x)^(m-j)*(-1)))
  rw [he,hs1,hs2]
  ring

private noncomputable def bernTail (m d n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n+1), bernTerm m (d+k) x

private theorem bernTail_deriv (d n : ℕ) (hd : 1 ≤ d) (x : ℝ) :
    HasDerivAt (bernTail (d+n) d n)
      (((d+n:ℕ):ℝ)*((d+n-1).choose n:ℝ)*x^(d-1)*(1-x)^n) x := by
  let m := d+n-1
  have hM : m+1 = d+n := by dsimp [m]; omega
  have hD (k : ℕ) (hk : k ∈ Finset.range (n+1)) :=
    deriv_bern (m:=m) (j:=d+k) (by omega)
      (by have h := Finset.mem_range.mp hk; omega) x
  have he := HasDerivAt.fun_sum (u:=Finset.range (n+1)) hD
  have hval : (∑ k ∈ Finset.range (n+1),
      ((m+1:ℕ):ℝ)*(bernTerm m (d+k-1) x-bernTerm m (d+k) x)) =
      ((m+1:ℕ):ℝ)*((m.choose n:ℝ)*x^(d-1)*(1-x)^n) := by
    rw [← Finset.mul_sum]
    congr 1
    have hshift (k : ℕ) : d+k-1 = d-1+k := by omega
    simp_rw [hshift,show ∀ k : ℕ, d+k = d-1+(k+1) by omega]
    rw [Finset.sum_range_sub']
    have hz : bernTerm m (d-1+(n+1)) x = 0 := by
      unfold bernTerm
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
    rw [hz,sub_zero,add_zero]
    unfold bernTerm
    have hh := (Nat.choose_symm (show d-1 ≤ m by omega)).symm
    rw [show m-(d-1)=n by omega] at hh ⊢
    rw [hh]
  rw [hval] at he
  rw [hM] at he
  convert he using 1
  unfold m
  ring

private theorem bernTail_at_zero (d n : ℕ) (hd : 1 ≤ d) :
    bernTail (d+n) d n 0 = 0 := by
  unfold bernTail
  apply Finset.sum_eq_zero
  intro k _
  simp [bernTerm,zero_pow (show d+k ≠ 0 by omega)]

private theorem bernTail_at_half (d n : ℕ) :
    bernTail (d+n) d n (1/2) = ((∑ k ∈ Finset.range (n+1), (d+n).choose k):ℝ) / 2^(d+n) := by
  classical
  unfold bernTail
  simp only [show (1:ℝ)-1/2=1/2 by norm_num,div_eq_mul_inv,one_mul]
  have h (k : ℕ) (hk : k ∈ Finset.range (n+1)) :
      bernTerm (d+n) (d+k) (2:ℝ)⁻¹ =
        ((d+n).choose (n-k):ℝ) * ((2:ℝ)⁻¹)^(d+n) := by
    have hkn : k ≤ n := by have h := Finset.mem_range.mp hk; omega
    have hs : d+n-(d+k) = n-k := by omega
    have he : d+k+(n-k) = d+n := by omega
    unfold bernTerm
    rw [show (1:ℝ)-(2:ℝ)⁻¹=(2:ℝ)⁻¹ by norm_num, mul_assoc, ←pow_add, hs, he]
    have hh := (Nat.choose_symm (show d+k ≤ d+n by omega)).symm
    rw [hs] at hh
    rw [hh]
  rw [Finset.sum_congr rfl h,← Finset.sum_mul,inv_pow]
  congr 1
  refine Finset.sum_bij (fun k _ => n-k) ?_ ?_ ?_ ?_
  · intro k hk
    change n-k ∈ Finset.range (n+1)
    exact Finset.mem_range.mpr (by omega)
  · intro i hi j hj he
    have h1 := Finset.mem_range.mp hi
    have h2 := Finset.mem_range.mp hj
    change n-i = n-j at he
    omega
  · intro k hk
    have h1 := Finset.mem_range.mp hk
    refine ⟨n-k,Finset.mem_range.mpr (by omega),?_⟩
    change n-(n-k)=k
    omega
  · intros
    rfl

private theorem functional_integral_binomial_base (d n : ℕ) (hd : 1 ≤ d) :
    (((d+n:ℕ):ℝ)*functionalIntegral d n) =
      ((∑ k ∈ Finset.range (n+1), (d+n).choose k):ℝ)/((d+n-1).choose n:ℝ) := by
  let f := fun x : ℝ => x^(d-1)*(1-x)^n
  let coefficient : ℝ := ((d+n:ℕ):ℝ)*((d+n-1).choose n:ℝ)
  have hf : Continuous f := by unfold f; fun_prop
  have hD (x : ℝ) : HasDerivAt (bernTail (d+n) d n) (coefficient*f x) x := by
    have he : coefficient*f x = (((d+n:ℕ):ℝ)*((d+n-1).choose n:ℝ)*x^(d-1)*(1-x)^n) := by
      unfold coefficient f
      ring
    rw [he]
    exact bernTail_deriv d n hd x
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=bernTail (d+n) d n)
    (f':=fun x => coefficient*f x) (a:=0) (b:=1/2) (fun x _ => hD x)
    ((continuous_const.mul hf).intervalIntegrable 0 (1/2))
  rw [bernTail_at_half,bernTail_at_zero d n hd, sub_zero,intervalIntegral.integral_const_mul] at he
  have hscale : functionalIntegral d n = (2:ℝ)^(d+n) * ∫ x : ℝ in 0..1/2, f x := by
    let g := fun x : ℝ => x^(d-1)*(2-x)^n
    have ht := intervalIntegral.integral_comp_mul_left (a:=0) (b:=1/2) g (show (2:ℝ) ≠ 0 by norm_num)
    rw [mul_zero,show (2:ℝ)*(1/2)=1 by norm_num,smul_eq_mul] at ht
    have hg (x : ℝ) : g (2*x) = (2:ℝ)^(d+n-1) * f x := by
      have hp : d-1+n = d+n-1 := by omega
      unfold g f
      rw [show 2-2*x = 2*(1-x) by ring, mul_pow,mul_pow]
      calc
        _ = ((2:ℝ)^(d-1)*2^n)*(x^(d-1)*(1-x)^n) := by ring
        _ = _ := by rw [←pow_add,hp]
    simp_rw [hg, intervalIntegral.integral_const_mul] at ht
    have hpow : (2:ℝ)^(d+n) = 2*2^(d+n-1) := by
      calc
        _ = (2:ℝ)^(d+n-1+1) := by rw [Nat.sub_add_cancel (by omega)]
        _ = _ := by rw [pow_succ,mul_comm]
    unfold functionalIntegral
    change (∫ x : ℝ in 0..1, g x) = _
    rw [hpow]
    linarith
  rw [hscale]
  have hpow : (2:ℝ)^(d+n) ≠ 0 := by positivity
  have hchoose' : (((d+n-1).choose n:ℕ):ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show n ≤ d+n-1 by omega)).ne'
  apply (eq_div_iff hchoose').2
  have hh := (eq_div_iff hpow).mp he
  unfold coefficient at hh
  linear_combination hh

/-- The exact binomial expression for the matching-domain integral. -/
theorem functional_integral_binomial {m n : ℕ} (hm : n < m) :
    (m:ℝ)*functionalIntegral (m-n) n =
      ((∑ k ∈ Finset.range (n+1), m.choose k):ℝ)/((m-1).choose n:ℝ) := by
  have h := functional_integral_binomial_base (m-n) n (by omega)
  rwa [Nat.sub_add_cancel hm.le] at h

end PHP
