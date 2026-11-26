import PHP.FunctionalFiniteRate
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace PHP
open Set

noncomputable def binaryEntropyGap (p : ℝ) : ℝ :=
  Real.log 2 + p*Real.log p + (1-p)*Real.log (1-p)

noncomputable def entropySlope (p : ℝ) : ℝ := Real.log p - Real.log (1-p)

private theorem entropy_half : binaryEntropyGap (1/2) = 0 := by
  unfold binaryEntropyGap
  rw [show (1:ℝ)-1/2=1/2 by norm_num,one_div,Real.log_inv]
  ring

private theorem entropy_deriv {x : ℝ} (hx : 0 < x) (hx' : x < 1) :
    HasDerivAt binaryEntropyGap (entropySlope x) x := by
  have hx2 : 1-x ≠ 0 := by linarith
  have h₁ := (hasDerivAt_id x).mul (Real.hasDerivAt_log hx.ne')
  have h₂ := (hasDerivAt_id x).const_sub 1
  have h₃ := h₂.mul ((Real.hasDerivAt_log hx2).comp x h₂)
  have h := (h₁.const_add (Real.log 2)).add h₃
  convert h using 1
  unfold entropySlope
  simp only [id,Function.comp_apply]
  field_simp
  <;> ring

private theorem entropy_slope_deriv {x : ℝ} (hx : 0 < x) (hx' : x < 1) :
    HasDerivAt entropySlope (1/(x*(1-x))) x := by
  have hx2 : 1-x ≠ 0 := by linarith
  have h₂ := (hasDerivAt_id x).const_sub 1
  have h := (Real.hasDerivAt_log hx.ne').sub ((Real.hasDerivAt_log hx2).comp x h₂)
  convert h using 1
  change 1/(x*(1-x)) = x⁻¹ - (1-x)⁻¹*(-1)
  field_simp
  <;> ring

private theorem endpoint_of_nonnegative_deriv {a b : ℝ} {f f' : ℝ → ℝ} (hab : a ≤ b)
    (hD : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hp : ∀ x ∈ Icc a b, 0 ≤ f' x) :
    f a ≤ f b := by
  have hm : MonotoneOn f (Icc a b) :=
    monotoneOn_of_deriv_nonneg (convex_Icc a b)
      (fun x hx => (hD x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hD x (interior_subset hx)).differentiableAt.differentiableWithinAt)
      (fun x hx => by rw [(hD x (interior_subset hx)).deriv]; exact hp x (interior_subset hx))
  exact hm (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab

/-- Exact finite quadratic bounds for the binary entropy gap. The upper
coefficient tends to the lower coefficient as p tends to a half. -/
theorem entropy_quadratic_squeeze {p : ℝ} (hp : 1/2 ≤ p) (hp' : p < 1) :
    2*(p-1/2)^2 ≤ binaryEntropyGap p ∧
    binaryEntropyGap p ≤ (1/(2*p*(1-p)))*(p-1/2)^2 := by
  have pd : 0 < p*(1-p) := mul_pos (by linarith) (by linarith)
  let K := 1/(p*(1-p))
  have hK (x : ℝ) (hx : x ∈ Icc (1/2) p) :
      4 ≤ 1/(x*(1-x)) ∧ 1/(x*(1-x)) ≤ K := by
    have hx0 : 0 < x*(1-x) := mul_pos (by linarith [hx.1]) (by linarith [hx.2])
    have hmul : p*(1-p) ≤ x*(1-x) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hx.2)
        (show 0 ≤ p+x-1 by linarith [hx.1])]
    exact ⟨(le_div_iff₀ hx0).mpr (by nlinarith [sq_nonneg (x-1/2)]),
      one_div_le_one_div_of_le pd hmul⟩
  have hS (x : ℝ) (hx : x ∈ Icc (1/2) p) :
      4*(x-1/2) ≤ entropySlope x ∧ entropySlope x ≤ K*(x-1/2) := by
    have hs (z : ℝ) (hz : z ∈ Icc (1/2) x) : z ∈ Icc (1/2) p := ⟨hz.1,hz.2.trans hx.2⟩
    have hAt (z : ℝ) (hz : z ∈ Icc (1/2) x) :=
      entropy_slope_deriv (show 0 < z by linarith [hz.1]) (show z < 1 by linarith [(hs z hz).2])
    have hlin (s z : ℝ) : HasDerivAt (fun y : ℝ => s*(y-1/2)) s z := by
      simpa only [mul_one,id] using ((hasDerivAt_id z).sub_const (1/2)).const_mul s
    have hl := endpoint_of_nonnegative_deriv hx.1
      (fun z hz => (hAt z hz).sub (hlin 4 z))
      (fun z hz => sub_nonneg.mpr (hK z (hs z hz)).1)
    have hu := endpoint_of_nonnegative_deriv hx.1
      (fun z hz => (hlin K z).sub (hAt z hz))
      (fun z hz => sub_nonneg.mpr (hK z (hs z hz)).2)
    have hzero : entropySlope (1/2) = 0 := by unfold entropySlope; congr 1 <;> norm_num
    simp only [Pi.sub_apply,hzero,sub_self,mul_zero,sub_zero] at hl hu
    exact ⟨sub_nonneg.mp hl,sub_nonneg.mp hu⟩
  have hquad (s z : ℝ) : HasDerivAt (fun y : ℝ => (s/2)*(y-1/2)^2) (s*(z-1/2)) z := by
    have h := (((hasDerivAt_id z).sub_const (1/2)).pow 2).const_mul (s/2)
    convert h using 1
    norm_num
    ring
  have hAt (z : ℝ) (hz : z ∈ Icc (1/2) p) :=
    entropy_deriv (show 0 < z by linarith [hz.1]) (show z < 1 by linarith [hz.2])
  have hl := endpoint_of_nonnegative_deriv hp
    (fun z hz => (hAt z hz).sub (hquad 4 z))
    (fun z hz => sub_nonneg.mpr (hS z hz).1)
  have hu := endpoint_of_nonnegative_deriv hp
    (fun z hz => (hquad K z).sub (hAt z hz))
    (fun z hz => sub_nonneg.mpr (hS z hz).2)
  simp only [Pi.sub_apply,entropy_half,sub_self,zero_pow (by decide : (2:ℕ) ≠ 0),mul_zero,sub_zero,zero_sub,neg_zero] at hl hu
  constructor
  · linarith
  · have hh : K/2 = 1/(2*p*(1-p)) := by unfold K; field_simp
    rwa [hh,sub_nonneg] at hu

private theorem functionalRateMass_log {m n : ℕ} (hn : 1 ≤ n) (hm : n < m) :
    Real.log (functionalRateMass m n) = (m:ℝ)*binaryEntropyGap ((n:ℝ)/m) := by
  have hN : 0 < (n:ℝ) := by exact_mod_cast hn
  have hM : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hd : 0 < ((m-n:ℕ):ℝ) := by exact_mod_cast (show 0 < m-n by omega)
  have he : 1-(n:ℝ)/m = ((m-n:ℕ):ℝ)/m := by
    rw [Nat.cast_sub hm.le]
    field_simp
  unfold functionalRateMass binaryEntropyGap
  rw [he,Real.log_div (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_pow]
  rw [Real.log_div hN.ne' hM.ne', Real.log_div hd.ne' hM.ne']
  rw [Nat.cast_sub hm.le]
  field_simp
  <;> ring

theorem functional_entropy_bounds {m n : ℕ} (hn : 4 ≤ n) (hm : n < m) (h2 : m ≤ 2*n) :
    (m:ℝ)*binaryEntropyGap ((n:ℝ)/m)-Real.log 2 ≤ Real.log (optimalFunctionalMass m n) ∧
    Real.log (optimalFunctionalMass m n) ≤
      (m:ℝ)*binaryEntropyGap ((n:ℝ)/m) + Real.log (functionalChargeBudget m n*((m:ℝ)+1)) := by
  obtain ⟨hl,hu⟩ := functional_rate_sandwich hn hm h2
  have hE : 0 < functionalRateMass m n := by
    have hN : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hM : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hd : (0:ℝ) < ((m-n:ℕ):ℝ) := by exact_mod_cast (show 0 < m-n by omega)
    unfold functionalRateMass
    positivity
  have hT := (div_pos hE (by norm_num : (0:ℝ) < 2)).trans_le hl
  have hR : 0 < functionalChargeBudget m n*((m:ℝ)+1) := by
    have h := hT.trans_le hu
    by_contra! hbad
    exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hbad hE.le)) h
  have hlog := functionalRateMass_log (by omega : 1 ≤ n) hm
  have h₁ := Real.log_le_log (div_pos hE (by norm_num : (0:ℝ) < 2)) hl
  have h₂ := Real.log_le_log hT hu
  rw [Real.log_div hE.ne' (by norm_num),hlog] at h₁
  rw [Real.log_mul hR.ne' hE.ne',hlog,add_comm] at h₂
  exact ⟨h₁,h₂⟩

end PHP
