import PHP.SupportPolynomial
import PHP.EndpointExtrapolation
import PHP.AmplificationIntegral
import PHP.PhaseDensity

namespace PHP
set_option maxHeartbeats 900000

noncomputable def uniformDelta : ℝ := 1/1048576
noncomputable def uniformBase : ℝ := 1+uniformDelta/256

theorem uniformDelta_pos : 0 < uniformDelta := by norm_num [uniformDelta]
theorem uniformBase_gt : 1 < uniformBase := by norm_num [uniformBase,uniformDelta]

theorem uniform_score_window {C : ℕ} (hC : 1 ≤ C)
    (B : CalibratedBlock (8*C) (6*C^2)) (hB : 9*(C:ℝ)^2 ≤ B.expectedSupport) :
    let s := 8*C
    let δ := uniformDelta
    let lo := 1-δ/(s:ℝ)^2
    let hi := 1-δ/(2*(s:ℝ)^2)
    0 < lo ∧ lo < hi ∧ hi < 1 ∧ 1/2 ≤ lo ∧
    (∀ x ∈ Set.Icc lo hi, uniformBase ≤ scoreEnvelope B C x) := by
  dsimp only
  let s := 8*C
  let δ := uniformDelta
  let lo := 1-δ/(s:ℝ)^2
  let hi := 1-δ/(2*(s:ℝ)^2)
  have hs : 0 < s := by dsimp [s]; omega
  have hsR : 0 < (s:ℝ) := by exact_mod_cast hs
  have hs1 : 1 ≤ (s:ℝ) := by exact_mod_cast hs
  have hδ : 0 < δ := uniformDelta_pos
  have hdiv : 0 < δ/(s:ℝ)^2 := by positivity
  have hhalf : δ/(2*(s:ℝ)^2) = (δ/(s:ℝ)^2)/2 := by field_simp
  have hδsmall : δ ≤ 1/1048576 := le_rfl
  have hlo' : δ/(s:ℝ)^2 ≤ δ := (div_le_iff₀ (by positivity)).mpr
    (le_mul_of_one_le_right hδ.le (one_le_pow₀ hs1))
  have hLo : 1/2 ≤ lo := by dsimp [lo]; linarith
  change 0 < lo ∧ lo < hi ∧ hi < 1 ∧ 1/2 ≤ lo ∧ _
  refine ⟨by linarith,by dsimp [lo,hi]; linarith,by dsimp [hi]; linarith,hLo,?_⟩
  intro x hx
  have hxp : 1/2 ≤ x := hLo.trans hx.1
  have hxn : 0 < x := by linarith
  have hxu : x ≤ 1 := by have hh := hx.2; change x ≤ 1-δ/(2*(s:ℝ)^2) at hh; linarith
  let u := 1-x
  let w := (s:ℝ)^2*u
  let y := x⁻¹-1
  have hu : 0 ≤ u := sub_nonneg.mpr hxu
  have hwlo : δ/2 ≤ w := by
    have hh := hx.2
    change x ≤ 1-δ/(2*(s:ℝ)^2) at hh
    have h : δ/(2*(s:ℝ)^2) ≤ u := by dsimp [u]; linarith
    have he := mul_le_mul_of_nonneg_right h (sq_nonneg (s:ℝ))
    have hh' : δ/(2*(s:ℝ)^2)*(s:ℝ)^2 = δ/2 := by field_simp
    rw [hh'] at he
    exact he.trans_eq (by unfold w; ring)
  have hwhi : w ≤ δ := by
    have hh : u ≤ δ/(s:ℝ)^2 := by have he := hx.1; dsimp [lo,u] at *; linarith
    have h := mul_le_mul_of_nonneg_left hh (sq_nonneg (s:ℝ))
    have he : (s:ℝ)^2*(δ/(s:ℝ)^2) = δ := by field_simp
    rwa [he] at h
  have hw0 : 0 ≤ w := by linarith
  have hy : y = u/x := by dsimp [y,u]; field_simp
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hyu : u ≤ y := by
    rw [hy]
    exact (le_div_iff₀ hxn).mpr (by nlinarith [mul_le_mul_of_nonneg_left hxu hu])
  have hy2u : y ≤ 2*u := by
    rw [hy]
    exact (div_le_iff₀ hxn).mpr (by nlinarith [mul_le_mul_of_nonneg_right hxp hu])
  have hys : (s:ℝ)^2*y ≤ 2*w := by
    have h := mul_le_mul_of_nonneg_left hy2u (sq_nonneg (s:ℝ))
    dsimp [w]; linarith
  have hySmall : y ≤ 1/(8*(s:ℝ)^2) := (le_div_iff₀ (by positivity)).mpr (by
    have h : y*(8*(s:ℝ)^2) = 8*((s:ℝ)^2*y) := by ring
    rw [h]
    linarith)
  have hTail := extrapolate_quadratic hs (supportPoly_natDegree B)
    (fun q hq => supportPoly_abs_le_one B hq.1 hq.2) hy0 hySmall
  rw [supportPoly_one,supportPoly_deriv] at hTail
  have hh := (abs_le.mp hTail).1
  have hSC : (s:ℝ) = 8*(C:ℝ) := by dsimp [s]; push_cast; rfl
  have hhSupport : (9/64:ℝ)*(s:ℝ)^2 ≤ B.expectedSupport := by rw [hSC]; nlinarith
  have hLinear : (9/64:ℝ)*w ≤ y*B.expectedSupport := by
    calc
      _ = ((9/64:ℝ)*(s:ℝ)^2)*u := by unfold w; ring
      _ ≤ ((9/64:ℝ)*(s:ℝ)^2)*y := mul_le_mul_of_nonneg_left hyu (by positivity)
      _ ≤ _ := by exact (mul_le_mul_of_nonneg_right hhSupport hy0).trans_eq (by ring)
  have hSquare : 256*((s:ℝ)^2*y)^2 ≤ 1024*w^2 := by
    have h := pow_le_pow_left₀ (mul_nonneg (sq_nonneg (s:ℝ)) hy0) hys 2
    nlinarith
  have hSupport : 1+(9/64:ℝ)*w-1024*w^2 ≤ (supportPoly B).eval x⁻¹ := by
    have he : 1+y = x⁻¹ := by unfold y; ring
    rw [he] at hh
    linarith
  have hBern : 1-w/8 ≤ x^(C*s) := by
    have h := one_add_mul_sub_le_pow (show -1 ≤ x by linarith) (C*s)
    have he : ((C*s:ℕ):ℝ)*(x-1) = -w/8 := by unfold w u; push_cast; rw [hSC]; ring
    rw [he] at h
    linarith
  have hw2 : w^2 ≤ δ*w := by nlinarith [mul_le_mul_of_nonneg_right hwhi hw0]
  have hSup0 : 0 ≤ 1+(9/64:ℝ)*w-1024*w^2 := by
    have h := mul_le_mul_of_nonneg_right hδsmall hw0
    nlinarith
  have hprod := mul_le_mul hBern hSupport hSup0 (pow_nonneg hxn.le (C*s))
  have hG : scoreEnvelope B C x = x^(C*s)*(supportPoly B).eval x⁻¹ := by
    unfold scoreEnvelope
    rw [supportPoly_reciprocal B hxn.ne',←mul_assoc,←pow_add]
    have hCs : (C-1)+1 = C := Nat.sub_add_cancel hC
    have he : (C-1)*s+s = C*s := by
      calc
        _ = ((C-1)+1)*s := by ring
        _ = _ := by rw [hCs]
    change x^((C-1)*s+s)*_ = _
    rw [he]
  rw [hG]
  apply le_trans _ hprod
  have hδw := mul_le_mul_of_nonneg_right hδsmall hw0
  have hw3 : 0 ≤ w^3 := by positivity
  change 1+δ/256 ≤ _
  nlinarith

end PHP
