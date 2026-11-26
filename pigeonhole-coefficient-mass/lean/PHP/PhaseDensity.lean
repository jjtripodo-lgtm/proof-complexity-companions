import PHP.PhaseRecurrence
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

namespace PHP.Phase

open scoped BigOperators

private theorem density_angle (C : ℝ) (hC : 1 ≤ C) :
    ∃ θ : ℝ, Real.cos θ = 1 - 1/(12*C^2) ∧ 3 ≤ 8*C*θ ∧ 8*C*θ ≤ 7/2 := by
  let q := 1 - 1/(12*C^2)
  let θ := Real.arccos q
  have hCP : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hD : 0 < 12*C^2 := by positivity
  have hq : -1 ≤ q := by
    have h2 : 1 ≤ C^2 := by nlinarith
    have hle : 1/(12*C^2) ≤ (2 : ℝ) := (div_le_iff₀ hD).mpr (by linarith)
    unfold q
    linarith
  have hq' : q ≤ 1 := by unfold q; linarith [one_div_nonneg.mpr hD.le]
  have hc : Real.cos θ = q := Real.cos_arccos hq hq'
  have h0 : 0 ≤ θ := Real.arccos_nonneg _
  have hπ : θ ≤ Real.pi := Real.arccos_le_pi _
  let v := θ/2
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hvπ : v ≤ Real.pi/2 := by dsimp [v]; linarith
  have hs0 : 0 ≤ Real.sin v := Real.sin_nonneg_of_nonneg_of_le_pi hv0 (by linarith [Real.pi_pos])
  have hsv : Real.sin v ^ 2 = 1 / (24*C^2) := by
    rw [Real.sin_sq_eq_half_sub, show 2*v = θ by unfold v; ring,hc]
    unfold q
    field_simp
    ring
  have hCsq : (C*Real.sin v)^2 = 1/24 := by
    rw [mul_pow,hsv]
    field_simp
  have hClower : (3/16 : ℝ) ≤ C*Real.sin v := by
    have he : 0 ≤ C*Real.sin v := mul_nonneg hCP.le hs0
    by_contra! h
    have h' := mul_lt_mul_of_pos_left h (show 0 < 3/16 + C*Real.sin v by positivity)
    nlinarith
  have hCupper : C*Real.sin v ≤ 21/100 := by
    have he : 0 ≤ C*Real.sin v := mul_nonneg hCP.le hs0
    by_contra! h
    have h' := mul_lt_mul_of_pos_left h (show 0 < 21/100 + C*Real.sin v by positivity)
    nlinarith
  have hsin_v : Real.sin v ≤ v := by
    simpa [abs_of_nonneg hs0,abs_of_nonneg hv0] using (Real.abs_sin_le_abs (x:=v))
  have hlower : 3 ≤ 8*C*θ := by
    have hs := mul_le_mul_of_nonneg_left hsin_v hCP.le
    dsimp [v] at hs
    linarith
  let y := 7/(32*C)
  have hy0 : 0 < y := by unfold y; positivity
  have hymax : y ≤ (7/32 : ℝ) := by
    unfold y
    apply (div_le_iff₀ (show 0 < 32*C by positivity)).mpr
    nlinarith
  have hyone : y ≤ 1 := by linarith
  have hyC : C*y = 7/32 := by unfold y; field_simp
  have hcube : C*y^3 ≤ (7/32 : ℝ)^3 := by
    have hpow := pow_le_pow_left₀ hy0.le hymax 2
    calc
      _ = (C*y)*y^2 := by ring
      _ ≤ _ := by rw [hyC]; nlinarith
  have hsin := mul_lt_mul_of_pos_left (Real.sin_gt_sub_cube hy0 hyone) hCP
  have hys : 21/100 < C * Real.sin y := by nlinarith
  have hless : Real.sin v < Real.sin y :=
    lt_of_mul_lt_mul_left (hCupper.trans_lt hys) hCP.le
  have hvy : v < y := by
    by_contra! hy
    have hh := Real.sin_le_sin_of_le_of_le_pi_div_two
      (show -(Real.pi/2) ≤ y by linarith [Real.pi_pos]) hvπ hy
    exact hless.not_ge hh
  have hupper : 8*C*θ ≤ 7/2 := by
    have h := mul_le_mul_of_nonneg_left hvy.le hCP.le
    dsimp [v] at h
    linarith
  exact ⟨θ,hc,hlower,hupper⟩

private theorem cosine_window (a : ℝ) (ha : 3 ≤ a) (hb : a ≤ 7/2) :
    Real.cos a ≤ -(1/2) := by
  have hlo : -1 ≤ a - Real.pi := by linarith [Real.pi_lt_four]
  have hhi : a - Real.pi ≤ 1 := by linarith [Real.pi_gt_three]
  have hsq : (a - Real.pi)^2 ≤ 1 := by
    have hs : |a - Real.pi| ≤ (1 : ℝ) := abs_le.mpr ⟨hlo,hhi⟩
    have hh : |a - Real.pi| ≤ |(1 : ℝ)| := by simpa using hs
    simpa using (sq_le_sq.mpr hh)
  have h := Real.one_sub_sq_div_two_le_cos (x := a-Real.pi)
  have he : Real.cos (a-Real.pi) = -Real.cos a := by simp [Real.cos_sub,Real.cos_pi,Real.sin_pi]
  rw [he] at h
  linarith

/-- An explicit phase block for every integer density factor C. Its row
footprint is no more than C times its column footprint, and its signed
used-label expectation is strictly larger than C times that footprint. -/
theorem density_block_margin (C : ℕ) (hC : 1 ≤ C) :
    ∃ B : CalibratedBlock (8*C) (6*C^2),
      9*(C:ℝ)^2 ≤ B.expectedSupport := by
  let s := 8*C
  let R := 6*C^2
  have hCP : 0 < C := by omega
  have hs : 0 < s := by unfold s; positivity
  have hR : 0 < R := by unfold R; positivity
  let B := calibrated s R hR
  refine ⟨B,?_⟩
  have hC' : (1 : ℝ) ≤ C := by exact_mod_cast hC
  obtain ⟨θ,hcos,hmin,hmax⟩ := density_angle (C : ℝ) hC'
  have hθ : Real.cos θ = 1 - 1/(2*(R : ℝ)) := by
    rw [hcos]
    congr 2
    dsimp [R]
    push_cast
    ring
  have hsθ : (s : ℝ)*θ = 8*(C : ℝ)*θ := by dsimp [s]; push_cast; ring
  have hc := cosine_window ((s : ℝ)*θ) (by rwa [hsθ]) (by rwa [hsθ])
  have hv : phaseValue R s ≤ -(1/2) := by rwa [phaseValue_cos R θ hθ s]
  have hcast : (R : ℝ) = 6*(C : ℝ)^2 := by dsimp [R]; push_cast; rfl
  have hscast : (s : ℝ) = 8*(C : ℝ) := by dsimp [s]; push_cast; rfl
  change 9*(C:ℝ)^2 ≤ (calibrated s R hR).expectedSupport
  rw [used_expectation hR,hcast]
  have hmul := mul_le_mul_of_nonneg_left hv (show 0 ≤ 6*(C : ℝ)^2 by positivity)
  nlinarith [sq_pos_of_ne_zero (show (C : ℝ) ≠ 0 by positivity)]

theorem density_block (C : ℕ) (hC : 1 ≤ C) :
    ∃ (s R : ℕ) (B : CalibratedBlock s R),
      0 < s ∧ R ≤ C*s ∧ (C : ℝ)*s < B.expectedSupport := by
  obtain ⟨B, hB⟩ := density_block_margin C hC
  have hC0 : (0:ℝ) < C := by exact_mod_cast hC
  refine ⟨8*C,6*C^2,B,by omega,by nlinarith,?_⟩
  push_cast
  nlinarith [sq_pos_of_ne_zero hC0.ne']

end PHP.Phase
