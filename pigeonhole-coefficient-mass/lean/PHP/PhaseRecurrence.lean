import PHP.PhasePlane
import PHP.GenericBlockMoment
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

namespace PHP.Phase

open scoped BigOperators ComplexConjugate

theorem phaseValue_zero (R : ℕ) : phaseValue R 0 = 1 := by
  simp [phaseValue,pairAt]

theorem phaseValue_one (R : ℕ) :
    phaseValue R 1 = 1 - 1/(2*(R : ℝ)) := by
  have hmul : conj eta*eta = 1 := by rw [mul_comm,eta_mul_conj]
  have hh : (1-conj eta)*(eta-1) = -1 := by
    calc
      _ = (eta+conj eta) - conj eta*eta - 1 := by ring
      _ = _ := by rw [eta_add_conj,hmul]; ring
  have hh' : conj eta*(eta-1) = 1-conj eta := by rw [mul_sub,hmul,mul_one]
  have hpoly :
      (1 + (1-conj eta)*(eta-1)/(R : ℂ)) +
        (conj eta*(eta-1))/(R : ℂ) = 1 - conj eta/(R : ℂ) := by
    rw [hh,hh']
    simp only [div_eq_mul_inv]
    ring
  unfold phaseValue
  simp only [pairAt,stepPair,mul_one,mul_zero,add_zero]
  rw [hpoly]
  have hcast : (R : ℂ)⁻¹ = (((R : ℝ)⁻¹ : ℝ) : ℂ) := by rw [Complex.ofReal_inv, Complex.ofReal_natCast]
  simp only [div_eq_mul_inv,hcast,Complex.sub_re,Complex.one_re,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,Complex.conj_re,Complex.conj_im,mul_zero,sub_zero,eta]
  ring

theorem phaseValue_step (R s : ℕ) :
    phaseValue R (s+2) = (2-(R : ℝ)⁻¹)*phaseValue R (s+1) - phaseValue R s := by
  have ha := stepPair_recurrence R (pairAt R s)
  have h1 : (pairAt R (s+2)).1 = (2 - (R : ℂ)⁻¹)*(pairAt R (s+1)).1 - (pairAt R s).1 :=
    congrArg Prod.fst ha
  have h2 : (pairAt R (s+2)).2 = (2 - (R : ℂ)⁻¹)*(pairAt R (s+1)).2 - (pairAt R s).2 :=
    congrArg Prod.snd ha
  unfold phaseValue
  rw [h1,h2]
  have hrew :
      (2 - (R : ℂ)⁻¹)*(pairAt R (s+1)).1 - (pairAt R s).1 +
        ((2 - (R : ℂ)⁻¹)*(pairAt R (s+1)).2 - (pairAt R s).2)/(R : ℂ) =
      (2 - (R : ℂ)⁻¹)*((pairAt R (s+1)).1+(pairAt R (s+1)).2/(R : ℂ)) -
        ((pairAt R s).1+(pairAt R s).2/(R : ℂ)) := by
    simp only [div_eq_mul_inv]
    ring
  rw [hrew]
  have hcast : (R : ℂ)⁻¹ = (((R : ℝ)⁻¹ : ℝ) : ℂ) := by rw [Complex.ofReal_inv, Complex.ofReal_natCast]
  rw [hcast]
  norm_num [Complex.sub_re,Complex.mul_re,Complex.sub_im]

theorem phaseValue_cos (R : ℕ) (θ : ℝ) (hθ : Real.cos θ = 1 - 1/(2*(R : ℝ))) :
    ∀ s : ℕ, phaseValue R s = Real.cos (s*θ) := by
  have hcoef : (2-(R : ℝ)⁻¹) = 2*Real.cos θ := by rw [hθ]; simp only [div_eq_mul_inv,mul_inv]; ring
  apply Nat.twoStepInduction
  · simp [phaseValue_zero]
  · simpa [phaseValue_one] using hθ.symm
  · intro s h₀ h₁
    rw [phaseValue_step,h₀,h₁,hcoef]
    push_cast
    have h := Real.cos_add ((s : ℝ)*θ + θ) θ
    have h' := Real.cos_sub ((s : ℝ)*θ + θ) θ
    have hleft : (s : ℝ)*θ + θ + θ = ((s : ℝ)+2)*θ := by ring
    have hmid : (s : ℝ)*θ + θ = ((s : ℝ)+1)*θ := by ring
    rw [hleft,hmid] at h
    rw [add_sub_cancel_right,hmid] at h'
    linarith

noncomputable def calibrated (s R : ℕ) (hR : 0 < R) : CalibratedBlock s R where
  weight := nu
  total := nu_total hR
  box_bound := fun P hp => nu_rectangle hR P hp

theorem used_expectation {s : ℕ} (hR : 0 < R) :
    (calibrated s R hR).expectedSupport = (R : ℝ)*(1-phaseValue R s) := by
  classical
  have havoid (r : Fin R) :
      (∑ w : TileWord s R, if (∀ c, w c ≠ some r) then nu w else 0) = phaseValue R s := by
    have h := nu_rectangle_identity (s:=s) (fun _ => avoid r)
    rw [← avoid_score hR r s, ← h]
    apply Finset.sum_congr rfl
    intro w _
    by_cases hh : ∀ c, w c ≠ some r
    · simp [avoid,hh]
    · simp [avoid,hh]
  have hused (r : Fin R) :
      (∑ w : TileWord s R, if r ∈ tileUsed w then nu w else 0) = 1 - phaseValue R s := by
    have hterm (w : TileWord s R) :
        (if r ∈ tileUsed w then nu w else 0) =
          nu w - (if ∀ c, w c ≠ some r then nu w else 0) := by
      by_cases h : r ∈ tileUsed w
      · obtain ⟨c,hc⟩ := (mem_tileUsed w r).mp h
        have hn : ¬ ∀ c, w c ≠ some r := fun hn => (hn c) hc
        simp [h,hn]
      · have hh : ∀ c, w c ≠ some r := fun c hc => h ((mem_tileUsed w r).mpr ⟨c,hc⟩)
        simp [h,hh]
    simp_rw [hterm,Finset.sum_sub_distrib,havoid r,nu_total hR]
  unfold CalibratedBlock.expectedSupport
  change (∑ w : TileWord s R, nu w * (tileSupport w : ℝ)) = _
  have hsum (w : TileWord s R) :
      ((tileSupport w : ℕ) : ℝ) = ∑ r : Fin R, if r ∈ tileUsed w then (1 : ℝ) else 0 := by
    rw [Finset.sum_boole]
    have he : Finset.univ.filter (fun r => r ∈ tileUsed w) = tileUsed w := by ext r; simp
    rw [he]
    rfl
  simp_rw [hsum,Finset.mul_sum,mul_ite,mul_one,mul_zero]
  rw [Finset.sum_comm]
  simp_rw [hused]
  simp [Finset.sum_const,nsmul_eq_mul]
  ring

end PHP.Phase
