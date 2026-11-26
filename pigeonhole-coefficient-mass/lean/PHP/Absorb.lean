import PHP.UpperStep
import Mathlib.Analysis.SpecificLimits.Basic

namespace PHP

/-- Eliminate the circular fallback with finitely many explicit substitutions.
No existence of a minimum-mass certificate is needed. -/
theorem bounded_absorb {m n : ℕ} {A θ E : ℝ}
    (hA : 0 ≤ A) (hθ : 0 ≤ θ) (hθ' : θ < 1)
    (hE : 0 < E)
    (hinit : ∃ C, BoundedCombination (@Plain m n) (fun _ => 1) C)
    (hstep : ∀ C, BoundedCombination (@Plain m n) (fun _ => 1) C →
      BoundedCombination (@Plain m n) (fun _ => 1) (A+θ*C)) :
    BoundedCombination (@Plain m n) (fun _ => 1) (A/(1-θ)+E) := by
  obtain ⟨C,hC⟩ := hinit
  let U := A/(1-θ)
  have hU : 0 ≤ U := div_nonneg hA (by linarith)
  have hfixed : A + θ*U = U := by
    have h := (eq_div_iff (by linarith : 1-θ ≠ 0)).1 (show U = A/(1-θ) from rfl)
    linarith only [h]
  have hc (k : ℕ) : BoundedCombination (@Plain m n) (fun _ => 1) (U + θ^k*C) := by
    induction k with
    | zero => exact hC.cost_mono (by simpa using (le_add_of_nonneg_left (a:=C) hU))
    | succ k ih =>
      have hh := hstep _ ih
      have he : A+θ*(U+θ^k*C) = U+θ^(k+1)*C := by
        rw [pow_succ, mul_add,← add_assoc,hfixed]
        ring
      exact he ▸ hh
  by_cases hCz : C ≤ 0
  · exact (hc 0).cost_mono (by rw [pow_zero,one_mul]; linarith)
  · have hCp : 0 < C := lt_of_not_ge hCz
    obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one (div_pos hE hCp) hθ'
    exact (hc k).cost_mono (add_le_add_left ((lt_div_iff₀ hCp).mp hk).le _)

end PHP
