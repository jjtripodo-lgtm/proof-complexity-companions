module

public import PHP.PaperRate
public import PHP.FunctionalCubic

public section

namespace PHP

/-- At twice as many pigeons as holes, plain real-coefficient weakening
refutations have exponential coefficient mass whereas the functional system
admits a polynomial-mass refutation. Pigeonhole terms are checked on every
Boolean board. -/
theorem paper_diagonal_separation (n : ℕ) (hn : 1 ≤ n) :
    (∀ t (r : Refutation (@Plain (2*n) n) t), Real.exp ((149/1000 : ℝ)*n-8) ≤ r.mass)
    ∧ (∃ (t : ℕ) (r : Refutation (@Functional (2*n) n) t), r.mass ≤ 16*(n:ℝ)^3) := by
  exact ⟨fun _ r => plain_paper_rate hn le_rfl r, functional_cubic n hn⟩

end PHP
