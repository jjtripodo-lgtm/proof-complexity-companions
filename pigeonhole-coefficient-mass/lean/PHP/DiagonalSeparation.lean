import PHP.FunctionalCubic
import PHP.PaperRate

namespace PHP

/-- An end-to-end polynomial versus exponential separation in the same
real-coefficient literal-weakening model on the full Boolean board.
The only difference is the addition of the within-row collision sources. -/
theorem diagonal_separation (n : ℕ) (hn : 1 ≤ n) :
    (∃ (t : ℕ) (r : Refutation (@Functional (2*n) n) t),
      r.mass ≤ 16*(n : ℝ)^3) ∧
    (∀ (t : ℕ) (r : Refutation (@Plain (2*n) n) t),
      Real.exp ((149/1000 : ℝ)*n - 8) ≤ r.mass) :=
  ⟨functional_cubic n hn, fun _ r => plain_paper_rate hn (by rfl) r⟩

end PHP
