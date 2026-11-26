import PHP.AlgebraicNormalForm
import PHP.PaperRate
import PHP.FunctionalCubic

namespace PHP
open MvPolynomial
open scoped BigOperators

/-- Algebraic identity for a list of weakenings; this permits repeated
and conflicting source/multiplier literals. Boolean/twin ideal terms
contribute no mass. This is the charged decomposition used in Definitions
6–9 and Remark 10 of Potechin–Zhang. -/
def RawWeakeningIdentity {m n t : ℕ} (s d : Fin t → Cube m n) (a : Fin t → ℝ) : Prop :=
  ((∑ i, C (a i) * (cubePolynomial (s i) * cubePolynomial (d i))) - 1) ∈
    booleanTwinIdeal (Cell m n) ℝ

/-- Normalize arbitrary source times literal-monomial weakenings on the
full board. Shared literals are idempotent; inconsistent products vanish
and their coefficients are replaced by zero. This does not increase mass. -/
theorem normalize_raw_weakenings {m n t : ℕ} {S A : Cube m n → Prop}
    (s d : Fin t → Cube m n) (a : Fin t → ℝ)
    (hmono : ∀ {c e}, Extends e c → A c → A e)
    (hsource : ∀ i, S (s i))
    (hlegal : ∀ c, S c → A c)
    (h : RawWeakeningIdentity s d a) :
    ∃ r : Refutation A t, r.mass ≤ ∑ i, |a i| := by
  classical
  unfold RawWeakeningIdentity at h
  have hzero := (boolean_twin_ideal_iff _).mp h
  let r : Refutation A t :=
    { cube := fun i => join (s i) (d i)
      coeff := fun i => if Compatible (s i) (d i) then a i else 0
      legal := fun i => hmono (join_extends_left _ _) (hlegal _ (hsource i))
      identity := fun x => by
        have hv := hzero x
        simp only [map_sub,map_sum,map_mul,map_one,assignmentEval_C,evaluate_cubePolynomial,
          sub_eq_zero] at hv
        rw [← hv]
        apply Finset.sum_congr rfl
        intro i _
        rw [eval_product]
        by_cases hi : Compatible (s i) (d i) <;> simp [hi] }
  exact ⟨r,Finset.sum_le_sum (fun i _ => by
    change |if Compatible (s i) (d i) then a i else (0:ℝ)| ≤ |a i|
    split <;> simp)⟩

/-- Extending the model statement beyond the disjoint normal form:
the same budgets are feasible in the original algebraic plain system and
the finite real cube system, in both directions. -/
theorem plain_budget_iff_algebraic {m n : ℕ} (B : ℝ) :
    (∃ (t : ℕ) (r : Refutation (@Plain m n) t), r.mass ≤ B) ↔
    (∃ (t : ℕ) (s d : Fin t → Cube m n) (a : Fin t → ℝ),
      (∀ i, PlainSource (s i)) ∧ RawWeakeningIdentity s d a ∧ (∑ i, |a i|) ≤ B) := by
  constructor
  · rintro ⟨t,r,hr⟩
    obtain ⟨s,d,hs,h⟩ := plain_refutation_normal_form r
    exact ⟨t,s,d,r.coeff,fun i => (hs i).1,h,hr⟩
  · rintro ⟨t,s,d,a,hs,h,ha⟩
    obtain ⟨r,hr⟩ := normalize_raw_weakenings s d a
      (fun he hc => plain_mono he hc) hs (fun c hc => by
        apply (plain_iff_normalized_weakening c).2
        exact ⟨c,(fun _ => none),hc,(fun _ _ _ => rfl),by funext ij; cases hci : c ij <;> simp [join,hci,Option.orElse]⟩) h
    exact ⟨t,r,hr.trans ha⟩

theorem functional_budget_iff_algebraic {m n : ℕ} (B : ℝ) :
    (∃ (t : ℕ) (r : Refutation (@Functional m n) t), r.mass ≤ B) ↔
    (∃ (t : ℕ) (s d : Fin t → Cube m n) (a : Fin t → ℝ),
      (∀ i, FunctionalSource (s i)) ∧ RawWeakeningIdentity s d a ∧ (∑ i, |a i|) ≤ B) := by
  constructor
  · rintro ⟨t,r,hr⟩
    obtain ⟨s,d,hs,h⟩ := functional_refutation_normal_form r
    exact ⟨t,s,d,r.coeff,fun i => (hs i).1,h,hr⟩
  · rintro ⟨t,s,d,a,hs,h,ha⟩
    obtain ⟨r,hr⟩ := normalize_raw_weakenings s d a
      (fun he hc => functional_mono he hc) hs (fun c hc => by
        apply (functional_iff_normalized_weakening c).2
        exact ⟨c,(fun _ => none),hc,(fun _ _ _ => rfl),by funext ij; cases hci : c ij <;> simp [join,hci,Option.orElse]⟩) h
    exact ⟨t,r,hr.trans ha⟩

/-- The original paper-model separation in one statement. The algebraic
lower bound accepts overlapping multipliers, and the upper produces a
free-ideal correction rather than an equality on a restricted domain. -/
theorem algebraic_diagonal_separation (n : ℕ) (hn : 1 ≤ n) :
    (∀ t (s d : Fin t → Cube (2*n) n) (a : Fin t → ℝ),
      (∀ i, PlainSource (s i)) → RawWeakeningIdentity s d a →
        Real.exp ((149/1000 : ℝ)*n-8) ≤ ∑ i, |a i|) ∧
    (∃ (t : ℕ) (s d : Fin t → Cube (2*n) n) (a : Fin t → ℝ),
      (∀ i, FunctionalSource (s i)) ∧ RawWeakeningIdentity s d a ∧
        (∑ i, |a i|) ≤ 16*(n:ℝ)^3) := by
  constructor
  · intro t s d a hs ha
    obtain ⟨r,u,hu⟩ := (plain_budget_iff_algebraic (∑ i, |a i|)).mpr
      ⟨t,s,d,a,hs,ha,le_rfl⟩
    exact (plain_paper_rate hn le_rfl u).trans hu
  · exact (functional_budget_iff_algebraic _).mp (functional_cubic n hn)

end PHP
