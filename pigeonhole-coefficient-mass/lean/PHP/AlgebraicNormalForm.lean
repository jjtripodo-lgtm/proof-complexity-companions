import PHP.BooleanTwinIdeal

namespace PHP
open MvPolynomial Finset
open scoped BigOperators

noncomputable def literalFactor {m n : ℕ} (c : Cube m n) (ij : Cell m n) :
    TwinPolynomials (Cell m n) ℝ :=
  match c ij with
  | none => 1
  | some true => X (.inl ij)
  | some false => X (.inr ij)

noncomputable def cubePolynomial {m n : ℕ} (c : Cube m n) :
    TwinPolynomials (Cell m n) ℝ := ∏ ij, literalFactor c ij

private theorem evaluate_literalFactor {m n : ℕ} (c : Cube m n) (ij : Cell m n) (x : Board m n) :
    assignmentEval x (literalFactor c ij) = if ∀ b, c ij = some b → x ij = b then 1 else 0 := by
  classical
  cases hc : c ij with
  | none => simp [literalFactor,hc]
  | some b =>
    cases b <;> cases hx : x ij <;> simp [literalFactor,hc,assignmentEval_X,boolValue,hx]

theorem evaluate_cubePolynomial {m n : ℕ} (c : Cube m n) (x : Board m n) :
    assignmentEval x (cubePolynomial c) = eval c x := by
  classical
  rw [cubePolynomial,map_prod]
  by_cases ht : Holds c x
  · rw [show eval c x = 1 by simp [eval,ht]]
    apply Finset.prod_eq_one
    intro ij _
    rw [evaluate_literalFactor,if_pos (ht ij)]
  · rw [show eval c x = 0 by simp [eval,ht]]
    have ha : ∃ ij, ¬ (∀ b, c ij = some b → x ij = b) := by
      by_contra h
      apply ht
      intro ij b hb
      exact (Classical.byContradiction fun he => h ⟨ij,he⟩) b hb
    obtain ⟨ij,hi⟩ := ha
    exact Finset.prod_eq_zero (Finset.mem_univ ij) (by rw [evaluate_literalFactor,if_neg hi])

theorem cubePolynomial_join {m n : ℕ} {c d : Cube m n} (h : LiteralDisjoint c d) :
    cubePolynomial (join c d) = cubePolynomial c*cubePolynomial d := by
  unfold cubePolynomial
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro ij _
  cases hc : c ij with
  | none => simp [literalFactor,join,hc,Option.orElse]
  | some b =>
    have hd := h ij b hc
    cases b <;> simp [literalFactor,join,hc,hd,Option.orElse]

/-- A finite linear combination equals one on the whole Boolean board iff
its literal-monomial polynomial is one modulo the free Boolean/twin ideal. -/
theorem combination_normal_form {m n : ℕ} {J : Type} [Fintype J] (E : Combination m n J) :
    (∀ x : Board m n, E.value x = 1) ↔
      ((∑ i, C (E.coeff i)*cubePolynomial (E.cube i))-1) ∈ booleanTwinIdeal (Cell m n) ℝ := by
  rw [boolean_twin_ideal_iff]
  constructor <;> intro h x
  · simp only [map_sub,map_sum,map_mul,map_one,assignmentEval_C,evaluate_cubePolynomial,
      sub_eq_zero]
    exact h x
  · have h' := h x
    simp only [map_sub,map_sum,map_mul,map_one,assignmentEval_C,evaluate_cubePolynomial,
      sub_eq_zero] at h'
    exact h'

/-- The original finite proof translates without changing the charged
coefficient list: only the free ideal corrections change the formal sum. -/
theorem plain_refutation_normal_form {m n t : ℕ} (r : Refutation (@Plain m n) t) :
    ∃ s d : Fin t → Cube m n,
      (∀ i, PlainSource (s i) ∧ LiteralDisjoint (s i) (d i)) ∧
      ((∑ i, C (r.coeff i)*(cubePolynomial (s i)*cubePolynomial (d i)))-1) ∈
        booleanTwinIdeal (Cell m n) ℝ := by
  classical
  choose s d hc using fun i => (plain_iff_normalized_weakening (r.cube i)).mp (r.legal i)
  refine ⟨s,d,fun i => ⟨(hc i).1,(hc i).2.1⟩,?_⟩
  have h (i : Fin t) : cubePolynomial (s i)*cubePolynomial (d i) = cubePolynomial (r.cube i) := by
    rw [←cubePolynomial_join (hc i).2.1,(hc i).2.2]
  simp_rw [h]
  exact (combination_normal_form (⟨r.cube,r.coeff⟩ : Combination m n (Fin t))).mp r.identity

theorem functional_refutation_normal_form {m n t : ℕ} (r : Refutation (@Functional m n) t) :
    ∃ s d : Fin t → Cube m n,
      (∀ i, FunctionalSource (s i) ∧ LiteralDisjoint (s i) (d i)) ∧
      ((∑ i, C (r.coeff i)*(cubePolynomial (s i)*cubePolynomial (d i)))-1) ∈
        booleanTwinIdeal (Cell m n) ℝ := by
  classical
  choose s d hc using fun i => (functional_iff_normalized_weakening (r.cube i)).mp (r.legal i)
  refine ⟨s,d,fun i => ⟨(hc i).1,(hc i).2.1⟩,?_⟩
  have h (i : Fin t) : cubePolynomial (s i)*cubePolynomial (d i) = cubePolynomial (r.cube i) := by
    rw [←cubePolynomial_join (hc i).2.1,(hc i).2.2]
  simp_rw [h]
  exact (combination_normal_form (⟨r.cube,r.coeff⟩ : Combination m n (Fin t))).mp r.identity

end PHP
