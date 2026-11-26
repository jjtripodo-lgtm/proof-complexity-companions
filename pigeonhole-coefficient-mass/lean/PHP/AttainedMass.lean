import PHP.FiniteMassClosure
import PHP.FunctionalFiniteRate

namespace PHP

open Set
open scoped BigOperators

private theorem continuous_normCube {m n : ℕ} : Continuous (@normCube m n) := by
  classical
  unfold normCube
  apply continuous_finset_sum
  intro x _
  exact (continuous_apply x).abs

private theorem continuous_cube_value {m n : ℕ} : Continuous (@evalVector m n) := by
  classical
  apply continuous_pi
  intro x
  unfold evalVector
  apply continuous_finset_sum
  intro c _
  exact (continuous_apply c).mul continuous_const

/-- A lower infimum in the finite model is actually reached by an original finite
certificate. Consolidating equal literal cubes keeps the feasible set compact. -/
theorem coefficient_minimum_exists {m n : ℕ} {A : Cube m n → Prop} {B : ℝ}
    (h : BoundedCombination A (fun _ => 1) B) :
    ∃ (s : ℕ) (r : Refutation A s), ∀ (t : ℕ) (r' : Refutation A t), r.mass ≤ r'.mass := by
  classical
  let F := CoefficientBudget A B ∩ evalVector ⁻¹' ({fun _ : Board m n => 1} : Set (Board m n → ℝ))
  have hC : IsCompact F := (coefficientBudget_isCompact A B).inter_right
    (isClosed_singleton.preimage continuous_cube_value)
  have hne : F.Nonempty := by
    obtain ⟨a,ha,he⟩ := boundedCombination_iff_vector.mp h
    exact ⟨a,ha,he⟩
  obtain ⟨a,ha,hmin⟩ := hC.exists_isMinOn hne continuous_normCube.continuousOn
  have hval : evalVector a = fun _ => 1 := ha.2
  have hcost : normCube a ≤ B := ha.1.1
  let comb : Combination m n (Cube m n) := ⟨id,a⟩
  have hlegal : comb.legal A := by
    intro c hc
    exact Classical.byContradiction (fun h => hc (ha.1.2 c h))
  have hid (x : Board m n) : comb.value x = 1 := congrFun hval x
  obtain ⟨s,r,hr⟩ := Combination.refutation_of_value_one comb hlegal hid
  refine ⟨s,r,fun t r' => ?_⟩
  rw [hr]
  change normCube a ≤ r'.mass
  by_cases hsmall : r'.mass ≤ B
  · let comb' : Combination m n (Fin t) := ⟨r'.cube,r'.coeff⟩
    have hC' : BoundedCombination A (fun _ => 1) r'.mass :=
      ⟨Fin t,inferInstance,comb',fun i _ => r'.legal i,r'.identity,le_rfl⟩
    obtain ⟨a',ha',hv'⟩ := boundedCombination_iff_vector.mp hC'
    have hF : a' ∈ F := ⟨⟨ha'.1.trans hsmall,ha'.2⟩,hv'⟩
    exact (hmin hF).trans ha'.1
  · exact hcost.trans (le_of_not_ge hsmall)

theorem plain_optimum_attained {m n : ℕ} (hm : n < m) :
    ∃ (s : ℕ) (r : Refutation (@Plain m n) s), r.mass = optimalPlainMass m n := by
  obtain ⟨s,r,h⟩ := coefficient_minimum_exists (plain_exponential_seed hm)
  refine ⟨s,r,le_antisymm ?_ (optimal_plain_le_certificate r)⟩
  apply le_csInf (plainMassSet_nonempty hm)
  rintro _ ⟨_,r',rfl⟩
  exact h _ r'

theorem functional_optimum_attained {m n : ℕ} (hm : n < m) :
    ∃ (s : ℕ) (r : Refutation (@Functional m n) s), r.mass = optimalFunctionalMass m n := by
  obtain ⟨s,r,_⟩ := functional_general_upper hm
  let comb : Combination m n (Fin s) := ⟨r.cube,r.coeff⟩
  have hC : BoundedCombination (@Functional m n) (fun _ => 1) r.mass :=
    ⟨Fin s,inferInstance,comb,fun i _ => r.legal i,r.identity,le_rfl⟩
  obtain ⟨t,r',h⟩ := coefficient_minimum_exists hC
  refine ⟨t,r',le_antisymm ?_ ?_⟩
  · apply le_csInf (show (functionalMassSet m n).Nonempty from ⟨r.mass,s,r,rfl⟩)
    rintro _ ⟨_,g,rfl⟩
    exact h _ g
  · apply csInf_le _ (show r'.mass ∈ functionalMassSet m n from ⟨t,r',rfl⟩)
    refine ⟨1,?_⟩
    rintro _ ⟨_,g,rfl⟩
    exact g.one_le_mass

end PHP
