import PHP.BoundedCombination
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Order.Group
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Order.Compact

namespace PHP
open Finset Filter
open scoped BigOperators Topology

noncomputable def normCube {m n : ℕ} (a : Cube m n → ℝ) : ℝ := ∑ c, |a c|
noncomputable def evalVector {m n : ℕ} (a : Cube m n → ℝ) (x : Board m n) : ℝ :=
  ∑ c, a c*eval c x

def CoefficientBudget {m n : ℕ} (A : Cube m n → Prop) (B : ℝ) :
    Set (Cube m n → ℝ) :=
  { a | normCube a ≤ B ∧ ∀ c, ¬ A c → a c = 0 }

theorem boundedCombination_iff_vector {m n : ℕ} {A : Cube m n → Prop}
    {f : Board m n → ℝ} {B : ℝ} :
    BoundedCombination A f B ↔ f ∈ evalVector '' CoefficientBudget A B := by
  classical
  constructor
  · rintro ⟨I,inst,E,hE,hv,hc⟩
    let a : Cube m n → ℝ := fun c => ∑ i : I, if E.cube i = c then E.coeff i else 0
    have ha (c : Cube m n) (hc : ¬ A c) : a c = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases h : E.cube i = c
      · rw [if_pos h]
        by_contra hn
        exact hc (h ▸ hE i hn)
      · exact if_neg h
    have hnorm : normCube a ≤ E.cost := by
      unfold normCube
      calc
        _ ≤ ∑ c : Cube m n, ∑ i : I, |if E.cube i = c then E.coeff i else 0| :=
          Finset.sum_le_sum (fun c _ => Finset.abs_sum_le_sum_abs _ _)
        _ = E.cost := by
          unfold Combination.cost
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_eq_single (E.cube i)]
          · simp
          · intro c _ hc'; simp [Ne.symm hc']
          · simp
    refine ⟨a,⟨hnorm.trans hc,ha⟩,?_⟩
    funext x
    rw [←hv x]
    unfold evalVector Combination.value
    simp_rw [a,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single (E.cube i)]
    · simp
    · intro c _ hc'; simp [Ne.symm hc']
    · simp
  · rintro ⟨a,⟨hcost,hzero⟩,rfl⟩
    have he : (⟨id, a⟩ : Combination m n (Cube m n)).legal A := by
      intro c h
      exact Classical.byContradiction fun h' => h (hzero c h')
    exact ⟨Cube m n,inferInstance,⟨id,a⟩,he,fun _ => rfl,hcost⟩

theorem coefficientBudget_isClosed {m n : ℕ} (A : Cube m n → Prop) (B : ℝ) :
    IsClosed (CoefficientBudget A B) := by
  classical
  have hnorm : Continuous (@normCube m n) := by
    unfold normCube
    apply continuous_finset_sum
    intro c _
    exact (continuous_apply c).abs
  have hole : IsClosed {a : Cube m n → ℝ | ∀ c, ¬ A c → a c = 0} := by
    have he : {a : Cube m n → ℝ | ∀ c, ¬ A c → a c = 0} =
        ⋂ (c : { c : Cube m n // ¬ A c }), {a : Cube m n → ℝ | a c = 0} := by
      ext a
      simp
    rw [he]
    exact isClosed_iInter (fun c => isClosed_eq (continuous_apply c.val) continuous_const)
  exact (isClosed_le hnorm continuous_const).inter hole

theorem coefficientBudget_isCompact {m n : ℕ} (A : Cube m n → Prop) (B : ℝ) :
    IsCompact (CoefficientBudget A B) := by
  have hbox : IsCompact {a : Cube m n → ℝ | ∀ c, a c ∈ Set.Icc (-B) B} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  refine hbox.of_isClosed_subset (coefficientBudget_isClosed A B) ?_
  intro a ha c
  apply abs_le.mp
  have hnorm : |a c| ≤ normCube a :=
    Finset.single_le_sum (f:=fun i => |a i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ c)
  exact hnorm.trans ha.1

private theorem continuous_evalVector {m n : ℕ} :
    Continuous (@evalVector m n) := by
  apply continuous_pi
  intro x
  unfold evalVector
  apply continuous_finset_sum
  intro c _
  exact (continuous_apply c).mul continuous_const

/-- On a fixed finite Boolean board, uniformly bounded masses survive
pointwise limits without assuming a minimum has been found. -/
theorem boundedCombination_closed {m n : ℕ} {A : Cube m n → Prop} {B : ℝ} :
    IsClosed {f : Board m n → ℝ | BoundedCombination A f B} := by
  have he : {f : Board m n → ℝ | BoundedCombination A f B} =
      evalVector '' CoefficientBudget A B := by
    ext f
    exact boundedCombination_iff_vector
  rw [he]
  exact ((coefficientBudget_isCompact A B).image continuous_evalVector).isClosed

theorem boundedCombination_tendsto {α : Type*} {l : Filter α} [NeBot l] {m n : ℕ}
    {A : Cube m n → Prop} {B : ℝ} {f : α → Board m n → ℝ} {g : Board m n → ℝ}
    (h : ∀ x, Tendsto (fun i => f i x) l (𝓝 (g x)))
    (hF : ∀ᶠ i in l, BoundedCombination A (f i) B) :
    BoundedCombination A g B :=
  boundedCombination_closed.mem_of_tendsto (tendsto_pi_nhds.mpr h) hF

end PHP
