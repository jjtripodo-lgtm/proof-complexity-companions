import PHP.BlockLayout
import PHP.ProductLaw
import PHP.SymmetricLift
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.FieldSimp

namespace PHP.BlockLayout

open scoped BigOperators

variable {k m n : ℕ}

abbrev Assembly (k : ℕ) := Fin k → Block.Tile

noncomputable def weight (t : Assembly k) : ℝ := ∏ g, Block.tileWeight (t g)

noncomputable def permMass (m : ℕ) : ℝ := Fintype.card (Equiv.Perm (Fin m))

theorem permMass_pos (m : ℕ) : 0 < permMass m := by
  have hp : 0 < Fintype.card (Equiv.Perm (Fin m)) := Fintype.card_pos
  unfold permMass
  exact_mod_cast hp

noncomputable def sampleWeight (D : BlockLayout k m n) (σ : Equiv.Perm (Fin m))
    (a : Word m n) : ℝ := by
  classical
  exact ∑ t : Assembly k, if D.embedWord σ t = a then weight t else 0

noncomputable def smallLaw (D : BlockLayout k m n) (a : Word m n) : ℝ :=
  (permMass m)⁻¹ * ∑ σ : Equiv.Perm (Fin m), D.sampleWeight σ a

/-- Reindex an arbitrary test through the finite push-forward law. -/
theorem sample_moment (D : BlockLayout k m n) (σ : Equiv.Perm (Fin m))
    (f : Word m n → ℝ) :
    (∑ a, D.sampleWeight σ a * f a) =
      ∑ t : Assembly k, weight t * f (D.embedWord σ t) := by
  classical
  unfold sampleWeight
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  simp_rw [ite_mul,zero_mul]
  rw [Finset.sum_eq_single (D.embedWord σ t)]
  · simp
  · intro a _ hn
    simp [Ne.symm hn]
  · simp

theorem small_moment (D : BlockLayout k m n) (f : Word m n → ℝ) :
    (∑ a, D.smallLaw a * f a) =
      (permMass m)⁻¹ * ∑ σ : Equiv.Perm (Fin m),
        ∑ t : Assembly k, weight t * f (D.embedWord σ t) := by
  classical
  calc
    _ = ∑ a, (permMass m)⁻¹ * ∑ σ : Equiv.Perm (Fin m), D.sampleWeight σ a * f a := by
      apply Finset.sum_congr rfl
      intro a _
      rw [smallLaw,mul_assoc,Finset.sum_mul]
    _ = (permMass m)⁻¹ * ∑ a, ∑ σ : Equiv.Perm (Fin m), D.sampleWeight σ a * f a := by
      rw [Finset.mul_sum]
    _ = _ := by
      rw [Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro σ _
      exact D.sample_moment σ f

def relabel (π : Equiv.Perm (Fin m)) (a : Word m n) : Word m n :=
  fun j => (a j).map π

theorem relabel_injective (π : Equiv.Perm (Fin m)) :
    Function.Injective (@relabel m n π) := by
  intro a b h
  funext j
  have he := congrFun h j
  cases ha : a j <;> cases hb : b j <;>
    simp_all [relabel,π.injective.eq_iff]

def rightPerm (π : Equiv.Perm (Fin m)) : Equiv.Perm (Equiv.Perm (Fin m)) where
  toFun σ := σ.trans π
  invFun σ := σ.trans π.symm
  left_inv σ := by ext i; simp
  right_inv σ := by ext i; simp

theorem sample_relabel (D : BlockLayout k m n) (σ π : Equiv.Perm (Fin m))
    (a : Word m n) : D.sampleWeight (σ.trans π) (relabel π a) = D.sampleWeight σ a := by
  classical
  unfold sampleWeight
  apply Finset.sum_congr rfl
  intro t _
  rw [D.embedWord_relabel]
  have he : (fun j => (D.embedWord σ t j).map π) = relabel π a ↔
      D.embedWord σ t = a := (relabel_injective π).eq_iff
  simp [he]

theorem small_invariant (D : BlockLayout k m n) : RowInvariant D.smallLaw := by
  intro π a
  have he := Fintype.sum_equiv (rightPerm π)
    (fun σ => D.sampleWeight σ a)
    (fun τ => D.sampleWeight τ (relabel π a))
    (fun σ => (D.sample_relabel σ π a).symm)
  change D.smallLaw (relabel π a) = D.smallLaw a
  unfold smallLaw
  rw [← he]

noncomputable def tileTest (D : BlockLayout k m n) (σ : Equiv.Perm (Fin m))
    (C : Cube m n) (g : Fin k) (t : Block.Tile) : ℝ := by
  classical
  exact if ∀ c, Accept C (D.cols (g,c)) (D.label σ g (t c))
    then Block.tileWeight t else 0

theorem eval_times_weight (D : BlockLayout k m n) (σ : Equiv.Perm (Fin m))
    (C : Cube m n) (hC : D.OutsideAccept C) (t : Assembly k) :
    weight t * eval C (D.embedWord σ t).board =
    ∏ g, D.tileTest σ C g (t g) := by
  classical
  by_cases h : ∀ g c, Accept C (D.cols (g,c)) (D.label σ g (t g c))
  · have hh := (D.holds_embedWord σ t C).mpr ⟨hC,h⟩
    have he : ∀ g, D.tileTest σ C g (t g) = Block.tileWeight (t g) := by
      intro g
      simp [tileTest,h g]
    simp only [eval,if_pos hh,mul_one,he,weight]
  · have hh : ¬ Holds C (D.embedWord σ t).board := fun hh => h ((D.holds_embedWord σ t C).mp hh).2
    have hh' : ∃ g, ¬ ∀ c, Accept C (D.cols (g,c)) (D.label σ g (t g c)) := by
      by_contra hf
      exact h (fun g => not_not.mp (fun hg => hf ⟨g,hg⟩))
    obtain ⟨g,hg⟩ := hh'
    have hz : D.tileTest σ C g (t g) = 0 := by simp [tileTest,hg]
    rw [show eval C (D.embedWord σ t).board = 0 by simp [eval,hh],mul_zero]
    exact (Finset.prod_eq_zero (f := fun g => D.tileTest σ C g (t g)) (Finset.mem_univ g) hz).symm

theorem sample_calibrated (D : BlockLayout k m n) (σ : Equiv.Perm (Fin m))
    (C : Cube m n) : |∑ a, D.sampleWeight σ a * eval C a.board| ≤ 1 := by
  classical
  rw [D.sample_moment σ (fun a => eval C a.board)]
  by_cases h : D.OutsideAccept C
  · simp_rw [D.eval_times_weight σ C h]
    apply rectangle_product_bound
    intro g
    exact Block.rectangle_semantic (fun c v => Accept C (D.cols (g,c)) (D.label σ g v))
      (fun c => D.accept_label_allowed σ C g c)
  · have hz (t : Assembly k) : eval C (D.embedWord σ t).board = 0 := by
      have hh : ¬ Holds C (D.embedWord σ t).board := fun hh => h ((D.holds_embedWord σ t C).mp hh).1
      simp [eval,hh]
    simp [hz]

theorem small_calibrated (D : BlockLayout k m n) (C : Cube m n) :
    |∑ a, D.smallLaw a * eval C a.board| ≤ 1 := by
  classical
  rw [D.small_moment (fun a => eval C a.board), Finset.mul_sum]
  apply calibrated_mixture
  · intro σ
    exact inv_nonneg.mpr (permMass_pos m).le
  · simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ]
    change permMass m * (permMass m)⁻¹ = 1
    exact mul_inv_cancel₀ (permMass_pos m).ne' 
  · intro σ
    rw [← D.sample_moment σ (fun a => eval C a.board)]
    exact D.sample_calibrated σ C

end PHP.BlockLayout
