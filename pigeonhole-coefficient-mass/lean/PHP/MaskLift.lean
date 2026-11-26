import PHP.GroupedCollision

namespace PHP

open scoped BigOperators
open Finset

/-- Extend a cube to an embedded subboard, leaving all other cells free. -/
noncomputable def subboardCube {m n p q : ℕ} (er : Fin p ↪ Fin m) (ec : Fin q ↪ Fin n)
    (C : Cube p q) : Cube m n := by
  classical
  exact fun ij => if h : ∃ k : Cell p q, (er k.1,ec k.2) = ij
    then C (Classical.choose h) else none

def subboard {m n p q : ℕ} (er : Fin p ↪ Fin m) (ec : Fin q ↪ Fin n) (x : Board m n) :
    Board p q := fun ij => x (er ij.1,ec ij.2)

theorem subboardCube_on {m n p q : ℕ} (er : Fin p ↪ Fin m) (ec : Fin q ↪ Fin n)
    (C : Cube p q) (k : Cell p q) : subboardCube er ec C (er k.1,ec k.2) = C k := by
  have he : ∃ l : Cell p q, (er l.1,ec l.2) = (er k.1,ec k.2) := ⟨k,rfl⟩
  unfold subboardCube
  rw [dif_pos he]
  have h := Classical.choose_spec he
  congr 1
  exact Prod.ext (er.injective (congrArg Prod.fst h)) (ec.injective (congrArg Prod.snd h))

theorem subboardCube_holds {m n p q : ℕ} (er : Fin p ↪ Fin m) (ec : Fin q ↪ Fin n)
    (C : Cube p q) (x : Board m n) : Holds (subboardCube er ec C) x ↔ Holds C (subboard er ec x) := by
  classical
  constructor
  · intro h ij b hb
    exact h (er ij.1,ec ij.2) b ((subboardCube_on er ec C ij).trans hb)
  · intro h ij b hb
    by_cases he : ∃ l : Cell p q, (er l.1,ec l.2) = ij
    · obtain ⟨k,rfl⟩ := he
      exact h k b ((subboardCube_on er ec C k).symm.trans hb)
    · simp [subboardCube,he] at hb

theorem covered_complement {m n p q : ℕ} (er : Fin p ↪ Fin m) (ec : Fin q ↪ Fin n)
    (G : Finset (Fin m)) (H : Finset (Fin n))
    (hG : ∀ i, er i ∈ G) (hH : ∀ j : Fin n, j ∈ H ∨ ∃ j', ec j' = j)
    {c : Cube p q} (hc : Plain c) :
    Plain (join (subboardCube er ec c) (zeroRect G H)) ∨
      ¬ Compatible (subboardCube er ec c) (zeroRect G H) := by
  classical
  by_cases h : Compatible (subboardCube er ec c) (zeroRect G H)
  · left
    rcases hc with ⟨i,hi⟩ | ⟨i,k,j,hne,hi,hk⟩
    · left
      refine ⟨er i,?_⟩
      intro j
      rcases hH j with hj | ⟨k,rfl⟩
      · exact join_extends_right h (er i,j) false (by simp [zeroRect,hG i,hj])
      · exact join_extends_left _ _ (er i,ec k) false ((subboardCube_on er ec c (i,k)).trans (hi k))
    · right
      exact ⟨er i,er k,ec j,fun he => hne (er.injective he),
        join_extends_left _ _ _ _ ((subboardCube_on er ec c (i,j)).trans hi),
        join_extends_left _ _ _ _ ((subboardCube_on er ec c (k,j)).trans hk)⟩
  · exact Or.inr h

/-- A mask restores each reduced row axiom to an actual original full-row
axiom. No implicit OR-variable or row-functionality axiom is used. -/
theorem masked_plain_lift {m n p q : ℕ} (er : Fin p ↪ Fin m) (ec : Fin q ↪ Fin n)
    (G : Finset (Fin m)) (H : Finset (Fin n))
    (hG : ∀ i, er i ∈ G) (hH : ∀ j : Fin n, j ∈ H ∨ ∃ j', ec j' = j)
    {B : ℝ} (hr : BoundedCombination (@Plain p q) (fun _ => 1) B) :
    BoundedCombination (@Plain m n) (fun x => bit (Inactive G H x)) B := by
  classical
  obtain ⟨I,inst,E,hlegal,hvalue,hcost⟩ := hr
  let a : Combination m n I := ⟨fun i => subboardCube er ec (E.cube i),E.coeff⟩
  let b : Combination m n Unit := ⟨fun _ => zeroRect G H,fun _ => 1⟩
  let d := a.prod b
  refine ⟨I × Unit,inferInstance,d,?_,?_,?_⟩
  · rintro ⟨i,u⟩ hu
    have hh : E.coeff i ≠ 0 := by
      intro hz
      simp [d,Combination.prod,a,b,hz] at hu
    rcases covered_complement er ec G H hG hH (hlegal i hh) with h | h
    · exact h
    · exfalso
      exact hu (by simp [d,Combination.prod,a,b,h])
  · intro x
    rw [show d.value x = a.value x * b.value x from Combination.value_prod a b x]
    have ha : a.value x = 1 := by
      unfold Combination.value at hvalue ⊢
      simpa [a,eval,subboardCube_holds] using hvalue (subboard er ec x)
    rw [ha,one_mul]
    simp [Combination.value,b,eval,bit,zeroRect_holds]
  · exact (Combination.cost_prod_le a b).trans (by
      simpa [Combination.cost,a,b] using hcost)

end PHP
