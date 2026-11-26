import PHP.GroupedCollision

namespace PHP
open scoped BigOperators
open Finset

theorem emptyRow_mono {m n : ℕ} {c d : Cube m n} (h : Extends d c)
    (hc : EmptyRow c) : EmptyRow d := by
  obtain ⟨i,hi⟩ := hc
  exact ⟨i,fun j => h (i,j) false (hi j)⟩

theorem empty_row_cost {m n : ℕ} (i : Fin m) :
    BoundedCombination (@EmptyRow m n) (fun x => bit (Inactive {i} univ x)) 1 := by
  have h : EmptyRow (zeroRect ({i}:Finset (Fin m)) (univ : Finset (Fin n))) :=
    ⟨i,fun j => by simp [zeroRect]⟩
  exact (BoundedCombination.atom _ h).of_eq fun x => by
    unfold eval bit
    split_ifs <;> simp_all [zeroRect_holds]

theorem one_sub_active_rows_cost {m n : ℕ} (s : Finset (Fin m)) :
    BoundedCombination (@EmptyRow m n)
      (fun x => 1-∏ i ∈ s, active {i} univ x) (2^s.card-1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using BoundedCombination.zero (@EmptyRow m n)
  | insert i s hi IH =>
    have hm := IH.mul_left emptyRow_mono (active_cost ({i}:Finset (Fin m)) (univ:Finset (Fin n)))
    have h := hm.add (empty_row_cost (n:=n) i)
    have hp : ((2:ℝ)^s.card-1)*2 + 1 = (2:ℝ)^(insert i s).card-1 := by
      rw [Finset.card_insert_of_notMem hi,pow_succ]
      ring
    rw [hp] at h
    apply h.of_eq
    intro x
    rw [Finset.prod_insert hi]
    unfold active
    ring

/-- A one-surplus seed obtained with singleton row groups on the literal board. -/
theorem plain_exponential_seed_sharp {m n : ℕ} (hm : n < m) :
    BoundedCombination (@Plain m n) (fun _ => 1) (2^(5*n) + 2^(n+1)-1) := by
  classical
  obtain ⟨s,_,hs⟩ := Finset.exists_subset_card_eq (s:=(Finset.univ : Finset (Fin m))) (n:=n+1)
    (by simp; omega)
  have he := (one_sub_active_rows_cost (n:=n) s).legal_mono (A' := @Plain m n) (fun _ => Or.inl)
  rw [hs] at he
  by_cases hn : n = 0
  · subst n
    refine (he.of_eq (fun x => ?_)).cost_mono (by norm_num)
    have h : ∀ i : Fin m, Inactive {i} (univ:Finset (Fin 0)) x :=
      fun _ _ _ j _ => Fin.elim0 j
    have hprod : ∏ i ∈ s, active {i} univ x = 0 := by
      obtain ⟨i,hi⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
      exact Finset.prod_eq_zero hi (by rw [active]; simp only [bit,if_pos (h i),sub_self])
    rw [hprod,sub_zero]
  · have h := grouped_collision_sharp5
      (fun i : Fin m => ({i}:Finset (Fin m))) 1 univ s
        (show 1 ≤ (univ:Finset (Fin n)).card by simp; omega) (by simpa using hs)
        (fun a _ b _ hab => by simpa using hab.symm) (by simp)
    have hc := h.legal_mono (A' := @Plain m n) (fun _ => Or.inr)
    simp only [Nat.cast_one,one_pow,one_mul,Finset.card_univ,Fintype.card_fin] at hc
    have hh := hc.add he
    rw [← add_sub_assoc] at hh
    apply hh.of_eq
    intro x
    ring

/-- A one-surplus seed obtained with singleton row groups on the literal board. -/
theorem plain_exponential_seed {m n : ℕ} (hm : n < m) :
    BoundedCombination (@Plain m n) (fun _ => 1) (2^(8*n) + 2^(n+1)-1) := by
  classical
  obtain ⟨s,_,hs⟩ := Finset.exists_subset_card_eq (s:=(Finset.univ : Finset (Fin m))) (n:=n+1)
    (by simp; omega)
  have he := (one_sub_active_rows_cost (n:=n) s).legal_mono (A' := @Plain m n) (fun _ => Or.inl)
  rw [hs] at he
  by_cases hn : n = 0
  · subst n
    refine (he.of_eq (fun x => ?_)).cost_mono (by norm_num)
    have h : ∀ i : Fin m, Inactive {i} (univ:Finset (Fin 0)) x :=
      fun _ _ _ j _ => Fin.elim0 j
    have hprod : ∏ i ∈ s, active {i} univ x = 0 := by
      obtain ⟨i,hi⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
      exact Finset.prod_eq_zero hi (by rw [active]; simp only [bit,if_pos (h i),sub_self])
    rw [hprod,sub_zero]
  · have h := grouped_collision_bound
      (fun i : Fin m => ({i}:Finset (Fin m))) 1 univ s
        (show 1 ≤ (univ:Finset (Fin n)).card by simp; omega) (by simpa using hs)
        (fun a _ b _ hab => by simpa using hab.symm) (by simp)
    have hc := h.legal_mono (A' := @Plain m n) (fun _ => Or.inr)
    simp only [Nat.cast_one,one_pow,one_mul,Finset.card_univ,Fintype.card_fin] at hc
    have hh := hc.add he
    rw [← add_sub_assoc] at hh
    apply hh.of_eq
    intro x
    ring

end PHP
