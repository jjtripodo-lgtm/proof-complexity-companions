import PHP.MatchingLaw

namespace PHP
open Finset
open scoped BigOperators

theorem matching_test_bound {m n : ℕ} (hn : 4 ≤ n) (hm : n ≤ m)
    (e : Fin n ↪ Fin m) (C : Cube m n) :
    |∑ a, matchingLaw e a * eval C a.board| ≤ 1 := by
  classical
  rw [matching_moment]
  simp_rw [matching_product_test e C]
  let P := positiveCols C
  let rest := P.map e
  have hpr (j : Fin n) (hj : j ∈ P) : ∃ i, C (i,j) = some true :=
    (positiveCols_mem C j).mp hj
  let target : Fin m → Fin m := fun r => if h : ∃ j ∈ P, e j = r then
    Classical.choose (hpr (Classical.choose h) (Classical.choose_spec h).1) else r
  have ht (j : Fin n) (hj : j ∈ P) : C (target (e j),j) = some true := by
    have h : ∃ k ∈ P, e k = e j := ⟨j,hj,rfl⟩
    unfold target
    rw [dif_pos h]
    have hs := Classical.choose_spec (hpr (Classical.choose h) (Classical.choose_spec h).1)
    have he := e.injective (Classical.choose_spec h).2
    let v := Classical.choose (hpr (Classical.choose h) (Classical.choose_spec h).1)
    exact (congrArg (fun k => C (v,k)) he).symm.trans hs
  let allowed : Equiv.Perm (Fin m) → Prop := fun σ => ∀ r ∈ rest, σ r = target r
  have htotal (σ : Equiv.Perm (Fin m)) :
      |∏ j : Fin n, colFactor C j (σ (e j))| ≤
        if allowed σ then (2:ℝ)^P.card else 0 := by
    by_cases h : allowed σ
    · rw [if_pos h,Finset.abs_prod]
      have hm' : (∏ j : Fin n, if j ∈ P then (2:ℝ) else 1) = 2^P.card := by
        rw [Finset.prod_ite]
        simp
      rw [←hm']
      exact Finset.prod_le_prod (fun _ _ => abs_nonneg _)
        (fun j _ => col_factor_bound (σ (e j)))
    · rw [if_neg h]
      have he : ∃ r ∈ rest, σ r ≠ target r := by
        unfold allowed at h
        push_neg at h
        exact h
      obtain ⟨r,hr,hnr⟩ := he
      obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hr
      rw [Finset.prod_eq_zero (Finset.mem_univ j) (col_factor_zero (C:=C) (j:=j) (p:=target (e j)) (i:=σ (e j)) (ht j hj) hnr),abs_zero]
  have hden : 0 < (m.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos m
  rw [abs_div,abs_of_pos hden,div_le_iff₀ hden,one_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum fun σ _ => htotal σ).trans
  by_cases hex : ∃ σ, allowed σ
  · obtain ⟨σ,hσ⟩ := hex
    have hc : (Finset.univ.filter allowed).card = (m-P.card).factorial := by
      simpa [allowed,rest] using pinned_perm_finset_card rest target σ hσ
    rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,hc]
    have hp : P.card ≤ n := by simpa using P.card_le_univ
    have h := pinned_mass_le_factorial hn hm hp
    exact_mod_cast (by simpa [mul_comm] using h)
  · have hz : ∀ σ, ¬ allowed σ := fun σ h => hex ⟨σ,h⟩
    simp [hz,hden.le]

end PHP
