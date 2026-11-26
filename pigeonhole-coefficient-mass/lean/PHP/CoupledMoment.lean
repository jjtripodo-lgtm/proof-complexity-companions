import PHP.CoupledLabels
import Mathlib.Data.Finset.Prod

namespace PHP
open Finset
open scoped BigOperators

private theorem iid_two_pins {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    (w : β → ℝ) (P : β → Prop) (hw : ∑ y, w y = 1) (i j : α) (hij : i ≠ j) :
    (∑ f : α → β, iidWeight w f * bit (P (f i) ∧ P (f j))) = (∑ y, w y * bit (P y))^2 := by
  classical
  let Q : α → β → Prop := fun k y => (k = i ∨ k = j) → P y
  have he (f : α → β) : P (f i) ∧ P (f j) ↔ ∀ k, Q k (f k) := by
    constructor
    · rintro ⟨hi,hj⟩ k (rfl|rfl) <;> assumption
    · intro h
      exact ⟨h i (Or.inl rfl),h j (Or.inr rfl)⟩
  simp_rw [he]
  rw [iid_product w Q]
  have h (k : α) : (∑ y : β, w y * bit (Q k y)) =
      if k ∈ ({i,j}:Finset α) then (∑ y : β, w y * bit (P y)) else 1 := by
    by_cases hk : k = i ∨ k = j <;> simp [Q,hk,hw,bit]
  simp_rw [h,Finset.prod_ite]
  have hset : (univ.filter (fun x => x = i ∨ x = j)) = ({i,j}:Finset α) := by ext x; simp
  simp [hset,hij]

theorem active_bins_le_rows {m n L : ℕ} (labels : Fin m → CoupledLabel L)
    (H : Finset (Fin n)) (x : Board m n) :
    (liveGroups (binRows labels) H (univ : Finset (Fin L)) x).card ≤ (allBinRows labels).card := by
  classical
  let S := liveGroups (binRows labels) H (univ : Finset (Fin L)) x
  have h (j : Fin L) (hj : j ∈ S) : 1 ≤ (binRows labels j).card := by
    have hn := (Finset.mem_filter.mp hj).2
    apply Finset.one_le_card.mpr
    by_contra hh
    apply hn
    intro i hi
    exact False.elim (hh ⟨i,hi⟩)
  have he : S.biUnion (binRows labels) ⊆ allBinRows labels := by
    intro i hi
    obtain ⟨j,hj,hi'⟩ := Finset.mem_biUnion.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨j,(Finset.mem_filter.mp hi').2⟩⟩
  calc
    _ = ∑ _j ∈ S, (1:ℕ) := by simp [S]
    _ ≤ ∑ j ∈ S, (binRows labels j).card := Finset.sum_le_sum h
    _ = (S.biUnion (binRows labels)).card := (Finset.card_biUnion
      (fun _ _ _ _ hij => binRows_disjoint labels hij)).symm
    _ ≤ _ := Finset.card_le_card he

private theorem offDiag_mass {m : ℕ} (U : Finset (Fin m)) :
    (U.offDiag.card:ℝ) = ((U.card:ℝ))*((U.card:ℝ)-1) := by
  rw [Finset.offDiag_card]
  have h : U.card ≤ U.card * U.card := by
    by_cases h : U.card = 0
    · simp [h]
    · exact Nat.le_mul_of_pos_right _ (by omega)
  rw [Nat.cast_sub h,Nat.cast_mul]
  ring

theorem coupled_factorial_moment {m L : ℕ} (hL : 0 < L) (a s : ℝ) :
    (∑ labels : Fin m → CoupledLabel L,
      iidWeight (coupledWeight L a s) labels *
      ((allBinRows labels).card:ℝ)*(((allBinRows labels).card:ℝ)-1)) =
       (m:ℝ)*((m:ℝ)-1)*s^2 := by
  classical
  let D := (univ : Finset (Fin m)).offDiag
  have hpair (labels : Fin m → CoupledLabel L) :
      ((allBinRows labels).card:ℝ)*(((allBinRows labels).card:ℝ)-1) =
        ∑ p ∈ D, bit (inBins (labels p.1) ∧ inBins (labels p.2)) := by
    rw [←offDiag_mass]
    have hD : D.filter (fun p => inBins (labels p.1) ∧ inBins (labels p.2)) =
        (allBinRows labels).offDiag := by
      ext p
      simp [D,allBinRows,Finset.mem_offDiag]
      tauto
    have h (p : Fin m × Fin m) :
        bit (inBins (labels p.1) ∧ inBins (labels p.2)) =
          if inBins (labels p.1) ∧ inBins (labels p.2) then (1:ℝ) else 0 := by
      by_cases h' : inBins (labels p.1) ∧ inBins (labels p.2) <;> simp [bit,h']
    simp_rw [h]
    rw [Finset.sum_boole,hD]
  simp_rw [mul_assoc,hpair,Finset.mul_sum]
  rw [Finset.sum_comm]
  have he (p : Fin m × Fin m) (hp : p ∈ D) :
      (∑ labels : Fin m → CoupledLabel L, iidWeight (coupledWeight L a s) labels *
          bit (inBins (labels p.1) ∧ inBins (labels p.2))) = s^2 := by
    have h := (Finset.mem_offDiag.mp hp).2.2
    rw [iid_two_pins _ _ (coupled_weight_sum hL a s) _ _ h,coupled_inBins_weight hL]
  rw [Finset.sum_congr rfl he,Finset.sum_const,nsmul_eq_mul]
  unfold D
  rw [offDiag_mass,Finset.card_univ,Fintype.card_fin,mul_assoc]

end PHP
