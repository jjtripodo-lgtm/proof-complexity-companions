import PHP.GroupedCollision
import Mathlib.Data.Finset.Sort

namespace PHP
open scoped BigOperators
open Finset

noncomputable def liveGroups {m n : ℕ} {ι : Type*} (G : ι → Finset (Fin m))
    (H : Finset (Fin n)) (s : Finset ι) (x : Board m n) : Finset ι := by
  classical exact s.filter (fun i => ¬ Inactive (G i) H x)

/-- Which groups outside the chosen prefix must be inactive. -/
noncomputable def skipped {ι : Type*} [LinearOrder ι] (s j : Finset ι) : Finset ι :=
  (s \ j).filter (fun i => ∃ k ∈ j, i < k)

theorem bit_and {p q : Prop} : bit (p ∧ q) = bit p * bit q := by
  by_cases hp : p <;> by_cases hq : q <;> simp [bit,hp,hq]

theorem prod_bits {ι : Type*} (s : Finset ι) (P : ι → Prop) :
    (∏ i ∈ s, bit (P i)) = bit (∀ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [bit]
  | insert i s hi IH =>
    rw [Finset.prod_insert hi,IH,← bit_and]
    congr 1
    simp

theorem active_eq_bit {m n : ℕ} (G : Finset (Fin m)) (H : Finset (Fin n)) (x : Board m n) :
    active G H x = bit (¬Inactive G H x) := by
  by_cases h : Inactive G H x <;> norm_num [active,bit,h]

def IsOrderedPrefix {ι : Type*} [LinearOrder ι] (t j : Finset ι) : Prop :=
  j ⊆ t ∧ ∀ i ∈ t \ j, ∀ k ∈ j, k ≤ i

theorem exists_unique_prefix {ι : Type*} [LinearOrder ι] (t : Finset ι) (q : ℕ)
    (hq : q ≤ t.card) : ∃! j : Finset ι, j.card = q ∧ IsOrderedPrefix t j := by
  classical
  let j := ((t.sort (· ≤ ·)).take q).toFinset
  have hl : ((t.sort (· ≤ ·)).take q).Nodup := (Finset.sort_nodup (· ≤ ·) t).take
  have hjcard : j.card = q := by
    simp [j,List.toFinset_card_of_nodup hl,Nat.min_eq_left hq]
  have hjsub : j ⊆ t := by
    intro i hi
    have h' : i ∈ (t.sort (· ≤ ·)).take q := List.mem_toFinset.mp hi
    exact (Finset.mem_sort (· ≤ ·)).mp (List.mem_of_mem_take h')
  have hfirst : IsOrderedPrefix t j := by
    refine ⟨hjsub,?_⟩
    intro i hi k hk
    have hk' : k ∈ (t.sort (· ≤ ·)).take q := List.mem_toFinset.mp hk
    have hi' : i ∈ (t.sort (· ≤ ·)).drop q := by
      have h : i ∈ (t.sort (· ≤ ·)) := (Finset.mem_sort (· ≤ ·)).mpr (Finset.mem_sdiff.mp hi).1
      have hh : i ∈ (t.sort (· ≤ ·)).take q ++ (t.sort (· ≤ ·)).drop q := by rwa [List.take_append_drop]
      exact (List.mem_append.mp hh).resolve_left (fun hmem => (Finset.mem_sdiff.mp hi).2 (List.mem_toFinset.mpr hmem))
    have hpair : ((t.sort (· ≤ ·)).take q ++ (t.sort (· ≤ ·)).drop q).Pairwise (· ≤ ·) := by
      rw [List.take_append_drop]
      exact Finset.sort_sorted (· ≤ ·) t
    exact (List.pairwise_append.mp hpair).2.2 k hk' i hi'
  refine ⟨j,⟨hjcard,hfirst⟩,?_⟩
  rintro u ⟨hucard,husub,hu⟩
  by_contra hne
  have hcard : j.card = u.card := hjcard.trans hucard.symm
  have hnu : ¬ u ⊆ j := fun h => hne (Finset.eq_of_subset_of_card_le h hcard.le)
  have hnj : ¬ j ⊆ u := fun h => hne (Finset.eq_of_subset_of_card_le h hcard.ge).symm
  obtain ⟨i,hi,hij⟩ := Finset.not_subset.mp hnu
  obtain ⟨k,hk,hku⟩ := Finset.not_subset.mp hnj
  have hki := hfirst.2 i (Finset.mem_sdiff.mpr ⟨husub hi,hij⟩) k hk
  have hik := hu k (Finset.mem_sdiff.mpr ⟨hjsub hk,hku⟩) i hi
  exact hij (le_antisymm hik hki ▸ hk)

theorem prefix_factor {m n : ℕ} {ι : Type*} [LinearOrder ι] (G : ι → Finset (Fin m))
    (H : Finset (Fin n)) (s j : Finset ι) (x : Board m n) :
    (∏ i ∈ j, active (G i) H x) * (∏ i ∈ skipped s j, bit (Inactive (G i) H x)) =
      bit (j ⊆ s ∧ IsOrderedPrefix (liveGroups G H s x) j) ∨ ¬ j ⊆ s := by
  classical
  by_cases hj : j ⊆ s
  · left
    simp_rw [active_eq_bit]
    rw [prod_bits,prod_bits,← bit_and]
    congr 1
    apply propext
    constructor
    · rintro ⟨ha,hb⟩
      refine ⟨hj,fun i hi => Finset.mem_filter.mpr ⟨hj hi,ha i hi⟩,?_⟩
      intro i hi k hk
      by_contra! hlt
      obtain ⟨hit,hin⟩ := Finset.mem_sdiff.mp hi
      obtain ⟨his,hia⟩ := Finset.mem_filter.mp hit
      exact hia (hb i (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨his,hin⟩,⟨k,hk,hlt⟩⟩))
    · rintro ⟨_,hsub,horder⟩
      refine ⟨fun i hi => (Finset.mem_filter.mp (hsub hi)).2,?_⟩
      intro i hi
      by_contra hin
      obtain ⟨him,k,hk,hki⟩ := Finset.mem_filter.mp hi
      obtain ⟨his,hij⟩ := Finset.mem_sdiff.mp him
      exact (not_le_of_gt hki) (horder i (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨his,hin⟩,hij⟩) k hk)
  · exact Or.inr hj

theorem threshold_prefix_sum {m n : ℕ} {ι : Type*} [LinearOrder ι]
    (G : ι → Finset (Fin m)) (H : Finset (Fin n)) (s : Finset ι) (x : Board m n) (q : ℕ) :
    bit (q ≤ (liveGroups G H s x).card) =
      ∑ j ∈ s.powersetCard q, (∏ i ∈ j, active (G i) H x) *
        (∏ i ∈ skipped s j, bit (Inactive (G i) H x)) := by
  classical
  have hfactor (u : Finset ι) (hu : u ∈ s.powersetCard q) := 
    (prefix_factor G H s u x).resolve_right (not_not_intro (Finset.mem_powersetCard.mp hu).1)
  by_cases hq : q ≤ (liveGroups G H s x).card
  · obtain ⟨j,⟨hjcard,hjp⟩,hunique⟩ := exists_unique_prefix (liveGroups G H s x) q hq
    have hsub : j ⊆ s := hjp.1.trans (Finset.filter_subset _ _)
    have hj : j ∈ s.powersetCard q := Finset.mem_powersetCard.mpr ⟨hsub,hjcard⟩
    rw [Finset.sum_eq_single_of_mem j hj,hfactor j hj]
    · simp [bit,hq,hsub,hjp]
    · intro u hu hne
      rw [hfactor u hu]
      have hnp : ¬ IsOrderedPrefix (liveGroups G H s x) u :=
        fun hup => hne (hunique u ⟨(Finset.mem_powersetCard.mp hu).2,hup⟩)
      simp [bit,hnp]
  · rw [show bit (q ≤ (liveGroups G H s x).card) = 0 by simp [bit,hq]]
    symm
    apply Finset.sum_eq_zero
    intro u hu
    rw [hfactor u hu]
    have hnp : ¬ IsOrderedPrefix (liveGroups G H s x) u := by
      intro hp
      exact hq ((Finset.mem_powersetCard.mp hu).2 ▸ Finset.card_le_card hp.1)
    simp [bit,hnp]

/-- Charge the high-occupancy residual using actual same-column pairs. -/
theorem collision_threshold_cost {m n : ℕ} {ι : Type*} [LinearOrder ι]
    (G : ι → Finset (Fin m)) (H : Finset (Fin n)) (s : Finset ι) (K : ℕ)
    (hH : 1 ≤ H.card)
    (hd : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → Disjoint (G a) (G b))
    (hK : ∀ a ∈ s, (G a).card ≤ K) :
    BoundedCombination ColumnCollision
      (fun x => bit (H.card+1 ≤ (liveGroups G H s x).card))
      ((s.card.choose (H.card+1) : ℝ) * ((K:ℝ)^2*2^(8*H.card))) := by
  classical
  have h (j : Finset ι) (hj : j ∈ s.powersetCard (H.card+1)) := by
    obtain ⟨hjs,hjc⟩ := Finset.mem_powersetCard.mp hj
    have hB := (grouped_collision_bound G K H j hH hjc
      (fun a ha b hb hab => hd a (hjs ha) b (hjs hb) hab)
      (fun a ha => hK a (hjs ha))).mul_left collision_mono (inactive_prod_cost (skipped s j) G H)
    simpa only [mul_one] using hB
  have hB := BoundedCombination.finset_sum (s.powersetCard (H.card+1)) _ _ h
  have hC := hB.of_eq (fun x => (threshold_prefix_sum G H s x (H.card+1)).symm)
  simpa [Finset.card_powersetCard,nsmul_eq_mul] using hC

end PHP
