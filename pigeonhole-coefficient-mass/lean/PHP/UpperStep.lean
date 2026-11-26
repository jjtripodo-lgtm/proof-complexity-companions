import PHP.CollisionThreshold
import PHP.MaskLift
import PHP.UpperBase

namespace PHP
open scoped BigOperators
open Finset

/-- A finite interpolation step separated from the analytic choice of masks.
The signed weight of the bad masks is charged to a current-board certificate.
The residual must vanish on every low-occupancy assignment. -/
theorem finite_interpolation_step {m n p q : ℕ} {ι α : Type*} [LinearOrder ι]
    (H : Finset (Fin n)) (ec : Fin q ↪ Fin n)
    (hec : ∀ j : Fin n, j ∈ H ∨ ∃ j', ec j' = j)
    (G : ι → Finset (Fin m)) (groups : Finset ι) (K : ℕ) (hH : 1 ≤ H.card)
    (hd : ∀ a ∈ groups, ∀ b ∈ groups, a ≠ b → Disjoint (G a) (G b))
    (hK : ∀ a ∈ groups, (G a).card ≤ K)
    (s : Finset α) (mask : α → Finset (Fin m)) (coeff : α → ℝ)
    (good : α → Prop) [DecidablePred good]
    (hgood : ∀ i ∈ s, good i → ∃ er : Fin p ↪ Fin m, ∀ j, er j ∈ mask i)
    (hexact : ∀ x, (liveGroups G H groups x).card ≤ H.card →
      (∑ i ∈ s, coeff i * bit (Inactive (mask i) H x)) = 1)
    {B C : ℝ} (hB : BoundedCombination (@Plain p q) (fun _ => 1) B)
    (hC : BoundedCombination (@Plain m n) (fun _ => 1) C) :
    let W := ∑ i ∈ s, |coeff i|
    let bad := ∑ i ∈ s, if good i then 0 else |coeff i|
    BoundedCombination (@Plain m n) (fun _ => 1)
      (W*B + (1+W)*((groups.card.choose (H.card+1):ℝ)*((K:ℝ)^2*2^(8*H.card))) + bad*C) := by
  classical
  dsimp only
  let f : Board m n → ℝ := fun x => ∑ i ∈ s, coeff i * bit (Inactive (mask i) H x)
  let W := ∑ i ∈ s, |coeff i|
  let bad := ∑ i ∈ s, if good i then 0 else |coeff i|
  let cap := (groups.card.choose (H.card+1):ℝ)*((K:ℝ)^2*2^(8*H.card))
  change BoundedCombination _ _ (W*B + (1+W)*cap + bad*C)
  have ht := (collision_threshold_cost G H groups K hH hd hK).legal_mono (A' := @Plain m n) (fun _ => Or.inr)
  have hf : BoundedCombination Unlimited f W := by
    simpa [f,W] using BoundedCombination.finset_sum s _ _
      (fun i _ => by simpa using (zeroRect_cost (mask i) H).smul (coeff i))
  have hr : BoundedCombination (@Plain m n) (fun x => 1 - f x) ((1+W)*cap) := by
    have hp := BoundedCombination.mul_right plain_mono ((BoundedCombination.one (m:=m) (n:=n)).add hf.neg) ht
    apply hp.of_eq
    intro x
    by_cases hx : H.card+1 ≤ (liveGroups G H groups x).card
    · simp [bit,hx,sub_eq_add_neg]
    · have hx' := hexact x (by omega)
      simp [bit,hx,show f x = 1 from hx']
  have hm (i : α) (hi : i ∈ s) :
      BoundedCombination (@Plain m n) (fun x => coeff i * bit (Inactive (mask i) H x))
        ((if good i then |coeff i| else 0)*B + (if good i then 0 else |coeff i|)*C) := by
    by_cases h : good i
    · obtain ⟨er,her⟩ := hgood i hi h
      simpa [h] using (masked_plain_lift er ec (mask i) H her hec hB).smul (coeff i)
    · have hh := hC.mul_left plain_mono (zeroRect_cost (mask i) H)
      have he := hh.of_eq (g:=fun x => bit (Inactive (mask i) H x)) (fun x => by simp)
      simpa [h] using he.smul (coeff i)
  have ha := BoundedCombination.finset_sum s _ _ hm
  change BoundedCombination _ f _ at ha
  simp_rw [Finset.sum_add_distrib,← Finset.sum_mul] at ha
  have hh := (ha.add hr).of_eq (g:=fun _ => 1) (fun x => by ring)
  apply hh.cost_mono
  have hle : (∑ i ∈ s, if good i then |coeff i| else 0) ≤ W := by
    apply Finset.sum_le_sum
    intro i _
    split_ifs <;> simp
  have hx := mul_le_mul_of_nonneg_right hle hB.cost_nonneg
  change _ + bad*C + (1+W)*cap ≤ _
  linarith

end PHP
