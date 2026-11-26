import PHP.BlockSemantics
import Mathlib.Data.List.Nodup
import Mathlib.Data.Fin.SuccPred
import Mathlib.Tactic.NormNum

namespace PHP.Block

/-- Every function on the first k bits has a fitting natural-number mask. -/
theorem mask_of_bits (k : ℕ) (f : Fin k → Bool) :
    ∃ b : ℕ, b < 2^k ∧ ∀ i : Fin k, b.testBit i.val = f i := by
  induction k with
  | zero => exact ⟨0,by decide,fun i => i.elim0⟩
  | succ k ih =>
    obtain ⟨b,hb,h⟩ := ih (fun i => f i.castSucc)
    cases hlast : f (Fin.last k)
    · refine ⟨b,?_,?_⟩
      · rw [pow_succ]; omega
      · intro i
        by_cases hi : i.val < k
        · exact h ⟨i.val,hi⟩
        · have hi' : i = Fin.last k := by apply Fin.ext; simp; omega
          rw [hi', hlast]
          exact Nat.testBit_lt_two_pow hb
    · refine ⟨2^k+b,?_,?_⟩
      · rw [pow_succ]; omega
      · intro i
        by_cases hi : i.val < k
        · rw [Nat.testBit_two_pow_add_gt hi]
          exact h ⟨i.val,hi⟩
        · have hi' : i = Fin.last k := by apply Fin.ext; simp; omega
          rw [hi',hlast]
          change (2^k+b).testBit k = true
          rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hb]
          rfl

def AllowedPred (P : Fin 7 → Prop) : Prop :=
  (∀ t, ¬ P t) ∨ (∃ i : Fin 7, i ≠ 0 ∧ ∀ t, P t ↔ t = i) ∨ P 0

theorem mem_mask_positive (b : ℕ) (j : Fin 6) :
    j.val+1 ∈ (List.range 6).filterMap
                (fun i => if b.testBit i then some (i+1) else none) ↔
     b.testBit j.val = true := by
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨i,hi,h⟩
    by_cases hb : b.testBit i = true
    · have hi' : i = j.val := by simp [hb] at h; omega
      simpa [hi'] using hb
    · simp [hb] at h
  · intro h
    exact ⟨j.val,List.mem_range.mpr j.isLt,by simp [h]⟩

theorem mem_mask_zero (b : ℕ) :
    0 ∉ (List.range 6).filterMap
                (fun i => if b.testBit i then some (i+1) else none) := by
  rw [List.mem_filterMap]
  rintro ⟨i,hi,hh⟩
  by_cases hb : b.testBit i = true <;> simp [hb] at hh

/-- The 71 codes cover every allowed predicate on the seven literal labels. -/
theorem allowed_pred_code (P : Fin 7 → Prop) (h : AllowedPred P) :
    ∃ c : Fin 71, ∀ t : Fin 7, P t ↔ t.val ∈ allowed c.val := by
  classical
  rcases h with he | ⟨i,hi,hs⟩ | hzero
  · refine ⟨0,fun t => ?_⟩
    simp [allowed,he t]
  · have hib : i.val < 7 := i.isLt
    have hni : i.val ≠ 0 := fun h => hi (Fin.ext h)
    refine ⟨⟨i.val,by omega⟩,fun t => ?_⟩
    simp [allowed,hni,show i.val ≤ 6 by omega,hs t,Fin.ext_iff]
  · obtain ⟨b,hb,hbits⟩ := mask_of_bits 6 (fun t => decide (P t.succ))
    norm_num at hb
    let c : Fin 71 := ⟨7+b,by omega⟩
    refine ⟨c,?_⟩
    intro t
    have hc0 : 7+b ≠ 0 := by omega
    have hc6 : ¬ 7+b ≤ 6 := by omega
    have hc7 : 7+b-7=b := by omega
    change P t ↔ t.val ∈ allowed (7+b)
    simp only [allowed, beq_iff_eq, hc0, hc6, if_false, hc7]
    refine Fin.cases ?_ (fun j => ?_) t
    · simp [hzero]
    · change P j.succ ↔ j.val+1 ∈ 0 :: (List.range 6).filterMap (fun i =>
        if b.testBit i then some (i+1) else none)
      rw [List.mem_cons, mem_mask_positive, hbits j]
      simp

theorem allowed_bounded (c : Fin 71) {i : ℕ} (h : i ∈ allowed c.val) : i < 7 := by
  unfold allowed at h
  by_cases h0 : c.val = 0
  · simp [h0] at h
  by_cases h6 : c.val ≤ 6
  · simp [h0,h6] at h
    omega
  · simp only [beq_iff_eq,h0,h6,if_false,List.mem_cons,List.mem_filterMap] at h
    rcases h with h | ⟨j,hj,he⟩
    · omega
    · have hj' := List.mem_range.mp hj
      by_cases hh : (c.val-7).testBit j = true
      · simp [hh] at he
        omega
      · simp [hh] at he

theorem allowed_nodup (c : Fin 71) : (allowed c.val).Nodup := by
  unfold allowed
  by_cases h0 : c.val = 0
  · simp [h0]
  by_cases h6 : c.val ≤ 6
  · simp [h0,h6]
  · simp only [beq_iff_eq,h0,h6,if_false,List.nodup_cons]
    refine ⟨mem_mask_zero _,?_⟩
    apply List.Nodup.filterMap _ List.nodup_range
    intro a b t ha hb
    by_cases h_a : (c.val-7).testBit a = true
    · by_cases h_b : (c.val-7).testBit b = true
      · simp [h_a] at ha
        simp [h_b] at hb
        omega
      · simp [h_b] at hb
    · simp [h_a] at ha

end PHP.Block
