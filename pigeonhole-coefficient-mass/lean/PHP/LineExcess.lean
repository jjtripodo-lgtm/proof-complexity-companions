import PHP.Combination
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

namespace PHP

open scoped BigOperators

noncomputable def bit (p : Prop) : ℝ := by
  classical exact if p then 1 else 0

noncomputable def ones {r : ℕ} (f : Fin r → Bool) : ℝ :=
  ∑ j, bit (f j = true)

def IsFirst {r : ℕ} (f : Fin r → Bool) (a : Fin r) : Prop :=
  f a = true ∧ ∀ j < a, f j = false

def Extra {r : ℕ} (f : Fin r → Bool) (a b : Fin r) : Prop :=
  IsFirst f a ∧ a < b ∧ f b = true

theorem first_unique {r : ℕ} {f : Fin r → Bool} {a b : Fin r}
    (ha : IsFirst f a) (hb : IsFirst f b) : a = b := by
  rcases lt_trichotomy a b with h | h | h
  · have hf := hb.2 a h
    rw [ha.1] at hf
    contradiction
  · exact h
  · have hf := ha.2 b h
    rw [hb.1] at hf
    contradiction

theorem excess_count {r : ℕ} (f : Fin r → Bool) :
    (∑ a : Fin r, ∑ b : Fin r, bit (Extra f a b)) =
      ones f + bit (∀ j, f j = false) - 1 := by
  classical
  by_cases hE : ∀ j, f j = false
  · have hf : ∀ a b, ¬ Extra f a b := by
      intro a b h
      have h' := h.1.1
      rw [hE a] at h'
      contradiction
    simp [ones,bit,hE,hf]
  let s := Finset.univ.filter (fun j => f j = true)
  have hs : s.Nonempty := by
    by_contra h
    apply hE
    intro j
    cases hj : f j
    · rfl
    · exact False.elim (h ⟨j, by simp [s,hj]⟩)
  let a := s.min' hs
  have ha_mem : a ∈ s := s.min'_mem hs
  have ha_val : f a = true := (Finset.mem_filter.mp ha_mem).2
  have ha : IsFirst f a := by
    refine ⟨ha_val,?_⟩
    intro j hj
    cases h : f j
    · rfl
    · have hjmem : j ∈ s := by simp [s,h]
      exact False.elim ((not_le_of_gt hj) (s.min'_le _ hjmem))
  rw [Finset.sum_eq_single a]
  · have he (b : Fin r) : bit (Extra f a b) =
        if b ∈ s.erase a then 1 else 0 := by
      have hh : Extra f a b ↔ b ∈ s.erase a := by
        constructor
        · intro h
          exact Finset.mem_erase.mpr ⟨ne_of_gt h.2.1, by simp [s,h.2.2]⟩
        · intro h
          obtain ⟨hne,hmem⟩ := Finset.mem_erase.mp h
          exact ⟨ha,lt_of_le_of_ne (s.min'_le _ hmem) (Ne.symm hne),
            (Finset.mem_filter.mp hmem).2⟩
      simp [bit,hh]
    simp_rw [he]
    have hs' : ones f = (s.card : ℝ) := by
      unfold ones
      have heq : (∑ j : Fin r, bit (f j = true)) =
          ∑ j : Fin r, (if f j = true then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : f j = true <;> simp [bit,h]
      rw [heq, Finset.sum_boole]
    rw [hs']
    have hcard : 1 ≤ s.card := Finset.one_le_card.mpr hs
    have herase : ((s.erase a).card : ℝ) = (s.card : ℝ) - 1 := by
      rw [Finset.card_erase_of_mem ha_mem, Nat.cast_sub hcard]
      norm_num
    have hfilter : Finset.univ.filter (fun b => b ∈ s.erase a) = s.erase a := by
      ext b; simp
    rw [Finset.sum_boole, hfilter, herase]
    simp only [bit, if_neg hE, add_zero]
  · intro a' _ hne
    apply Finset.sum_eq_zero
    intro b _
    have hn : ¬ Extra f a' b := fun h => hne (first_unique h.1 ha)
    simp [bit,hn]
  · simp

/-- The signed count uses an explicit cube that marks the first two specified
hits and requires zeros only before the first hit. -/
def excessPattern {r : ℕ} (a b : Fin r) (j : Fin r) : Option Bool :=
  if j = a ∨ j = b then some true else if j < a then some false else none

theorem excessPattern_holds {r : ℕ} {f : Fin r → Bool} {a b : Fin r} (h : a < b) :
    (∀ j v, excessPattern a b j = some v → f j = v) ↔ Extra f a b := by
  constructor
  · intro hC
    refine ⟨⟨hC a true (by simp [excessPattern]),?_⟩,h,hC b true (by simp [excessPattern])⟩
    intro j hj
    have hja : j ≠ a := ne_of_lt hj
    have hjb : j ≠ b := ne_of_lt (hj.trans h)
    exact hC j false (by simp [excessPattern,hja,hjb,hj])
  · rintro ⟨⟨ha,hpre⟩,_,hb⟩ j v hv
    rcases eq_or_ne j a with rfl | hja
    · have hv' : true = v := by simpa [excessPattern] using hv
      exact ha.trans hv'
    rcases eq_or_ne j b with rfl | hjb
    · have hv' : true = v := by simpa [excessPattern] using hv
      exact hb.trans hv'
    by_cases hj : j < a
    · have hv' : false = v := by simpa [excessPattern,hja,hjb,hj] using hv
      exact (hpre j hj).trans hv'
    · simp [excessPattern,hja,hjb,hj] at hv

end PHP
