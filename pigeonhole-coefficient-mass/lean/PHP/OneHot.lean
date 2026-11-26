import PHP.Model
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace PHP

open scoped BigOperators

abbrev Assignment (m n : ℕ) := Fin m → Fin n

def oneHotBoard {m n : ℕ} (f : Assignment m n) : Board m n :=
  fun ij => decide (f ij.1 = ij.2)

/-- Counting ordered one-hot row assignments after forcing two distinct rows. -/
theorem count_two_rows {m n : ℕ} {i i' : Fin m} (h : i ≠ i') (j : Fin n) :
    (Finset.univ.filter (fun f : Assignment m n => f i = j ∧ f i' = j)).card =
      n^(m-2) := by
  classical
  let fixed : Finset (Fin m) := {i,i'}
  let choices : Fin m → Finset (Fin n) := fun u =>
    if u ∈ fixed then {j} else Finset.univ
  have hm : ∀ f : Assignment m n,
      f ∈ Fintype.piFinset choices ↔ f i = j ∧ f i' = j := by
    intro f
    rw [Fintype.mem_piFinset]
    constructor
    · intro hf
      exact ⟨by simpa [choices,fixed] using hf i, by simpa [choices,fixed] using hf i'⟩
    · rintro ⟨h₁,h₂⟩ u
      by_cases hu : u ∈ fixed
      · have hu' : u = i ∨ u = i' := by simpa [fixed] using hu
        rcases hu' with rfl | rfl
        · simp [choices,fixed,h₁]
        · simp [choices,fixed,h₂]
      · simp [choices,hu]
  have hset : Finset.univ.filter (fun f : Assignment m n => f i = j ∧ f i' = j) =
      Fintype.piFinset choices := by ext f; simp [hm]
  rw [hset, Fintype.card_piFinset]
  have hc : ∀ u, (choices u).card = if u ∈ fixed then 1 else n := by
    intro u
    by_cases hu : u ∈ fixed <;> simp [choices,hu]
  simp_rw [hc, Finset.prod_ite]
  have hf : Finset.univ.filter (fun u => u ∉ fixed) = Finset.univ \ fixed := by ext u; simp
  rw [hf]
  have hs : fixed.card = 2 := by simp [fixed,h]
  simp [Finset.card_sdiff,hs]

/-- The paper's polynomial floor, valid even after adding the row functionality
axioms. The refutation still must hold on the entire Boolean board. -/
theorem onehot_lower {m n t : ℕ} (hm : 2 ≤ m) (hn : 1 ≤ n)
    (r : Refutation (@Functional m n) t) : (n : ℝ)^2 ≤ r.mass := by
  classical
  let c : ℝ := (n : ℝ) ^ 2 / (n : ℝ) ^ m
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hc0 : 0 ≤ c := by unfold c; positivity
  have hmass := dual_bound_on r oneHotBoard (fun _ : Assignment m n => c)
  have hw : ∀ C, Functional C → |∑ f : Assignment m n, c * eval C (oneHotBoard f)| ≤ 1 := by
    intro C hC
    have hpos : ∀ f : Assignment m n, 0 ≤ eval C (oneHotBoard f) := by
      intro f; unfold eval; split <;> norm_num
    rw [abs_of_nonneg (Finset.sum_nonneg fun f _ => mul_nonneg hc0 (hpos f))]
    rcases hC with (⟨i,hi⟩ | ⟨i,i',j,hd,h₁,h₂⟩) | ⟨i,j,j',hd,h₁,h₂⟩
    · have hz : ∀ f : Assignment m n, eval C (oneHotBoard f) = 0 := by
        intro f
        have hno : ¬ Holds C (oneHotBoard f) := by
          intro h
          have := h (i,f i) false (hi (f i))
          simp [oneHotBoard] at this
        simp [eval,hno]
      simp [hz]
    · have hle (f : Assignment m n) : eval C (oneHotBoard f) ≤
          if f i = j ∧ f i' = j then (1 : ℝ) else 0 := by
        by_cases hh : Holds C (oneHotBoard f)
        · have e₁ : f i = j := of_decide_eq_true (hh _ _ h₁)
          have e₂ : f i' = j := of_decide_eq_true (hh _ _ h₂)
          simp [eval,hh,e₁,e₂]
        · simp [eval,hh]; split <;> norm_num
      calc
        _ ≤ ∑ f : Assignment m n, c * (if f i = j ∧ f i' = j then 1 else 0) :=
          Finset.sum_le_sum fun f _ => mul_le_mul_of_nonneg_left (hle f) hc0
        _ = c * (n : ℝ)^(m-2) := by
          rw [← Finset.mul_sum, ← Finset.sum_filter]
          simp [nsmul_eq_mul,count_two_rows hd j]
        _ = 1 := by
          unfold c
          have he : m = 2 + (m-2) := by omega
          nth_rewrite 1 [he]
          rw [pow_add]
          field_simp
    · have hz : ∀ f : Assignment m n, eval C (oneHotBoard f) = 0 := by
        intro f
        have hno : ¬ Holds C (oneHotBoard f) := by
          intro h
          have e₁ : f i = j := of_decide_eq_true (h _ _ h₁)
          have e₂ : f i = j' := of_decide_eq_true (h _ _ h₂)
          exact hd (e₁.symm.trans e₂)
        simp [eval,hno]
      simp [hz]
  have hv := hmass hw
  have hsum : (∑ _ : Assignment m n, c) = (n : ℝ)^2 := by
    simp [nsmul_eq_mul,c]
    field_simp
  rw [hsum] at hv
  exact hv

theorem plain_onehot_lower {m n t : ℕ} (hm : 2 ≤ m) (hn : 1 ≤ n)
    (r : Refutation (@Plain m n) t) : (n : ℝ)^2 ≤ r.mass :=
  onehot_lower hm hn ⟨r.cube,r.coeff,fun k => Or.inl (r.legal k),r.identity⟩

end PHP
