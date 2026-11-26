import PHP.SymmetricLift
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace PHP

open scoped BigOperators

def Omits {m n : ℕ} (a : Word m n) (i : Fin m) : Prop := ∀ j, a j ≠ some i

noncomputable instance {m n : ℕ} (a : Word m n) (i : Fin m) : Decidable (Omits a i) :=
  Classical.propDecidable _

noncomputable def omissions {m n : ℕ} (a : Word m n) : ℝ := by
  classical
  exact ∑ i : Fin m, if Omits a i then 1 else 0

theorem omits_retained {m n : ℕ} (a : Word m n) (i : Fin (m+1)) (p : Fin m) :
    Omits (a.insertRow i) (i.succAbove p) ↔ Omits a p := by
  unfold Omits
  apply forall_congr'
  intro j
  cases h : a j <;> simp [Word.insertRow,h]

theorem omissions_insertRow {m n : ℕ} (a : Word m n) (i : Fin (m+1)) :
    omissions (a.insertRow i) = 1 + omissions a := by
  classical
  unfold omissions
  rw [Fin.sum_univ_succAbove _ i]
  have hi : Omits (a.insertRow i) i := insertedRow_absent i a
  rw [if_pos hi]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  simp [omits_retained]

theorem omission_nonneg {m n : ℕ} (a : Word m n) : 0 ≤ omissions a := by
  classical
  unfold omissions
  exact Finset.sum_nonneg fun _ _ => by split <;> norm_num

theorem sum_insertRow {m n : ℕ} (i : Fin (m+1)) (f : Word (m+1) n → ℝ) :
    (∑ a : Word (m+1) n, if Omits a i then f a else 0) =
      ∑ b : Word m n, f (b.insertRow i) := by
  classical
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_nbij (fun b => b.insertRow i)
  · intro b _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, insertedRow_absent i b⟩
  · exact (insertRow_injective i).injOn
  · intro a ha
    obtain ⟨b,hb⟩ := exists_insertRow i a (Finset.mem_filter.mp ha).2
    exact ⟨b,Finset.mem_univ _,hb⟩
  · simp

theorem lift_zero_if_no_omission {m n : ℕ} (L : Word m n → ℝ)
    (a : Word (m+1) n) (h : ¬ ∃ i, Omits a i) : liftSymmetric L a = 0 := by
  classical
  unfold liftSymmetric
  apply dif_neg
  rintro ⟨i,b,rfl⟩
  exact h ⟨i,insertedRow_absent i b⟩

/-- Double-count the missing row itself, avoiding a falling-factorial count
of every word-pattern fiber. An inserted word has one more omission than the
small word. -/
theorem lift_mass_by_omissions {m n : ℕ} (L : Word m n → ℝ)
    (hinv : RowInvariant L) :
    (∑ a : Word (m+1) n, liftSymmetric L a) =
      ((m+1 : ℕ) : ℝ) * ∑ b : Word m n, L b / (1 + omissions b) := by
  classical
  have hsplit (a : Word (m+1) n) :
      liftSymmetric L a = ∑ i : Fin (m+1),
        if Omits a i then liftSymmetric L a / omissions a else 0 := by
    by_cases he : ∃ i, Omits a i
    · obtain ⟨i, hi⟩ := he
      obtain ⟨b,hb⟩ := exists_insertRow i a hi
      have hn : omissions a ≠ 0 := by
        rw [← hb, omissions_insertRow]
        have hp := omission_nonneg b
        linarith
      let c := liftSymmetric L a / omissions a
      have hterm (j : Fin (m+1)) :
          (if Omits a j then c else 0) = c * (if Omits a j then 1 else 0) := by
        split <;> simp
      change _ = ∑ i : Fin (m+1), if Omits a i then c else 0
      simp_rw [hterm, ← Finset.mul_sum]
      change _ = (liftSymmetric L a / omissions a) * omissions a
      exact (div_mul_cancel₀ _ hn).symm
    · rw [lift_zero_if_no_omission L a he]
      simp
  calc
    _ = ∑ a : Word (m+1) n, ∑ i : Fin (m+1),
        if Omits a i then liftSymmetric L a / omissions a else 0 :=
      Finset.sum_congr rfl fun a _ => hsplit a
    _ = ∑ i : Fin (m+1), ∑ b : Word m n, L b / (1 + omissions b) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [sum_insertRow]
      simp_rw [liftSymmetric_insert hinv, omissions_insertRow]
    _ = _ := by simp [nsmul_eq_mul]

end PHP
