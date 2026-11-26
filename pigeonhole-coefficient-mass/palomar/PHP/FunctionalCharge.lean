module

public import PHP.LineExcess
public import PHP.EmptyColumns
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace PHP

open scoped BigOperators

def rowEmptyCube {m n : ℕ} (i : Fin m) : Cube m n :=
  fun ij => if ij.1 = i then some false else none

def colExtraCube {m n : ℕ} (j : Fin n) (a b : Fin m) : Cube m n :=
  fun ij => if ij.2 = j then excessPattern a b ij.1 else none

def rowExtraCube {m n : ℕ} (i : Fin m) (a b : Fin n) : Cube m n :=
  fun ij => if ij.1 = i then excessPattern a b ij.2 else none

theorem eval_rowEmptyCube {m n : ℕ} (i : Fin m) (x : Board m n) :
    eval (rowEmptyCube i) x = bit (∀ j, x (i,j) = false) := by
  classical
  have hh : Holds (rowEmptyCube i) x ↔ (∀ j, x (i,j) = false) := by
    constructor
    · intro h j
      exact h (i,j) false (by simp [rowEmptyCube])
    · intro h ij b hb
      obtain ⟨p,j⟩ := ij
      by_cases hp : p = i
      · subst p
        have he : false = b := by simpa [rowEmptyCube] using hb
        exact (h j).trans he
      · simp [rowEmptyCube,hp] at hb
  simp [eval,bit,hh]

theorem holds_colExtraCube {m n : ℕ} (j : Fin n) (a b : Fin m) (x : Board m n) :
    Holds (colExtraCube j a b) x ↔
      (∀ i v, excessPattern a b i = some v → x (i,j) = v) := by
  constructor
  · intro h i v hv
    exact h (i,j) v (by simpa [colExtraCube] using hv)
  · intro h ij v hv
    obtain ⟨i,q⟩ := ij
    by_cases hq : q = j
    · subst q
      exact h i v (by simpa [colExtraCube] using hv)
    · simp [colExtraCube,hq] at hv

theorem holds_rowExtraCube {m n : ℕ} (i : Fin m) (a b : Fin n) (x : Board m n) :
    Holds (rowExtraCube i a b) x ↔
      (∀ j v, excessPattern a b j = some v → x (i,j) = v) := by
  constructor
  · intro h j v hv
    exact h (i,j) v (by simpa [rowExtraCube] using hv)
  · intro h ij v hv
    obtain ⟨q,j⟩ := ij
    by_cases hq : q = i
    · subst q
      exact h j v (by simpa [rowExtraCube] using hv)
    · simp [rowExtraCube,hq] at hv

abbrev ChargeIndex (m n : ℕ) :=
  Fin m ⊕ ((Fin n × Fin m × Fin m) ⊕ (Fin m × Fin n × Fin n))

noncomputable def charge (m n : ℕ) : Combination m n (ChargeIndex m n) where
  cube
    | .inl i => rowEmptyCube i
    | .inr (.inl (j,a,b)) => colExtraCube j a b
    | .inr (.inr (i,a,b)) => rowExtraCube i a b
  coeff
    | .inl _ => 1
    | .inr (.inl (_,a,b)) => if a < b then 1 else 0
    | .inr (.inr (_,a,b)) => if a < b then -1 else 0

theorem charge_legal (m n : ℕ) : (charge m n).legal Functional := by
  rintro (i | ⟨j,a,b⟩ | ⟨i,a,b⟩) h
  · exact Or.inl (Or.inl ⟨i,fun j => by simp [charge,rowEmptyCube]⟩)
  · have hab : a < b := by by_contra h'; simp [charge,h'] at h
    exact Or.inl (Or.inr ⟨a,b,j,ne_of_lt hab,
      by simp [charge,colExtraCube,excessPattern], by simp [charge,colExtraCube,excessPattern]⟩)
  · have hab : a < b := by by_contra h'; simp [charge,h'] at h
    exact Or.inr ⟨i,a,b,ne_of_lt hab,
      by simp [charge,rowExtraCube,excessPattern], by simp [charge,rowExtraCube,excessPattern]⟩

theorem charge_value {m n : ℕ} (x : Board m n) :
    (charge m n).value x = (m : ℝ) - (n : ℝ) + ((vacancies x).card : ℝ) := by
  classical
  have hcol (j : Fin n) (a b : Fin m) :
      (if a < b then (1 : ℝ) else 0) * eval (colExtraCube j a b) x =
        bit (Extra (fun i => x (i,j)) a b) := by
    by_cases h : a < b
    · have hh := (holds_colExtraCube j a b x).trans (excessPattern_holds h)
      simp [h,eval,bit,hh]
    · have hf : ¬ Extra (fun i => x (i,j)) a b := fun hx => h hx.2.1
      simp [h,bit,hf]
  have hrow (i : Fin m) (a b : Fin n) :
      (if a < b then (-1 : ℝ) else 0) * eval (rowExtraCube i a b) x =
        - bit (Extra (fun j => x (i,j)) a b) := by
    by_cases h : a < b
    · have hh := (holds_rowExtraCube i a b x).trans (excessPattern_holds h)
      by_cases he : Extra (fun j => x (i,j)) a b <;> simp [h,eval,bit,hh,he]
    · have hf : ¬ Extra (fun j => x (i,j)) a b := fun hx => h hx.2.1
      simp [h,bit,hf]
  have hcols : (∑ j : Fin n, bit (∀ i, x (i,j) = false)) =
      ((vacancies x).card : ℝ) := by
    have heq : (∑ j : Fin n, bit (∀ i, x (i,j) = false)) =
        ∑ j : Fin n, (if vacant x j then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : vacant x j
      · simp only [vacant] at h
        simp [bit,vacant,h]
      · simp only [vacant] at h
        simp [bit,vacant,h]
    rw [heq, Finset.sum_boole]
    rfl
  have hones : (∑ j : Fin n, ones (fun i => x (i,j))) =
      ∑ i : Fin m, ones (fun j => x (i,j)) := by
    unfold ones
    rw [Finset.sum_comm]
  unfold Combination.value
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,charge,one_mul,
    eval_rowEmptyCube,hcol,hrow,Finset.sum_neg_distrib,excess_count]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    nsmul_eq_mul, Finset.card_univ, Fintype.card_fin, mul_one, hcols,hones]
  ring

theorem charge_cost (m n : ℕ) :
    (charge m n).cost ≤ (m : ℝ) + (n : ℝ)*m*m + (m : ℝ)*n*n := by
  classical
  have h (a : ChargeIndex m n) : |(charge m n).coeff a| ≤ 1 := by
    rcases a with i | ⟨j,a,b⟩ | ⟨i,a,b⟩
    · simp [charge]
    · by_cases h : a < b <;> simp [charge,h]
    · by_cases h : a < b <;> simp [charge,h]
  calc
    _ ≤ ∑ _ : ChargeIndex m n, (1 : ℝ) := Finset.sum_le_sum fun i _ => h i
    _ = _ := by
      simp [Finset.sum_const,nsmul_eq_mul,Fintype.card_sum,Fintype.card_prod]
      ring

end PHP
