import PHP.MatchingPermutations
import PHP.LiftValue
import PHP.FunctionalUpper
import PHP.CollisionThreshold

namespace PHP
open Finset
open scoped BigOperators Nat

noncomputable def matchingSample {m n : ℕ} (e : Fin n ↪ Fin m)
    (σ : Equiv.Perm (Fin m)) (J : Finset (Fin n)) : Word m n :=
  fun j => if j ∈ J then some (σ (e j)) else none

noncomputable def matchingCoeff {n : ℕ} (J : Finset (Fin n)) : ℝ :=
  ∏ j : Fin n, if j ∈ J then (2:ℝ) else -1

noncomputable def matchingLaw {m n : ℕ} (e : Fin n ↪ Fin m) (a : Word m n) : ℝ :=
  (∑ σ : Equiv.Perm (Fin m), ∑ J : Finset (Fin n),
    matchingCoeff J * bit (matchingSample e σ J = a)) / (m.factorial : ℝ)

theorem matching_moment {m n : ℕ} (e : Fin n ↪ Fin m) (f : Word m n → ℝ) :
    (∑ a, matchingLaw e a*f a) =
      (∑ σ : Equiv.Perm (Fin m), ∑ J : Finset (Fin n), matchingCoeff J*f (matchingSample e σ J)) /
        (m.factorial : ℝ) := by
  classical
  simp only [matchingLaw,div_mul_eq_mul_div,← Finset.sum_div]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J _
  simp_rw [mul_assoc,← Finset.mul_sum]
  congr 1
  rw [Finset.sum_eq_single (matchingSample e σ J)]
  · simp [bit]
  · intro a _ ha
    simp [bit,Ne.symm ha]
  · simp

def IsMatching {m n : ℕ} (a : Word m n) : Prop :=
  ∀ j k i, a j = some i → a k = some i → j = k

theorem matchingSample_isMatching {m n : ℕ} (e : Fin n ↪ Fin m)
    (σ : Equiv.Perm (Fin m)) (J : Finset (Fin n)) :
    IsMatching (matchingSample e σ J) := by
  intro j k i hj hk
  have h (j : Fin n) (hj : matchingSample e σ J j = some i) : σ (e j) = i := by
    by_cases hh : j ∈ J <;> simpa [matchingSample,hh] using hj
  exact e.injective (σ.injective ((h j hj).trans (h k hk).symm))

theorem matchingLaw_support {m n : ℕ} (e : Fin n ↪ Fin m) {a : Word m n} (h : ¬ IsMatching a) :
    matchingLaw e a = 0 := by
  have hz (σ : Equiv.Perm (Fin m)) (J : Finset (Fin n)) : ¬ matchingSample e σ J = a :=
    fun he => h (he ▸ matchingSample_isMatching e σ J)
  simp [matchingLaw,bit,hz]

theorem matching_rowInvariant {m n : ℕ} (e : Fin n ↪ Fin m) : RowInvariant (matchingLaw e) := by
  classical
  intro τ a
  let E : Equiv.Perm (Fin m) ≃ Equiv.Perm (Fin m) :=
    { toFun := fun σ => σ.trans τ
      invFun := fun σ => σ.trans τ.symm
      left_inv := fun σ => Equiv.ext (by simp)
      right_inv := fun σ => Equiv.ext (by simp) }
  unfold matchingLaw
  congr 1
  calc
    _ = ∑ σ : Equiv.Perm (Fin m), ∑ J : Finset (Fin n),
         matchingCoeff J * bit (matchingSample e (E σ) J = fun j => (a j).map τ) :=
      (E.sum_comp _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro σ _
      apply Finset.sum_congr rfl
      intro J _
      congr 1
      apply congrArg bit
      apply propext
      rw [funext_iff,funext_iff]
      apply forall_congr'
      intro j
      by_cases hj : j ∈ J <;> cases ha : a j <;>
        simp [matchingSample,E,hj,ha,τ.injective.eq_iff]

def ColumnPass {m n : ℕ} (C : Cube m n) (j : Fin n) (b : Option (Fin m)) : Prop :=
  ∀ i v, C (i,j) = some v → decide (b = some i) = v

noncomputable def colFactor {m n : ℕ} (C : Cube m n) (j : Fin n) (i : Fin m) : ℝ :=
  2*bit (ColumnPass C j (some i)) - bit (ColumnPass C j none)

theorem matching_product_test {m n : ℕ} (e : Fin n ↪ Fin m) (C : Cube m n)
    (σ : Equiv.Perm (Fin m)) :
    (∑ J : Finset (Fin n), matchingCoeff J * eval C (matchingSample e σ J).board) =
      ∏ j : Fin n, colFactor C j (σ (e j)) := by
  classical
  let A := fun j => 2*bit (ColumnPass C j (some (σ (e j))))
  let B := fun j => (-1)*bit (ColumnPass C j none)
  have hprod : (∏ j : Fin n, colFactor C j (σ (e j))) = ∏ j : Fin n, (A j+B j) := by
    simp [colFactor,A,B,sub_eq_add_neg]
  rw [hprod,Fintype.prod_add]
  apply Finset.sum_congr rfl
  intro J _
  have he : eval C (matchingSample e σ J).board =
      ∏ j : Fin n, bit (ColumnPass C j (matchingSample e σ J j)) := by
    rw [prod_bits]
    unfold eval bit
    have h := holds_word_iff_columns C (matchingSample e σ J)
    have h' : Holds C (matchingSample e σ J).board ↔
        ∀ j ∈ (univ : Finset (Fin n)), ColumnPass C j (matchingSample e σ J j) := by
      simpa [ColumnPass] using h
    by_cases hc : Holds C (matchingSample e σ J).board
    · rw [if_pos hc,if_pos (h'.mp hc)]
    · rw [if_neg hc,if_neg (mt h'.mpr hc)]
  rw [he,matchingCoeff,← Finset.prod_mul_distrib,← Finset.prod_sdiff (Finset.subset_univ J)]
  change (∏ x ∈ Jᶜ, _) * (∏ x ∈ J, _) = _
  rw [mul_comm (∏ i ∈ Jᶜ, _) (∏ i ∈ J, _)]
  congr 1
  · apply Finset.prod_congr rfl
    intro j hj
    simp [A,matchingSample,hj]
  · apply Finset.prod_congr rfl
    intro j hj
    have hj' : j ∉ J := Finset.mem_compl.mp hj
    simp [B,matchingSample,hj']

noncomputable def positiveCols {m n : ℕ} (C : Cube m n) : Finset (Fin n) := by
  classical exact univ.filter (fun j => ∃ i, C (i,j) = some true)

theorem positiveCols_mem {m n : ℕ} (C : Cube m n) (j : Fin n) :
    j ∈ positiveCols C ↔ ∃ i, C (i,j) = some true := by
  simp [positiveCols]

theorem column_none_pass {m n : ℕ} (C : Cube m n) (j : Fin n) :
    ColumnPass C j none ↔ j ∉ positiveCols C := by
  rw [positiveCols_mem]
  constructor
  · intro h ⟨i,hi⟩
    have hf := h i true hi
    simp at hf
  · intro h i v hv
    cases v
    · simp
    · exact (h ⟨i,hv⟩).elim

theorem col_factor_bound {m n : ℕ} {C : Cube m n} {j : Fin n} (i : Fin m) :
    |colFactor C j i| ≤ if j ∈ positiveCols C then (2:ℝ) else 1 := by
  classical
  by_cases h : j ∈ positiveCols C <;> by_cases hp : ColumnPass C j (some i) <;>
    norm_num [colFactor,bit,h,hp,column_none_pass]

theorem col_factor_zero {m n : ℕ} {C : Cube m n} {j : Fin n} {p i : Fin m}
    (hp : C (p,j) = some true) (hi : i ≠ p) : colFactor C j i = 0 := by
  have hn : ¬ ColumnPass C j (some i) := by
    intro h
    have he := h p true hp
    simpa [hi] using he
  have hm : j ∈ positiveCols C := (positiveCols_mem C j).mpr ⟨p,hp⟩
  simp [colFactor,bit,hn,column_none_pass,hm]

end PHP
