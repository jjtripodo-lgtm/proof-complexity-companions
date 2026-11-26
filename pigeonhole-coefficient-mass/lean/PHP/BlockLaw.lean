import PHP.BlockMaskBridge
import PHP.Model
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FinCases

namespace PHP.Block

open scoped BigOperators

theorem sum_code {A : Type*} [AddCommMonoid A] (c : Fin 71) (f : Nat → A) :
    (∑ i : Fin 7, if i.val ∈ allowed c.val then f i.val else 0) =
      ((allowed c.val).map f).sum := by
  classical
  rw [← Finset.sum_filter, ← List.sum_toFinset f (allowed_nodup c)]
  apply Finset.sum_nbij Fin.val
  · intro i hi
    simpa using (Finset.mem_filter.mp hi).2
  · exact Fin.val_injective.injOn
  · intro i hi
    have hh : i ∈ allowed c.val := by simpa using hi
    exact ⟨⟨i,allowed_bounded c hh⟩,by simp [hh],rfl⟩
  · simp

abbrev Tile := Fin 3 → Fin 7

def tileEquiv : Tile ≃ Fin 7 × Fin 7 × Fin 7 where
  toFun a := (a 0,a 1,a 2)
  invFun p := Fin.cases p.1 (Fin.cases p.2.1 (fun _ => p.2.2))
  left_inv a := by funext i; fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨i,j,k⟩; rfl

def tileWeight30 (a : Tile) : ℤ := weight30 (a 0).val (a 1).val (a 2).val

noncomputable def tileWeight (a : Tile) : ℝ := (tileWeight30 a : ℝ) / 30

def tileSupport (a : Tile) : ℕ := supportSize (a 0).val (a 1).val (a 2).val

theorem rectangle_semantic (P : Fin 3 → Fin 7 → Prop)
    (hP : ∀ i, AllowedPred (P i)) :
    (by classical exact |∑ a : Tile, if (∀ i, P i (a i)) then tileWeight a else 0| ≤ 1) := by
  classical
  obtain ⟨c₀,h₀⟩ := allowed_pred_code (P 0) (hP 0)
  obtain ⟨c₁,h₁⟩ := allowed_pred_code (P 1) (hP 1)
  obtain ⟨c₂,h₂⟩ := allowed_pred_code (P 2) (hP 2)
  have htriple (a : Tile) :
      (∀ i, P i (a i)) ↔
        (a 0).val ∈ allowed c₀.val ∧
        (a 1).val ∈ allowed c₁.val ∧ (a 2).val ∈ allowed c₂.val := by
    constructor
    · intro h
      exact ⟨(h₀ _).mp (h 0),(h₁ _).mp (h 1),(h₂ _).mp (h 2)⟩
    · rintro ⟨ha,hb,hc⟩ i
      fin_cases i
      · exact (h₀ _).mpr ha
      · exact (h₁ _).mpr hb
      · exact (h₂ _).mpr hc
  have hsum :
      (∑ a : Tile, if (∀ i, P i (a i)) then tileWeight30 a else 0) =
        rectangle30 c₀.val c₁.val c₂.val := by
    rw [Fintype.sum_equiv tileEquiv _
      (fun p => if p.1.val ∈ allowed c₀.val ∧ p.2.1.val ∈ allowed c₁.val ∧
        p.2.2.val ∈ allowed c₂.val
        then weight30 p.1.val p.2.1.val p.2.2.val else 0)]
    · rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type, ite_and]
      have reform (i j k : Fin 7) :
          (if i.val ∈ allowed c₀.val then
            if j.val ∈ allowed c₁.val then
              if k.val ∈ allowed c₂.val then weight30 i.val j.val k.val else 0
            else 0 else 0) =
          (if k.val ∈ allowed c₂.val then
            if i.val ∈ allowed c₀.val then
              if j.val ∈ allowed c₁.val then weight30 i.val j.val k.val else 0
            else 0 else 0) := by
        split_ifs <;> rfl
      simp_rw [reform]
      have hswap :
          (∑ i : Fin 7, ∑ j : Fin 7, ∑ k : Fin 7,
              if k.val ∈ allowed c₂.val then
                if i.val ∈ allowed c₀.val then
                  if j.val ∈ allowed c₁.val then weight30 i.val j.val k.val else 0
                else 0 else 0) =
          (∑ k : Fin 7, ∑ i : Fin 7, ∑ j : Fin 7,
              if k.val ∈ allowed c₂.val then
                if i.val ∈ allowed c₀.val then
                  if j.val ∈ allowed c₁.val then weight30 i.val j.val k.val else 0
                else 0 else 0) := by
        simp_rw [show ∀ i : Fin 7,
          (∑ j : Fin 7, ∑ k : Fin 7, _) =
          (∑ k : Fin 7, ∑ j : Fin 7,
              if k.val ∈ allowed c₂.val then
                if i.val ∈ allowed c₀.val then
                  if j.val ∈ allowed c₁.val then weight30 i.val j.val k.val else 0
                else 0 else 0) from fun i => Finset.sum_comm]
        exact Finset.sum_comm
      rw [hswap]
      have pull {I : Type} [Fintype I] (q : Prop) [Decidable q] (f : I → ℤ) :
          (∑ i, if q then f i else 0) = if q then ∑ i, f i else 0 := by
        by_cases h : q <;> simp [h]
      simp_rw [pull]
      unfold rectangle30 slice
      rw [sum_code c₂ (fun k =>
        ∑ i : Fin 7, if i.val ∈ allowed c₀.val then
          ∑ j : Fin 7, if j.val ∈ allowed c₁.val then weight30 i.val j.val k else 0
        else 0)]
      congr 1
      apply List.map_congr_left
      intro k _
      rw [sum_code c₀ (fun i =>
        ∑ j : Fin 7, if j.val ∈ allowed c₁.val then weight30 i j.val k else 0)]
      congr 1
      apply List.map_congr_left
      intro i _
      exact sum_code c₁ (fun j => weight30 i j k)
    · intro a
      unfold tileWeight30
      simp only [tileEquiv, Equiv.coe_fn_mk, htriple]
  have hcast :
      (∑ a : Tile, if (∀ i, P i (a i)) then tileWeight a else 0) =
        (rectangle30 c₀.val c₁.val c₂.val : ℝ) / 30 := by
    rw [← hsum, Int.cast_sum, div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : ∀ i, P i (a i) <;> simp [h,tileWeight,div_eq_mul_inv]
  rw [hcast, abs_div]
  norm_num
  have hR := rectangle30_bound c₀ c₁ c₂
  have hlo : -(30 : ℝ) ≤ (rectangle30 c₀.val c₁.val c₂.val : ℝ) := by exact_mod_cast hR.1
  have hhi : (rectangle30 c₀.val c₁.val c₂.val : ℝ) ≤ 30 := by exact_mod_cast hR.2
  exact (div_le_iff₀ (by norm_num)).mpr (by simpa using abs_le.mpr ⟨hlo,hhi⟩)

end PHP.Block
