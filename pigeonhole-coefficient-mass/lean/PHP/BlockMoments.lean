import PHP.BlockLaw
import PHP.LowerEstimate
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace PHP.Block

open scoped BigOperators

def tileUsed (a : Tile) : Finset (Fin 6) :=
  Finset.univ.filter (fun p => a 0 = p.succ ∨ a 1 = p.succ ∨ a 2 = p.succ)

theorem mem_tileUsed (a : Tile) (p : Fin 6) :
    p ∈ tileUsed a ↔ ∃ c : Fin 3, a c = p.succ := by
  constructor
  · intro h
    have h' := (Finset.mem_filter.mp h).2
    rcases h' with h' | h' | h'
    · exact ⟨0,h'⟩
    · exact ⟨1,h'⟩
    · exact ⟨2,h'⟩
  · rintro ⟨c,h⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    fin_cases c
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

private theorem supportTable :
    ∀ i j k : Fin 7,
      (tileUsed (tileEquiv.symm (i,j,k))).card = supportSize i.val j.val k.val ∧
      supportSize i.val j.val k.val ≤ 3 := by decide

theorem tileUsed_card (a : Tile) : (tileUsed a).card = tileSupport a := by
  have h := (supportTable (a 0) (a 1) (a 2)).1
  have hh : tileEquiv.symm (a 0,a 1,a 2) = a := tileEquiv.symm_apply_apply a
  rwa [hh] at h

theorem tileSupport_le (a : Tile) : tileSupport a ≤ 3 :=
  (supportTable (a 0) (a 1) (a 2)).2

def momentCoeff30 (p : ℕ) : ℤ :=
  ∑ i : Fin 7, ∑ j : Fin 7, ∑ k : Fin 7,
    if supportSize i.val j.val k.val = p then weight30 i.val j.val k.val else 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 15000 in
private theorem coefficientTable :
    momentCoeff30 0 = -30 ∧ momentCoeff30 1 = 360 ∧
    momentCoeff30 2 = -900 ∧ momentCoeff30 3 = 600 := by decide

noncomputable def momentCoeff (p : ℕ) : ℝ :=
  ∑ a ∈ (Finset.univ : Finset Tile).filter (fun a => tileSupport a = p),
    tileWeight a

theorem momentCoeff_cast (p : ℕ) : momentCoeff p = (momentCoeff30 p : ℝ)/30 := by
  classical
  have h :
      (∑ a : Tile, if tileSupport a = p then tileWeight30 a else 0) = momentCoeff30 p := by
    unfold momentCoeff30
    rw [Fintype.sum_equiv tileEquiv _
      (fun t => if supportSize t.1.val t.2.1.val t.2.2.val = p then
        weight30 t.1.val t.2.1.val t.2.2.val else 0)]
    · rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]
    · intro a
      rfl
  unfold momentCoeff
  rw [Finset.sum_filter,← h,Int.cast_sum,div_eq_mul_inv,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  by_cases he : tileSupport a = p <;> simp [he,tileWeight,div_eq_mul_inv]

theorem tile_polynomial (x : ℝ) :
    (∑ a : Tile, tileWeight a * x^(3-tileSupport a)) = blockPolynomial x := by
  classical
  have hh : ∀ a : Tile, a ∈ (Finset.univ : Finset Tile) →
      tileSupport a ∈ Finset.range 4 := by
    intro a _
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (tileSupport_le a))
  rw [← Finset.sum_fiberwise_of_maps_to hh]
  have hfac (p : ℕ) :
      (∑ a ∈ (Finset.univ : Finset Tile).filter (fun a => tileSupport a = p),
        tileWeight a * x^(3-tileSupport a)) = momentCoeff p * x^(3-p) := by
    unfold momentCoeff
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    rw [(Finset.mem_filter.mp ha).2]
  simp_rw [hfac,momentCoeff_cast]
  have ⟨h0,h1,h2,h3⟩ := coefficientTable
  norm_num [Finset.sum_range_succ,h0,h1,h2,h3,blockPolynomial]
  ring

end PHP.Block
