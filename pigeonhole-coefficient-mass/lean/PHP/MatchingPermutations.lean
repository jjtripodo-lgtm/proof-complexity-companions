import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring

namespace PHP
open Finset
open scoped Nat

/-- Count the permutations respecting prescribed images on a finite set. -/
theorem pinned_perm_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (f : ι → ι) (e : Equiv.Perm ι) (he : ∀ i ∈ S, e i = f i) :
    Fintype.card {σ : Equiv.Perm ι // ∀ i ∈ S, σ i = f i} =
      (Fintype.card ι-S.card).factorial := by
  classical
  let Rest := {i : ι // i ∉ S}
  let Fix := {σ : Equiv.Perm ι // ∀ i ∈ S, σ i = i}
  let eFix : {σ : Equiv.Perm ι // ∀ i ∈ S, σ i = f i} ≃ Fix :=
    { toFun := fun σ => ⟨σ.val.trans e.symm,fun i hi => by simp [σ.property i hi,← he i hi]⟩
      invFun := fun σ => ⟨σ.val.trans e,fun i hi => by simp [σ.property i hi, he i hi]⟩
      left_inv := fun σ => Subtype.ext (Equiv.ext fun i => by simp)
      right_inv := fun σ => Subtype.ext (Equiv.ext fun i => by simp) }
  have hrest (σ : Fix) (i : ι) : i ∉ S ↔ σ.val i ∉ S := by
    constructor
    · intro hi hσ
      have h := σ.val.injective (σ.property _ hσ)
      exact hi (h ▸ hσ)
    · intro hi h
      apply hi
      rw [σ.property i h]
      exact h
  let eRest : Fix ≃ Equiv.Perm Rest :=
    { toFun := fun σ => σ.val.subtypeEquiv (hrest σ)
      invFun := fun σ => ⟨σ.extendDomain (Equiv.refl Rest),fun i hi =>
        σ.extendDomain_apply_not_subtype _ (by simpa using hi)⟩
      left_inv := by
        intro σ
        apply Subtype.ext
        ext i
        by_cases hi : i ∉ S
        · change Equiv.Perm.extendDomain (σ.val.subtypeEquiv (hrest σ)) (Equiv.refl Rest) i = _
          exact Equiv.Perm.extendDomain_apply_subtype (σ.val.subtypeEquiv (hrest σ)) (Equiv.refl Rest) (b:=i) hi
        · have hi' : i ∈ S := by simpa using hi
          change Equiv.Perm.extendDomain (σ.val.subtypeEquiv (hrest σ)) (Equiv.refl Rest) i = _
          exact (Equiv.Perm.extendDomain_apply_not_subtype (σ.val.subtypeEquiv (hrest σ)) (Equiv.refl Rest) (b:=i) hi).trans (σ.property i hi').symm
      right_inv := by
        intro σ
        ext i
        change σ.extendDomain (Equiv.refl Rest) i.val = _
        exact σ.extendDomain_apply_image (Equiv.refl Rest) i }
  rw [Fintype.card_congr (eFix.trans eRest),Fintype.card_perm]
  congr 1
  change Fintype.card {i : ι // i ∉ S} = _
  have hs := Fintype.card_subtype_compl (p:=fun i : ι => i ∈ S)
  simpa using hs

theorem pinned_perm_finset_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (f : ι → ι) (e : Equiv.Perm ι) (he : ∀ i ∈ S, e i = f i) :
    (Finset.univ.filter (fun σ : Equiv.Perm ι => ∀ i ∈ S, σ i = f i)).card =
      (Fintype.card ι-S.card).factorial := by
  rw [← Fintype.card_subtype]
  exact pinned_perm_card S f e he

private theorem factorial_ge_two_pow {p : ℕ} (hp : 4 ≤ p) : 2^p ≤ p.factorial := by
  induction p with
  | zero => omega
  | succ p ih =>
    by_cases h : p = 3
    · subst p; decide
    · rw [pow_succ,Nat.factorial_succ,mul_comm (2^p) 2]
      exact Nat.mul_le_mul (by omega) (ih (by omega))

/-- If there are at least four columns and at least that many rows, two
signed active choices per forced column cost at most one after averaging. -/
theorem pinned_mass_le_factorial {m n p : ℕ} (hn : 4 ≤ n) (hm : n ≤ m) (hp : p ≤ n) :
    2^p*(m-p).factorial ≤ m.factorial := by
  by_cases hm' : p < m
  · induction p with
    | zero => simp
    | succ p ih =>
      rw [pow_succ]
      have hr : m-p = (m-(p+1))+1 := by omega
      have hi := ih (by omega) (by omega)
      rw [hr,Nat.factorial_succ] at hi
      have hb : 2*(m-(p+1)).factorial ≤ (m-(p+1)+1)*(m-(p+1)).factorial :=
        Nat.mul_le_mul_right _ (by omega)
      exact (show 2^p*2*(m-(p+1)).factorial = 2^p*(2*(m-(p+1)).factorial) by ring).le.trans
        ((Nat.mul_le_mul_left _ hb).trans hi)
  · have h : p = m := by omega
    subst p
    simp [factorial_ge_two_pow (by omega : 4 ≤ m)]

end PHP
