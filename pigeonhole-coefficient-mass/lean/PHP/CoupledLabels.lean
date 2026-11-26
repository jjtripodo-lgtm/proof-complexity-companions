import PHP.CollisionThreshold
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FieldSimp

namespace PHP
open Finset
open scoped BigOperators

noncomputable def iidWeight {α β : Type*} [Fintype α] (w : β → ℝ) (f : α → β) : ℝ :=
  ∏ i : α, w (f i)

theorem iid_product {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    (w : β → ℝ) (P : α → β → Prop) :
    (∑ f : α → β, iidWeight w f * bit (∀ i, P i (f i))) =
      ∏ i : α, ∑ y : β, w y * bit (P i y) := by
  classical
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro f _
  rw [iidWeight,Finset.prod_mul_distrib,prod_bits]
  simp

theorem iid_total {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] (w : β → ℝ)
    (hw : ∑ i, w i = 1) : (∑ f : α → β, iidWeight w f) = 1 := by
  simpa [bit,hw] using iid_product (α:=α) w (fun _ _ => True)

abbrev CoupledLabel (L : ℕ) := Unit ⊕ (Unit ⊕ Fin L)

noncomputable def coupledWeight (L : ℕ) (a s : ℝ) : CoupledLabel L → ℝ
  | .inl _ => a
  | .inr (.inl _) => 1-a-s
  | .inr (.inr _) => s/L

def prefixLabel (L : ℕ) : CoupledLabel L := .inl ()
def binLabel {L : ℕ} (k : Fin L) : CoupledLabel L := .inr (.inr k)

def inBins {L : ℕ} (x : CoupledLabel L) : Prop := ∃ j : Fin L, x = binLabel j

noncomputable def prefixRows {m L : ℕ} (labels : Fin m → CoupledLabel L) : Finset (Fin m) := by
  classical exact univ.filter (fun i => labels i = prefixLabel L)

noncomputable def binRows {m L : ℕ} (labels : Fin m → CoupledLabel L) (j : Fin L) : Finset (Fin m) := by
  classical exact univ.filter (fun i => labels i = binLabel j)

noncomputable def allBinRows {m L : ℕ} (labels : Fin m → CoupledLabel L) : Finset (Fin m) := by
  classical exact univ.filter (fun i => inBins (labels i))

noncomputable def coupledMask {m L : ℕ} (labels : Fin m → CoupledLabel L) (J : Finset (Fin L)) : Finset (Fin m) :=
  prefixRows labels ∪ J.biUnion (binRows labels)

theorem coupled_weight_nonneg {L : ℕ} {a s : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (ht : a+s ≤ 1)
    (j : CoupledLabel L) : 0 ≤ coupledWeight L a s j := by
  rcases j with u|u|j
  · exact ha
  · exact (by dsimp [coupledWeight]; linarith)
  · exact div_nonneg hs (Nat.cast_nonneg _)

theorem coupled_weight_sum {L : ℕ} (hL : 0 < L) (a s : ℝ) :
    (∑ j : CoupledLabel L, coupledWeight L a s j) = 1 := by
  simp only [CoupledLabel,Fintype.sum_sum_type,Fintype.sum_unique,coupledWeight,Finset.sum_const,
    nsmul_eq_mul,Finset.card_univ,Fintype.card_fin,Fintype.card_unit,Nat.cast_one,one_mul]
  have hL' : (L:ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  field_simp
  <;> ring

theorem coupled_selected_weight {L : ℕ} (a s : ℝ) (J : Finset (Fin L)) :
    (∑ j : CoupledLabel L, coupledWeight L a s j *
      bit (j = prefixLabel L ∨ ∃ k ∈ J, j = binLabel k)) =
      a+s/L*J.card := by
  classical
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  have h (k : Fin L) :
      bit (binLabel k = prefixLabel L ∨ ∃ k' ∈ J, binLabel k = binLabel k') =
        if k ∈ J then (1:ℝ) else 0 := by
    simp [bit,binLabel,prefixLabel]
  simp only [Fintype.sum_unique, coupledWeight,prefixLabel,binLabel,bit,
    Sum.inl.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl,Sum.inr.injEq,not_false_eq_true,
    false_or, true_or, exists_false, and_false, or_false, if_true, if_false,mul_one,mul_zero,zero_add]
  simp_rw [←Finset.mul_sum]
  rw [Finset.sum_boole]
  have hf : univ.filter (fun x => ∃ k ∈ J, x = k) = J := by ext x; simp
  rw [hf]

theorem coupled_inBins_weight {L : ℕ} (hL : 0 < L) (a s : ℝ) :
    (∑ j : CoupledLabel L, coupledWeight L a s j * bit (inBins j)) = s := by
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp [CoupledLabel,bit,inBins,binLabel,coupledWeight,Finset.sum_const,nsmul_eq_mul]
  have hL' : (L:ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  exact mul_div_cancel₀ s hL'

theorem coupledMask_mem {m L : ℕ} (labels : Fin m → CoupledLabel L) (J : Finset (Fin L)) (i : Fin m) :
    i ∈ coupledMask labels J ↔ labels i = prefixLabel L ∨ ∃ k ∈ J, labels i = binLabel k := by
  simp [coupledMask,prefixRows,binRows]

theorem coupledMask_inactive {m n L : ℕ} (labels : Fin m → CoupledLabel L)
    (J : Finset (Fin L)) (H : Finset (Fin n)) (x : Board m n) :
    Inactive (coupledMask labels J) H x ↔
      Inactive (prefixRows labels) H x ∧ ∀ j ∈ J, Inactive (binRows labels j) H x := by
  constructor
  · intro h
    exact ⟨fun i hi j hj => h i (Finset.mem_union_left _ hi) j hj,fun k hk i hi j hj =>
      h i (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k,hk,hi⟩)) j hj⟩
  · rintro ⟨hpre,hbin⟩ i hi j hj
    rcases Finset.mem_union.mp hi with hp|hb
    · exact hpre i hp j hj
    · obtain ⟨k,hk,hi'⟩ := Finset.mem_biUnion.mp hb
      exact hbin k hk i hi' j hj

theorem binRows_disjoint {m L : ℕ} (labels : Fin m → CoupledLabel L) {i j : Fin L} (h : i ≠ j) :
    Disjoint (binRows labels i) (binRows labels j) := by
  apply Finset.disjoint_left.mpr
  intro u hu hv
  have h1 := (Finset.mem_filter.mp hu).2
  have h2 := (Finset.mem_filter.mp hv).2
  exact h (by simpa [binLabel] using h1.symm.trans h2)

theorem binRows_card_le {m L : ℕ} (labels : Fin m → CoupledLabel L) (j : Fin L) :
    (binRows labels j).card ≤ (allBinRows labels).card := by
  classical
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,⟨j,(Finset.mem_filter.mp hi).2⟩⟩

noncomputable def activeRows {m n : ℕ} (H : Finset (Fin n)) (x : Board m n) : Finset (Fin m) := by
  classical exact univ.filter (fun i => ¬ Inactive {i} H x)

theorem expected_coupled_mask {m n L : ℕ} (hL : 0 < L) (a s : ℝ) (J : Finset (Fin L))
    (H : Finset (Fin n)) (x : Board m n) :
    (∑ labels : Fin m → CoupledLabel L,
      iidWeight (coupledWeight L a s) labels * bit (Inactive (coupledMask labels J) H x))
      = (1-(a+s/L*J.card))^(activeRows H x).card := by
  classical
  let P := fun (i : Fin m) (y : CoupledLabel L) =>
    i ∈ activeRows H x → ¬ (y = prefixLabel L ∨ ∃ j ∈ J, y = binLabel j)
  have hP (labels : Fin m → CoupledLabel L) : Inactive (coupledMask labels J) H x ↔ ∀ i, P i (labels i) := by
    constructor
    · intro h i hi hh
      have hz : Inactive ({i}:Finset (Fin m)) H x := by
        intro j hj c hc
        have he : j = i := Finset.mem_singleton.mp hj
        subst j
        exact h i ((coupledMask_mem labels J i).mpr hh) c hc
      exact (Finset.mem_filter.mp hi).2 hz
    · intro h i hi j hj
      have hx' : Inactive ({i}:Finset (Fin m)) H x := by
        by_contra he
        exact h i (Finset.mem_filter.mpr ⟨Finset.mem_univ i,he⟩) ((coupledMask_mem labels J i).mp hi)
      exact hx' i (by simp) j hj
  simp_rw [hP]
  rw [iid_product (coupledWeight L a s) P]
  have hΩ (i : Fin m) :
      (∑ y : CoupledLabel L, coupledWeight L a s y * bit (P i y)) =
        if i ∈ activeRows H x then (1-(a+s/L*J.card)) else 1 := by
    by_cases hi : i ∈ activeRows H x
    · rw [if_pos hi]
      have hbit (y : CoupledLabel L) : bit (P i y) =
          1-bit (y = prefixLabel L ∨ ∃ j ∈ J, y = binLabel j) := by
        unfold P
        rw [show (i ∈ activeRows H x → ¬(y=prefixLabel L ∨
          ∃ j ∈ J, y=binLabel j)) ↔ ¬(y=prefixLabel L ∨
          ∃ j ∈ J, y=binLabel j) by simp [hi]]
        by_cases h : y=prefixLabel L ∨ ∃ j ∈ J, y=binLabel j <;> simp [bit,h]
      simp_rw [hbit,mul_sub,mul_one]
      rw [Finset.sum_sub_distrib,coupled_weight_sum hL,coupled_selected_weight]
    · simp [P,bit,hi,coupled_weight_sum hL]
  simp_rw [hΩ,Finset.prod_ite]
  simp

end PHP
