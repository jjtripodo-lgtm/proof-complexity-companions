import PHP.Absorb
import PHP.BatchInterpolation
import PHP.GroupSampling
import Mathlib.Logic.Equiv.Fin.Basic

namespace PHP
open scoped BigOperators
open Finset

noncomputable def equalGroups (r K : ℕ) (i : Fin r) : Finset (Fin (r*K)) :=
  univ.map ⟨fun j : Fin K => finProdFinEquiv (i,j),fun _ _ h => congrArg Prod.snd (finProdFinEquiv.injective h)⟩

theorem equalGroups_card (r K : ℕ) (i : Fin r) : (equalGroups r K i).card = K := by
  simp [equalGroups]

theorem equalGroups_disjoint {r K : ℕ} {i j : Fin r} (h : i ≠ j) :
    Disjoint (equalGroups r K i) (equalGroups r K j) := by
  apply Finset.disjoint_left.mpr
  intro k hi hj
  obtain ⟨x,_,hx⟩ := Finset.mem_map.mp hi
  obtain ⟨y,_,hy⟩ := Finset.mem_map.mp hj
  exact h (congrArg Prod.fst (finProdFinEquiv.injective (hx.trans hy.symm)))

theorem equalGroups_union_card {r K : ℕ} (j : Finset (Fin r)) :
    (j.biUnion (equalGroups r K)).card = j.card*K := by
  rw [Finset.card_biUnion (fun a _ b _ hab => equalGroups_disjoint hab)]
  simp [equalGroups_card]

theorem embed_into_finset {m p : ℕ} (s : Finset (Fin m)) (h : p ≤ s.card) :
    ∃ e : Fin p ↪ Fin m, ∀ i, e i ∈ s := by
  classical
  obtain ⟨t,ht,hc⟩ := Finset.exists_subset_card_eq h
  let eq : Fin p ≃ ↥(t : Set (Fin m)) := ((Finset.equivFin t).trans (finCongr hc)).symm
  let e : Fin p ↪ Fin m := eq.toEmbedding.trans ⟨Subtype.val,Subtype.val_injective⟩
  exact ⟨e,fun i => ht (eq i).property⟩

theorem embed_complement {n : ℕ} (H : Finset (Fin n)) :
    ∃ ec : Fin (n-H.card) ↪ Fin n, ∀ j : Fin n, j ∈ H ∨ ∃ j', ec j' = j := by
  classical
  let t := univ \ H
  have hc : t.card = n-H.card := by simp [t,Finset.card_sdiff_of_subset (Finset.subset_univ H)]
  let eq : Fin (n-H.card) ≃ ↥(t : Set (Fin n)) := ((Finset.equivFin t).trans (finCongr hc)).symm
  let ec : Fin (n-H.card) ↪ Fin n := eq.toEmbedding.trans ⟨Subtype.val,Subtype.val_injective⟩
  refine ⟨ec,?_⟩
  intro j
  by_cases h : j ∈ H
  · exact Or.inl h
  · exact Or.inr ⟨eq.symm ⟨j,by simp [t,h]⟩,congrArg Subtype.val (eq.apply_symm_apply ⟨j,by simp [t,h]⟩)⟩

/-- The one-stage bound on a real board of r groups of K rows; no recursive
certificate is assumed for undersized masks. -/
theorem sampled_block_step {r K n b k : ℕ} (hb : 0 < b) (hbn : b ≤ n) (hm : n < r*K)
    {a B : ℝ} (ha : 1 < a) (ha' : a ≤ 2)
    (htail : (k:ℝ) - ((a-1)/(a+1))^2 * r/2 ≤ -(b:ℝ)-1)
    (hsmall : BoundedCombination (@Plain (k*K) (n-b)) (fun _ => 1) B) :
    BoundedCombination (@Plain (r*K) n) (fun _ => 1)
      (2*(a^b*B+(1+a^b)*((r.choose (b+1):ℝ)*((K:ℝ)^2*2^(8*b))))+1) := by
  classical
  let G := equalGroups r K
  let S : Finset (Fin r) := univ
  let D : Finset (Fin (b+1) × Finset (Fin r)) := (univ : Finset (Fin (b+1))) ×ˢ S.powerset
  let w := extWeight b (extPoint a)
  let z := batchNode b a
  let c := fun ij : Fin (b+1) × Finset (Fin r) => w ij.1 * bernoulliWeight S ij.2 (z ij.1)
  let M := fun ij : Fin (b+1) × Finset (Fin r) => ij.2.biUnion G
  let good := fun ij : Fin (b+1) × Finset (Fin r) => k ≤ ij.2.card
  let W := ∑ i ∈ D, |c i|
  let θ := ∑ i ∈ D, if good i then 0 else |c i|
  let A := W*B+(1+W)*((r.choose (b+1):ℝ)*((K:ℝ)^2*2^(8*b)))
  have hzs (i : Fin (b+1)) : 0 ≤ z i ∧ z i ≤ 1 := by
    have h := batchNode_bounds ha i
    exact ⟨(sq_nonneg _).trans h.1,h.2⟩
  have habs (ij : Fin (b+1) × Finset (Fin r)) :
      |c ij| = |w ij.1| * bernoulliWeight S ij.2 (z ij.1) := by
    simp [c,abs_mul,abs_of_nonneg (bernoulliWeight_nonneg S ij.2 (hzs ij.1).1 (hzs ij.1).2)]
  have hWexact : W = ∑ i : Fin (b+1), |w i| := by
    unfold W D
    rw [Finset.sum_product]
    simp_rw [habs,←Finset.mul_sum,bernoulli_total,mul_one]
  have hW : W ≤ a^b := hWexact.le.trans (batch_weight_bound hb ha)
  have hθ : 0 ≤ θ := by
    apply Finset.sum_nonneg
    intro i _
    split_ifs <;> positivity
  have hθ' : θ ≤ 1/2 := by
    have hbad (i : Fin (b+1)) :
        (∑ j ∈ S.powerset, if j.card < k then bernoulliWeight S j (z i) else 0)
          ≤ Real.exp (-(b:ℝ)-1) := by
      apply (bernoulli_bad_bound S k (hzs i).1 (hzs i).2).trans
      apply Real.exp_le_exp.mpr
      simp only [S,Finset.card_univ,Fintype.card_fin]
      have h := mul_le_mul_of_nonneg_right (batchNode_bounds ha i).1 (Nat.cast_nonneg r)
      change _ ≤ z i * r at h
      linarith
    have hθW : θ ≤ W*Real.exp (-(b:ℝ)-1) := by
      unfold θ D
      rw [Finset.sum_product,hWexact,Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _
      have h := mul_le_mul_of_nonneg_left (hbad i) (abs_nonneg (w i))
      rw [Finset.mul_sum] at h
      convert h using 1
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : k ≤ j.card
      · simp [good,hj,not_lt.mpr hj]
      · simp [good,hj, Nat.lt_of_not_ge hj,habs]
    have hap : a^b ≤ Real.exp (b:ℝ) := by
      rw [← mul_one (b:ℝ),Real.exp_nat_mul]
      have he : (2:ℝ) ≤ Real.exp 1 := by simpa only [one_add_one_eq_two] using Real.add_one_le_exp 1
      exact pow_le_pow_left₀ (by linarith) (ha'.trans he) _
    calc
      θ ≤ W*Real.exp (-(b:ℝ)-1) := hθW
      _ ≤ Real.exp (b:ℝ)*Real.exp (-(b:ℝ)-1) := mul_le_mul_of_nonneg_right (hW.trans hap) (by positivity)
      _ = (Real.exp 1)⁻¹ := by rw [← Real.exp_add,show (b:ℝ)+(-b-1) = -1 by ring,Real.exp_neg]
      _ ≤ 1/2 := by
        rw [one_div]
        exact inv_anti₀ (by norm_num)
          (by simpa only [one_add_one_eq_two] using Real.add_one_le_exp 1)
  obtain ⟨H,_,hH⟩ := Finset.exists_subset_card_eq (s:=(univ:Finset (Fin n))) (n:=b) (by simpa)
  obtain ⟨ec0,hec0⟩ := embed_complement H
  let ee := finCongr (by omega : n-b = n-H.card)
  let ec := ee.toEmbedding.trans ec0
  have hec (j : Fin n) : j ∈ H ∨ ∃ j', ec j' = j := by
    rcases hec0 j with hj | ⟨i,hi⟩
    · exact Or.inl hj
    · exact Or.inr ⟨ee.symm i,by simpa [ec] using hi⟩
  have hex (x : Board (r*K) n) (hx : (liveGroups G H S x).card ≤ H.card) :
      (∑ i ∈ D, c i*bit (Inactive (M i) H x)) = 1 := by
    unfold D
    rw [Finset.sum_product]
    simp_rw [c,M,mul_assoc,← Finset.mul_sum,expected_inactive_mask]
    exact batch_interp_exact hb (hx.trans_eq hH) ha
  have hg (i : Fin (b+1) × Finset (Fin r)) (_ : i ∈ D) (hi : good i) :
      ∃ er : Fin (k*K) ↪ Fin (r*K), ∀ j, er j ∈ M i := by
    apply embed_into_finset
    rw [equalGroups_union_card]
    exact Nat.mul_le_mul_right K hi
  have hAw : 0 ≤ A := by
    have hw : 0 ≤ W := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    have hB := hsmall.cost_nonneg
    dsimp only [A]
    positivity
  have hresult := bounded_absorb hAw hθ (by linarith : θ < 1) (by norm_num : 0 < (1:ℝ))
    ⟨_,plain_exponential_seed hm⟩ (fun C hC => by
      have hh := finite_interpolation_step H ec hec G S K (hH.symm ▸ hb)
        (fun _ _ _ _ hab => equalGroups_disjoint hab) (fun i _ => (equalGroups_card r K i).le)
        D M c good hg hex hsmall hC
      dsimp only at hh
      simpa only [hH,S,Finset.card_univ,Fintype.card_fin] using hh)
  apply hresult.cost_mono
  have hden : 0 < 1-θ := by linarith
  have hbound : A/(1-θ) ≤ 2*A := (div_le_iff₀ hden).mpr (by nlinarith [mul_nonneg hAw (show 0 ≤ 1-2*θ by linarith)])
  have hmono : A ≤ a^b*B+(1+a^b)*((r.choose (b+1):ℝ)*((K:ℝ)^2*2^(8*b))) := by
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right hW hsmall.cost_nonneg
    · exact mul_le_mul_of_nonneg_right (add_le_add_left hW 1) (by positivity)
  linarith

end PHP
