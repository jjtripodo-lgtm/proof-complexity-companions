import PHP.Absorb
import PHP.SampledStep
import PHP.DyadicCoupling

namespace PHP
open scoped BigOperators
open Finset Polynomial

/-- The exact mask-transfer step, accepting a separately charged residual. -/
theorem mask_transfer_with_residual {m n p q : ℕ} {α : Type*}
    (H : Finset (Fin n)) (ec : Fin q ↪ Fin n)
    (hec : ∀ j : Fin n, j ∈ H ∨ ∃ j', ec j' = j)
    (s : Finset α) (mask : α → Finset (Fin m)) (coeff : α → ℝ)
    (good : α → Prop) [DecidablePred good]
    (hgood : ∀ i ∈ s, good i → ∃ er : Fin p ↪ Fin m, ∀ j, er j ∈ mask i)
    {B C R : ℝ} (hB : BoundedCombination (@Plain p q) (fun _ => 1) B)
    (hC : BoundedCombination (@Plain m n) (fun _ => 1) C)
    (hR : BoundedCombination (@ColumnCollision m n)
      (fun x => 1-(∑ i ∈ s, coeff i*bit (Inactive (mask i) H x))) R) :
    let W := ∑ i ∈ s, |coeff i|
    let bad := ∑ i ∈ s, if good i then 0 else |coeff i|
    BoundedCombination (@Plain m n) (fun _ => 1) (W*B+R+bad*C) := by
  classical
  dsimp only
  let f : Board m n → ℝ := fun x => ∑ i ∈ s, coeff i * bit (Inactive (mask i) H x)
  let W := ∑ i ∈ s, |coeff i|
  let bad := ∑ i ∈ s, if good i then 0 else |coeff i|
  change BoundedCombination _ _ (W*B+R+bad*C)
  have hm (i : α) (hi : i ∈ s) :
      BoundedCombination (@Plain m n) (fun x => coeff i * bit (Inactive (mask i) H x))
        ((if good i then |coeff i| else 0)*B + (if good i then 0 else |coeff i|)*C) := by
    by_cases h : good i
    · obtain ⟨er,her⟩ := hgood i hi h
      simpa only [if_pos h,zero_mul,add_zero] using (masked_plain_lift er ec (mask i) H her hec hB).smul (coeff i)
    · have hh := hC.mul_left plain_mono (zeroRect_cost (mask i) H)
      have he := hh.of_eq (g:=fun x => bit (Inactive (mask i) H x)) (fun x => by simp)
      simpa only [if_neg h,zero_mul,zero_add,mul_one] using he.smul (coeff i)
  have ha := BoundedCombination.finset_sum s _ _ hm
  change BoundedCombination _ f _ at ha
  simp_rw [Finset.sum_add_distrib,← Finset.sum_mul] at ha
  have hR' : BoundedCombination (@Plain m n) (fun x => 1-f x) R :=
    hR.legal_mono (fun _ => Or.inr)
  have hh := (ha.add hR').of_eq (g:=fun _ => 1) (fun x => by ring)
  apply hh.cost_mono
  have hle : (∑ i ∈ s, if good i then |coeff i| else 0) ≤ W := by
    apply Finset.sum_le_sum
    intro i _
    split_ifs <;> simp
  have hx := mul_le_mul_of_nonneg_right hle hB.cost_nonneg
  change _ + bad*C + R ≤ _
  linarith

/-- Chebyshev weights reproduce every polynomial of degree at most b at
the extrapolation point u = 0 in the original Bernoulli variable. -/
theorem cheb_mask_polynomial {b : ℕ} (hb : 0 < b) {a : ℝ} (ha : 1 < a)
    (P : ℝ[X]) (hP : P.natDegree ≤ b) :
    (∑ j : Fin (b+1), extWeight b (extPoint a) j*P.eval (batchNode b a j)) = P.eval 0 := by
  let U : ℝ[X] := 1-((1+X)*C (1+extPoint a)⁻¹)
  let Q := P.comp U
  have hU : U.natDegree ≤ 1 := by
    unfold U
    apply le_trans (natDegree_sub_le _ _)
    apply max_le (by simp)
    apply le_trans natDegree_mul_le
    simp only [natDegree_C,add_zero]
    exact (natDegree_add_le _ _).trans (by simp)
  have hQ : Q.natDegree ≤ b := natDegree_comp_le.trans
    ((Nat.mul_le_mul hP hU).trans_eq (Nat.mul_one b))
  have h := interp_polynomial hb (extPoint a) Q hQ
  have hx : 0 < 1+extPoint a := by linarith [extPoint_gt ha]
  have he (u : ℝ) : Q.eval u = P.eval (1-(1+u)/(1+extPoint a)) := by
    simp [Q,U,Polynomial.eval_comp,Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_add,div_eq_mul_inv]
  simp_rw [he] at h
  rw [div_self hx.ne',sub_self] at h
  exact h

/-- A single column-removal step with actual row masks and the sharper
coupled-interpolation residual. -/
theorem sharp_sampled_step {m n b k : ℕ} (hb : 0 < b) (hbn : b ≤ n) (hm : n < m)
    {a B : ℝ} (ha : 1 < a) (ha' : a ≤ 2)
    (htail : (k:ℝ) - ((a-1)/(a+1))^2 * (m:ℝ)/2 ≤ -(b:ℝ)-1)
    (hsmall : BoundedCombination (@Plain k (n-b)) (fun _ => 1) B) :
    BoundedCombination (@Plain m n) (fun _ => 1)
      (2*(a^b*B+(1+a^b)*coupledConstant m b)+1) := by
  classical
  let G : Fin m → Finset (Fin m) := fun i => {i}
  let S : Finset (Fin m) := univ
  let D : Finset (Fin (b+1) × Finset (Fin m)) := (univ : Finset (Fin (b+1))) ×ˢ S.powerset
  let w := extWeight b (extPoint a)
  let z := batchNode b a
  let c := fun ij : Fin (b+1) × Finset (Fin m) => w ij.1 * bernoulliWeight S ij.2 (z ij.1)
  let good := fun ij : Fin (b+1) × Finset (Fin m) => k ≤ ij.2.card
  let W := ∑ i ∈ D, |c i|
  let θ := ∑ i ∈ D, if good i then 0 else |c i|
  let A := W*B+(1+W)*coupledConstant m b
  have hIn (i : Fin (b+1)) : 0 ≤ z i ∧ z i ≤ 1 := by
    have he := batchNode_bounds ha i
    exact ⟨(sq_nonneg _).trans he.1,he.2⟩
  have habs (ij : Fin (b+1) × Finset (Fin m)) :
      |c ij| = |w ij.1| * bernoulliWeight S ij.2 (z ij.1) := by
    simp [c,abs_mul,abs_of_nonneg (bernoulliWeight_nonneg S ij.2 (hIn ij.1).1 (hIn ij.1).2)]
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
      apply (bernoulli_bad_bound S k (hIn i).1 (hIn i).2).trans
      apply Real.exp_le_exp.mpr
      simp only [S,Finset.card_univ,Fintype.card_fin]
      have h := mul_le_mul_of_nonneg_right (batchNode_bounds ha i).1 (Nat.cast_nonneg m)
      change _ ≤ z i * m at h
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
      · simp [good,hj,Nat.lt_of_not_ge hj,habs]
    have hA : a^b ≤ Real.exp (b:ℝ) := by
      rw [←mul_one (b:ℝ),Real.exp_nat_mul]
      have h : (2:ℝ) ≤ Real.exp 1 := by simpa only [one_add_one_eq_two] using Real.add_one_le_exp 1
      exact pow_le_pow_left₀ (by linarith) (ha'.trans h) _
    calc
      θ ≤ W*Real.exp (-(b:ℝ)-1) := hθW
      _ ≤ Real.exp (b:ℝ)*Real.exp (-(b:ℝ)-1) := mul_le_mul_of_nonneg_right (hW.trans hA) (by positivity)
      _ = (Real.exp 1)⁻¹ := by rw [←Real.exp_add,show (b:ℝ)+(-b-1)=-1 by ring,Real.exp_neg]
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
  have hg (i : Fin (b+1) × Finset (Fin m)) (_ : i ∈ D) (hi : good i) :
      ∃ er : Fin k ↪ Fin m, ∀ j, er j ∈ i.2 := embed_into_finset i.2 hi
  have hB (J : Finset (Fin m)) : J.biUnion G = J := by ext j; simp [G]
  have hActive (x : Board m n) : liveGroups G H S x = activeRows H x := by
    ext i
    simp [liveGroups,G,S,activeRows]
  have hF (x : Board m n) :
      (∑ i ∈ D, c i*bit (Inactive i.2 H x)) =
        ∑ j : Fin (b+1), w j*(1-z j)^(activeRows H x).card := by
    unfold D
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro j _
    have he := expected_inactive_mask G H S x (z j)
    simp only [hB,hActive] at he
    simp only [c,mul_assoc,←Finset.mul_sum]
    rw [he]
  let node : Unit ⊕ Fin (b+1) → ℝ := Sum.elim (fun _ => 0) z
  let coeff : Unit ⊕ Fin (b+1) → ℝ := Sum.elim (fun _ => 1) (fun j => -w j)
  have hnode (i : Unit ⊕ Fin (b+1)) (_ : i ∈ univ) : 0 ≤ node i ∧ node i ≤ 1 := by
    rcases i with u|j
    · norm_num [node]
    · exact hIn j
  have hann (P : ℝ[X]) (hP : P.natDegree ≤ b) : ∑ i : Unit ⊕ Fin (b+1), coeff i*P.eval (node i) = 0 := by
    simp only [Fintype.sum_sum_type,Fintype.sum_unique,coeff,node,Sum.elim_inl,Sum.elim_inr,
      one_mul,neg_mul,Finset.sum_neg_distrib]
    have h := cheb_mask_polynomial hb ha P hP
    change (∑ j : Fin (b+1), w j*P.eval (z j)) = _ at h
    rw [h,add_neg_cancel]
  have hr := coupled_interpolation (m:=m) H hH hb univ node coeff hnode hann
  have hcost : (∑ i : Unit ⊕ Fin (b+1), |coeff i|) = 1+W := by
    simp [coeff,Fintype.sum_sum_type,hWexact]
  rw [hcost,mul_comm] at hr
  have hr' := hr.of_eq (g:=fun x => 1-(∑ i ∈ D, c i*bit (Inactive i.2 H x))) (fun x => by
    change _ = 1-(∑ i ∈ D, c i*bit (Inactive i.2 H x))
    rw [hF x]
    simp [coeff,node,Fintype.sum_sum_type,Finset.sum_neg_distrib,sub_eq_add_neg])
  have hA : 0 ≤ A := by
    have hw : 0 ≤ W := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    have hB := hsmall.cost_nonneg
    have hc : 0 ≤ coupledConstant m b := (dyadic_error_cost (m:=m) H hH hb
      (u:=0) (by norm_num) (by norm_num)).cost_nonneg
    unfold A
    positivity
  have hres := bounded_absorb hA hθ (by linarith : θ < 1) (by norm_num : 0 < (1:ℝ))
    ⟨_,plain_exponential_seed hm⟩ (fun C hC => mask_transfer_with_residual H ec hec
      D Prod.snd c good hg hsmall hC hr')
  refine hres.cost_mono ?_
  have hden : 0 < 1-θ := by linarith
  have h1 : A/(1-θ) ≤ 2*A := (div_le_iff₀ hden).mpr
    (by nlinarith [mul_nonneg hA (show 0 ≤ 1-2*θ by linarith)])
  have h2 : A ≤ a^b*B+(1+a^b)*coupledConstant m b := by
    have hc : 0 ≤ coupledConstant m b :=
      (dyadic_error_cost (m:=m) H hH hb (u:=0) (by norm_num) (by norm_num)).cost_nonneg
    exact add_le_add (mul_le_mul_of_nonneg_right hW hsmall.cost_nonneg)
      (mul_le_mul_of_nonneg_right (add_le_add_left hW 1) hc)
  linarith

end PHP
