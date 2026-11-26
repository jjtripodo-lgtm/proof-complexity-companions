import PHP.CoupledBinPoly
import PHP.CoupledMoment
import PHP.UniformInterpolation

namespace PHP
open Finset Polynomial
open scoped BigOperators

noncomputable def localApprox {m n : ℕ} (b : ℕ) (H : Finset (Fin n))
    (a s t : ℝ) (x : Board m n) : ℝ :=
  ∑ i ∈ range (b+1), uniformWeight b t i * (1-(a+s/(b:ℝ)*(i:ℝ)))^(activeRows H x).card

private theorem affine_interp (b : ℕ) (t c d : ℝ) (P : ℝ[X]) (hP : P.natDegree ≤ b) :
    (∑ i ∈ range (b+1), uniformWeight b t i * P.eval (c+d*(i:ℝ))) = P.eval (c+d*t) := by
  let U : ℝ[X] := C c + C d*X
  have hd : U.natDegree ≤ 1 := by
    apply (natDegree_add_le _ _).trans
    have hm : (C d*X).natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans (by simp)
    simp [hm]
  have hPU : (P.comp U).natDegree ≤ b := natDegree_comp_le.trans
    ((Nat.mul_le_mul hP hd).trans_eq (Nat.mul_one b))
  have h := uniform_interp b t (P.comp U) hPU
  simp [U,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_mul] at h
  exact h

private theorem averageMask_cost {m n L : ℕ} (labels : Fin m → CoupledLabel L)
    (H : Finset (Fin n)) {z : ℕ} (hz : z ≤ L) :
    BoundedCombination Unlimited (averageMaskAt labels H z) 1 := by
  classical
  let U := (univ : Finset (Fin L)).powersetCard z
  have hc : U.card = L.choose z := by simp [U,Finset.card_powersetCard]
  have hp : 0 < (L.choose z:ℝ) := by exact_mod_cast Nat.choose_pos hz
  have h := (BoundedCombination.finset_sum U
    (fun J x => bit (Inactive (coupledMask labels J) H x))
    (fun _ => (1:ℝ)) (fun J _ => zeroRect_cost (coupledMask labels J) H)).smul (L.choose z:ℝ)⁻¹
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one,hc,abs_of_pos (inv_pos.mpr hp),inv_mul_cancel₀ hp.ne'] at h
  apply h.of_eq
  intro x
  unfold averageMaskAt
  rw [div_eq_mul_inv,mul_comm]

noncomputable def conditionedApprox {m n L : ℕ} (b : ℕ) (labels : Fin m → CoupledLabel L)
    (H : Finset (Fin n)) (t : ℝ) (grid : ℕ → ℕ) (x : Board m n) : ℝ :=
  ∑ i ∈ range (b+1), uniformWeight b t i * averageMaskAt labels H (grid i) x

theorem conditionedApprox_cost {m n L b : ℕ} (labels : Fin m → CoupledLabel L)
    (H : Finset (Fin n)) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ b)
    (grid : ℕ → ℕ) (hg : ∀ i ≤ b, grid i ≤ L) :
    BoundedCombination Unlimited (conditionedApprox b labels H t grid) ((8:ℝ)^b) := by
  classical
  have hf := BoundedCombination.finset_sum (range (b+1))
    (fun i x => uniformWeight b t i * averageMaskAt labels H (grid i) x)
    (fun i => |uniformWeight b t i|)
    (fun (i : ℕ) hi => by
      have h := averageMask_cost labels H (hg i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
      simpa only [mul_one] using h.smul (uniformWeight b t i))
  exact hf.cost_mono (uniform_weight_budget ht0 ht1)

private theorem conditioned_difference_vanish {m n b : ℕ} (labels : Fin m → CoupledLabel (2*b))
    (H : Finset (Fin n)) (t : ℝ) (o : ℕ) (ho : o ≤ b) (x : Board m n)
    (h : (liveGroups (binRows labels) H (univ : Finset (Fin (2*b))) x).card ≤ b) :
    conditionedApprox b labels H t (fun i => 2*i) x =
      conditionedApprox b labels H (2*t-(o:ℝ)) (fun i => o+i) x := by
  classical
  let q := avoidPoly (2*b) (liveGroups (binRows labels) H univ x).card
  have hd : q.natDegree ≤ b := (avoidPoly_degree _ _).trans h
  let e := bit (Inactive (prefixRows labels) H x)
  have hL : conditionedApprox b labels H t (fun i => 2*i) x = e*q.eval (2*t) := by
    unfold conditionedApprox
    have hs : (∑ i ∈ range (b+1), uniformWeight b t i * averageMaskAt labels H (2*i) x) =
        e * ∑ i ∈ range (b+1), uniformWeight b t i * q.eval (0+2*(i:ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hn := Finset.mem_range.mp hi
      rw [conditioned_mask_formula labels H x (show 2*i≤2*b by omega)]
      push_cast
      dsimp [e,q]
      ring
    rw [hs,affine_interp b t 0 2 q hd,zero_add]
  have hR : conditionedApprox b labels H (2*t-(o:ℝ)) (fun i => o+i) x = e*q.eval (2*t) := by
    unfold conditionedApprox
    have hs : (∑ i ∈ range (b+1), uniformWeight b (2*t-(o:ℝ)) i * averageMaskAt labels H (o+i) x) =
        e*∑ i ∈ range (b+1), uniformWeight b (2*t-(o:ℝ)) i * q.eval ((o:ℝ)+1*(i:ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hn := Finset.mem_range.mp hi
      rw [conditioned_mask_formula labels H x (show o+i≤2*b by omega)]
      push_cast
      dsimp [e,q]
      ring
    rw [hs,affine_interp b (2*t-(o:ℝ)) o 1 q hd]
    congr 2
    ring
  exact hL.trans hR.symm

private theorem conditioned_difference_cost {m n b : ℕ} (labels : Fin m → CoupledLabel (2*b))
    (H : Finset (Fin n)) (hH : H.card = b) (hb : 0 < b) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ b)
    (o : ℕ) (ho : o ≤ b) (hu0 : 0 ≤ 2*t-(o:ℝ)) (hu1 : 2*t-(o:ℝ) ≤ b) :
    BoundedCombination ColumnCollision
      (fun x => conditionedApprox b labels H t (fun i => 2*i) x -
        conditionedApprox b labels H (2*t-(o:ℝ)) (fun i => o+i) x)
      (4*(8:ℝ)^b*2^(10*b)*(((allBinRows labels).card:ℝ)*(((allBinRows labels).card:ℝ)-1))) := by
  classical
  let Y := (allBinRows labels).card
  let F := fun x => conditionedApprox b labels H t (fun i => 2*i) x -
    conditionedApprox b labels H (2*t-(o:ℝ)) (fun i => o+i) x
  have hzero (x : Board m n) (hx : (liveGroups (binRows labels) H univ x).card ≤ b) : F x = 0 :=
    sub_eq_zero.mpr (conditioned_difference_vanish labels H t o ho x hx)
  have hK0 : (0:ℝ) ≤ (Y:ℝ)*((Y:ℝ)-1) := by
    by_cases he : Y=0
    · simp [he]
    · exact mul_nonneg (by positivity) (sub_nonneg.mpr (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr he))
  by_cases hy : 2 ≤ Y
  · have hb' : 1 ≤ H.card := by omega
    have hd := collision_threshold_cost (binRows labels) H univ Y hb'
      (fun _ _ _ _ hij => binRows_disjoint labels hij) (fun i _ => binRows_card_le labels i)
    have h := (conditionedApprox_cost labels H ht0 ht1 (fun i => 2*i) (fun i hi => by dsimp; omega)).add
      (conditionedApprox_cost labels H hu0 hu1 (fun i => o+i) (fun i hi => by dsimp; omega)).neg
    have hprod := hd.mul_left collision_mono h
    refine (hprod.of_eq ?_).cost_mono ?_
    · intro x
      by_cases hx : b+1 ≤ (liveGroups (binRows labels) H univ x).card
      · simp [hH,bit,hx,F,sub_eq_add_neg]
      · have h' := hzero x (by omega)
        simpa [hH,bit,hx] using h'.symm
    simp only [hH,Finset.card_univ,Fintype.card_fin]
    have hChoose : ((2*b).choose (b+1):ℝ) ≤ 2^(2*b) := by
      exact_mod_cast (Nat.choose_le_two_pow (2*b) (b+1))
    have hyR : (2:ℝ) ≤ Y := by exact_mod_cast hy
    have hY : (Y:ℝ)^2 ≤ 2*((Y:ℝ)*((Y:ℝ)-1)) := by
      nlinarith [mul_nonneg (show 0 ≤ (Y:ℝ)-2 by linarith) (Nat.cast_nonneg (α:=ℝ) Y)]
    have hc := mul_le_mul hChoose (mul_le_mul_of_nonneg_right hY (show (0:ℝ) ≤ 2^(8*b) by positivity))
      (by positivity) (by positivity)
    have hcc := mul_le_mul_of_nonneg_right hc (show 0 ≤ (8:ℝ)^b+(8:ℝ)^b by positivity)
    have he : (2:ℝ)^(2*b)*((2*((Y:ℝ)*((Y:ℝ)-1)))*2^(8*b))*(8^b+8^b) =
      4*(8:ℝ)^b*2^(10*b)*((Y:ℝ)*((Y:ℝ)-1)) := by
      rw [show 10*b=2*b+8*b by omega,pow_add]
      ring
    exact hcc.trans_eq he
  · have hh : ∀ x, (liveGroups (binRows labels) H univ x).card ≤ b := by
      intro x
      have hw := active_bins_le_rows labels H x
      omega
    have hz := (BoundedCombination.zero (@ColumnCollision m n)).of_eq (fun x => (hzero x (hh x)).symm)
    exact hz.cost_mono (by positivity)

private theorem local_eq_average {m n b : ℕ} (H : Finset (Fin n)) (hb : 0 < b)
    (a s t : ℝ) (o : ℕ) (ho : o ≤ b) (x : Board m n) :
    (∑ labels : Fin m → CoupledLabel (2*b),
      iidWeight (coupledWeight (2*b) a s) labels*
      (conditionedApprox b labels H t (fun i => 2*i) x -
        conditionedApprox b labels H (2*t-(o:ℝ)) (fun i => o+i) x)) =
      localApprox b H a s t x -
        localApprox b H (a+s/(2*(b:ℝ))*(o:ℝ)) (s/2) (2*t-(o:ℝ)) x := by
  classical
  have hh : (0:ℝ) < b := by exact_mod_cast hb
  simp only [mul_sub,Finset.sum_sub_distrib]
  congr 1
  · unfold conditionedApprox localApprox
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    simp_rw [mul_left_comm (_ : ℝ) (uniformWeight b t i),←Finset.mul_sum]
    rw [average_mask_fubini (by omega : 0 < 2*b) a s H x (by omega : 2*i ≤ 2*b)]
    have he : s/(↑(2*b:ℕ):ℝ)*(↑(2*i:ℕ):ℝ) = s/(b:ℝ)*(i:ℝ) := by push_cast; field_simp
    rw [he]
  · unfold conditionedApprox localApprox
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    simp_rw [mul_left_comm (_ : ℝ) (uniformWeight b (2*t-(o:ℝ)) i),←Finset.mul_sum]
    rw [average_mask_fubini (by omega : 0 < 2*b) a s H x (by omega : o+i ≤ 2*b)]
    have he : a+s/(↑(2*b:ℕ):ℝ)*(↑(o+i:ℕ):ℝ) =
       a+s/(2*(b:ℝ))*(o:ℝ)+(s/2)/(b:ℝ)*(i:ℝ) := by push_cast; field_simp; ring
    rw [he]

/-- The original coupled interpolation estimate for a single bisection.
The length-squared factor comes from two distinct actual rows. -/
theorem local_coupled_cost {m n b : ℕ} (H : Finset (Fin n)) (hH : H.card = b) (hb : 0 < b)
    {a s t : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (has : a+s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ b)
    (o : ℕ) (ho : o ≤ b) (hu0 : 0 ≤ 2*t-(o:ℝ)) (hu1 : 2*t-(o:ℝ) ≤ b) :
    BoundedCombination (@ColumnCollision m n)
      (fun x => localApprox b H a s t x -
        localApprox b H (a+s/(2*(b:ℝ))*(o:ℝ)) (s/2) (2*t-(o:ℝ)) x)
      (4*(8:ℝ)^b*2^(10*b)*((m:ℝ)*((m:ℝ)-1))*s^2) := by
  classical
  let D := 4*(8:ℝ)^b*2^(10*b)
  let w := iidWeight (coupledWeight (2*b) a s) (α:=Fin m)
  let Y := fun labels : Fin m → CoupledLabel (2*b) => ((allBinRows labels).card:ℝ)
  have hw (labels : Fin m → CoupledLabel (2*b)) : 0 ≤ w labels :=
    Finset.prod_nonneg (fun i _ => coupled_weight_nonneg ha hs has _)
  have h (labels : Fin m → CoupledLabel (2*b)) :
      BoundedCombination ColumnCollision
        (fun x => w labels*(conditionedApprox b labels H t (fun i => 2*i) x -
          conditionedApprox b labels H (2*t-(o:ℝ)) (fun i => o+i) x))
        (w labels*(D*(Y labels*(Y labels-1)))) := by
    simpa only [abs_of_nonneg (hw labels)] using
      (conditioned_difference_cost labels H hH hb ht0 ht1 o ho hu0 hu1).smul (w labels)
  have hh := BoundedCombination.finset_sum univ _ _ (fun labels _ => h labels)
  apply (hh.of_eq (local_eq_average H hb a s t o ho)).cost_mono
  have he (labels : Fin m → CoupledLabel (2*b)) : w labels*(D*(Y labels*(Y labels-1))) =
      D*(w labels*Y labels*(Y labels-1)) := by ring
  simp_rw [he,←Finset.mul_sum]
  rw [coupled_factorial_moment (by omega : 0 < 2*b)]
  unfold D
  linarith only [show 4*(8:ℝ)^b*2^(10*b)*((m:ℝ)*((m:ℝ)-1)*s^2) =
    4*(8:ℝ)^b*2^(10*b)*((m:ℝ)*((m:ℝ)-1))*s^2 by ring]

end PHP
