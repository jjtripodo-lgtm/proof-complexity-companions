import PHP.CoupledLocal
import PHP.FiniteMassClosure
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

namespace PHP
open Finset Filter Polynomial
open scoped BigOperators Topology

structure BisectionState where
  start : ℝ
  width : ℝ
  index : ℝ

noncomputable def BisectionState.offset (b : ℕ) (s : BisectionState) : ℕ :=
  if 2*s.index ≤ (b:ℝ) then 0 else b

noncomputable def BisectionState.step (b : ℕ) (s : BisectionState) : BisectionState :=
  ⟨s.start+s.width/(2*(b:ℝ))*(s.offset b:ℝ),s.width/2,2*s.index-(s.offset b:ℝ)⟩

noncomputable def dyadicState (b : ℕ) (u : ℝ) : ℕ → BisectionState
  | 0 => ⟨0,1,(b:ℝ)*u⟩
  | k+1 => (dyadicState b u k).step b

private theorem dyadic_invariant {b : ℕ} (hb : 0 < b) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (k : ℕ) :
    let d := dyadicState b u k
    0 ≤ d.start ∧ d.width = (1/2:ℝ)^k ∧ d.start+d.width ≤ 1 ∧
    0 ≤ d.index ∧ d.index ≤ b ∧ d.start+d.width/(b:ℝ)*d.index = u := by
  have hbR : 0 < (b:ℝ) := by exact_mod_cast hb
  induction k with
  | zero =>
    dsimp [dyadicState]
    refine ⟨le_rfl,rfl,by norm_num,mul_nonneg hbR.le hu0,?_,?_⟩
    · nlinarith [mul_le_mul_of_nonneg_left hu1 hbR.le]
    · field_simp; ring
  | succ k IH =>
    obtain ⟨h0,hw,h1,h2,h3,h4⟩ := IH
    let d := dyadicState b u k
    have hs : 0 ≤ d.width := by rw [show d.width=(1/2:ℝ)^k from hw]; positivity
    have hW : d.width/2 = (1/2:ℝ)^(k+1) := by rw [show d.width=(1/2:ℝ)^k from hw,pow_succ]; ring
    have hB : d.width/(2*(b:ℝ))*(b:ℝ) = d.width/2 := by field_simp
    change 0 ≤ (d.step b).start ∧ (d.step b).width = (1/2:ℝ)^(k+1) ∧
      (d.step b).start+(d.step b).width ≤ 1 ∧
      0 ≤ (d.step b).index ∧ (d.step b).index ≤ b ∧
      (d.step b).start+(d.step b).width/(b:ℝ)*(d.step b).index = u
    unfold BisectionState.step BisectionState.offset
    split_ifs with h
    · simp only [Nat.cast_zero,mul_zero,add_zero,sub_zero]
      have he : d.start+d.width/2/(b:ℝ)*(2*d.index) = d.start+d.width/(b:ℝ)*d.index := by ring
      exact ⟨h0,hW,by linarith,by linarith,h,he.trans h4⟩
    · rw [hB]
      have he : d.start+d.width/2+d.width/2/(b:ℝ)*(2*d.index-(b:ℝ)) =
          d.start+d.width/(b:ℝ)*d.index := by field_simp; ring
      exact ⟨by linarith,hW,by linarith,by linarith,by linarith,he.trans h4⟩

private theorem pow_lipschitz {p q : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (hq : 0 ≤ q) (hq' : q ≤ 1)
    (h : ℕ) : |p^h-q^h| ≤ (h:ℝ)*|p-q| := by
  induction h with
  | zero => simp
  | succ h IH =>
    rw [pow_succ,pow_succ]
    have e : p^h*p-q^h*q = p^h*(p-q)+(p^h-q^h)*q := by ring
    rw [e]
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul,abs_of_nonneg (pow_nonneg hp _),abs_of_nonneg hq]
    have h₁ := mul_le_mul_of_nonneg_right (pow_le_one₀ (n:=h) hp hp') (abs_nonneg (p-q))
    have h₂ := mul_le_mul IH hq' hq (by positivity)
    push_cast
    linarith

private theorem local_approx_error {m n b : ℕ} (H : Finset (Fin n)) (hb : 0 < b)
    {a s t u : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (has : a+s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ b) (htu : a+s/(b:ℝ)*t = u) (x : Board m n) :
    |localApprox b H a s t x - (1-u)^(activeRows H x).card| ≤ (8:ℝ)^b*(m:ℝ)*s := by
  have hbR : 0 < (b:ℝ) := by exact_mod_cast hb
  let q := (activeRows H x).card
  let z := fun i : ℕ => a+s/(b:ℝ)*(i:ℝ)
  have hSum : (∑ i ∈ range (b+1), uniformWeight b t i) = 1 := by
    simpa using uniform_interp b t (1:ℝ[X]) (by simp)
  have hz (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ b) : a ≤ a+s/(b:ℝ)*w ∧ a+s/(b:ℝ)*w ≤ a+s := by
    have hd : 0 ≤ s/(b:ℝ) := by positivity
    have h := mul_le_mul_of_nonneg_left hw1 hd
    rw [div_mul_cancel₀ s hbR.ne'] at h
    exact ⟨by linarith [mul_nonneg hd hw0],by linarith⟩
  have huk := hz t ht0 ht1
  rw [htu] at huk
  have hen (i : ℕ) (hi : i ∈ range (b+1)) :
      |(1-z i)^q-(1-u)^q| ≤ (m:ℝ)*s := by
    have hIR : (i:ℝ) ≤ b := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have ht := hz i (by positivity) hIR
    have e : |(1-z i)-(1-u)| ≤ s := by
      apply abs_le.mpr
      change a ≤ z i ∧ z i ≤ a+s at ht
      constructor <;> linarith [ht.1,ht.2,huk.1,huk.2]
    have hP := pow_lipschitz (p:=1-z i) (q:=1-u)
      (by change a ≤ z i ∧ z i ≤ a+s at ht; linarith [ht.2])
      (by change a ≤ z i ∧ z i ≤ a+s at ht; linarith [ht.1])
      (by linarith [huk.2]) (by linarith [huk.1]) q
    have hq : (q:ℝ) ≤ m := by
      exact_mod_cast (show q ≤ m by dsimp [q]; simpa using (activeRows H x).card_le_univ)
    exact hP.trans (mul_le_mul hq e (abs_nonneg _) (by positivity))
  have he : localApprox b H a s t x - (1-u)^q =
      ∑ i ∈ range (b+1), uniformWeight b t i*((1-z i)^q-(1-u)^q) := by
    simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,hSum,one_mul]
    rfl
  change |localApprox b H a s t x - (1-u)^q| ≤ _
  rw [he]
  calc
    _ ≤ ∑ i ∈ range (b+1), |uniformWeight b t i*((1-z i)^q-(1-u)^q)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range (b+1), |uniformWeight b t i| * ((m:ℝ)*s) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hen i hi) (abs_nonneg _)
    _ ≤ _ := by
      rw [←Finset.sum_mul]
      have h := mul_le_mul_of_nonneg_right (uniform_weight_budget ht0 ht1) (by positivity : 0 ≤ (m:ℝ)*s)
      exact h.trans_eq (by ring)

noncomputable def dyadicApprox {m n : ℕ} (b : ℕ) (H : Finset (Fin n)) (u : ℝ) (k : ℕ) :
    Board m n → ℝ :=
  let d := dyadicState b u k
  localApprox b H d.start d.width d.index

private theorem dyadic_tendsto {m n b : ℕ} (H : Finset (Fin n)) (hb : 0 < b)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (x : Board m n) :
    Tendsto (fun k => dyadicApprox b H u k x) atTop (𝓝 ((1-u)^(activeRows H x).card)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have h : Tendsto (fun k : ℕ => ((8:ℝ)^b*(m:ℝ))* (1/2:ℝ)^k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
      (by norm_num)).const_mul ((8:ℝ)^b*m)
  apply squeeze_zero (fun _ => dist_nonneg) _ h
  intro k
  obtain ⟨ha,hs,hss,ht0,ht1,hE⟩ := dyadic_invariant hb hu0 hu1 k
  have hsw : 0 ≤ (dyadicState b u k).width := by rw [hs]; positivity
  have hErr := local_approx_error H hb ha hsw hss ht0 ht1 hE x
  rw [Real.dist_eq]
  unfold dyadicApprox
  rw [hs]
  rw [hs] at hErr
  exact hErr

noncomputable def coupledConstant (m b : ℕ) : ℝ := 8*(8:ℝ)^b*2^(10*b)*((m:ℝ)*((m:ℝ)-1))

private theorem dyadic_pair_cost {m n b : ℕ} (H : Finset (Fin n)) (hH : H.card = b)
    (hb : 0 < b) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (k : ℕ) :
    BoundedCombination (@ColumnCollision m n)
      (fun x => dyadicApprox b H u k x-dyadicApprox b H u (k+1) x)
      ((coupledConstant m b/2)*(1/4:ℝ)^k) := by
  let d := dyadicState b u k
  let o := d.offset b
  have h' := dyadic_invariant hb hu0 hu1 k
  obtain ⟨ha,hs,hss,ht0,ht1,hE⟩ := h'
  obtain ⟨_,_,_,hu'0,hu'1,_⟩ := dyadic_invariant hb hu0 hu1 (k+1)
  have ho : o ≤ b := by unfold o BisectionState.offset; split_ifs <;> omega
  have hs0 : 0 ≤ d.width := by change d.width = _ at hs; rw [hs]; positivity
  have he := local_coupled_cost (m:=m) H hH hb ha hs0 hss ht0 ht1 o ho hu'0 hu'1
  change BoundedCombination _ _ (4*(8:ℝ)^b*2^(10*b)*((m:ℝ)*((m:ℝ)-1))*d.width^2) at he
  change d.width = _ at hs
  have hp : (((1/2:ℝ)^k)^2) = (1/4:ℝ)^k := by
    rw [←pow_mul,Nat.mul_comm,pow_mul]
    norm_num
  change BoundedCombination (@ColumnCollision m n)
    (fun x => dyadicApprox b H u k x-dyadicApprox b H u (k+1) x) _ at he
  apply he.cost_mono
  rw [hs,hp]
  unfold coupledConstant
  ring_nf
  exact le_rfl

private theorem coupledConstant_nonneg (m b : ℕ) : 0 ≤ coupledConstant m b := by
  unfold coupledConstant
  by_cases hm : m = 0
  · simp [hm]
  · have h : (1:ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
    have h' : 0 ≤ (m:ℝ)-1 := sub_nonneg.mpr h
    positivity

private theorem dyadic_telescope {m n b : ℕ} (H : Finset (Fin n)) (hH : H.card = b)
    (hb : 0 < b) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (k : ℕ) :
    BoundedCombination (@ColumnCollision m n)
      (fun x => dyadicApprox b H u 0 x-dyadicApprox b H u k x)
      (coupledConstant m b*(1-(1/4:ℝ)^k)) := by
  let C := coupledConstant m b
  have hC : 0 ≤ C := coupledConstant_nonneg _ _
  induction k with
  | zero => simpa using BoundedCombination.zero (@ColumnCollision m n)
  | succ k IH =>
    have hs := dyadic_pair_cost (m:=m) H hH hb hu0 hu1 k
    have hh := (IH.add hs).of_eq (g:=fun x => dyadicApprox b H u 0 x-dyadicApprox b H u (k+1) x)
      (fun x => by ring)
    apply hh.cost_mono
    change C*(1-(1/4:ℝ)^k)+(C/2)*(1/4:ℝ)^k ≤ C*(1-(1/4:ℝ)^(k+1))
    rw [pow_succ]
    nlinarith [mul_nonneg hC (pow_nonneg (by norm_num : (0:ℝ)≤1/4) k)]

/-- A uniform collision certificate for the interpolation error. Local
differences telescope. Compactness consolidates coefficients of the
finitely many possible literal cubes rather than an infinite refutation. -/
theorem dyadic_error_cost {m n b : ℕ} (H : Finset (Fin n)) (hH : H.card = b)
    (hb : 0 < b) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    BoundedCombination (@ColumnCollision m n)
      (fun x => dyadicApprox b H u 0 x-(1-u)^(activeRows H x).card)
      (coupledConstant m b) := by
  refine boundedCombination_tendsto (l:=atTop)
    (f:=fun k x => dyadicApprox b H u 0 x-dyadicApprox b H u k x)
    (fun x => tendsto_const_nhds.sub (dyadic_tendsto H hb hu0 hu1 x)) ?_
  refine Eventually.of_forall fun k => (dyadic_telescope (m:=m) H hH hb hu0 hu1 k).cost_mono ?_
  have hh := mul_nonneg (coupledConstant_nonneg m b) (pow_nonneg (by norm_num : (0:ℝ)≤1/4) k)
  nlinarith

private theorem dyadic_root_polynomial {m n b : ℕ} (H : Finset (Fin n)) (x : Board m n) :
    ∃ P : ℝ[X], P.natDegree ≤ b ∧ ∀ u : ℝ, P.eval u = dyadicApprox b H u 0 x := by
  classical
  let v := fun i : ℕ => (i:ℝ)
  let s := range (b+1)
  let Q := fun i => (Lagrange.basis s v i).comp (C (b:ℝ)*X)
  have hinj : Set.InjOn v ↑s := by
    intro i _ j _ h
    change (i:ℝ)=j at h
    exact_mod_cast h
  let P := ∑ i ∈ s, C ((1-(0+1/(b:ℝ)*(i:ℝ)))^(activeRows H x).card) * Q i
  refine ⟨P,?_,?_⟩
  · unfold P
    apply natDegree_sum_le_of_forall_le
    intro i hi
    apply (natDegree_C_mul_le _ _).trans
    apply natDegree_comp_le.trans
    have hD := Lagrange.natDegree_basis hinj hi
    simp [s] at hD
    have hh : (C (b:ℝ)*X).natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans (by simp)
    change (Lagrange.basis s v i).natDegree * _ ≤ b
    rw [hD]
    simpa using Nat.mul_le_mul_left b hh
  · intro u
    simp [P,Q,s,v,dyadicApprox,dyadicState,localApprox,uniformWeight,
      Polynomial.eval_finset_sum,Polynomial.eval_mul,Polynomial.eval_comp,mul_comm]

/-- Coupled interpolation: every finite signed polynomial-annihilating
functional of the Bernoulli no-hit curve is cheap in true collision cubes. -/
theorem coupled_interpolation {m n b : ℕ} (H : Finset (Fin n)) (hH : H.card = b) (hb : 0 < b)
    {ι : Type*} (S : Finset ι) (node coeff : ι → ℝ)
    (hnode : ∀ i ∈ S, 0 ≤ node i ∧ node i ≤ 1)
    (hann : ∀ P : ℝ[X], P.natDegree ≤ b → ∑ i ∈ S, coeff i*P.eval (node i) = 0) :
    BoundedCombination (@ColumnCollision m n)
      (fun x => ∑ i ∈ S, coeff i*(1-node i)^(activeRows H x).card)
      (coupledConstant m b * ∑ i ∈ S, |coeff i|) := by
  have h (i : ι) (hi : i ∈ S) :=
    ((dyadic_error_cost (m:=m) H hH hb (hnode i hi).1 (hnode i hi).2).neg).smul (coeff i)
  have he := BoundedCombination.finset_sum S _ _ h
  simp_rw [mul_comm (|coeff _|) (coupledConstant m b),←Finset.mul_sum] at he
  apply he.of_eq
  intro x
  obtain ⟨P,hP,hx⟩ := dyadic_root_polynomial (b:=b) H x
  have hn := hann P hP
  simp_rw [hx] at hn
  simp_rw [neg_sub, mul_sub, Finset.sum_sub_distrib, hn, sub_zero]

end PHP
