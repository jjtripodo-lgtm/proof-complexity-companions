import PHP.BoundedCombination
import PHP.LineExcess
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max

namespace PHP
open scoped BigOperators
open Finset

def Inactive {m n : ℕ} (G : Finset (Fin m)) (H : Finset (Fin n)) (x : Board m n) : Prop :=
  ∀ i ∈ G, ∀ j ∈ H, x (i,j) = false

noncomputable def zeroRect {m n : ℕ} (G : Finset (Fin m)) (H : Finset (Fin n)) : Cube m n :=
  fun ij => if ij.1 ∈ G ∧ ij.2 ∈ H then some false else none

noncomputable def active {m n : ℕ} (G : Finset (Fin m)) (H : Finset (Fin n)) (x : Board m n) : ℝ :=
  1 - bit (Inactive G H x)

theorem zeroRect_holds {m n : ℕ} (G : Finset (Fin m)) (H : Finset (Fin n)) (x : Board m n) :
    Holds (zeroRect G H) x ↔ Inactive G H x := by
  constructor
  · intro h i hi j hj
    exact h (i,j) false (by simp [zeroRect,hi,hj])
  · intro h ⟨i,j⟩ b hb
    by_cases hh : i ∈ G ∧ j ∈ H
    · simp [zeroRect,hh] at hb
      exact (h i hh.1 j hh.2).trans hb.symm
    · simp [zeroRect,hh] at hb

theorem zeroRect_cost {m n : ℕ} (G : Finset (Fin m)) (H : Finset (Fin n)) :
    BoundedCombination Unlimited (fun x => bit (Inactive G H x)) 1 :=
  (BoundedCombination.atom (zeroRect G H) trivial).of_eq fun x => by
    unfold eval bit
    split_ifs <;> simp_all [zeroRect_holds]

theorem active_cost {m n : ℕ} (G : Finset (Fin m)) (H : Finset (Fin n)) :
    BoundedCombination Unlimited (active G H) 2 := by
  apply ((BoundedCombination.one (m:=m) (n:=n)).add (zeroRect_cost G H).neg).of_eq (fun x => by simp [active,sub_eq_add_neg]) |>.cost_mono
  norm_num

theorem active_split {m n : ℕ} (G : Finset (Fin m)) (L R : Finset (Fin n)) (x : Board m n) :
    active G (L ∪ R) x = active G L x + bit (Inactive G L x) * active G R x := by
  have hh : Inactive G (L ∪ R) x ↔ Inactive G L x ∧ Inactive G R x := by
    simp only [Inactive,Finset.mem_union]
    constructor
    · intro h
      exact ⟨fun i hi j hj => h i hi j (Or.inl hj),fun i hi j hj => h i hi j (Or.inr hj)⟩
    · rintro ⟨hl,hr⟩ i hi j (hj|hj)
      · exact hl i hi j hj
      · exact hr i hi j hj
  by_cases hl : Inactive G L x <;> by_cases hr : Inactive G R x <;>
    norm_num [active,bit,hh,hl,hr]

def FirstIn {m n : ℕ} (G : Finset (Fin m)) (j : Fin n) (x : Board m n) (a : Fin m) : Prop :=
  x (a,j) = true ∧ ∀ i ∈ G, i < a → x (i,j) = false

noncomputable def firstInCube {m n : ℕ} (G : Finset (Fin m)) (j : Fin n) (a : Fin m) : Cube m n :=
  fun ij => if ij.2 = j then if ij.1 = a then some true
    else if ij.1 ∈ G ∧ ij.1 < a then some false else none else none

theorem firstIn_holds {m n : ℕ} (G : Finset (Fin m)) (j : Fin n) (a : Fin m)
    (x : Board m n) : Holds (firstInCube G j a) x ↔ FirstIn G j x a := by
  constructor
  · intro h
    refine ⟨h (a,j) true (by simp [firstInCube]),?_⟩
    intro i hi hia
    exact h (i,j) false (by simp [firstInCube,hi,hia,ne_of_lt hia])
  · rintro ⟨ha,hpre⟩ ⟨i,k⟩ b hb
    by_cases hk : k = j
    · subst k
      by_cases hi : i = a
      · subst i
        exact ha.trans (by simpa [firstInCube] using hb)
      · by_cases hh : i ∈ G ∧ i < a
        · exact (hpre i hh.1 hh.2).trans (by simpa [firstInCube,hi,hh] using hb)
        · simp [firstInCube,hi,hh] at hb
    · simp [firstInCube,hk] at hb

theorem active_singleton_sum {m n : ℕ} (G : Finset (Fin m)) (j : Fin n) (x : Board m n) :
    active G {j} x = ∑ a ∈ G, eval (firstInCube G j a) x := by
  classical
  have hE : Inactive G {j} x ↔ ∀ a ∈ G, x (a,j) = false := by
    simp [Inactive]
  by_cases h : Inactive G {j} x
  · simp only [active,bit,if_pos h,sub_self]
    symm
    apply Finset.sum_eq_zero
    intro a ha
    have hn : ¬ FirstIn G j x a := by
      intro hf
      exact Bool.noConfusion (hf.1.symm.trans (hE.mp h a ha))
    simp [eval,firstIn_holds,hn]
  let S := G.filter (fun a => x (a,j) = true)
  have hs : S.Nonempty := by
    by_contra hn
    apply h
    rw [hE]
    intro a ha
    cases hv : x (a,j)
    · rfl
    · exact False.elim (hn ⟨a,by simp [S,ha,hv]⟩)
  let a := S.min' hs
  have ham := Finset.mem_filter.mp (S.min'_mem hs)
  have haf : FirstIn G j x a := by
    refine ⟨ham.2,?_⟩
    intro i hi hia
    cases hz : x (i,j)
    · rfl
    · exact False.elim ((not_le_of_gt hia) (S.min'_le i (by simp [S,hi,hz])))
  rw [Finset.sum_eq_single a]
  · simp [active,bit,h,eval,firstIn_holds,haf]
  · intro i hi hne
    have hn : ¬ FirstIn G j x i := by
      intro hf
      rcases lt_or_gt_of_ne hne with hia | hai
      · exact Bool.noConfusion (hf.1.symm.trans (haf.2 i hi hia))
      · exact Bool.noConfusion (haf.1.symm.trans (hf.2 a ham.1 hai))
    simp [eval,firstIn_holds,hn]
  · exact fun hn => False.elim (hn ham.1)

theorem collision_mono {m n : ℕ} {c d : Cube m n} (h : Extends d c)
    (hc : ColumnCollision c) : ColumnCollision d := by
  obtain ⟨i,k,j,hi,hj,hk⟩ := hc
  exact ⟨i,k,j,hi,h _ _ hj,h _ _ hk⟩

theorem grouped_singleton_collision {m n : ℕ} {G D : Finset (Fin m)}
    (hGD : Disjoint G D) (j : Fin n) :
    BoundedCombination ColumnCollision (fun x => active G {j} x * active D {j} x)
      ((G.card : ℝ) * D.card) := by
  classical
  have h (a : Fin m) (ha : a ∈ G) (b : Fin m) (hb : b ∈ D) :
      BoundedCombination ColumnCollision
        (fun x => eval (firstInCube G j a) x * eval (firstInCube D j b) x) 1 := by
    by_cases hc : Compatible (firstInCube G j a) (firstInCube D j b)
    · have ha' : firstInCube G j a (a,j) = some true := by simp [firstInCube]
      have hb' : firstInCube D j b (b,j) = some true := by simp [firstInCube]
      have hn : a ≠ b := fun he => Finset.disjoint_left.mp hGD ha (he ▸ hb)
      have hc' : ColumnCollision (join (firstInCube G j a) (firstInCube D j b)) :=
        ⟨a,b,j,hn,join_extends_left _ _ _ _ ha',join_extends_right hc _ _ hb'⟩
      exact (BoundedCombination.atom _ hc').of_eq (fun x => by rw [eval_product,if_pos hc])
    · exact (BoundedCombination.zero _).of_eq (fun x => by rw [eval_product,if_neg hc])
        |>.cost_mono (by norm_num)
  have hg := BoundedCombination.finset_sum G
    (fun a x => ∑ b ∈ D, eval (firstInCube G j a) x * eval (firstInCube D j b) x)
    (fun _ => ∑ _b ∈ D, (1 : ℝ))
    (fun a ha => BoundedCombination.finset_sum D _ _ (h a ha))
  convert hg using 1
  · ext x
    rw [active_singleton_sum,active_singleton_sum,Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  · simp


theorem active_prod_cost {m n : ℕ} {ι : Type*} (s : Finset ι)
    (G : ι → Finset (Fin m)) (H : Finset (Fin n)) :
    BoundedCombination Unlimited (fun x => ∏ i ∈ s, active (G i) H x) (2 ^ s.card) := by
  simpa using BoundedCombination.finset_prod_unlimited s
    (fun i => active (G i) H) (fun _ => (2:ℝ)) (fun i _ => active_cost (G i) H)

theorem inactive_prod_cost {m n : ℕ} {ι : Type*} (s : Finset ι)
    (G : ι → Finset (Fin m)) (H : Finset (Fin n)) :
    BoundedCombination Unlimited (fun x => ∏ i ∈ s, bit (Inactive (G i) H x)) 1 := by
  simpa using BoundedCombination.finset_prod_unlimited s
    (fun i x => bit (Inactive (G i) H x)) (fun _ => (1:ℝ)) (fun i _ => zeroRect_cost (G i) H)

theorem grouped_collision_sharp5 {m n : ℕ} {ι : Type*} [DecidableEq ι]
    (G : ι → Finset (Fin m)) (K : ℕ)
    (H : Finset (Fin n)) (s : Finset ι) (hH : 1 ≤ H.card) (hs : s.card = H.card+1)
    (hd : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → Disjoint (G a) (G b))
    (hK : ∀ a ∈ s, (G a).card ≤ K) :
    BoundedCombination ColumnCollision (fun x => ∏ i ∈ s, active (G i) H x)
      ((K:ℝ)^2 * 2^(5*H.card)) := by
  classical
  generalize hq : H.card = q at *
  induction q using Nat.strong_induction_on generalizing s H with
  | h q IH =>
    by_cases h1 : q = 1
    · subst q
      obtain ⟨j,rfl⟩ := Finset.card_eq_one.mp h1
      obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp (show s.card = 2 by omega)
      have h := grouped_singleton_collision (hd a (by simp) b (by simp) hab) j
      have ha : ((G a).card:ℝ) ≤ K := by exact_mod_cast hK a (by simp)
      have hb : ((G b).card:ℝ) ≤ K := by exact_mod_cast hK b (by simp)
      have hc := mul_le_mul ha hb (by positivity) (by positivity)
      have hh : ((K:ℝ)*K) ≤ (K:ℝ)^2 * 2^(5*({j}:Finset (Fin n)).card) := by
        simp only [Finset.card_singleton]
        norm_num
        nlinarith [sq_nonneg (K:ℝ)]
      simpa [Finset.prod_insert,hab] using h.cost_mono (hc.trans hh)
    · obtain ⟨L,hLH,hL⟩ := Finset.exists_subset_card_eq (s:=H) (n:=q/2) (by omega)
      let R := H \ L
      have hR : R.card = q-q/2 := by rw [Finset.card_sdiff_of_subset hLH,hq,hL]
      have hcover : L ∪ R = H := Finset.union_sdiff_of_subset hLH
      let T := (q+1)/2
      have hltL : L.card < q := by omega
      have hltR : R.card < q := by omega
      have hT : 4*T+2*q+1 ≤ 5*q := by dsimp [T]; omega
      have hmass (J : Finset (Fin n)) (a b : Finset ι)
          (ha : a ⊆ s) (hb : b ⊆ s) (hc : J.card < a.card) (hj : 1 ≤ J.card)
          (hlt : J.card < q) (ht : J.card ≤ T) (hcard : a.card+b.card = q+1)
          (Y : Finset (Fin n)) :
          BoundedCombination ColumnCollision
            (fun x => (∏ i ∈ a, active (G i) J x) * ∏ i ∈ b, active (G i) Y x)
              ((K:ℝ)^2 * 2^(4*T+q)) := by
        obtain ⟨u,hua,hu⟩ := Finset.exists_subset_card_eq (s:=a) (n:=J.card+1) (by omega)
        have hu' := IH J.card hlt J u
          (fun i hi j hj' hij => hd i (ha (hua hi)) j (ha (hua hj')) hij)
          (fun i hi => hK i (ha (hua hi))) rfl hj hu
        have hq' := (hu'.mul_left collision_mono (active_prod_cost (a \ u) G J)).mul_left
          collision_mono (active_prod_cost b G Y)
        apply (hq'.of_eq (fun x => by rw [mul_comm (∏ i ∈ u, _) (∏ i ∈ a \ u, _), Finset.prod_sdiff hua])).cost_mono
        rw [mul_assoc, mul_assoc ((K:ℝ)^2), ← pow_add, ← pow_add]
        refine mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num) ?_) (sq_nonneg _)
        have hdu := Finset.card_sdiff_of_subset hua
        omega
      have hbranch (j : Finset ι) (hj : j ∈ s.powerset) :
          BoundedCombination ColumnCollision
            (fun x => (∏ i ∈ j, active (G i) L x) *
              ∏ i ∈ s \ j, bit (Inactive (G i) L x) * active (G i) R x)
            ((K:ℝ)^2 * 2^(4*T+q)) := by
        have hjs := Finset.mem_powerset.mp hj
        have hjc := Finset.card_sdiff_of_subset hjs
        have h1 : j.card + (s \ j).card = q+1 := by have := Finset.card_le_card hjs; omega
        have hcase : L.card < j.card ∨ R.card < (s \ j).card := by omega
        have hres : BoundedCombination ColumnCollision
            (fun x => (∏ i ∈ j, active (G i) L x) * ∏ i ∈ s \ j, active (G i) R x)
            ((K:ℝ)^2 * 2^(4*T+q)) := by
          rcases hcase with ha | hb
          · exact hmass L j (s \ j) hjs Finset.sdiff_subset ha (by omega) hltL (by dsimp [T]; omega) h1 R
          · apply (hmass R (s \ j) j Finset.sdiff_subset hjs hb (by omega) hltR
              (by dsimp [T]; omega) (by omega) L).of_eq
            intro x
            exact mul_comm _ _
        have hfinal := hres.mul_left collision_mono (inactive_prod_cost (s \ j) G L)
        simp only [mul_one] at hfinal
        apply hfinal.of_eq
        intro x
        rw [Finset.prod_mul_distrib]
        ring
      have hall := BoundedCombination.finset_sum s.powerset _ _ hbranch
      refine (hall.of_eq ?_).cost_mono ?_
      · intro x
        rw [← hcover]
        simp_rw [active_split]
        exact (Finset.prod_add _ _ _).symm
      · simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_powerset, Nat.cast_pow, Nat.cast_ofNat]
        rw [mul_left_comm, ← pow_add, hs]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num) (by omega : q+1+(4*T+q) ≤ 5*q)) (sq_nonneg _)

/-- Convenient looser constant, preserving the original downstream interface. -/
theorem grouped_collision_bound {m n : ℕ} {ι : Type*} [DecidableEq ι]
    (G : ι → Finset (Fin m)) (K : ℕ)
    (H : Finset (Fin n)) (s : Finset ι) (hH : 1 ≤ H.card) (hs : s.card = H.card+1)
    (hd : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → Disjoint (G a) (G b))
    (hK : ∀ a ∈ s, (G a).card ≤ K) :
    BoundedCombination ColumnCollision (fun x => ∏ i ∈ s, active (G i) H x)
      ((K:ℝ)^2 * 2^(8*H.card)) := by
  apply (grouped_collision_sharp5 G K H s hH hs hd hK).cost_mono
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by norm_num) (by omega : 5*H.card ≤ 8*H.card)) (sq_nonneg _)

end PHP
