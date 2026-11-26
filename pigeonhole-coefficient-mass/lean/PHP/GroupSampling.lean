import PHP.CollisionThreshold
import Mathlib.Analysis.SpecialFunctions.Exp

namespace PHP
open scoped BigOperators
open Finset

noncomputable def bernoulliWeight {ι : Type*} [DecidableEq ι] (s j : Finset ι) (p : ℝ) : ℝ :=
  p^j.card * (1-p)^(s\j).card

theorem bernoulliWeight_nonneg {ι : Type*} [DecidableEq ι] (s j : Finset ι) {p : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) : 0 ≤ bernoulliWeight s j p := by
  unfold bernoulliWeight
  exact mul_nonneg (pow_nonneg hp _) (pow_nonneg (sub_nonneg.mpr hp') _)

theorem bernoulli_generating {ι : Type*} [DecidableEq ι] (s : Finset ι) (p z : ℝ) :
    (∑ j ∈ s.powerset, bernoulliWeight s j p * z^j.card) = (p*z+(1-p))^s.card := by
  rw [← Finset.prod_const, Finset.prod_add]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.prod_const, bernoulliWeight, mul_pow]
  ring

theorem bernoulli_total {ι : Type*} [DecidableEq ι] (s : Finset ι) (p : ℝ) :
    (∑ j ∈ s.powerset, bernoulliWeight s j p) = 1 := by
  simpa using bernoulli_generating s p 1

theorem inactive_unionGroups {m n : ℕ} {ι : Type*} [DecidableEq ι]
    (G : ι → Finset (Fin m)) (H : Finset (Fin n)) (j : Finset ι) (x : Board m n) :
    Inactive (j.biUnion G) H x ↔ ∀ i ∈ j, Inactive (G i) H x := by
  constructor
  · intro h i hi k hk a ha
    exact h k (Finset.mem_biUnion.mpr ⟨i,hi,hk⟩) a ha
  · intro h k hk a ha
    obtain ⟨i,hi,hki⟩ := Finset.mem_biUnion.mp hk
    exact h i hi k hki a ha

theorem expected_inactive_mask {m n : ℕ} {ι : Type*} [DecidableEq ι]
    (G : ι → Finset (Fin m)) (H : Finset (Fin n)) (s : Finset ι) (x : Board m n) (p : ℝ) :
    (∑ j ∈ s.powerset, bernoulliWeight s j p * bit (Inactive (j.biUnion G) H x)) =
      (1-p)^(liveGroups G H s x).card := by
  classical
  let f := fun i => if Inactive (G i) H x then p else 0
  calc
    _ = ∑ j ∈ s.powerset, (∏ i ∈ j, f i) * ∏ _i ∈ s\j, (1-p) := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases h : Inactive (j.biUnion G) H x
      · have he := (inactive_unionGroups G H j x).mp h
        simp only [bit,if_pos h,mul_one,bernoulliWeight,Finset.prod_const]
        congr 1
        exact (Finset.prod_congr rfl (fun i hi => show f i = p from if_pos (he i hi))).trans (Finset.prod_const p) |>.symm
      · have hz : ¬ ∀ i ∈ j, Inactive (G i) H x :=
          fun h' => h ((inactive_unionGroups G H j x).mpr h')
        push_neg at hz
        obtain ⟨i,hi,hia⟩ := hz
        rw [Finset.prod_eq_zero hi (if_neg hia)]
        simp [bit,h]
    _ = ∏ i ∈ s, (f i + (1-p)) := (Finset.prod_add _ _ _).symm
    _ = _ := by
      let L := liveGroups G H s x
      have hls : L ⊆ s := Finset.filter_subset _ _
      rw [← Finset.prod_sdiff hls]
      have hL : (∏ i ∈ L, (f i+(1-p))) = (1-p)^L.card := by
        rw [← Finset.prod_const]
        apply Finset.prod_congr rfl
        intro i hi
        have hn := (Finset.mem_filter.mp hi).2
        simp [f,hn]
      have hrest : (∏ i ∈ s\L, (f i+(1-p))) = 1 := by
        apply Finset.prod_eq_one
        intro i hi
        obtain ⟨his,hin⟩ := Finset.mem_sdiff.mp hi
        have h : Inactive (G i) H x := by
          by_contra hn
          exact hin (Finset.mem_filter.mpr ⟨his,hn⟩)
        simp [f,h]
      rw [hrest,hL,one_mul]

/-- A direct half-weight moment bounds all undersized masks; this avoids
probability libraries or a full Chernoff theorem. -/
theorem bernoulli_bad_bound {ι : Type*} [DecidableEq ι] (s : Finset ι) (k : ℕ)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) :
    (∑ j ∈ s.powerset, if j.card < k then bernoulliWeight s j p else 0)
      ≤ Real.exp ((k:ℝ)-p*s.card/2) := by
  classical
  have h1 : (∑ j ∈ s.powerset, if j.card < k then bernoulliWeight s j p else 0)
      ≤ (2:ℝ)^k * ∑ j ∈ s.powerset, bernoulliWeight s j p * (1/2:ℝ)^j.card := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have hn := bernoulliWeight_nonneg s j hp hp'
    by_cases hj : j.card < k
    · rw [if_pos hj, mul_left_comm]
      have hpow : (1:ℝ) ≤ 2^k * (1/2:ℝ)^j.card := by
        rw [one_div,inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity),one_mul]
        exact pow_le_pow_right₀ (by norm_num) hj.le
      simpa using mul_le_mul_of_nonneg_left hpow hn
    · rw [if_neg hj]
      positivity
  rw [bernoulli_generating] at h1
  have h2 : (2:ℝ)^k ≤ Real.exp k := by
    rw [← mul_one (k:ℝ),Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) (by simpa only [one_add_one_eq_two] using Real.add_one_le_exp 1) _
  have h3 : (p*(1/2)+(1-p))^s.card ≤ Real.exp (-(p/2)*s.card) := by
    rw [mul_comm _ (s.card:ℝ),Real.exp_nat_mul]
    have hrew : p*(1/2)+(1-p) = 1+ -(p/2) := by ring
    rw [hrew]
    apply pow_le_pow_left₀
    · linarith
    · simpa [add_comm] using Real.add_one_le_exp (-(p/2))
  have hm := h1.trans (mul_le_mul h2 h3 (pow_nonneg (by linarith : 0 ≤ p*(1/2)+(1-p)) _) (by positivity))
  rw [← Real.exp_add] at hm
  convert hm using 1
  congr 1
  ring

end PHP
