import PHP.FunctionalBinomial
import PHP.FunctionalGaussian

namespace PHP
open Finset
open scoped BigOperators

def functionalMassSet (m n : ℕ) : Set ℝ :=
  { c | ∃ (s : ℕ) (r : Refutation (@Functional m n) s), c = r.mass }

noncomputable def optimalFunctionalMass (m n : ℕ) : ℝ := sInf (functionalMassSet m n)

noncomputable def functionalChargeBudget (m n : ℕ) : ℝ :=
  (m:ℝ)+(n:ℝ)*((m:ℝ)*(m-1)/2)+(m:ℝ)*((n:ℝ)*(n-1)/2)

theorem optimal_functional_sandwich {m n : ℕ} (hn : 4 ≤ n) (hm : n < m) :
    (m:ℝ)*functionalIntegral (m-n) n ≤ optimalFunctionalMass m n ∧
    optimalFunctionalMass m n ≤ functionalChargeBudget m n*functionalIntegral (m-n) n := by
  obtain ⟨s,r,hr⟩ := functional_general_upper hm
  have hne : (functionalMassSet m n).Nonempty := ⟨r.mass,s,r,rfl⟩
  have hb : BddBelow (functionalMassSet m n) := by
    refine ⟨1,?_⟩
    rintro _ ⟨s,r,rfl⟩
    exact r.one_le_mass
  constructor
  · apply le_csInf hne
    rintro _ ⟨s,r,rfl⟩
    exact functional_matching_lower hn hm r
  · exact (csInf_le hb (show r.mass ∈ functionalMassSet m n from ⟨s,r,rfl⟩)).trans hr

theorem functionalChargeBudget_nonneg (m n : ℕ) : 0 ≤ functionalChargeBudget m n := by
  rw [← show (charge m n).cost = functionalChargeBudget m n from charge_cost_exact m n]
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

private theorem binomial_prefix_half {m n : ℕ} (hn : n ≤ m) (hm : m ≤ 2*n) :
    (2:ℝ)^m/2 ≤ ∑ k ∈ Finset.range (n+1), (m.choose k:ℝ) := by
  have htot : (∑ k ∈ Finset.range (m+1), (m.choose k:ℝ)) = (2:ℝ)^m := by
    exact_mod_cast Nat.sum_range_choose m
  let S := Finset.range (n+1)
  let T := (Finset.range (m+1))\S
  have hST : S ⊆ Finset.range (m+1) := Finset.range_mono (by omega)
  have hsum : (∑ k ∈ S, (m.choose k:ℝ)) + (∑ k ∈ T, (m.choose k:ℝ)) = (∑ k ∈ Finset.range (m+1), (m.choose k:ℝ)) := by
    rw [add_comm,Finset.sum_sdiff hST]
  have hc : (∑ k ∈ T, (m.choose k:ℝ)) ≤ ∑ k ∈ S, (m.choose k:ℝ) := by
    classical
    have hpinj : Set.InjOn (fun k => m-k) ↑T := by
      intro i hi j hj he
      have h1 := Finset.mem_range.mp (Finset.mem_sdiff.mp hi).1
      have h2 := Finset.mem_range.mp (Finset.mem_sdiff.mp hj).1
      change m-i = m-j at he
      omega
    have hsub : T.image (fun k => m-k) ⊆ S := by
      intro i hi
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨h1,h2⟩ := Finset.mem_sdiff.mp hj
      have h3 := Finset.mem_range.mp h1
      change ¬ j ∈ Finset.range (n+1) at h2
      rw [Finset.mem_range] at h2
      exact Finset.mem_range.mpr (by omega)
    have he : (∑ k ∈ T.image (fun k => m-k), (m.choose k:ℝ)) =
        ∑ k ∈ T, (m.choose k:ℝ) := by
      rw [Finset.sum_image hpinj]
      apply Finset.sum_congr rfl
      intro j hj
      have h1 := Finset.mem_range.mp (Finset.mem_sdiff.mp hj).1
      rw [Nat.choose_symm (by omega : j ≤ m)]
    rw [←he]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  change (∑ k ∈ S, (m.choose k:ℝ)) + ∑ k ∈ T, (m.choose k:ℝ) = _ at hsum
  rw [htot] at hsum
  linarith

private noncomputable def unscaledBinomial (m n j : ℕ) : ℝ :=
  (m.choose j:ℝ)*(n:ℝ)^j*((m-n:ℕ):ℝ)^(m-j)

private theorem unscaled_binomial_recurrence {m n j : ℕ} (hj : j < m) :
    ((j:ℝ)+1)*((m-n:ℕ):ℝ)*unscaledBinomial m n (j+1) =
      ((m-j:ℕ):ℝ)*(n:ℝ)*unscaledBinomial m n j := by
  have he : ((j:ℝ)+1)*(m.choose (j+1):ℝ) = ((m-j:ℕ):ℝ)*(m.choose j:ℝ) := by
    have h1 := Nat.succ_mul_choose_eq (m-1) j
    rw [show (m-1).succ=m by omega] at h1
    have h2 := Nat.choose_mul_succ_eq (m-1) j
    rw [Nat.sub_add_cancel (by omega : 1 ≤ m)] at h2
    have h3 : (j+1)*m.choose (j+1) = (m-j)*m.choose j := by
      calc
        _ = m*(m-1).choose j := (Nat.mul_comm _ _).trans h1.symm
        _ = _ := (Nat.mul_comm _ _).trans (h2.trans (Nat.mul_comm _ _))
    exact_mod_cast h3
  have hd : m-j = m-(j+1)+1 := by omega
  unfold unscaledBinomial
  have hpow : (((m-n:ℕ):ℝ))^(m-j) = (((m-n:ℕ):ℝ))^(m-(j+1))*(((m-n:ℕ):ℝ)) := by
    rw [←pow_succ,←hd]
  rw [pow_succ (n:ℝ),hpow]
  linear_combination he * (((m-n:ℕ):ℝ)*(n:ℝ)^(j+1)*((m-n:ℕ):ℝ)^(m-(j+1)))

private theorem unscaled_mode {m n j : ℕ} (hn : 1 ≤ n) (hm : n < m) (hj : j ≤ m) :
    unscaledBinomial m n j ≤ unscaledBinomial m n n := by
  let f := unscaledBinomial m n
  let d : ℝ := ((m-n:ℕ):ℝ)
  have hd : 0 < d := by dsimp [d]; exact_mod_cast (show 0 < m-n by omega)
  have hd' : d = (m:ℝ)-n := by dsimp [d]; exact Nat.cast_sub hm.le
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  have hnon (k : ℕ) : 0 ≤ f k := by dsimp [f,unscaledBinomial]; positivity
  have hrec (k : ℕ) (hk : k < m) : ((k:ℝ)+1)*d*f (k+1) = ((m:ℝ)-k)*n*f k := by
    have hh := unscaled_binomial_recurrence (m:=m) (n:=n) hk
    rw [Nat.cast_sub hk.le] at hh
    exact hh
  have hleft (k : ℕ) (hk : k < n) : f k ≤ f (k+1) := by
    have hkn : (k:ℝ)+1 ≤ n := by exact_mod_cast hk
    have hcoef : ((k:ℝ)+1)*d ≤ ((m:ℝ)-k)*n := by
      calc
        _ ≤ (n:ℝ)*d := mul_le_mul_of_nonneg_right hkn hd.le
        _ ≤ _ := by rw [mul_comm (n:ℝ) d, hd']; gcongr
    apply le_of_mul_le_mul_left _ (show 0 < ((k:ℝ)+1)*d by positivity)
    rw [hrec _ (hk.trans hm)]
    exact mul_le_mul_of_nonneg_right hcoef (hnon k)
  have hright (k : ℕ) (hk : n ≤ k) (hk' : k < m) : f (k+1) ≤ f k := by
    have hkn : (n:ℝ) ≤ k := by exact_mod_cast hk
    have hcoef : ((m:ℝ)-k)*n ≤ ((k:ℝ)+1)*d := by
      calc
        _ ≤ (n:ℝ)*d := by rw [mul_comm (n:ℝ) d, hd']; gcongr
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hd.le
    apply le_of_mul_le_mul_left _ (show 0 < ((k:ℝ)+1)*d by positivity)
    rw [hrec _ hk']
    exact mul_le_mul_of_nonneg_right hcoef (hnon k)
  by_cases h : j ≤ n
  · have step (p : ℕ) (hp : j+p ≤ n) : f j ≤ f (j+p) := by
      induction p with
      | zero => simp
      | succ p IH => exact (IH (by omega)).trans (hleft (j+p) (by omega))
    have he : j+(n-j) = n := by omega
    simpa only [he] using step (n-j) (by omega)
  · have step (p : ℕ) (hp : n+p ≤ m) : f (n+p) ≤ f n := by
      induction p with
      | zero => simp
      | succ p IH => exact (hright (n+p) (by omega) (by omega)).trans (IH (by omega))
    have he : n+(j-n) = j := by omega
    simpa only [he] using step (j-n) (by omega)

/-- The unscaled binomial weight at n is maximal among the m+1 entries. -/
theorem binomial_at_mean_bounds {m n : ℕ} (hn : 1 ≤ n) (hm : n < m) :
    (m:ℝ)^m/(m+1) ≤ unscaledBinomial m n n ∧ unscaledBinomial m n n ≤ (m:ℝ)^m := by
  classical
  have hsum : (∑ j ∈ Finset.range (m+1), unscaledBinomial m n j) = (m:ℝ)^m := by
    have he : (n:ℝ)+((m-n:ℕ):ℝ) = m := by rw [Nat.cast_sub hm.le]; ring
    rw [←he,add_pow]
    apply Finset.sum_congr rfl
    intro j _
    unfold unscaledBinomial
    ring
  constructor
  · apply (div_le_iff₀ (by positivity : (0:ℝ) < (m:ℝ)+1)).2
    have h := Finset.sum_le_sum (s:=Finset.range (m+1))
      (f:=fun j => unscaledBinomial m n j) (g:=fun _ => unscaledBinomial m n n)
      (fun j hj => unscaled_mode hn hm (by have hh := Finset.mem_range.mp hj; omega))
    rw [hsum] at h
    simp [Finset.sum_const,nsmul_eq_mul] at h
    simpa [mul_comm] using h
  · rw [←hsum]
    exact Finset.single_le_sum (f:=fun j => unscaledBinomial m n j)
      (fun _ _ => by unfold unscaledBinomial; positivity) (Finset.mem_range.mpr (by omega))


noncomputable def functionalRateMass (m n : ℕ) : ℝ :=
  (2:ℝ)^m * ((n:ℝ)^n*((m-n:ℕ):ℝ)^(m-n))/(m:ℝ)^m

/-- A finite multiplicative version of the functional entropy law, with
explicit polynomial slack. -/
theorem functional_rate_sandwich {m n : ℕ} (hn : 4 ≤ n) (hm : n < m) (h2 : m ≤ 2*n) :
    functionalRateMass m n / 2 ≤ optimalFunctionalMass m n ∧
      optimalFunctionalMass m n ≤
        functionalChargeBudget m n*((m:ℝ)+1)*functionalRateMass m n := by
  let S := ∑ k ∈ Finset.range (n+1), (m.choose k:ℝ)
  let E := functionalRateMass m n
  let D := ((m-1).choose n:ℝ)
  let B := (m.choose n:ℝ)
  let C := functionalChargeBudget m n
  have hB : 0 < B := by dsimp [B]; exact_mod_cast Nat.choose_pos hm.le
  have hD : 0 < D := by dsimp [D]; exact_mod_cast Nat.choose_pos (by omega : n ≤ m-1)
  have hM : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hD' : D*(m:ℝ) = B*((m-n:ℕ):ℝ) := by
    dsimp [D,B]
    have he := Nat.choose_mul_succ_eq (m-1) n
    rw [Nat.sub_add_cancel (by omega : 1 ≤ m)] at he
    exact_mod_cast he
  have hDB : D ≤ B := by
    apply le_of_mul_le_mul_right _ hM
    rw [hD']
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.sub_le m n) hB.le
  have hDB' : B ≤ D*(m:ℝ) := by
    rw [hD']
    have hd : (1:ℝ) ≤ ((m-n:ℕ):ℝ) := by exact_mod_cast (by omega : 1 ≤ m-n)
    simpa using mul_le_mul_of_nonneg_left hd hB.le
  obtain ⟨hl,hu⟩ := binomial_at_mean_bounds (m:=m) (n:=n) (by omega) hm
  have hEB : E*B ≤ (2:ℝ)^m := by
    have hh : E*B = (2:ℝ)^m*(unscaledBinomial m n n/(m:ℝ)^m) := by
      unfold E functionalRateMass B unscaledBinomial
      ring
    rw [hh]
    have hp : unscaledBinomial m n n/(m:ℝ)^m ≤ 1 :=
      (div_le_iff₀ (pow_pos hM m)).mpr (by simpa using hu)
    simpa using mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ (2:ℝ)^m)
  have hEB' : (2:ℝ)^m ≤ ((m:ℝ)+1)*E*B := by
    have hh : ((m:ℝ)+1)*E*B = (2:ℝ)^m*((m+1)*unscaledBinomial m n n/(m:ℝ)^m) := by
      unfold E functionalRateMass B unscaledBinomial
      ring
    rw [hh]
    have hp := (div_le_iff₀ (by positivity : (0:ℝ)<(m:ℝ)+1)).mp hl
    have ho : 1 ≤ ((m:ℝ)+1)*unscaledBinomial m n n/(m:ℝ)^m :=
      (le_div_iff₀ (pow_pos hM m)).mpr (by simpa [mul_comm] using hp)
    simpa using mul_le_mul_of_nonneg_left ho (by positivity : 0 ≤ (2:ℝ)^m)
  have hs : S ≤ (2:ℝ)^m := by
    have htot : (∑ k ∈ Finset.range (m+1), (m.choose k:ℝ)) = (2:ℝ)^m := by exact_mod_cast Nat.sum_range_choose m
    rw [←htot]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun _ _ _ => by positivity)
  have hs' : (2:ℝ)^m/2 ≤ S := binomial_prefix_half hm.le h2
  have hb := optimal_functional_sandwich hn hm
  have hi : (m:ℝ)*functionalIntegral (m-n) n = S/D := by
    unfold S D
    exact functional_integral_binomial hm
  have hE : 0 ≤ E := by unfold E functionalRateMass; positivity
  constructor
  · apply le_trans _ hb.1
    rw [hi]
    apply (le_div_iff₀ hD).mpr
    have hh := mul_le_mul_of_nonneg_left hDB (show 0 ≤ E/2 by positivity)
    linarith
  · apply hb.2.trans
    have hi' : functionalIntegral (m-n) n = S/(D*(m:ℝ)) := by
      apply (eq_div_iff (mul_pos hD hM).ne').mpr
      have h := (eq_div_iff hD.ne').mp hi
      linarith only [show functionalIntegral (m-n) n*(D*(m:ℝ)) =
        ((m:ℝ)*functionalIntegral (m-n) n)*D by ring, h]
    rw [hi']
    have hC : 0 ≤ C := functionalChargeBudget_nonneg m n
    have hbound : S/(D*(m:ℝ)) ≤ ((m:ℝ)+1)*E := by
      apply (div_le_iff₀ (mul_pos hD hM)).mpr
      apply (hs.trans hEB').trans
      exact mul_le_mul_of_nonneg_left hDB' (by positivity)
    have hh := mul_le_mul_of_nonneg_left hbound hC
    simpa only [mul_assoc] using hh

end PHP
