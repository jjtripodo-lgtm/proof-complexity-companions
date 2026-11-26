import PHP.MatchingCalibration
import PHP.GenericOccupancy

namespace PHP
open Finset
open scoped BigOperators

theorem matchingSample_omissions {m n : ℕ} (e : Fin n ↪ Fin m)
    (σ : Equiv.Perm (Fin m)) (J : Finset (Fin n)) :
    omissions (matchingSample e σ J) = ((m-J.card:ℕ):ℝ) := by
  classical
  let E := e.trans σ.toEmbedding
  have he : GenericLayout.usedRows (matchingSample e σ J) = J.map E := by
    ext i
    rw [GenericLayout.mem_usedRows,Finset.mem_map]
    constructor
    · rintro ⟨j,hj⟩
      by_cases h : j ∈ J
      · exact ⟨j,h,by simpa [matchingSample,h,E] using hj⟩
      · simp [matchingSample,h] at hj
    · rintro ⟨j,hj,rfl⟩
      exact ⟨j,by simp [matchingSample,hj,E]⟩
  rw [GenericLayout.omissions_eq_cast]
  simp [GenericLayout.missingNat,he]

theorem matchingCoeff_closed {n : ℕ} (J : Finset (Fin n)) :
    matchingCoeff J = (2:ℝ)^J.card * (-1:ℝ)^(n-J.card) := by
  rw [matchingCoeff,Finset.prod_ite]
  have h : (Finset.univ.filter (fun j => j ∈ J)) = J := by ext j; simp
  have hc : (Finset.univ.filter (fun j => j ∉ J)) = Jᶜ := by ext j; simp
  rw [h,hc]
  simp [Finset.card_compl]

private theorem matching_poly (m n : ℕ) (hm : n ≤ m) (x : ℝ) :
    (∑ J : Finset (Fin n), matchingCoeff J * x^(m-J.card)) =
      x^(m-n)*(2-x)^n := by
  classical
  have hx : (∑ J : Finset (Fin n), (2:ℝ)^J.card * (-x)^(n-J.card)) = (2-x)^n := by
    have h := (Fintype.prod_add (fun _ : Fin n => (2:ℝ)) (fun _ => -x)).symm
    simpa [sub_eq_add_neg,Finset.card_compl] using h
  rw [←hx,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J _
  have hJ : J.card ≤ n := by simpa using J.card_le_univ
  have he : m-J.card = (m-n)+(n-J.card) := by omega
  rw [matchingCoeff_closed,he,pow_add,show -x = (-1:ℝ)*x by ring,mul_pow]
  ring

private theorem matching_integral_mean {m n : ℕ} (hm : n ≤ m) :
    (∑ J : Finset (Fin n), matchingCoeff J/(1+(((m-J.card:ℕ):ℝ)))) =
      functionalIntegral (m+1-n) n := by
  have h (J : Finset (Fin n)) : Continuous (fun x : ℝ => matchingCoeff J*x^(m-J.card)) := by fun_prop
  calc
    _ = ∑ J : Finset (Fin n), ∫ x : ℝ in 0..1, matchingCoeff J*x^(m-J.card) := by
      apply Finset.sum_congr rfl
      intro J _
      rw [intervalIntegral.integral_const_mul, integral_unit_powNat]
      rw [add_comm (1:ℝ),div_eq_mul_inv]
    _ = ∫ x : ℝ in 0..1, ∑ J : Finset (Fin n), matchingCoeff J*x^(m-J.card) :=
      (intervalIntegral.integral_finset_sum (fun J _ => (h J).intervalIntegrable _ _)).symm
    _ = functionalIntegral (m+1-n) n := by
      simp_rw [matching_poly m n hm]
      have hh : m+1-n-1 = m-n := by omega
      simp [functionalIntegral,hh]

/-- The lifted matching law has exactly the mass of the paper's integral. -/
theorem matching_lift_mass {m n : ℕ} (hm : n ≤ m) (e : Fin n ↪ Fin m) :
    (∑ a : Word (m+1) n, liftSymmetric (matchingLaw e) a) =
      ((m+1:ℕ):ℝ)*functionalIntegral (m+1-n) n := by
  rw [lift_mass_by_omissions (matchingLaw e) (matching_rowInvariant e)]
  congr 1
  have h := matching_moment e (fun a => (1+omissions a)⁻¹)
  simp_rw [← div_eq_mul_inv,matchingSample_omissions] at h
  rw [h]
  simp [Finset.sum_const,nsmul_eq_mul,Fintype.card_perm,Nat.factorial_ne_zero,matching_integral_mean hm]

theorem matching_insert {m n : ℕ} {a : Word m n} (h : IsMatching a) (i : Fin (m+1)) :
    IsMatching (a.insertRow i) := by
  intro j k r hj hk
  cases hja : a j with
  | none => simp [Word.insertRow,hja] at hj
  | some p =>
    cases hka : a k with
    | none => simp [Word.insertRow,hka] at hk
    | some q =>
      have hp : i.succAbove p = r := by simpa [Word.insertRow,hja] using hj
      have hq : i.succAbove q = r := by simpa [Word.insertRow,hka] using hk
      have he := Fin.succAbove_right_injective (hp.trans hq.symm)
      exact h j k p hja (he.symm ▸ hka)

theorem matching_lift_support {m n : ℕ} (e : Fin n ↪ Fin m) {a : Word (m+1) n}
    (h : ¬ IsMatching a) : liftSymmetric (matchingLaw e) a = 0 := by
  classical
  unfold liftSymmetric
  split
  · rename_i hv
    let i := Classical.choose hv
    let b := Classical.choose (Classical.choose_spec hv)
    have hb : b.insertRow i = a := Classical.choose_spec (Classical.choose_spec hv)
    exact matchingLaw_support e (fun hm => h (hb ▸ matching_insert hm i))
  · rfl

theorem matching_row_collision_not_holds {m n : ℕ} {a : Word m n} (h : IsMatching a)
    {C : Cube m n} (hc : RowCollision C) : ¬ Holds C a.board := by
  intro he
  obtain ⟨i,j,k,hne,hj,hk⟩ := hc
  exact hne (h j k i (of_decide_eq_true (he _ _ hj)) (of_decide_eq_true (he _ _ hk)))

private theorem matching_empty_comparison {m n : ℕ} (e : Fin n ↪ Fin m)
    (C : Cube (m+1) n) {i : Fin (m+1)} (he : ∀ j, C (i,j) = some false) :
    (∑ a : Word (m+1) n, liftSymmetric (matchingLaw e) a * eval C a.board) =
    ∑ a : Word m n, matchingLaw e a * eval (pullRow i C) a.board := by
  classical
  let f : Word (m+1) n → ℝ := fun a => liftSymmetric (matchingLaw e) a*eval C a.board
  have hz (a : Word (m+1) n) (ha : ¬ Omits a i) : f a = 0 := by
    have hh : ¬ Holds C a.board := fun h => ha (empty_row_forces_absence a he h)
    simp [f,eval,hh]
  calc
    _ = ∑ a : Word (m+1) n, if Omits a i then f a else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : Omits a i <;> simp [ha,f,hz a]
    _ = ∑ b : Word m n, f (b.insertRow i) := sum_insertRow i f
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      unfold f
      rw [liftSymmetric_insert (matching_rowInvariant e)]
      simp [eval, holds_insertRow i a C he]

/-- The lower half of the functional matching sandwich, against every
coefficient-mass refutation on the whole Boolean board. -/
theorem functional_matching_lower {m n s : ℕ} (hn : 4 ≤ n) (hm : n < m)
    (r : Refutation (@Functional m n) s) : (m:ℝ)*functionalIntegral (m-n) n ≤ r.mass := by
  rcases m with _ | m
  · omega
  have hnm : n ≤ m := by omega
  let e : Fin n ↪ Fin m := Fin.castLEEmb hnm
  rw [← matching_lift_mass hnm e]
  apply dual_bound_on r Word.board (liftSymmetric (matchingLaw e))
  intro C hC
  rcases hC with (he | hc) | hr
  · obtain ⟨i,hi⟩ := he
    rw [matching_empty_comparison e C hi]
    exact matching_test_bound hn hnm e _
  · simp [eval,column_collision_not_holds _ hc]
  · have hz (a : Word (m+1) n) :
        liftSymmetric (matchingLaw e) a * eval C a.board = 0 := by
      by_cases h : IsMatching a
      · simp [eval,matching_row_collision_not_holds h hr]
      · rw [matching_lift_support e h,zero_mul]
    simp [hz]

end PHP
