import PHP.FunctionalEntropy
import PHP.FunctionalCubic
import PHP.RowMonotonicity

namespace PHP

theorem functional_optimum_le {m n s : ℕ} (r : Refutation (@Functional m n) s) :
    optimalFunctionalMass m n ≤ r.mass := by
  apply csInf_le
  · refine ⟨1,?_⟩
    rintro _ ⟨s',r',rfl⟩
    exact r'.one_le_mass
  · exact ⟨s,r,rfl⟩

private theorem extendCube_functional {m m' n : ℕ} (e : Fin m ↪ Fin m')
    {c : Cube m n} (h : Functional c) : Functional (extendCube e c) := by
  rcases h with h | ⟨i,j,k,hD,hj,hk⟩
  · exact Or.inl (plain_extendCube e h)
  · exact Or.inr ⟨e i,j,k,hD,by rwa [extendCube_on],by rwa [extendCube_on]⟩

noncomputable def Refutation.addFunctionalRows {m m' n s : ℕ} (e : Fin m ↪ Fin m')
    (r : Refutation (@Functional m n) s) : Refutation (@Functional m' n) s where
  cube j := extendCube e (r.cube j)
  coeff := r.coeff
  legal j := extendCube_functional e (r.legal j)
  identity x := by
    classical
    simpa only [eval,holds_extendCube] using r.identity (restrictBoard e x)

theorem functional_poly_above_two {m n : ℕ} (hn : 1 ≤ n) (h : 2*n ≤ m) :
    optimalFunctionalMass m n ≤ 16*(n:ℝ)^3 := by
  obtain ⟨s,r,hr⟩ := functional_cubic n hn
  exact (functional_optimum_le (r.addFunctionalRows (Fin.castLEEmb h))).trans hr

/-- Finite critical-window law, retaining the exact coefficients before
taking any limit. The log-mass slack is at most a polynomial's logarithm. -/
theorem functional_window_finite {m n : ℕ} (hn : 4 ≤ n) (hm : n < m) (h2 : m ≤ 2*n) :
    let k : ℝ := (2*n:ℕ)- (m:ℝ)
    k^2/(2*(m:ℝ))-Real.log 2 ≤ Real.log (optimalFunctionalMass m n) ∧
    Real.log (optimalFunctionalMass m n) ≤
      (m:ℝ)*k^2/(8*(n:ℝ)*((m:ℝ)-n)) +
        Real.log (functionalChargeBudget m n*((m:ℝ)+1)) := by
  dsimp only
  let p : ℝ := (n:ℝ)/m
  let k : ℝ := (2*n:ℕ)-(m:ℝ)
  have hM : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hN : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hmn : (n:ℝ) < m := by exact_mod_cast hm
  have h2R : (m:ℝ) ≤ 2*(n:ℝ) := by exact_mod_cast h2
  have hp : 1/2 ≤ p := (le_div_iff₀ hM).mpr (by linarith)
  have hp' : p < 1 := (div_lt_iff₀ hM).mpr (by linarith)
  have hpk : p-1/2 = k/(2*(m:ℝ)) := by unfold p k; push_cast; field_simp
  have hq : 1-p = ((m:ℝ)-n)/(m:ℝ) := by unfold p; field_simp
  obtain ⟨hl,hu⟩ := entropy_quadratic_squeeze hp hp'
  have hlow : k^2/(2*(m:ℝ)) ≤ (m:ℝ)*binaryEntropyGap p := by
    have h := mul_le_mul_of_nonneg_left hl hM.le
    rw [hpk] at h
    convert h using 1
    field_simp
  have hupp : (m:ℝ)*binaryEntropyGap p ≤ (m:ℝ)*k^2/(8*(n:ℝ)*((m:ℝ)-n)) := by
    have h := mul_le_mul_of_nonneg_left hu hM.le
    rw [hpk,hq] at h
    unfold p at h
    convert h using 1
    have hd : (m:ℝ)-n ≠ 0 := by linarith
    field_simp [hM.ne',hN.ne',hd]
    <;> ring
  obtain ⟨hL,hU⟩ := functional_entropy_bounds hn hm h2
  exact ⟨(sub_le_sub_right hlow _).trans hL,hU.trans (add_le_add_right hupp _)⟩

private theorem functional_slack_le {m n : ℕ} (hn : 1 ≤ n) (hm : n < m) (h2 : m ≤ 2*n) :
    functionalChargeBudget m n*((m:ℝ)+1) ≤ 24*(n:ℝ)^4 := by
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hmn : (n:ℝ) < m := by exact_mod_cast hm
  have hmR : (m:ℝ) ≤ 2*(n:ℝ) := by exact_mod_cast h2
  have hm0 : (0:ℝ) ≤ m := by positivity
  have hn0 : (0:ℝ) ≤ n := by positivity
  have hm1 : (0:ℝ) ≤ (m:ℝ)-1 := by linarith
  have hn1 : (0:ℝ) ≤ (n:ℝ)-1 := by linarith
  have hm_sq : (m:ℝ)^2 ≤ (2*(n:ℝ))^2 := pow_le_pow_left₀ hm0 hmR _
  have hpow : (n:ℝ) ≤ (n:ℝ)^3 := by
    have hh := one_le_pow₀ (n:=2) hnR
    nlinarith [mul_le_mul_of_nonneg_right hh hn0]
  have hb : functionalChargeBudget m n ≤ 8*(n:ℝ)^3 := by
    unfold functionalChargeBudget
    nlinarith [mul_le_mul_of_nonneg_left hm_sq hn0,
      mul_le_mul_of_nonneg_right hmR (sq_nonneg (n:ℝ)),mul_nonneg hm0 hn0]
  have hM : (m:ℝ)+1 ≤ 3*(n:ℝ) := by linarith
  exact (mul_le_mul hb hM (by positivity) (by positivity)).trans_eq (by ring)

theorem functional_window_simple {m n : ℕ} (hn : 4 ≤ n) (hm : n < m) (h2 : m ≤ 2*n) :
    let k : ℝ := (2*n:ℕ) - (m:ℝ)
    k^2/(4*(n:ℝ))-Real.log 2 ≤ Real.log (optimalFunctionalMass m n) ∧
    (k ≤ (n:ℝ)/2 →
      Real.log (optimalFunctionalMass m n) ≤ k^2/(2*(n:ℝ)) + Real.log 24+4*Real.log n) := by
  dsimp only
  let k : ℝ := (2*n:ℕ)-(m:ℝ)
  have hM : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hN : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hmn : (n:ℝ) < m := by exact_mod_cast hm
  have h2R : (m:ℝ) ≤ 2*(n:ℝ) := by exact_mod_cast h2
  obtain ⟨hl,hu⟩ := functional_window_finite hn hm h2
  refine ⟨(sub_le_sub_right (div_le_div_of_nonneg_left (sq_nonneg k) (by positivity) (by linarith)) _).trans hl,?_⟩
  intro hk
  have hk' : (3/2:ℝ)*(n:ℝ) ≤ m := by
    change k ≤ (n:ℝ)/2 at hk
    dsimp [k] at hk
    push_cast at hk
    linarith
  have hpow : (m:ℝ)*k^2/(8*(n:ℝ)*((m:ℝ)-n)) ≤ k^2/(2*(n:ℝ)) := by
    have hD : 0 < 8*(n:ℝ)*((m:ℝ)-n) := mul_pos (mul_pos (by norm_num) hN) (sub_pos.mpr hmn)
    apply (div_le_iff₀ hD).mpr
    have hh : k^2/(2*(n:ℝ))*(8*(n:ℝ)*((m:ℝ)-n)) = k^2*(4*((m:ℝ)-n)) := by field_simp; ring
    rw [hh,mul_comm (m:ℝ)]
    exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg k)
  have hR : 0 < functionalChargeBudget m n*((m:ℝ)+1) := by
    have hm0 : (1:ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
    have hn0 : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have hms : 0 ≤ (m:ℝ)-1 := sub_nonneg.mpr hm0
    have hns : 0 ≤ (n:ℝ)-1 := sub_nonneg.mpr hn0
    unfold functionalChargeBudget
    positivity
  have hlog := Real.log_le_log hR (functional_slack_le (by omega) hm h2)
  rw [Real.log_mul (by norm_num : (24:ℝ) ≠ 0) (by positivity : (n:ℝ)^4 ≠ 0),Real.log_pow] at hlog
  norm_num at hlog
  change _ ≤ k^2/(2*(n:ℝ)) + _ + _ 
  change _ ≤ (m:ℝ)*k^2/(8*(n:ℝ)*((m:ℝ)-n)) + _ at hu
  linarith

end PHP
