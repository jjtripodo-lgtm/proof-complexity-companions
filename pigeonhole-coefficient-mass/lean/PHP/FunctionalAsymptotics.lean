import PHP.FunctionalThreshold
import Mathlib.Algebra.Order.Floor.Semiring

namespace PHP
open Filter
open scoped Topology

private theorem charge_cap {m n : ℕ} {D : ℝ} (hD : 1 ≤ D) (hn : 1 ≤ n)
    (hnm : n < m) (hm : (m:ℝ) ≤ D*(n:ℝ)) :
    functionalChargeBudget m n ≤ (D+D^2/2+D/2)*(n:ℝ)^3 := by
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hn0 : (0:ℝ) ≤ n := by positivity
  have hm0 : (0:ℝ) ≤ m := by positivity
  have hN : (n:ℝ) ≤ (n:ℝ)^3 := by
    have h := one_le_pow₀ (n:=2) hnR
    nlinarith [mul_le_mul_of_nonneg_right h hn0]
  have hM2 := pow_le_pow_left₀ hm0 hm 2
  have hM3 := mul_le_mul_of_nonneg_left hM2 hn0
  have hM4 := mul_le_mul_of_nonneg_right hm (sq_nonneg (n:ℝ))
  have hh := mul_le_mul_of_nonneg_left hN (show 0 ≤ D by linarith)
  unfold functionalChargeBudget
  nlinarith [mul_nonneg hm0 hn0]

theorem functional_optimum_row_mono {m m' n : ℕ} (h : m ≤ m') (hm : n < m) :
    optimalFunctionalMass m' n ≤ optimalFunctionalMass m n := by
  obtain ⟨s,r,_⟩ := functional_general_upper hm
  apply le_csInf (show (functionalMassSet m n).Nonempty from ⟨r.mass,s,r,rfl⟩)
  rintro _ ⟨s',r',rfl⟩
  exact functional_optimum_le (r'.addFunctionalRows (Fin.castLEEmb h))

theorem optimal_functional_quadratic_lower {m n : ℕ} (hn : 1 ≤ n) (hm : n < m) :
    (n:ℝ)^2 ≤ optimalFunctionalMass m n := by
  obtain ⟨s,r,_⟩ := functional_general_upper hm
  apply le_csInf (show (functionalMassSet m n).Nonempty from ⟨r.mass,s,r,rfl⟩)
  rintro _ ⟨s',r',rfl⟩
  exact onehot_lower (by omega : 2 ≤ m) hn r'

/-- Above every fixed positive surplus past the 2:1 ratio, the optimal
functional coefficient mass has quadratic growth, even if m is enormous. -/
theorem functional_above_two_quadratic (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {m n : ℕ}, 1 ≤ n → (2+δ)*(n:ℝ) ≤ (m:ℝ) →
      (n:ℝ)^2 ≤ optimalFunctionalMass m n ∧ optimalFunctionalMass m n ≤ C*(n:ℝ)^2 := by
  let D := δ+3
  let K := D+D^2/2+D/2
  have hD : 1 ≤ D := by dsimp [D]; linarith
  have hDP : 0 < D := zero_lt_one.trans_le hD
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K/δ,div_pos hK hδ,?_⟩
  intro m n hn hmn
  let E := ⌈δ*(n:ℝ)⌉₊
  let M := 2*n+E
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hIn : δ*(n:ℝ) ≤ (E:ℝ) := Nat.le_ceil _
  have hE : 0 < E := by
    have hE : 0 < (E:ℝ) := (mul_pos hδ hnR).trans_le hIn
    exact_mod_cast hE
  have hM : M ≤ m := by
    have h := Nat.ceil_le.mpr (show δ*(n:ℝ) ≤ ((m-2*n:ℕ):ℝ) by
      have he : 2*n ≤ m := by
        exact_mod_cast (show (2:ℝ)*(n:ℝ) ≤ m by nlinarith [mul_nonneg hδ.le hnR.le])
      rw [Nat.cast_sub he]
      push_cast
      linarith)
    change E ≤ m-2*n at h
    unfold M
    omega
  have hceil : (E:ℝ) < δ*(n:ℝ)+1 := Nat.ceil_lt_add_one (mul_nonneg hδ.le hnR.le)
  have hMD : (M:ℝ) ≤ D*(n:ℝ) := by
    unfold M D
    push_cast
    nlinarith
  have hM2 : 2*n < M := by unfold M; omega
  have hsurplus : δ*(n:ℝ) ≤ (M:ℝ)-2*(n:ℝ) := by
    unfold M
    push_cast
    linarith
  refine ⟨optimal_functional_quadratic_lower hn (by omega),?_⟩
  apply (functional_optimum_row_mono hM (by omega)).trans
  apply (optimal_functional_surplus_upper hM2).trans
  have hcap := charge_cap hD hn (by omega : n < M) hMD
  change functionalChargeBudget M n ≤ K*(n:ℝ)^3 at hcap
  have hδN := mul_pos hδ hnR
  have hne := hδN.trans_le hsurplus
  calc
    _ ≤ functionalChargeBudget M n/(δ*(n:ℝ)) :=
      div_le_div_of_nonneg_left (functionalChargeBudget_nonneg _ _) hδN hsurplus
    _ ≤ (K*(n:ℝ)^3)/(δ*(n:ℝ)) := div_le_div_of_nonneg_right hcap hδN.le
    _ = _ := by field_simp

private theorem functional_log_slack {m n : ℕ} (hn : 4 ≤ n) (hm : n < m) (h2 : m ≤ 2*n) :
    Real.log (functionalChargeBudget m n*((m:ℝ)+1)) ≤ Real.log 24+4*Real.log n := by
  have hnR : 1 ≤ (n:ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hmR : 1 ≤ (m:ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
  have h0 : 0 < (n:ℝ) := by linarith
  have h1 : 0 ≤ (n:ℝ)-1 := sub_nonneg.mpr hnR
  have h2' : 0 ≤ (m:ℝ)-1 := sub_nonneg.mpr hmR
  have hm2 : (m:ℝ) ≤ 2*(n:ℝ) := by exact_mod_cast h2
  have hpos : 0 < functionalChargeBudget m n*((m:ℝ)+1) := by
    unfold functionalChargeBudget
    positivity
  have hcap := charge_cap (by norm_num : (1:ℝ) ≤ 2) (by omega : 1 ≤ n) hm hm2
  have hA : functionalChargeBudget m n ≤ 8*(n:ℝ)^3 := by norm_num at hcap; nlinarith
  have hM : (m:ℝ)+1 ≤ 3*(n:ℝ) := by linarith
  have hB := mul_le_mul hA hM (show 0 ≤ (m:ℝ)+1 by positivity) (show 0 ≤ 8*(n:ℝ)^3 by positivity)
  have h := Real.log_le_log hpos (hB.trans_eq (show 8*(n:ℝ)^3*(3*(n:ℝ)) = 24*(n:ℝ)^4 by ring))
  rw [Real.log_mul (by norm_num : (24:ℝ) ≠ 0) (pow_ne_zero _ h0.ne'),Real.log_pow] at h
  exact h

/-- Exact functional rate for every fixed ratio strictly between one and two. -/
theorem functional_fixed_ratio_limit (m n : ℕ → ℕ) {c : ℝ} (hc : 1 < c) (hc' : c < 2)
    (hn : Tendsto n atTop atTop)
    (hr : Tendsto (fun i => (m i:ℝ)/(n i:ℝ)) atTop (𝓝 c)) :
    Tendsto (fun i => Real.log (optimalFunctionalMass (m i) (n i))/(n i:ℝ)) atTop
      (𝓝 (c*binaryEntropyGap (1/c))) := by
  have hc0 : 0 < c := by linarith
  have hP0 : 0 < 1/c := by positivity
  have hP1 : 1/c < 1 := (div_lt_iff₀ hc0).mpr (by linarith)
  have hp : Tendsto (fun i => (n i:ℝ)/(m i:ℝ)) atTop (𝓝 (1/c)) := by
    simpa only [inv_div,one_div] using hr.inv₀ hc0.ne'
  have hCont : ContinuousAt binaryEntropyGap (1/c) := by
    unfold binaryEntropyGap
    have h₁ := (Real.hasDerivAt_log hP0.ne').continuousAt
    have h₂ := ((Real.hasDerivAt_log (show 1-1/c ≠ 0 by linarith)).comp _
      ((hasDerivAt_id (1/c)).const_sub 1)).continuousAt
    exact (continuousAt_const.add (continuousAt_id.mul h₁)).add
      ((continuousAt_const.sub continuousAt_id).mul h₂)
  have hCore := hr.mul (hCont.tendsto.comp hp)
  have hN := hn.eventually_ge_atTop 4
  have hL := hr.eventually (eventually_gt_nhds hc)
  have hU := hr.eventually (eventually_lt_nhds hc')
  have hcast : Tendsto (fun i => (n i:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hn
  have hi : Tendsto (fun i => (n i:ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hcast
  have he : Tendsto (fun i => Real.log (n i:ℝ)/(n i:ℝ)) atTop (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => Real.log x/x) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    exact h.comp hcast
  have hbottom : Tendsto (fun i => (m i:ℝ)/(n i:ℝ)*binaryEntropyGap ((n i:ℝ)/(m i:ℝ)) -
      Real.log 2*(n i:ℝ)⁻¹) atTop (𝓝 (c*binaryEntropyGap (1/c))) := by
    simpa using hCore.sub (hi.const_mul (Real.log 2))
  have htop : Tendsto (fun i => (m i:ℝ)/(n i:ℝ)*binaryEntropyGap ((n i:ℝ)/(m i:ℝ)) +
      Real.log 24*(n i:ℝ)⁻¹ + 4*(Real.log (n i:ℝ)/(n i:ℝ))) atTop
      (𝓝 (c*binaryEntropyGap (1/c))) := by
    simpa using (hCore.add (hi.const_mul (Real.log 24))).add (he.const_mul 4)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hbottom htop
  · filter_upwards [hN,hL,hU] with i hi hli hui
    have hnR : 0 < (n i:ℝ) := by exact_mod_cast (show 0 < n i by omega)
    have hmn : n i < m i := by
      exact_mod_cast (show (n i:ℝ) < m i from by simpa using (lt_div_iff₀ hnR).mp hli)
    have h2n : m i ≤ 2*n i := by
      exact_mod_cast (show (m i:ℝ) ≤ 2*(n i:ℝ) from (div_lt_iff₀ hnR).mp hui |>.le)
    have h := div_le_div_of_nonneg_right (functional_entropy_bounds hi hmn h2n).1 hnR.le
    convert h using 1
    ring
  · filter_upwards [hN,hL,hU] with i hi hli hui
    have hnR : 0 < (n i:ℝ) := by exact_mod_cast (show 0 < n i by omega)
    have hmn : n i < m i := by
      exact_mod_cast (show (n i:ℝ) < m i from by simpa using (lt_div_iff₀ hnR).mp hli)
    have h2n : m i ≤ 2*n i := by
      exact_mod_cast (show (m i:ℝ) ≤ 2*(n i:ℝ) from (div_lt_iff₀ hnR).mp hui |>.le)
    have h := div_le_div_of_nonneg_right
      ((functional_entropy_bounds hi hmn h2n).2.trans (add_le_add_left (functional_log_slack hi hmn h2n) _)) hnR.le
    convert h using 1
    ring


theorem functional_fixed_ratio_rate_formula {c : ℝ} (hc : 1 < c) :
    c*binaryEntropyGap (1/c) =
      c*Real.log 2-c*Real.log c+(c-1)*Real.log (c-1) := by
  have hc0 : 0 < c := by linarith
  have hd : 0 < c-1 := by linarith
  have he : 1-1/c=(c-1)/c := by field_simp
  unfold binaryEntropyGap
  rw [he,Real.log_div (by norm_num : (1:ℝ) ≠ 0) hc0.ne',Real.log_one,
    Real.log_div hd.ne' hc0.ne']
  field_simp
  <;> ring

/-- In the moderate lower-side window the logarithmic rate has exact
1/4 coefficient, not just order k²/n. The hypotheses are equivalent
to sqrt(n log n) ≪ k ≪ n with a positive eventual gap. -/
theorem functional_moderate_gap_limit (m n : ℕ → ℕ)
    (hn : Tendsto n atTop atTop)
    (hm : ∀ᶠ i in atTop, n i < m i ∧ m i < 2*n i)
    (hsmall : Tendsto (fun i => ((2*n i-m i:ℕ):ℝ)/(n i:ℝ)) atTop (𝓝 0))
    (hlarge : Tendsto (fun i =>
      ((n i:ℝ)*Real.log (n i:ℝ))/(((2*n i-m i:ℕ):ℝ)^2)) atTop (𝓝 0)) :
    Tendsto (fun i => ((n i:ℝ)/(((2*n i-m i:ℕ):ℝ)^2))*
      Real.log (optimalFunctionalMass (m i) (n i))) atTop (𝓝 (1/4)) := by
  let k : ℕ → ℝ := fun i => ((2*n i-m i:ℕ):ℝ)
  let u : ℕ → ℝ := fun i => (m i:ℝ)/(n i:ℝ)
  let e : ℕ → ℝ := fun i => (n i:ℝ)/(k i)^2
  have hN := hn.eventually_ge_atTop 4
  have hLog := (Real.tendsto_log_atTop.comp
    (show Tendsto (fun i => (n i:ℝ)) atTop atTop from tendsto_natCast_atTop_atTop.comp hn)).eventually_ge_atTop 1
  have heq : (fun i => 2-k i/(n i:ℝ)) =ᶠ[atTop] u := by
    filter_upwards [hN,hm] with i hN hm
    have hn0 : 0 < (n i:ℝ) := by exact_mod_cast (show 0<n i by omega)
    unfold u k
    rw [Nat.cast_sub hm.2.le]
    push_cast
    field_simp
    ring
  have hU : Tendsto u atTop (𝓝 2) := by
    have h := (tendsto_const_nhds (x:=(2:ℝ))).sub hsmall
    apply Tendsto.congr' heq
    simpa using h
  have hE : Tendsto e atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => by unfold e; positivity) _ hlarge
    filter_upwards [hLog] with i hi
    unfold e k
    exact div_le_div_of_nonneg_right
      (le_mul_of_one_le_right (by positivity) hi) (by positivity)
  have hK : Tendsto (fun i => ((n i:ℝ)*Real.log (n i:ℝ))/(k i)^2) atTop (𝓝 0) := hlarge
  have hLower : Tendsto (fun i => 1/(2*u i)-Real.log 2*e i) atTop (𝓝 (1/4)) := by
    have h := (tendsto_const_nhds (x:=(1:ℝ))).div (hU.const_mul 2) (by norm_num)
    have j := h.sub (hE.const_mul (Real.log 2))
    change Tendsto (fun i => 1/(2*u i)-Real.log 2*e i) atTop (𝓝 ((1:ℝ)/(2*2)-Real.log 2*0)) at j
    simpa only [mul_zero,sub_zero,show (1:ℝ)/(2*2)=1/4 by norm_num] using j
  have hUpper : Tendsto (fun i => u i/(8*(u i-1))+Real.log 24*e i +
      4*((n i:ℝ)*Real.log (n i:ℝ)/(k i)^2)) atTop (𝓝 (1/4)) := by
    have h := hU.div ((hU.sub_const 1).const_mul 8) (by norm_num)
    have j := (h.add (hE.const_mul (Real.log 24))).add (hK.const_mul 4)
    norm_num at j ⊢
    exact j
  change Tendsto (fun i => e i*Real.log (optimalFunctionalMass (m i) (n i))) atTop (𝓝 (1/4))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hLower hUpper
  · filter_upwards [hN,hm] with i hN hm
    have hn0 : 0 < (n i:ℝ) := by exact_mod_cast (show 0<n i by omega)
    have hm0 : 0 < (m i:ℝ) := by exact_mod_cast (show 0<m i by omega)
    have hk0 : 0 < k i := by unfold k; exact_mod_cast (show 0 < 2*n i-m i by omega)
    have hk : k i = ((2*n i:ℕ):ℝ)-(m i:ℝ) := Nat.cast_sub hm.2.le
    have hl := (functional_window_finite hN hm.1 hm.2.le).1
    rw [←hk] at hl
    have he := mul_le_mul_of_nonneg_left hl (show 0 ≤ e i by unfold e; positivity)
    have ht : e i*((k i)^2/(2*(m i:ℝ))-Real.log 2) = 1/(2*u i)-Real.log 2*e i := by
      unfold e u
      field_simp [hk0.ne', hn0.ne', hm0.ne']
      <;> ring
    exact ht ▸ he
  · filter_upwards [hN,hm] with i hN hm
    have hn0 : 0 < (n i:ℝ) := by exact_mod_cast (show 0<n i by omega)
    have hm0 : 0 < (m i:ℝ) := by exact_mod_cast (show 0<m i by omega)
    have hdm : 0 < (m i:ℝ)-(n i:ℝ) := sub_pos.mpr (by exact_mod_cast hm.1)
    have hk0 : 0 < k i := by unfold k; exact_mod_cast (show 0 < 2*n i-m i by omega)
    have hk : k i = ((2*n i:ℕ):ℝ)-(m i:ℝ) := Nat.cast_sub hm.2.le
    have hl := (functional_window_finite hN hm.1 hm.2.le).2
    rw [←hk] at hl
    have hSlack := functional_log_slack hN hm.1 hm.2.le
    have hu := hl.trans (add_le_add_left hSlack _)
    have he := mul_le_mul_of_nonneg_left hu (show 0 ≤ e i by unfold e; positivity)
    have ht : e i*((m i:ℝ)*(k i)^2/(8*(n i:ℝ)*((m i:ℝ)-(n i:ℝ))) +
      (Real.log 24+4*Real.log (n i:ℝ))) =
        u i/(8*(u i-1))+Real.log 24*e i+4*((n i:ℝ)*Real.log (n i:ℝ)/(k i)^2) := by
      have hr : u i-1 = ((m i:ℝ)-(n i:ℝ))/(n i:ℝ) := by unfold u; field_simp
      rw [hr]
      unfold e u
      field_simp [hk0.ne',hn0.ne',hdm.ne']
      <;> ring
    exact he.trans_eq ht

end PHP
