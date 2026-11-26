import PHP.GenericWitness
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.DenselyOrdered

namespace PHP
open scoped BigOperators Topology
open Filter Set

noncomputable def scoreEnvelope {s R : ℕ} (B : CalibratedBlock s R) (C : ℕ) (x : ℝ) : ℝ :=
  x^((C-1)*s) * B.polynomial x

private theorem left_increase_of_neg {g : ℝ → ℝ} {d : ℝ}
    (hg : HasDerivAt g d 1) (hd : d < 0) :
    ∃ x : ℝ, 0 < x ∧ x < 1 ∧ g 1 < g x := by
  have hSlope := (hasDerivAt_iff_tendsto_slope.mp hg).eventually (gt_mem_nhds hd)
  have hMono : 𝓝[<] (1 : ℝ) ≤ 𝓝[≠] (1 : ℝ) := by
    apply nhdsWithin_mono
    intro x hx
    exact ne_of_lt hx
  have eSlope := hSlope.filter_mono hMono
  have ePos : ∀ᶠ x : ℝ in 𝓝[<] (1 : ℝ), 0 < x :=
    eventually_nhdsWithin_of_eventually_nhds (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have eLt : ∀ᶠ x : ℝ in 𝓝[<] (1 : ℝ), x < 1 := self_mem_nhdsWithin
  obtain ⟨x,hx₁,hx₂,hx₃⟩ := (ePos.and (eLt.and eSlope)).exists
  refine ⟨x,hx₁,hx₂,?_⟩
  change slope g 1 x < 0 at hx₃
  rw [slope_def_field] at hx₃
  have h := (div_lt_iff_of_neg (sub_neg.mpr hx₂)).mp hx₃
  linarith

theorem score_window {s R : ℕ} (B : CalibratedBlock s R) (C : ℕ)
    (hC : 1 ≤ C) (hs : (C : ℝ)*s < B.expectedSupport) :
    ∃ a b base : ℝ,
      0 < a ∧ a < b ∧ b < 1 ∧ 1 < base ∧
      ∀ x ∈ Set.Icc a b, base ≤ scoreEnvelope B C x := by
  let g := scoreEnvelope B C
  have hg1 : g 1 = 1 := by simp [g,scoreEnvelope]
  have hg : HasDerivAt g ((C : ℝ)*s - B.expectedSupport) 1 := by
    have h := (hasDerivAt_pow ((C-1)*s) (1 : ℝ)).mul B.polynomial_derivative
    have hC' : (((C-1)*s : ℕ) : ℝ) = ((C : ℝ)-1)*s := by
      push_cast [Nat.cast_sub hC]
      rfl
    simp only [one_pow,mul_one,B.polynomial_one,one_mul,hC'] at h
    (convert h using 1; ring)
  obtain ⟨x,hx0,hx1,hx⟩ := left_increase_of_neg hg (sub_neg.mpr hs)
  rw [hg1] at hx
  let base := (1+g x)/2
  have hb : 1 < base := by unfold base; linarith
  have hbg : base < g x := by unfold base; linarith
  have hcont : Continuous g := by unfold g scoreEnvelope CalibratedBlock.polynomial; fun_prop
  have he : {y : ℝ | base < g y} ∈ 𝓝 x :=
    hcont.continuousAt.preimage_mem_nhds (lt_mem_nhds hbg)
  obtain ⟨l,u,⟨hl,hu⟩,hd⟩ := mem_nhds_iff_exists_Ioo_subset.mp he
  let a := (max l 0+x)/2
  let b := (min u 1+x)/2
  have hal : l < a := by
    have h1 := le_max_left l (0 : ℝ)
    have h2 : max l 0 < x := max_lt_iff.mpr ⟨hl,hx0⟩
    unfold a
    linarith
  have hab : a < x := by unfold a; linarith [max_lt_iff.mpr ⟨hl,hx0⟩]
  have hxb : x < b := by unfold b; linarith [lt_min_iff.mpr ⟨hu,hx1⟩]
  have hbu : b < u := by unfold b; linarith [min_le_left u (1 : ℝ)]
  have ha : 0 < a := by unfold a; linarith [le_max_right l (0 : ℝ)]
  have hb1 : b < 1 := by unfold b; linarith [min_le_right u (1 : ℝ)]
  refine ⟨a,b,base,ha,hab.trans hxb,hb1,hb,fun y hy => ?_⟩
  exact le_of_lt (hd ⟨hal.trans_le hy.1,hy.2.trans_lt hbu⟩)

end PHP
