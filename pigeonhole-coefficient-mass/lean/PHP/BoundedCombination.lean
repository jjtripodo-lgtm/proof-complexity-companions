import PHP.Combination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace PHP

open scoped BigOperators

abbrev Unlimited {m n : ℕ} (_ : Cube m n) : Prop := True

def BoundedCombination {m n : ℕ} (A : Cube m n → Prop)
    (f : Board m n → ℝ) (B : ℝ) : Prop :=
  ∃ (I : Type) (inst : Fintype I) (E : Combination m n I),
    E.legal A ∧ (∀ x, @Combination.value m n I inst E x = f x) ∧
      @Combination.cost m n I inst E ≤ B

namespace BoundedCombination
variable {m n : ℕ} {A A' : Cube m n → Prop}
variable {f g : Board m n → ℝ} {B C : ℝ}

theorem of_eq (h : BoundedCombination A f B) (he : ∀ x, f x = g x) :
    BoundedCombination A g B := by
  obtain ⟨I,inst,E,hA,hv,hc⟩ := h
  exact ⟨I,inst,E,hA,fun x => (hv x).trans (he x),hc⟩

theorem cost_mono (h : BoundedCombination A f B) (he : B ≤ C) :
    BoundedCombination A f C := by
  obtain ⟨I,inst,E,hA,hv,hc⟩ := h
  exact ⟨I,inst,E,hA,hv,hc.trans he⟩

theorem legal_mono (h : BoundedCombination A f B) (he : ∀ c, A c → A' c) :
    BoundedCombination A' f B := by
  obtain ⟨I,inst,E,hA,hv,hc⟩ := h
  exact ⟨I,inst,E,fun i hi => he _ (hA i hi),hv,hc⟩

theorem cost_nonneg (h : BoundedCombination A f B) : 0 ≤ B := by
  obtain ⟨I,inst,E,hA,hv,hc⟩ := h
  exact (Finset.sum_nonneg fun _ _ => abs_nonneg _).trans hc

theorem atom (c : Cube m n) (h : A c) :
    BoundedCombination A (fun x => eval c x) 1 := by
  let E : Combination m n Unit := ⟨fun _ => c,fun _ => 1⟩
  refine ⟨Unit,inferInstance,E,fun _ _ => h,fun x => ?_,?_⟩
  · simp [Combination.value,E]
  · simp [Combination.cost,E]

theorem zero (A : Cube m n → Prop) : BoundedCombination A (fun _ => 0) 0 := by
  let E : Combination m n Unit := ⟨fun _ _ => none,fun _ => 0⟩
  refine ⟨Unit,inferInstance,E,fun _ h => False.elim (h rfl),fun x => ?_,?_⟩
  · simp [Combination.value,E]
  · simp [Combination.cost,E]

theorem one : BoundedCombination (@Unlimited m n) (fun _ => 1) 1 := by
  classical
  apply (atom (fun _ => none) trivial).of_eq
  intro x
  have h : Holds (fun _ : Cell m n => none) x := by simp [Holds]
  simp [eval,h]

theorem add (h : BoundedCombination A f B) (h' : BoundedCombination A g C) :
    BoundedCombination A (fun x => f x+g x) (B+C) := by
  obtain ⟨I,inst,E,hE,hv,hc⟩ := h
  obtain ⟨J,inst',F,hF,hw,hd⟩ := h'
  let G : Combination m n (I ⊕ J) := ⟨Sum.elim E.cube F.cube,Sum.elim E.coeff F.coeff⟩
  refine ⟨I⊕J,inferInstance,G,?_ ,?_ ,?_⟩
  · rintro (i|j) hi
    · exact hE i hi
    · exact hF j hi
  · intro x
    simp only [Combination.value,Fintype.sum_sum_type,G,Sum.elim_inl,Sum.elim_inr]
    exact congrArg₂ (·+·) (hv x) (hw x)
  · simp only [Combination.cost,Fintype.sum_sum_type,G,Sum.elim_inl,Sum.elim_inr]
    exact add_le_add hc hd

theorem smul (h : BoundedCombination A f B) (a : ℝ) :
    BoundedCombination A (fun x => a*f x) (|a| * B) := by
  obtain ⟨I,inst,E,hE,hv,hc⟩ := h
  let G : Combination m n I := ⟨E.cube,fun i => a*E.coeff i⟩
  refine ⟨I,inst,G,?_ ,?_ ,?_⟩
  · intro i hi
    exact hE i (fun h => hi (by simp [G,h]))
  · intro x
    unfold Combination.value at hv ⊢
    change _ = a*f x
    rw [← hv x,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [G,mul_assoc]
  · simp only [Combination.cost,G,abs_mul,← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hc (abs_nonneg _)

theorem neg (h : BoundedCombination A f B) :
    BoundedCombination A (fun x => - f x) B := by
  have he := h.smul (-1)
  simpa using he

theorem mul_left (mono : ∀ {c d : Cube m n}, Extends d c → A c → A d)
    (h : BoundedCombination A f B) (h' : BoundedCombination A' g C) :
    BoundedCombination A (fun x => f x*g x) (B*C) := by
  obtain ⟨I,inst,E,hE,hv,hc⟩ := h
  obtain ⟨J,inst',F,hF,hw,hd⟩ := h'
  let G := E.prod F
  refine ⟨I×J,inferInstance,G,Combination.legal_prod mono hE F,?_,?_⟩
  · intro x
    rw [show G.value x = E.value x * F.value x from Combination.value_prod E F x,hv,hw]
  · exact (Combination.cost_prod_le E F).trans
      (mul_le_mul hc hd (Finset.sum_nonneg fun _ _ => abs_nonneg _) ((Finset.sum_nonneg fun _ _ => abs_nonneg _).trans hc))

theorem mul_right (mono : ∀ {c d : Cube m n}, Extends d c → A c → A d)
    (h : BoundedCombination A' f B) (h' : BoundedCombination A g C) :
    BoundedCombination A (fun x => f x*g x) (B*C) := by
  simpa only [mul_comm] using mul_left mono h' h

theorem finset_sum {ι : Type*} (s : Finset ι)
    (v : ι → Board m n → ℝ) (c : ι → ℝ)
    (h : ∀ i ∈ s, BoundedCombination A (v i) (c i)) :
    BoundedCombination A (fun x => ∑ i ∈ s, v i x) (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero A
  | insert i s hi ih =>
    have hh := (h i (by simp)).add (ih fun x hx => h x (by simp [hx]))
    simpa only [Finset.sum_insert hi] using hh

theorem finset_prod_unlimited {ι : Type*} (s : Finset ι)
    (v : ι → Board m n → ℝ) (c : ι → ℝ)
    (h : ∀ i ∈ s, BoundedCombination Unlimited (v i) (c i)) :
    BoundedCombination (@Unlimited m n) (fun x => ∏ i ∈ s, v i x) (∏ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (one (m:=m) (n:=n))
  | insert i s hi ih =>
    have hh := mul_left (fun _ _ => trivial)
      (h i (by simp)) (ih fun x hx => h x (by simp [hx]))
    simpa only [Finset.prod_insert hi] using hh

theorem refutation (h : BoundedCombination A (fun _ => 1) B) :
    ∃ (t : ℕ) (r : Refutation A t), r.mass ≤ B := by
  obtain ⟨I,inst,E,hE,hv,hc⟩ := h
  obtain ⟨t,r,hr⟩ := Combination.refutation_of_value_one E hE hv
  exact ⟨t,r,hr.le.trans hc⟩

end BoundedCombination
end PHP
