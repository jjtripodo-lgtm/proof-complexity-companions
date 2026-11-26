module

public import PHP.BlockLaw
public import PHP.BoardBridge
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

namespace PHP

open scoped BigOperators

structure BlockLayout (k m n : ℕ) where
  cols : (Fin k × Fin 3) ↪ Fin n
  rows : (Fin k × Fin 6) ↪ Fin m

namespace BlockLayout

variable {k m n : ℕ}

def standard (hc : k*3 ≤ n) (hr : k*6 ≤ m) : BlockLayout k m n :=
  ⟨finProdFinEquiv.toEmbedding.trans (Fin.castLEEmb hc),
   finProdFinEquiv.toEmbedding.trans (Fin.castLEEmb hr)⟩

def label (D : BlockLayout k m n) (σ : Equiv.Perm (Fin m))
    (g : Fin k) : Fin 7 → Option (Fin m) :=
  Fin.cases none (fun p => some (σ (D.rows (g,p))))

@[simp] theorem label_zero (D : BlockLayout k m n) (σ : Equiv.Perm (Fin m))
    (g : Fin k) : D.label σ g 0 = none := rfl

@[simp] theorem label_succ (D : BlockLayout k m n) (σ : Equiv.Perm (Fin m))
    (g : Fin k) (p : Fin 6) : D.label σ g p.succ = some (σ (D.rows (g,p))) := rfl

theorem label_injective (D : BlockLayout k m n) (σ : Equiv.Perm (Fin m))
    (g : Fin k) : Function.Injective (D.label σ g) := by
  intro x y
  refine Fin.cases ?_ (fun x' => ?_) x <;> refine Fin.cases ?_ (fun y' => ?_) y
  · simp
  · simp
  · simp
  · intro h
    have h₁ := Option.some.inj h
    have h₂ := D.rows.injective (σ.injective h₁)
    exact congrArg Fin.succ (congrArg Prod.snd h₂)

noncomputable def embedWord (D : BlockLayout k m n) (σ : Equiv.Perm (Fin m))
    (t : Fin k → Block.Tile) : Word m n := by
  classical
  exact fun j =>
    if h : ∃ p, D.cols p = j then
      let p := Classical.choose h
      D.label σ p.1 (t p.1 p.2)
    else none

@[simp] theorem embedWord_col (D : BlockLayout k m n) (σ : Equiv.Perm (Fin m))
    (t : Fin k → Block.Tile) (g : Fin k) (c : Fin 3) :
    D.embedWord σ t (D.cols (g,c)) = D.label σ g (t g c) := by
  classical
  have hp : ∃ p, D.cols p = D.cols (g,c) := ⟨(g,c),rfl⟩
  unfold embedWord
  rw [dif_pos hp, D.cols.injective (Classical.choose_spec hp)]

theorem embedWord_outside (D : BlockLayout k m n) (σ : Equiv.Perm (Fin m))
    (t : Fin k → Block.Tile) (j : Fin n)
    (hj : ¬ ∃ p, D.cols p = j) : D.embedWord σ t j = none := by
  classical
  simp [embedWord,hj]

theorem embedWord_relabel (D : BlockLayout k m n)
    (σ π : Equiv.Perm (Fin m)) (t : Fin k → Block.Tile) :
    D.embedWord (σ.trans π) t = fun j => (D.embedWord σ t j).map π := by
  funext j
  by_cases h : ∃ p, D.cols p = j
  · obtain ⟨⟨g,c⟩,rfl⟩ := h
    simp only [embedWord_col]
    refine Fin.cases ?_ (fun x => ?_) (t g c)
    · rfl
    · rfl
  · rw [embedWord_outside _ _ _ _ h,embedWord_outside _ _ _ _ h]
    rfl

def Accept (C : Cube m n) (j : Fin n) (v : Option (Fin m)) : Prop :=
  ∀ i b, C (i,j) = some b → decide (v = some i) = b

theorem accept_label_allowed (D : BlockLayout k m n) (σ : Equiv.Perm (Fin m))
    (C : Cube m n) (g : Fin k) (c : Fin 3) :
    Block.AllowedPred (fun v => Accept C (D.cols (g,c)) (D.label σ g v)) := by
  classical
  let j := D.cols (g,c)
  let P := fun v => Accept C j (D.label σ g v)
  change Block.AllowedPred P
  by_cases h0 : P 0
  · exact Or.inr (Or.inr h0)
  by_cases hsome : ∃ i, C (i,j) = some true
  · obtain ⟨i,hi⟩ := hsome
    by_cases hp : ∃ v, P v
    · obtain ⟨v,hv⟩ := hp
      right; left
      refine ⟨v,fun h => h0 (h ▸ hv),fun w => ?_⟩
      constructor
      · intro hw
        apply D.label_injective σ g
        exact (of_decide_eq_true (hw i true hi)).trans
          (of_decide_eq_true (hv i true hi)).symm
      · rintro rfl
        exact hv
    · exact Or.inl (fun w hw => hp ⟨w,hw⟩)
  · exfalso
    apply h0
    intro i b hi
    cases b
    · simp
    · exact False.elim (hsome ⟨i,hi⟩)

def OutsideAccept (D : BlockLayout k m n) (C : Cube m n) : Prop :=
  ∀ j, (¬ ∃ p, D.cols p = j) → Accept C j none

theorem holds_embedWord (D : BlockLayout k m n) (σ : Equiv.Perm (Fin m))
    (t : Fin k → Block.Tile) (C : Cube m n) :
    Holds C (D.embedWord σ t).board ↔
      D.OutsideAccept C ∧ ∀ g c, Accept C (D.cols (g,c)) (D.label σ g (t g c)) := by
  rw [holds_word_iff_columns]
  constructor
  · intro h
    refine ⟨fun j hj => ?_,fun g c => ?_⟩
    · unfold Accept
      rw [← D.embedWord_outside σ t j hj]
      exact h j
    · unfold Accept
      rw [← D.embedWord_col σ t g c]
      exact h (D.cols (g,c))
  · rintro ⟨hout,hin⟩ j i b hb
    by_cases hj : ∃ p, D.cols p = j
    · obtain ⟨⟨g,c⟩,rfl⟩ := hj
      rw [D.embedWord_col]
      exact hin g c i b hb
    · rw [D.embedWord_outside σ t j hj]
      exact hout j hj i b hb

end BlockLayout

end PHP
