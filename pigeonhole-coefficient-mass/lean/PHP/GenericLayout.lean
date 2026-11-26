import PHP.BoardBridge
import Mathlib.Logic.Equiv.Fin.Basic

namespace PHP

open scoped BigOperators

abbrev TileWord (s R : ℕ) := Fin s → Option (Fin R)

def BoxAllowed {R : ℕ} (P : Option (Fin R) → Prop) : Prop :=
  (∀ a, ¬ P a) ∨ (∃ p : Fin R, ∀ a, P a ↔ a = some p) ∨ P none

structure CalibratedBlock (s R : ℕ) where
  weight : TileWord s R → ℝ
  total : ∑ a, weight a = 1
  box_bound (P : Fin s → Option (Fin R) → Prop) (hp : ∀ j, BoxAllowed (P j)) :
    (by classical exact |∑ a : TileWord s R, if ∀ j, P j (a j) then weight a else 0| ≤ 1)

structure GenericLayout (s R k m n : ℕ) where
  cols : (Fin k × Fin s) ↪ Fin n
  rows : (Fin k × Fin R) ↪ Fin m

namespace GenericLayout

variable {s R k m n : ℕ}

def standard (hc : k*s ≤ n) (hr : k*R ≤ m) : GenericLayout s R k m n :=
  ⟨finProdFinEquiv.toEmbedding.trans (Fin.castLEEmb hc),
   finProdFinEquiv.toEmbedding.trans (Fin.castLEEmb hr)⟩

def label (D : GenericLayout s R k m n) (σ : Equiv.Perm (Fin m)) (g : Fin k)
    (v : Option (Fin R)) : Option (Fin m) :=
  v.map (fun p => σ (D.rows (g,p)))

@[simp] theorem label_none (D : GenericLayout s R k m n) (σ : Equiv.Perm (Fin m))
    (g : Fin k) : D.label σ g none = none := rfl

@[simp] theorem label_some (D : GenericLayout s R k m n) (σ : Equiv.Perm (Fin m))
    (g : Fin k) (p : Fin R) : D.label σ g (some p) = some (σ (D.rows (g,p))) := rfl

theorem label_injective (D : GenericLayout s R k m n) (σ : Equiv.Perm (Fin m))
    (g : Fin k) : Function.Injective (D.label σ g) := by
  intro x y h
  cases x with
  | none => cases y <;> simp_all
  | some p =>
    cases y with
    | none => simp_all
    | some q =>
      have h₁ := Option.some.inj h
      have h₂ := D.rows.injective (σ.injective h₁)
      exact congrArg some (congrArg Prod.snd h₂)

abbrev Assembly (s R k : ℕ) := Fin k → TileWord s R

noncomputable def embedWord (D : GenericLayout s R k m n) (σ : Equiv.Perm (Fin m))
    (t : Assembly s R k) : Word m n := by
  classical
  exact fun j =>
    if h : ∃ p, D.cols p = j then
      let p := Classical.choose h
      D.label σ p.1 (t p.1 p.2)
    else none

@[simp] theorem embedWord_col (D : GenericLayout s R k m n) (σ : Equiv.Perm (Fin m))
    (t : Assembly s R k) (g : Fin k) (c : Fin s) :
    D.embedWord σ t (D.cols (g,c)) = D.label σ g (t g c) := by
  classical
  have hp : ∃ p, D.cols p = D.cols (g,c) := ⟨(g,c),rfl⟩
  unfold embedWord
  rw [dif_pos hp, D.cols.injective (Classical.choose_spec hp)]

theorem embedWord_outside (D : GenericLayout s R k m n) (σ : Equiv.Perm (Fin m))
    (t : Assembly s R k) (j : Fin n)
    (hj : ¬ ∃ p, D.cols p = j) : D.embedWord σ t j = none := by
  classical
  simp [embedWord,hj]

theorem embedWord_relabel (D : GenericLayout s R k m n)
    (σ π : Equiv.Perm (Fin m)) (t : Assembly s R k) :
    D.embedWord (σ.trans π) t = fun j => (D.embedWord σ t j).map π := by
  funext j
  by_cases h : ∃ p, D.cols p = j
  · obtain ⟨⟨g,c⟩,rfl⟩ := h
    simp only [embedWord_col]
    cases h : t g c <;> rfl
  · rw [embedWord_outside _ _ _ _ h,embedWord_outside _ _ _ _ h]
    rfl

def Accept (C : Cube m n) (j : Fin n) (v : Option (Fin m)) : Prop :=
  ∀ i b, C (i,j) = some b → decide (v = some i) = b

theorem accept_label_allowed (D : GenericLayout s R k m n) (σ : Equiv.Perm (Fin m))
    (C : Cube m n) (g : Fin k) (c : Fin s) :
    BoxAllowed (fun v => Accept C (D.cols (g,c)) (D.label σ g v)) := by
  classical
  let j := D.cols (g,c)
  let P := fun v => Accept C j (D.label σ g v)
  change BoxAllowed P
  by_cases h0 : P none
  · exact Or.inr (Or.inr h0)
  by_cases hsome : ∃ i, C (i,j) = some true
  · obtain ⟨i,hi⟩ := hsome
    by_cases hp : ∃ v, P v
    · obtain ⟨v,hv⟩ := hp
      cases v with
      | none => exact False.elim (h0 hv)
      | some v =>
        right; left
        refine ⟨v,fun w => ?_⟩
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

def OutsideAccept (D : GenericLayout s R k m n) (C : Cube m n) : Prop :=
  ∀ j, (¬ ∃ p, D.cols p = j) → Accept C j none

theorem holds_embedWord (D : GenericLayout s R k m n) (σ : Equiv.Perm (Fin m))
    (t : Assembly s R k) (C : Cube m n) :
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

end GenericLayout

end PHP
