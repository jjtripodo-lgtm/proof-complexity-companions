import PHP.FunctionalCharge

namespace PHP

def columnPairCube {m n : ℕ} (i i' : Fin m) (j : Fin n) : Cube m n :=
  fun ij => if ij = (i,j) ∨ ij = (i',j) then some true else none

def rowPairCube {m n : ℕ} (i : Fin m) (j j' : Fin n) : Cube m n :=
  fun ij => if ij = (i,j) ∨ ij = (i,j') then some true else none

inductive PlainSource {m n : ℕ} : Cube m n → Prop
  | empty (i : Fin m) : PlainSource (rowEmptyCube i)
  | col (i i' : Fin m) (j : Fin n) (hne : i ≠ i') : PlainSource (columnPairCube i i' j)

inductive FunctionalSource {m n : ℕ} : Cube m n → Prop
  | plain {c : Cube m n} : PlainSource c → FunctionalSource c
  | row (i : Fin m) (j j' : Fin n) (hne : j ≠ j') : FunctionalSource (rowPairCube i j j')

/-- There is no repeated cell in the source–multiplier product. -/
def LiteralDisjoint {m n : ℕ} (s d : Cube m n) : Prop :=
  ∀ ij b, s ij = some b → d ij = none

theorem literal_disjoint_compatible {m n : ℕ} {s d : Cube m n}
    (h : LiteralDisjoint s d) : Compatible s d := by
  intro ij b v hb hv
  rw [h ij b hb] at hv
  contradiction

noncomputable def residualCube {m n : ℕ} (s c : Cube m n) : Cube m n :=
  fun ij => if s ij = none then c ij else none

theorem residual_disjoint {m n : ℕ} (s c : Cube m n) :
    LiteralDisjoint s (residualCube s c) := by
  intro ij b hb
  simp [residualCube,hb]

theorem join_residual {m n : ℕ} {s c : Cube m n} (h : Extends c s) :
    join s (residualCube s c) = c := by
  funext ij
  cases hs : s ij with
  | none => simp [join,residualCube,hs]
  | some b => simp [join,hs,h ij b hs,Option.orElse]

private theorem plain_source_legal {m n : ℕ} {s : Cube m n} (h : PlainSource s) : Plain s := by
  cases h with
  | empty i => exact Or.inl ⟨i,fun j => by simp [rowEmptyCube]⟩
  | col i i' j hne => exact Or.inr ⟨i,i',j,hne,by simp [columnPairCube],by simp [columnPairCube]⟩

private theorem functional_source_legal {m n : ℕ} {s : Cube m n} (h : FunctionalSource s) :
    Functional s := by
  cases h with
  | plain h => exact Or.inl (plain_source_legal h)
  | row i j j' hne => exact Or.inr ⟨i,j,j',hne,by simp [rowPairCube],by simp [rowPairCube]⟩

theorem plain_contains_source {m n : ℕ} {c : Cube m n} (h : Plain c) :
    ∃ s : Cube m n, PlainSource s ∧ Extends c s := by
  rcases h with ⟨i,hi⟩ | ⟨i,i',j,hd,hi,hi'⟩
  · refine ⟨rowEmptyCube i,.empty i,?_⟩
    intro ⟨i',j⟩ b hb
    by_cases h : i'=i
    · subst i'
      have hh : false = b := by simpa [rowEmptyCube] using hb
      exact (hi j).trans (congrArg some hh)
    · simp [rowEmptyCube,h] at hb
  · refine ⟨columnPairCube i i' j,.col i i' j hd,?_⟩
    intro ij b hb
    by_cases h : ij=(i,j)∨ij=(i',j)
    · have hh : true = b := by simpa [columnPairCube,h] using hb
      rcases h with rfl|rfl
      · exact hi.trans (congrArg some hh)
      · exact hi'.trans (congrArg some hh)
    · simp [columnPairCube,h] at hb

theorem functional_contains_source {m n : ℕ} {c : Cube m n} (h : Functional c) :
    ∃ s : Cube m n, FunctionalSource s ∧ Extends c s := by
  rcases h with h | ⟨i,j,j',hd,hj,hj'⟩
  · obtain ⟨s,hs,h⟩ := plain_contains_source h
    exact ⟨s,.plain hs,h⟩
  · refine ⟨rowPairCube i j j',.row i j j' hd,?_⟩
    intro ij b hb
    by_cases h : ij=(i,j)∨ij=(i,j')
    · have hh : true = b := by simpa [rowPairCube,h] using hb
      rcases h with rfl|rfl
      · exact hj.trans (congrArg some hh)
      · exact hj'.trans (congrArg some hh)
    · simp [rowPairCube,h] at hb

/-- Normalized literal-monomial weakenings of the original plain axioms
are exactly the charged cubes used by the formalization. -/
theorem plain_iff_normalized_weakening {m n : ℕ} (c : Cube m n) :
    Plain c ↔ ∃ s d, PlainSource s ∧ LiteralDisjoint s d ∧ join s d = c := by
  constructor
  · intro h
    obtain ⟨s,hs,hc⟩ := plain_contains_source h
    exact ⟨s,residualCube s c,hs,residual_disjoint _ _,join_residual hc⟩
  · rintro ⟨s,d,hs,hd,rfl⟩
    exact plain_mono (join_extends_left _ _) (plain_source_legal hs)

theorem functional_iff_normalized_weakening {m n : ℕ} (c : Cube m n) :
    Functional c ↔ ∃ s d, FunctionalSource s ∧ LiteralDisjoint s d ∧ join s d = c := by
  constructor
  · intro h
    obtain ⟨s,hs,hc⟩ := functional_contains_source h
    exact ⟨s,residualCube s c,hs,residual_disjoint _ _,join_residual hc⟩
  · rintro ⟨s,d,hs,hd,rfl⟩
    exact functional_mono (join_extends_left _ _) (functional_source_legal hs)

theorem normalized_weakening_value {m n : ℕ} {s d : Cube m n} (h : LiteralDisjoint s d)
    (x : Board m n) : eval (join s d) x = eval s x*eval d x := by
  rw [eval_product,if_pos (literal_disjoint_compatible h)]

end PHP
