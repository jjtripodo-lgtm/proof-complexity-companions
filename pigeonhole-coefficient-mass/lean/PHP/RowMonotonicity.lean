import PHP.CubeProduct

namespace PHP

open scoped BigOperators

/-- Extend a source cube by leaving all new rows unconstrained. -/
noncomputable def extendCube {m m' n : ℕ} (e : Fin m ↪ Fin m') (C : Cube m n) :
    Cube m' n := by
  classical
  exact fun ij => if h : ∃ i, e i = ij.1 then C (Classical.choose h,ij.2) else none

def restrictBoard {m m' n : ℕ} (e : Fin m ↪ Fin m') (x : Board m' n) :
    Board m n := fun ij => x (e ij.1,ij.2)

theorem extendCube_on {m m' n : ℕ} (e : Fin m ↪ Fin m') (C : Cube m n)
    (i : Fin m) (j : Fin n) : extendCube e C (e i,j) = C (i,j) := by
  classical
  have h : ∃ i', e i' = e i := ⟨i,rfl⟩
  unfold extendCube
  rw [dif_pos h]
  rw [e.injective (Classical.choose_spec h)]

theorem holds_extendCube {m m' n : ℕ} (e : Fin m ↪ Fin m') (C : Cube m n)
    (x : Board m' n) : Holds (extendCube e C) x ↔ Holds C (restrictBoard e x) := by
  classical
  constructor
  · intro h ij b hb
    exact h (e ij.1,ij.2) b (by simpa only [extendCube_on] using hb)
  · intro h ij b hb
    rcases ij with ⟨i,j⟩
    by_cases he : ∃ k, e k = i
    · obtain ⟨k,rfl⟩ := he
      exact h (k,j) b (by simpa only [extendCube_on] using hb)
    · simp [extendCube,he] at hb

theorem plain_extendCube {m m' n : ℕ} (e : Fin m ↪ Fin m') {C : Cube m n}
    (hC : Plain C) : Plain (extendCube e C) := by
  rcases hC with ⟨i,h⟩ | ⟨i,i',j,hne,h₁,h₂⟩
  · exact Or.inl ⟨e i, fun j => by simpa only [extendCube_on] using h j⟩
  · exact Or.inr ⟨e i,e i',j,fun he => hne (e.injective he),
      by simpa only [extendCube_on] using h₁, by simpa only [extendCube_on] using h₂⟩

/-- A proof on fewer rows is a proof with the same mass on more rows. Hence
a lower bound at the larger row count also applies to the smaller one. -/
noncomputable def Refutation.addPlainRows {m m' n t : ℕ} (e : Fin m ↪ Fin m')
    (r : Refutation (@Plain m n) t) : Refutation (@Plain m' n) t where
  cube k := extendCube e (r.cube k)
  coeff := r.coeff
  legal k := plain_extendCube e (r.legal k)
  identity x := by
    classical
    simpa only [eval, holds_extendCube] using r.identity (restrictBoard e x)

theorem addPlainRows_preserves_mass {m m' n t : ℕ} (e : Fin m ↪ Fin m')
    (r : Refutation (@Plain m n) t) : (r.addPlainRows e).mass = r.mass := rfl

end PHP
