module

public import PHP.Model

@[expose] public section

namespace PHP

def Extends {m n : ℕ} (D C : Cube m n) : Prop :=
  ∀ ij b, C ij = some b → D ij = some b

def Compatible {m n : ℕ} (C D : Cube m n) : Prop :=
  ∀ ij b c, C ij = some b → D ij = some c → b = c

def join {m n : ℕ} (C D : Cube m n) : Cube m n :=
  fun ij => (C ij).orElse (fun _ => D ij)

theorem join_extends_left {m n : ℕ} (C D : Cube m n) : Extends (join C D) C := by
  intro ij b hb
  simp [join, hb, Option.orElse]

theorem join_extends_right {m n : ℕ} {C D : Cube m n} (h : Compatible C D) :
    Extends (join C D) D := by
  intro ij b hb
  cases hc : C ij with
  | none => simp [join, hc, hb, Option.orElse]
  | some c =>
    have he := h ij c b hc hb
    simp [join, hc, he, Option.orElse]

theorem holds_join {m n : ℕ} {C D : Cube m n} (hc : Compatible C D)
    (x : Board m n) : Holds (join C D) x ↔ Holds C x ∧ Holds D x := by
  constructor
  · intro h
    exact ⟨fun ij b hb => h ij b (join_extends_left C D ij b hb),
      fun ij b hb => h ij b (join_extends_right hc ij b hb)⟩
  · rintro ⟨hC,hD⟩ ij b hb
    cases h : C ij with
    | none =>
      have hb' : D ij = some b := by simpa [join, h, Option.orElse] using hb
      exact hD ij b hb'
    | some c =>
      have hb' : c = b := by simpa [join, h, Option.orElse] using hb
      exact (hC ij c h).trans hb'

theorem compatible_of_holds {m n : ℕ} {C D : Cube m n} {x : Board m n}
    (hC : Holds C x) (hD : Holds D x) : Compatible C D := by
  intro ij b c hb hc
  exact (hC ij b hb).symm.trans (hD ij c hc)

theorem eval_product {m n : ℕ} (C D : Cube m n) (x : Board m n) :
    eval C x * eval D x =
      (by classical exact if Compatible C D then eval (join C D) x else 0) := by
  classical
  by_cases hC : Holds C x <;> by_cases hD : Holds D x
  · have h := compatible_of_holds hC hD
    simp [eval, hC, hD, h, (holds_join h x).mpr ⟨hC,hD⟩]
  · by_cases h : Compatible C D
    · simp [eval, hC, hD, h, holds_join h x]
    · simp [eval, hC, hD, h]
  · by_cases h : Compatible C D
    · simp [eval, hC, hD, h, holds_join h x]
    · simp [eval, hC, hD, h]
  · by_cases h : Compatible C D
    · simp [eval, hC, hD, h, holds_join h x]
    · simp [eval, hC, hD, h]

theorem plain_mono {m n : ℕ} {C D : Cube m n} (h : Extends D C)
    (hC : Plain C) : Plain D := by
  rcases hC with ⟨i, hi⟩ | ⟨i, i', j, hne, h₁, h₂⟩
  · exact Or.inl ⟨i, fun j => h (i,j) false (hi j)⟩
  · exact Or.inr ⟨i,i',j,hne,h _ _ h₁,h _ _ h₂⟩

theorem functional_mono {m n : ℕ} {C D : Cube m n} (h : Extends D C)
    (hC : Functional C) : Functional D := by
  rcases hC with hC | ⟨i, j, j', hne, h₁, h₂⟩
  · exact Or.inl (plain_mono h hC)
  · exact Or.inr ⟨i,j,j',hne,h _ _ h₁,h _ _ h₂⟩

end PHP
