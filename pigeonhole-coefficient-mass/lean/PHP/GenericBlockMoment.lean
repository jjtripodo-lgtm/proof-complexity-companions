import PHP.GenericLayout
import PHP.EmptyColumns
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace PHP

open scoped BigOperators

variable {s R : ℕ}

noncomputable def tileUsed (w : TileWord s R) : Finset (Fin R) := by
  classical exact Finset.univ.filter (fun p => ∃ c : Fin s, w c = some p)

theorem mem_tileUsed (w : TileWord s R) (p : Fin R) :
    p ∈ tileUsed w ↔ ∃ c : Fin s, w c = some p := by
  classical simp [tileUsed]

noncomputable def tileSupport (w : TileWord s R) : ℕ := (tileUsed w).card

theorem tileSupport_le (w : TileWord s R) : tileSupport w ≤ s := by
  classical
  let someEmb : Fin R ↪ Option (Fin R) := ⟨some,fun _ _ h => Option.some.inj h⟩
  have hs : (tileUsed w).map someEmb ⊆ (Finset.univ : Finset (Fin s)).image w := by
    intro a ha
    obtain ⟨p,hp,rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨c,hc⟩ := (mem_tileUsed w p).mp hp
    exact Finset.mem_image.mpr ⟨c,Finset.mem_univ _,hc⟩
  calc
    _ = ((tileUsed w).map someEmb).card := (Finset.card_map _).symm
    _ ≤ ((Finset.univ : Finset (Fin s)).image w).card := Finset.card_le_card hs
    _ ≤ s := by simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin s))) (f:=w)

namespace CalibratedBlock

noncomputable def polynomial (B : CalibratedBlock s R) (x : ℝ) : ℝ :=
  ∑ w : TileWord s R, B.weight w * x^(s - tileSupport w)

noncomputable def expectedSupport (B : CalibratedBlock s R) : ℝ :=
  ∑ w : TileWord s R, B.weight w * tileSupport w

@[simp] theorem polynomial_one (B : CalibratedBlock s R) : B.polynomial 1 = 1 := by
  simp [polynomial,B.total]

theorem polynomial_derivative (B : CalibratedBlock s R) :
    HasDerivAt B.polynomial ((s : ℝ) - B.expectedSupport) 1 := by
  classical
  have hi (w : TileWord s R) : HasDerivAt (fun x : ℝ => B.weight w*x^(s-tileSupport w))
        (B.weight w*((s : ℝ)-tileSupport w)) 1 := by
    have h := (hasDerivAt_pow (s-tileSupport w) (1 : ℝ)).const_mul (B.weight w)
    simpa [Nat.cast_sub (tileSupport_le w)] using h
  have h := HasDerivAt.fun_sum (u := (Finset.univ : Finset (TileWord s R))) (fun w _ => hi w)
  unfold polynomial expectedSupport
  simp_rw [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,B.total,one_mul] at h
  exact h

end CalibratedBlock
end PHP
