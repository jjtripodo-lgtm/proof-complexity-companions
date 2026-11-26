module

public import PHP.BlockAverage
public import PHP.BlockMoments
public import PHP.LiftValue
public import Mathlib.Data.Finset.Prod
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace PHP.BlockLayout

open scoped BigOperators

variable {k m n : ℕ}

def usedPairs (t : Assembly k) : Finset (Fin k × Fin 6) :=
  Finset.univ.filter fun p => p.2 ∈ Block.tileUsed (t p.1)

noncomputable def usedRows (a : Word m n) : Finset (Fin m) := by
  classical exact Finset.univ.filter (fun i => ¬ Omits a i)

theorem mem_usedRows (a : Word m n) (i : Fin m) :
    i ∈ usedRows a ↔ ∃ j : Fin n, a j = some i := by
  classical
  unfold usedRows Omits
  simp

theorem usedRows_embed (D : BlockLayout k m n) (σ : Equiv.Perm (Fin m))
    (t : Assembly k) :
    usedRows (D.embedWord σ t) =
      (usedPairs t).image (fun p => σ (D.rows p)) := by
  classical
  ext i
  rw [mem_usedRows, Finset.mem_image]
  constructor
  · rintro ⟨j,hj⟩
    by_cases hr : ∃ p, D.cols p = j
    · obtain ⟨⟨g,c⟩,rfl⟩ := hr
      rw [D.embedWord_col] at hj
      cases hval : t g c using Fin.cases with
      | zero => simp [hval] at hj
      | succ p =>
        have he : σ (D.rows (g,p)) = i := by simpa [hval] using hj
        exact ⟨(g,p), Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Block.mem_tileUsed (t g) p).mpr ⟨c,hval⟩⟩, he⟩
    · rw [D.embedWord_outside σ t j hr] at hj
      contradiction
  · rintro ⟨⟨g,p⟩,h,he⟩
    have h' : p ∈ Block.tileUsed (t g) := (Finset.mem_filter.mp h).2
    obtain ⟨c,hc⟩ := (Block.mem_tileUsed (t g) p).mp h'
    exact ⟨D.cols (g,c), by rw [D.embedWord_col,hc,D.label_succ,he]⟩

theorem usedPairs_card (t : Assembly k) :
    (usedPairs t).card = ∑ g : Fin k, Block.tileSupport (t g) := by
  classical
  unfold usedPairs
  rw [Finset.card_eq_sum_ones,Finset.sum_filter,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro g _
  have hf : Finset.univ.filter (fun p : Fin 6 => p ∈ Block.tileUsed (t g)) =
      Block.tileUsed (t g) := by ext; simp
  rw [Finset.sum_boole,hf,Block.tileUsed_card]
  simp

theorem usedRows_embed_card (D : BlockLayout k m n) (σ : Equiv.Perm (Fin m))
    (t : Assembly k) :
    (usedRows (D.embedWord σ t)).card = ∑ g : Fin k, Block.tileSupport (t g) := by
  have hi : Function.Injective (fun p : Fin k × Fin 6 => σ (D.rows p)) :=
    σ.injective.comp D.rows.injective
  rw [D.usedRows_embed σ t, Finset.card_image_of_injective _ hi]
  exact usedPairs_card t

noncomputable def missingNat (a : Word m n) : ℕ := m - (usedRows a).card

theorem omissions_eq_cast (a : Word m n) : omissions a = (missingNat a : ℝ) := by
  classical
  unfold omissions missingNat usedRows
  have he :
      (∑ i : Fin m, if Omits a i then (1 : ℝ) else 0) =
        (((Finset.univ : Finset (Fin m)).filter (Omits a)).card : ℝ) :=
    Finset.sum_boole (Omits a) Finset.univ
  rw [he]
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m))) (Omits a)
  rw [Finset.card_univ,Fintype.card_fin] at h
  have heq :
      m - ((Finset.univ : Finset (Fin m)).filter (fun i => ¬ Omits a i)).card =
        ((Finset.univ : Finset (Fin m)).filter (Omits a)).card := by omega
  rw [heq]

theorem sum_tileSupport_le (t : Assembly k) :
    (∑ g : Fin k, Block.tileSupport (t g)) ≤ 3*k := by
  calc
    _ ≤ ∑ _ : Fin k, 3 := Finset.sum_le_sum fun g _ => Block.tileSupport_le (t g)
    _ = _ := by simp [Finset.sum_const,Nat.mul_comm]

theorem missing_embed_exponent (D : BlockLayout k m n) (σ : Equiv.Perm (Fin m))
    (t : Assembly k) (hm : 3*k ≤ m) :
    missingNat (D.embedWord σ t) =
      m-3*k + ∑ g : Fin k, (3 - Block.tileSupport (t g)) := by
  unfold missingNat
  rw [D.usedRows_embed_card σ t]
  have hh : (∑ g : Fin k, (3 - Block.tileSupport (t g))) =
      3*k - ∑ g : Fin k, Block.tileSupport (t g) := by
    rw [Finset.sum_tsub_distrib Finset.univ
      (by intro g _; exact Block.tileSupport_le (t g))]
    simp [Finset.sum_const,Nat.mul_comm]
  rw [hh]
  have h := sum_tileSupport_le t
  omega

theorem sample_polynomial (D : BlockLayout k m n) (σ : Equiv.Perm (Fin m))
    (hm : 3*k ≤ m) (x : ℝ) :
    (∑ t : Assembly k, weight t * x^(missingNat (D.embedWord σ t))) =
      x^(m-3*k) * blockPolynomial x^k := by
  classical
  have ht (t : Assembly k) :
      weight t * x^(missingNat (D.embedWord σ t)) =
        x^(m-3*k) * ∏ g, (Block.tileWeight (t g) * x^(3-Block.tileSupport (t g))) := by
    rw [D.missing_embed_exponent σ t hm,pow_add,Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, weight]
    ring
  simp_rw [ht, ← Finset.mul_sum]
  congr 1
  rw [← Fintype.prod_sum (fun (_g : Fin k) (u : Block.Tile) =>
    Block.tileWeight u * x^(3 - Block.tileSupport u))]
  simp [Block.tile_polynomial]

theorem small_polynomial (D : BlockLayout k m n) (hm : 3*k ≤ m) (x : ℝ) :
    (∑ a, D.smallLaw a * x^(missingNat a)) = x^(m-3*k) * blockPolynomial x^k := by
  classical
  rw [D.small_moment (fun a => x^(missingNat a))]
  simp_rw [D.sample_polynomial _ hm]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  change (permMass m)⁻¹ * (permMass m * _) = _
  rw [← mul_assoc,inv_mul_cancel₀ (permMass_pos m).ne',one_mul]

end PHP.BlockLayout
