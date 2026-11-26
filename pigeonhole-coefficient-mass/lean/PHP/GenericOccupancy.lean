import PHP.GenericAverage
import PHP.GenericBlockMoment
import PHP.LiftValue
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith

namespace PHP.GenericLayout

open scoped BigOperators

variable {s R k m n : ℕ}

noncomputable def usedPairs (t : Assembly s R k) : Finset (Fin k × Fin R) :=
  Finset.univ.filter fun p => p.2 ∈ tileUsed (t p.1)

noncomputable def usedRows (a : Word m n) : Finset (Fin m) := by
  classical exact Finset.univ.filter (fun i => ¬ Omits a i)

theorem mem_usedRows (a : Word m n) (i : Fin m) :
    i ∈ usedRows a ↔ ∃ j : Fin n, a j = some i := by
  classical
  unfold usedRows Omits
  simp

theorem usedRows_embed (D : GenericLayout s R k m n) (σ : Equiv.Perm (Fin m))
    (t : Assembly s R k) :
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
      cases hval : t g c with
      | none => simp [hval] at hj
      | some p =>
        have he : σ (D.rows (g,p)) = i := by simpa [hval] using hj
        exact ⟨(g,p), Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (mem_tileUsed (t g) p).mpr ⟨c,hval⟩⟩, he⟩
    · rw [D.embedWord_outside σ t j hr] at hj
      contradiction
  · rintro ⟨⟨g,p⟩,h,he⟩
    have h' : p ∈ tileUsed (t g) := (Finset.mem_filter.mp h).2
    obtain ⟨c,hc⟩ := (mem_tileUsed (t g) p).mp h'
    exact ⟨D.cols (g,c), by rw [D.embedWord_col,hc,D.label_some,he]⟩

theorem usedPairs_card (t : Assembly s R k) :
    (usedPairs t).card = ∑ g : Fin k, tileSupport (t g) := by
  classical
  unfold usedPairs
  rw [Finset.card_eq_sum_ones,Finset.sum_filter,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro g _
  have hf : Finset.univ.filter (fun p : Fin R => p ∈ tileUsed (t g)) =
      tileUsed (t g) := by ext; simp
  rw [Finset.sum_boole,hf]
  rfl

theorem usedRows_embed_card (D : GenericLayout s R k m n) (σ : Equiv.Perm (Fin m))
    (t : Assembly s R k) :
    (usedRows (D.embedWord σ t)).card = ∑ g : Fin k, tileSupport (t g) := by
  have hi : Function.Injective (fun p : Fin k × Fin R => σ (D.rows p)) :=
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
  have h := Finset.filter_card_add_filter_neg_card_eq_card (s := (Finset.univ : Finset (Fin m))) (Omits a)
  rw [Finset.card_univ,Fintype.card_fin] at h
  have heq :
      m - ((Finset.univ : Finset (Fin m)).filter (fun i => ¬ Omits a i)).card =
        ((Finset.univ : Finset (Fin m)).filter (Omits a)).card := by omega
  rw [heq]

theorem sum_tileSupport_le (t : Assembly s R k) :
    (∑ g : Fin k, tileSupport (t g)) ≤ s*k := by
  calc
    _ ≤ ∑ _ : Fin k, s := Finset.sum_le_sum fun g _ => tileSupport_le (t g)
    _ = _ := by simp [Finset.sum_const,Nat.mul_comm]

theorem missing_embed_exponent (D : GenericLayout s R k m n) (σ : Equiv.Perm (Fin m))
    (t : Assembly s R k) (hm : s*k ≤ m) :
    missingNat (D.embedWord σ t) =
      m-s*k + ∑ g : Fin k, (s - tileSupport (t g)) := by
  unfold missingNat
  rw [D.usedRows_embed_card σ t]
  have hh : (∑ g : Fin k, (s - tileSupport (t g))) =
      s*k - ∑ g : Fin k, tileSupport (t g) := by
    rw [Finset.sum_tsub_distrib Finset.univ
      (by intro g _; exact tileSupport_le (t g))]
    simp [Finset.sum_const,Nat.mul_comm]
  rw [hh]
  have h := sum_tileSupport_le t
  omega

theorem sample_polynomial (D : GenericLayout s R k m n) (B : CalibratedBlock s R) (σ : Equiv.Perm (Fin m))
    (hm : s*k ≤ m) (x : ℝ) :
    (∑ t : Assembly s R k, weight B t * x^(missingNat (D.embedWord σ t))) =
      x^(m-s*k) * B.polynomial x^k := by
  classical
  have ht (t : Assembly s R k) :
      weight B t * x^(missingNat (D.embedWord σ t)) =
        x^(m-s*k) * ∏ g, (B.weight (t g) * x^(s-tileSupport (t g))) := by
    rw [D.missing_embed_exponent σ t hm,pow_add,Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, weight]
    ring
  simp_rw [ht, ← Finset.mul_sum]
  congr 1
  rw [← Fintype.prod_sum (fun (_g : Fin k) (u : TileWord s R) =>
    B.weight u * x^(s - tileSupport u))]
  simp [CalibratedBlock.polynomial]

theorem small_polynomial (D : GenericLayout s R k m n) (B : CalibratedBlock s R) (hm : s*k ≤ m) (x : ℝ) :
    (∑ a, D.smallLaw B a * x^(missingNat a)) = x^(m-s*k) * B.polynomial x^k := by
  classical
  rw [D.small_moment B (fun a => x^(missingNat a))]
  simp_rw [D.sample_polynomial B _ hm]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  change (permMass m)⁻¹ * (permMass m * _) = _
  rw [← mul_assoc,inv_mul_cancel₀ (permMass_pos m).ne',one_mul]

end PHP.GenericLayout
