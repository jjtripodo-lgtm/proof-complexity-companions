import PHP.BlockSplit

namespace PHP.Block

private theorem filterMap_extrema (xs : List Nat) (p : Nat → Bool) (f : Nat → Int) :
    ((xs.map (fun j => min 0 (f j))).sum ≤
      (xs.filterMap (fun j => if p j then some (f j) else none)).sum) ∧
    ((xs.filterMap (fun j => if p j then some (f j) else none)).sum ≤
      (xs.map (fun j => max 0 (f j))).sum) := by
  induction xs with
  | nil => simp
  | cons j js ih =>
    have hl0 := min_le_left (0 : ℤ) (f j)
    have hlf := min_le_right (0 : ℤ) (f j)
    have hu0 := le_max_left (0 : ℤ) (f j)
    have huf := le_max_right (0 : ℤ) (f j)
    cases hp : p j <;> simp only [List.map_cons, List.filterMap_cons, hp, Bool.false_eq_true,
      ↓reduceIte, List.sum_cons] <;> omega

def rectangle30 (a b c : Nat) : Int :=
  ((allowed c).map (slice a b)).sum

/-- Exact direct bound on the signed cube sum, not only the acceptance bit of
the pair test. All three allowed-set codes are independently quantified. -/
theorem rectangle30_bound (a b c : Fin 71) :
    -30 ≤ rectangle30 a.val b.val c.val ∧ rectangle30 a.val b.val c.val ≤ 30 := by
  have hcheck := pairs_pass a b
  have hcheck' :
      (positives a.val b.val).all (fun v => decide (-30 ≤ v ∧ v ≤ 30)) = true ∧
      decide (-30 ≤ slice a.val b.val 0 + ((positives a.val b.val).map (min 0)).sum ∧
        slice a.val b.val 0 + ((positives a.val b.val).map (max 0)).sum ≤ 30) = true :=
    Bool.and_eq_true_iff.mp hcheck
  have hset := of_decide_eq_true hcheck'.2
  by_cases hz : c.val = 0
  · simp [rectangle30, allowed, hz]
  by_cases hs : c.val ≤ 6
  · have hg : slice a.val b.val c.val ∈ positives a.val b.val := by
      unfold positives
      apply List.mem_map.mpr
      refine ⟨c.val-1, List.mem_range.mpr (by omega), ?_⟩
      congr 1
      omega
    have hb := of_decide_eq_true ((List.all_eq_true.mp hcheck'.1) _ hg)
    simpa [rectangle30, allowed, hz, hs] using hb
  · have he := filterMap_extrema (List.range 6) (fun j => (c.val-7).testBit j)
      (fun j => slice a.val b.val (j+1))
    have hrewrite :
        rectangle30 a.val b.val c.val = slice a.val b.val 0 +
          ((List.range 6).filterMap (fun j =>
            if (c.val-7).testBit j then some (slice a.val b.val (j+1)) else none)).sum := by
      simp only [rectangle30, allowed, hz, hs, beq_iff_eq, ↓reduceIte, List.map_cons,
        List.sum_cons, List.map_filterMap]
      congr 3
      funext j
      cases (c.val-7).testBit j <;> rfl
    rw [hrewrite]
    simp only [positives, List.map_map] at hset
    change -30 ≤ slice a.val b.val 0 +
      ((List.range 6).map (fun j => min 0 (slice a.val b.val (j+1)))).sum ∧
      slice a.val b.val 0 +
      ((List.range 6).map (fun j => max 0 (slice a.val b.val (j+1)))).sum ≤ 30 at hset
    omega

end PHP.Block
