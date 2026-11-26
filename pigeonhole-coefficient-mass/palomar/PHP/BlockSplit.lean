module

public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! Integer certificate for the paper's block with six labels and three columns.
Weights, histograms and rectangle bounds are all scaled by 30. -/
namespace PHP.Block

def letters : List Nat := List.range 7

/-- 0 codes the empty set, 1..6 the positive singletons, and 7..70
code the sets containing 0 and any subset of the positive labels. -/
def allowed (code : Nat) : List Nat :=
  if code == 0 then [] else if code ≤ 6 then [code] else
    0 :: (List.range 6).filterMap (fun j =>
      if (code - 7).testBit j then some (j + 1) else none)

def supportSize (i j k : Nat) : Nat :=
  (([i,j,k].filter (· != 0)).eraseDups).length

def weight30 (i j k : Nat) : Int :=
  match supportSize i j k with
  | 0 => -30
  | 1 => if i != 0 && j != 0 && k != 0 then 0 else 10
  | 2 => if i != 0 && j != 0 && k != 0 then -4 else -6
  | _ => 5

def slice (a b k : Nat) : Int :=
  ((allowed a).map fun i => ((allowed b).map fun j => weight30 i j k).sum).sum

def positives (a b : Nat) : List Int :=
  (List.range 6).map fun k => slice a b (k + 1)

/-- Pair-compressed check. For the third set, a positive singleton contributes
one slice, while a set containing zero contributes the zero slice and a subset
of the six remaining slices. -/
def pairOK (a b : Nat) : Bool :=
  let g := positives a b
  let z := slice a b 0
  g.all (fun v => decide (-30 ≤ v ∧ v ≤ 30)) &&
    decide (-30 ≤ z + (g.map (min 0)).sum ∧ z + (g.map (max 0)).sum ≤ 30)

def histogram (p : Nat) : Int :=
  (letters.map fun i => (letters.map fun j => (letters.map fun k =>
    if supportSize i j k == p then weight30 i j k else 0).sum).sum).sum

theorem histogram_exact : histogram 0 = -30 ∧ histogram 1 = 360 ∧
    histogram 2 = -900 ∧ histogram 3 = 600 := by decide

set_option maxRecDepth 20000
set_option maxHeartbeats 0

private theorem check0 : (List.range 71).all (pairOK 0) = true := by decide
private theorem check1 : (List.range 71).all (pairOK 1) = true := by decide
private theorem check2 : (List.range 71).all (pairOK 2) = true := by decide
private theorem check3 : (List.range 71).all (pairOK 3) = true := by decide
private theorem check4 : (List.range 71).all (pairOK 4) = true := by decide
private theorem check5 : (List.range 71).all (pairOK 5) = true := by decide
private theorem check6 : (List.range 71).all (pairOK 6) = true := by decide
private theorem check7 : (List.range 71).all (pairOK 7) = true := by decide
private theorem check8 : (List.range 71).all (pairOK 8) = true := by decide
private theorem check9 : (List.range 71).all (pairOK 9) = true := by decide
private theorem check10 : (List.range 71).all (pairOK 10) = true := by decide
private theorem check11 : (List.range 71).all (pairOK 11) = true := by decide
private theorem check12 : (List.range 71).all (pairOK 12) = true := by decide
private theorem check13 : (List.range 71).all (pairOK 13) = true := by decide
private theorem check14 : (List.range 71).all (pairOK 14) = true := by decide
private theorem check15 : (List.range 71).all (pairOK 15) = true := by decide
private theorem check16 : (List.range 71).all (pairOK 16) = true := by decide
private theorem check17 : (List.range 71).all (pairOK 17) = true := by decide
private theorem check18 : (List.range 71).all (pairOK 18) = true := by decide
private theorem check19 : (List.range 71).all (pairOK 19) = true := by decide
private theorem check20 : (List.range 71).all (pairOK 20) = true := by decide
private theorem check21 : (List.range 71).all (pairOK 21) = true := by decide
private theorem check22 : (List.range 71).all (pairOK 22) = true := by decide
private theorem check23 : (List.range 71).all (pairOK 23) = true := by decide
private theorem check24 : (List.range 71).all (pairOK 24) = true := by decide
private theorem check25 : (List.range 71).all (pairOK 25) = true := by decide
private theorem check26 : (List.range 71).all (pairOK 26) = true := by decide
private theorem check27 : (List.range 71).all (pairOK 27) = true := by decide
private theorem check28 : (List.range 71).all (pairOK 28) = true := by decide
private theorem check29 : (List.range 71).all (pairOK 29) = true := by decide
private theorem check30 : (List.range 71).all (pairOK 30) = true := by decide
private theorem check31 : (List.range 71).all (pairOK 31) = true := by decide
private theorem check32 : (List.range 71).all (pairOK 32) = true := by decide
private theorem check33 : (List.range 71).all (pairOK 33) = true := by decide
private theorem check34 : (List.range 71).all (pairOK 34) = true := by decide
private theorem check35 : (List.range 71).all (pairOK 35) = true := by decide
private theorem check36 : (List.range 71).all (pairOK 36) = true := by decide
private theorem check37 : (List.range 71).all (pairOK 37) = true := by decide
private theorem check38 : (List.range 71).all (pairOK 38) = true := by decide
private theorem check39 : (List.range 71).all (pairOK 39) = true := by decide
private theorem check40 : (List.range 71).all (pairOK 40) = true := by decide
private theorem check41 : (List.range 71).all (pairOK 41) = true := by decide
private theorem check42 : (List.range 71).all (pairOK 42) = true := by decide
private theorem check43 : (List.range 71).all (pairOK 43) = true := by decide
private theorem check44 : (List.range 71).all (pairOK 44) = true := by decide
private theorem check45 : (List.range 71).all (pairOK 45) = true := by decide
private theorem check46 : (List.range 71).all (pairOK 46) = true := by decide
private theorem check47 : (List.range 71).all (pairOK 47) = true := by decide
private theorem check48 : (List.range 71).all (pairOK 48) = true := by decide
private theorem check49 : (List.range 71).all (pairOK 49) = true := by decide
private theorem check50 : (List.range 71).all (pairOK 50) = true := by decide
private theorem check51 : (List.range 71).all (pairOK 51) = true := by decide
private theorem check52 : (List.range 71).all (pairOK 52) = true := by decide
private theorem check53 : (List.range 71).all (pairOK 53) = true := by decide
private theorem check54 : (List.range 71).all (pairOK 54) = true := by decide
private theorem check55 : (List.range 71).all (pairOK 55) = true := by decide
private theorem check56 : (List.range 71).all (pairOK 56) = true := by decide
private theorem check57 : (List.range 71).all (pairOK 57) = true := by decide
private theorem check58 : (List.range 71).all (pairOK 58) = true := by decide
private theorem check59 : (List.range 71).all (pairOK 59) = true := by decide
private theorem check60 : (List.range 71).all (pairOK 60) = true := by decide
private theorem check61 : (List.range 71).all (pairOK 61) = true := by decide
private theorem check62 : (List.range 71).all (pairOK 62) = true := by decide
private theorem check63 : (List.range 71).all (pairOK 63) = true := by decide
private theorem check64 : (List.range 71).all (pairOK 64) = true := by decide
private theorem check65 : (List.range 71).all (pairOK 65) = true := by decide
private theorem check66 : (List.range 71).all (pairOK 66) = true := by decide
private theorem check67 : (List.range 71).all (pairOK 67) = true := by decide
private theorem check68 : (List.range 71).all (pairOK 68) = true := by decide
private theorem check69 : (List.range 71).all (pairOK 69) = true := by decide
private theorem check70 : (List.range 71).all (pairOK 70) = true := by decide

 theorem rowCheck (a : Fin 71) : (List.range 71).all (pairOK a.val) = true := by
  have h : a.val < 71 := a.isLt
  interval_cases ha : a.val
  · simpa only [ha] using check0
  · simpa only [ha] using check1
  · simpa only [ha] using check2
  · simpa only [ha] using check3
  · simpa only [ha] using check4
  · simpa only [ha] using check5
  · simpa only [ha] using check6
  · simpa only [ha] using check7
  · simpa only [ha] using check8
  · simpa only [ha] using check9
  · simpa only [ha] using check10
  · simpa only [ha] using check11
  · simpa only [ha] using check12
  · simpa only [ha] using check13
  · simpa only [ha] using check14
  · simpa only [ha] using check15
  · simpa only [ha] using check16
  · simpa only [ha] using check17
  · simpa only [ha] using check18
  · simpa only [ha] using check19
  · simpa only [ha] using check20
  · simpa only [ha] using check21
  · simpa only [ha] using check22
  · simpa only [ha] using check23
  · simpa only [ha] using check24
  · simpa only [ha] using check25
  · simpa only [ha] using check26
  · simpa only [ha] using check27
  · simpa only [ha] using check28
  · simpa only [ha] using check29
  · simpa only [ha] using check30
  · simpa only [ha] using check31
  · simpa only [ha] using check32
  · simpa only [ha] using check33
  · simpa only [ha] using check34
  · simpa only [ha] using check35
  · simpa only [ha] using check36
  · simpa only [ha] using check37
  · simpa only [ha] using check38
  · simpa only [ha] using check39
  · simpa only [ha] using check40
  · simpa only [ha] using check41
  · simpa only [ha] using check42
  · simpa only [ha] using check43
  · simpa only [ha] using check44
  · simpa only [ha] using check45
  · simpa only [ha] using check46
  · simpa only [ha] using check47
  · simpa only [ha] using check48
  · simpa only [ha] using check49
  · simpa only [ha] using check50
  · simpa only [ha] using check51
  · simpa only [ha] using check52
  · simpa only [ha] using check53
  · simpa only [ha] using check54
  · simpa only [ha] using check55
  · simpa only [ha] using check56
  · simpa only [ha] using check57
  · simpa only [ha] using check58
  · simpa only [ha] using check59
  · simpa only [ha] using check60
  · simpa only [ha] using check61
  · simpa only [ha] using check62
  · simpa only [ha] using check63
  · simpa only [ha] using check64
  · simpa only [ha] using check65
  · simpa only [ha] using check66
  · simpa only [ha] using check67
  · simpa only [ha] using check68
  · simpa only [ha] using check69
  · simpa only [ha] using check70

theorem pairs_pass (a b : Fin 71) : pairOK a.val b.val = true := by
  have hb : b.val ∈ List.range 71 := List.mem_range.mpr b.isLt
  exact List.all_eq_true.mp (rowCheck a) _ hb

end PHP.Block
