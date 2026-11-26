import PHP.PhaseBlock

namespace PHP.Phase

open scoped BigOperators ComplexConjugate

variable {R : ℕ}

def avoid (r : Fin R) (a : Letter R) : Prop := a ≠ some r

noncomputable def plane (r : Fin R) (a b : ℂ) : Vec R :=
  fun i => a + if i = r then b else 0

theorem avg_plane (hR : 0 < R) (r : Fin R) (a b : ℂ) :
    avg (plane r a b) = a + b/(R : ℂ) := by
  have hn : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  unfold avg plane
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Fintype.card_fin]
  rw [Finset.sum_ite_eq']
  simp
  field_simp

theorem rotation_plane (hR : 0 < R) (r : Fin R) (a b : ℂ) :
    rotation R (plane r a b) =
      plane r (a + (1-conj eta)*b/(R : ℂ)) (conj eta*b) := by
  funext i
  change avg (plane r a b) + conj eta * (plane r a b i - avg (plane r a b)) = _
  rw [avg_plane hR]
  unfold plane
  by_cases hi : i = r <;> simp [hi,div_eq_mul_inv] <;> ring

theorem boxCoeff_avoid (r i : Fin R) :
    boxCoeff (avoid r) i = if i = r then eta else 1 := by
  have hn : avoid r none := by simp [avoid]
  rw [boxCoeff_none _ hn]
  by_cases hi : i = r <;> simp [avoid,hi]

theorem avoid_diagonal_plane (r : Fin R) (a b : ℂ) :
    diagonal (boxCoeff (avoid r)) (plane r a b) =
      plane r a ((eta-1)*a + eta*b) := by
  funext i
  change boxCoeff (avoid r) i * plane r a b i = _
  rw [boxCoeff_avoid]
  unfold plane
  by_cases hi : i = r <;> simp [hi]
  ring

noncomputable def stepPair (R : ℕ) (p : ℂ × ℂ) : ℂ × ℂ :=
  let y := (eta-1)*p.1 + eta*p.2
  (p.1 + (1-conj eta)*y/(R : ℂ), conj eta*y)

theorem avoid_op_plane (hR : 0 < R) (r : Fin R) (a b : ℂ) :
    boxOp (avoid r) (plane r a b) =
      plane r (stepPair R (a,b)).1 (stepPair R (a,b)).2 := by
  rw [boxOp_eq]
  change rotation R (diagonal (boxCoeff (avoid r)) (plane r a b)) = _
  rw [avoid_diagonal_plane,rotation_plane hR]
  rfl

theorem eta_add_conj : eta + conj eta = 1 := by
  apply Complex.ext <;> norm_num [eta]

/-- Cayley–Hamilton in the two-coordinate representation, without an
eigenvector or analytic spectral argument. -/
theorem stepPair_recurrence (R : ℕ) (p : ℂ × ℂ) :
    stepPair R (stepPair R p) =
      ((2 - (R : ℂ)⁻¹) * (stepPair R p).1 - p.1,
       (2 - (R : ℂ)⁻¹) * (stepPair R p).2 - p.2) := by
  have hmul : eta * conj eta = 1 := eta_mul_conj
  have hadd : eta + conj eta = 1 := eta_add_conj
  have hh : (1-conj eta)*(eta-1) = -1 := by
    calc
      _ = (eta + conj eta) - (eta * conj eta) - 1 := by ring
      _ = _ := by rw [hadd,hmul]; ring
  have hcomm : conj eta * eta = 1 := by rwa [mul_comm]
  have hx :
      (eta-1) * (p.1 + (1-conj eta)*((eta-1)*p.1+eta*p.2)/(R : ℂ)) +
        eta * (conj eta*((eta-1)*p.1+eta*p.2)) =
      (2-(R : ℂ)⁻¹)*((eta-1)*p.1+eta*p.2) - eta*p.2 := by
    calc
      _ = (eta-1)*p.1 +
        (((1-conj eta)*(eta-1))*(R : ℂ)⁻¹ + eta*conj eta) *
          ((eta-1)*p.1+eta*p.2) := by rw [div_eq_mul_inv]; ring
      _ = _ := by rw [hh,hmul]; ring
  apply Prod.ext
  · change (p.1 + (1-conj eta)*((eta-1)*p.1+eta*p.2)/(R : ℂ))
        + (1-conj eta)*((eta-1) *
            (p.1+(1-conj eta)*((eta-1)*p.1+eta*p.2)/(R : ℂ)) +
          eta*(conj eta*((eta-1)*p.1+eta*p.2)))/(R : ℂ) =
      (2-(R : ℂ)⁻¹) * (p.1+(1-conj eta)*((eta-1)*p.1+eta*p.2)/(R : ℂ)) - p.1
    rw [hx]
    have hh' : (1-conj eta)*((eta-1)*p.1) = -p.1 := by rw [← mul_assoc,hh,neg_one_mul]
    calc
      _ = p.1 + (1-conj eta)*((eta-1)*p.1)/(R : ℂ) +
        (2-(R : ℂ)⁻¹) * ((1-conj eta)*((eta-1)*p.1+eta*p.2)/(R : ℂ)) := by
          simp only [div_eq_mul_inv]; ring
      _ = _ := by rw [hh']; simp only [div_eq_mul_inv]; ring
  · change conj eta*((eta-1) *
          (p.1+(1-conj eta)*((eta-1)*p.1+eta*p.2)/(R : ℂ)) +
          eta*(conj eta*((eta-1)*p.1+eta*p.2))) =
      (2-(R : ℂ)⁻¹)*(conj eta*((eta-1)*p.1+eta*p.2)) - p.2
    rw [hx]
    calc
      _ = (2-(R : ℂ)⁻¹)*(conj eta*((eta-1)*p.1+eta*p.2)) -
          (conj eta*eta)*p.2 := by ring
      _ = _ := by rw [hcomm,one_mul]

noncomputable def pairAt (R : ℕ) : ℕ → ℂ × ℂ
  | 0 => (1,0)
  | s+1 => stepPair R (pairAt R s)

theorem avoid_vector_eq (hR : 0 < R) (r : Fin R) (s : ℕ) :
    opProduct s (fun _ => boxOp (avoid r)) (onesVec R) =
      plane r (pairAt R s).1 (pairAt R s).2 := by
  induction s with
  | zero => funext i; simp [opProduct,onesVec,pairAt,plane]
  | succ s ih =>
    rw [opProduct]
    change boxOp (avoid r) (opProduct s (fun _ => boxOp (avoid r)) (onesVec R)) = _
    rw [ih,avoid_op_plane hR,pairAt]

noncomputable def phaseValue (R s : ℕ) : ℝ :=
  ((pairAt R s).1 + (pairAt R s).2/(R : ℂ)).re

theorem avoid_score (hR : 0 < R) (r : Fin R) (s : ℕ) :
    score (opProduct s (fun _ => boxOp (avoid r))) = phaseValue R s := by
  unfold score phaseValue
  rw [avoid_vector_eq hR r s, avg_plane hR]

end PHP.Phase
