import Yau.Proofs.Y06Homogeneous

/-! The complementary allowed projection used in each homogeneous layer. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open MvPolynomial Yau.Blueprint Yau.Blueprint.Alignment

variable {n m : ℕ}

def allowedProjection (w : Fin n → ℝ) (P : PolyMap n) : PolyMap n :=
  P - forbiddenProjection w P

theorem allowedProjection_coeff (w : Fin n → ℝ) (P : PolyMap n)
    (i : Fin n) (β : Fin n →₀ ℕ) :
    (allowedProjection w P i).coeff β =
      if w i < ∑ l, (β l : ℝ) * w l then 0 else (P i).coeff β := by
  classical
  change (P i).coeff β - (forbiddenProjection w P i).coeff β = _
  rw [forbiddenProjection_coeff]
  split_ifs <;> simp

theorem allowed_forbidden_sum (w : Fin n → ℝ) (P : PolyMap n) :
    allowedProjection w P + forbiddenProjection w P = P := sub_add_cancel P _

theorem allowedProjection_allowed (w : Fin n → ℝ) (P : PolyMap n) :
    Allowed (allowedProjection w P) w := by
  intro i β hdegree hβ
  rw [allowedProjection_coeff] at hβ
  by_contra hnot
  exact hβ (ite_eq_left (lt_of_not_ge hnot))

theorem allowedProjection_homogeneous (w : Fin n → ℝ) {P : PolyMap n}
    (hP : Homogeneous P m) : Homogeneous (allowedProjection w P) m := by
  intro i β hβ
  rw [allowedProjection_coeff] at hβ
  split_ifs at hβ
  · exact False.elim (hβ rfl)
  · exact hP i β hβ

theorem allowedProjection_coeffNorm (w : Fin n → ℝ) (P : PolyMap n) :
    (allowedProjection w P).coeffNorm ≤ P.coeffNorm := by
  have h : (allowedProjection w P).coeffNorm ≤ 1 * P.coeffNorm := by
    apply coeffNorm_le_of_coeff_bound
    intro i β
    rw [allowedProjection_coeff]
    split_ifs <;> simp
  simpa only [one_mul] using h

theorem forbiddenProjection_add (w : Fin n → ℝ) (P Q : PolyMap n) :
    forbiddenProjection w (P + Q) = forbiddenProjection w P + forbiddenProjection w Q := by
  classical
  funext i
  ext β
  by_cases hf : w i < ∑ l, (β l : ℝ) * w l <;>
    simp [forbiddenProjection_coeff, hf]

end Yau.Proofs.Y06Aux
