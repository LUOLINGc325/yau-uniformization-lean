import Yau.Proofs.Y06StrictWeight
import Yau.Proofs.Y06DiagonalCoefficients

/-! A true polynomial inverse obtained by finite substitution in strict
weight rank. A constant determinant alone is never used to assert inversion. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open MvPolynomial Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux
open Yau.Blueprint.Alignment.Y03Proof

variable {n : ℕ}

theorem strict_variables_comp_congr (N : PolyMap n) (w : Fin n → ℝ)
    (hN : ∀ i j, j ∈ (N i).vars → w j < w i) (U V : PolyMap n) (i : Fin n)
    (hUV : ∀ j, w j < w i → U j = V j) : (N.comp U) i = (N.comp V) i := by
  change aeval U (N i) = aeval V (N i)
  rw [aeval_eq_eval₂Hom, aeval_eq_eval₂Hom]
  apply eval₂Hom_congr' rfl _ rfl
  intro j hj hj'
  exact hUV j (hN i j hj)

def triangularInverseApprox (P : PolyMap n) (a : Fin n → ℂ) : ℕ → PolyMap n
  | 0 => 0
  | r + 1 => (linearPolynomial (Matrix.diagonal (fun i => (a i)⁻¹))).comp
      (PolyMap.id - (nonlinearPart P).comp (triangularInverseApprox P a r))

theorem triangularInverseApprox_succ_apply (P : PolyMap n) (a : Fin n → ℂ) (r : ℕ) (i : Fin n) :
    triangularInverseApprox P a (r + 1) i =
      C ((a i)⁻¹) * (X i - ((nonlinearPart P).comp (triangularInverseApprox P a r)) i) := by
  change ((linearPoly (Matrix.diagonal (fun i => (a i)⁻¹))).comp
    (PolyMap.id - (nonlinearPart P).comp (triangularInverseApprox P a r))) i = _
  rw [linearPoly_comp_apply]
  simp [Matrix.diagonal_apply, apply_ite, PolyMap.id]

theorem triangularInverseApprox_stable (P : PolyMap n) (a : Fin n → ℂ) (w : Fin n → ℝ)
    (hN : ∀ i j, j ∈ (nonlinearPart P i).vars → w j < w i) :
    ∀ r i, weightRank w i < r → triangularInverseApprox P a (r + 1) i = triangularInverseApprox P a r i := by
  intro r
  induction r with
  | zero => intro i hi; omega
  | succ r ih =>
    intro i hi
    rw [triangularInverseApprox_succ_apply, triangularInverseApprox_succ_apply]
    have htail : ((nonlinearPart P).comp (triangularInverseApprox P a (r + 1))) i =
        ((nonlinearPart P).comp (triangularInverseApprox P a r)) i := by
      apply strict_variables_comp_congr (nonlinearPart P) w hN
      intro j hj
      apply ih j
      have hrank := weightRank_strict hj
      omega
    rw [htail]

theorem comp_nonlinear_decomposition (P Q : PolyMap n) (a : Fin n → ℂ)
    (hlinear : P.linearPart = Matrix.diagonal a) (i : Fin n) :
    P.comp Q i = C (a i) * Q i + (nonlinearPart P).comp Q i := by
  have hsplit : P i = linearPolynomial P.linearPart i + nonlinearPart P i := by
    change P i = linearPolynomial P.linearPart i + (P i - linearPolynomial P.linearPart i)
    abel
  change bind₁ Q (P i) = _
  rw [hsplit, map_add]
  have hleft : bind₁ Q (linearPolynomial P.linearPart i) = C (a i) * Q i := by
    change ((linearPoly P.linearPart).comp Q) i = _
    rw [hlinear, linearPoly_comp_apply]
    simp [Matrix.diagonal_apply, apply_ite]
  rw [hleft]
  rfl

theorem strict_triangular_comp_cancel (P : PolyMap n) (a : Fin n → ℂ) (w : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) (hlinear : P.linearPart = Matrix.diagonal a)
    (hN : ∀ i j, j ∈ (nonlinearPart P i).vars → w j < w i)
    {U V : PolyMap n} (heq : P.comp U = P.comp V) : U = V := by
  have hcoord : ∀ r i, weightRank w i = r → U i = V i := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro i hi
      have htail : (nonlinearPart P).comp U i = (nonlinearPart P).comp V i := by
        apply strict_variables_comp_congr (nonlinearPart P) w hN
        intro j hj
        exact ih (weightRank w j) (by have := weightRank_strict hj; omega) j rfl
      have h := congrFun heq i
      rw [comp_nonlinear_decomposition P U a hlinear,
        comp_nonlinear_decomposition P V a hlinear, htail] at h
      exact mul_left_cancel₀ (C_ne_zero.mpr (ha i)) (add_right_cancel h)
  funext i
  exact hcoord (weightRank w i) i rfl

theorem strict_triangular_inverse (P : PolyMap n) (a : Fin n → ℂ) (w : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) (hlinear : P.linearPart = Matrix.diagonal a)
    (hN : ∀ i j, j ∈ (nonlinearPart P i).vars → w j < w i) :
    IsPolyAutomorphism P (triangularInverseApprox P a n) := by
  let Q := triangularInverseApprox P a n
  have hstable : triangularInverseApprox P a (n + 1) = Q := by
    funext i
    exact triangularInverseApprox_stable P a w hN n i (weightRank_lt w i)
  have hfixed i : Q i = C ((a i)⁻¹) * (X i - (nonlinearPart P).comp Q i) := by
    have h := congrFun hstable i
    rw [triangularInverseApprox_succ_apply] at h
    exact h.symm
  have hleft : P.comp Q = PolyMap.id := by
    funext i
    rw [comp_nonlinear_decomposition P Q a hlinear, hfixed i]
    change C (a i) * (C ((a i)⁻¹) * (X i - (nonlinearPart P).comp Q i)) +
      (nonlinearPart P).comp Q i = X i
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ (ha i), map_one, one_mul]
    exact sub_add_cancel _ _
  refine ⟨hleft, ?_⟩
  apply strict_triangular_comp_cancel P a w ha hlinear hN
  rw [← comp_assoc, hleft, id_comp, comp_id]

theorem allowed_polynomial_automorphism (P : PolyMap n) (a : Fin n → ℂ) (w : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) (hlinear : P.linearPart = Matrix.diagonal a)
    (hP : P.FixesZero) (hallowed : Allowed P w) (hw : ∀ i, 1 ≤ w i) :
    IsPolyAutomorphism P (triangularInverseApprox P a n) :=
  strict_triangular_inverse P a w ha hlinear (nonlinearPart_strict_variables hP hallowed hw)

end Yau.Proofs.Y06Aux
