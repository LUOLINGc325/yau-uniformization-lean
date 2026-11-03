import Yau.Proofs.U02SmallPolynomials
import Yau.Proofs.Y02Linear
import Yau.Proofs.V02FlowUniformLimit

/-! The quadratic error and its actual Fréchet derivative on small balls.
These estimates retain the fixed linear part used in the injectivity argument. -/

open scoped Topology ContDiff Matrix

noncomputable section
namespace Yau.NodeProofs.U02Proof

open Yau Blueprint
open Yau.Proofs.Y02Aux

theorem linearPoly_eval {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (z : ComplexVector n) :
    (linearPoly A).eval z = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A z := by
  ext i
  simp [linearPoly, linearForm, PolyMap.eval, Matrix.ofLp_toEuclideanCLM,
    Matrix.mulVec, dotProduct]

theorem polynomial_eval_sub {n : ℕ} (P Q : PolyMap n) (z : ComplexVector n) :
    (P - Q).eval z = P.eval z - Q.eval z := by
  ext i
  simp [PolyMap.eval]

def nonlinearPart {n : ℕ} (P : PolyMap n) : PolyMap n := P - linearPoly P.linearPart

theorem nonlinearPart_low_coeff {n : ℕ} (P : PolyMap n) (hP : P.FixesZero)
    (i : Fin n) (m : Fin n →₀ ℕ) (hm : (m.sum fun _ e => e) < 2) :
    (nonlinearPart P i).coeff m = 0 := by
  change (P i).coeff m - (linearPoly P.linearPart i).coeff m = 0
  by_cases hm0 : m = 0
  · subst m
    rw [hP i, linearPoly_fixesZero P.linearPart i, sub_self]
  · have hdegree : m.sum (fun _ e => e) = 1 := by
      have hpos : 0 < m.sum (fun _ e => e) :=
        Finsupp.sum_pos (fun j hj => Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hj)) hm0
      omega
    obtain ⟨j, rfl⟩ := (Finsupp.sum_eq_one_iff m).mp hdegree
    simp only [linearPoly, linearForm_coeff_single, PolyMap.linearPart, sub_self]

theorem nonlinearPart_coeffNorm_le {n : ℕ} (P : PolyMap n) :
    (nonlinearPart P).coeffNorm ≤ 2 * P.coeffNorm := by
  have h := coeffNorm_sub_le P (linearPoly P.linearPart)
  have hl := linearPoly_linearPart_coeffNorm_le P
  dsimp [nonlinearPart]
  linarith

theorem polynomial_quadratic_error {n : ℕ} (P : PolyMap n) (hP : P.FixesZero)
    {z : ComplexVector n} (hz : ‖z‖ ≤ 1) :
    ‖P.eval z - Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) P.linearPart z‖ ≤
      2 * P.coeffNorm * ‖z‖ ^ 2 := by
  rw [← linearPoly_eval, ← polynomial_eval_sub]
  exact (polynomial_norm_le (q := 2) (nonlinearPart P)
    (nonlinearPart_low_coeff P hP) hz).trans
      (mul_le_mul_of_nonneg_right (nonlinearPart_coeffNorm_le P) (sq_nonneg _))

/-- The constant is uniform over the complete smaller closed ball, and the
derivative is the actual complex Fréchet derivative. -/
theorem polynomial_derivative_error {n : ℕ} (P : PolyMap n) (hP : P.FixesZero)
    {r : ℝ} (hr : 0 < r) (hr1 : 2 * r ≤ 1)
    {y : ComplexVector n} (hy : y ∈ Metric.closedBall 0 r) :
    ‖fderiv ℂ P.eval y - Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) P.linearPart‖ ≤
      8 * P.coeffNorm * r := by
  have hcoeff : 0 ≤ P.coeffNorm := coeffNorm_nonneg P
  let L := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) P.linearPart
  have hL : (linearPoly P.linearPart).eval = L := funext (linearPoly_eval _)
  have hbound : ∀ z ∈ Metric.closedBall (0 : ComplexVector n) (2 * r),
      ‖P.eval z - (linearPoly P.linearPart).eval z‖ ≤
        2 * P.coeffNorm * (2 * r) ^ 2 := by
    intro z hz
    have hzr : ‖z‖ ≤ 2 * r := by simpa using hz
    rw [linearPoly_eval]
    exact (polynomial_quadratic_error P hP (hzr.trans hr1)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hzr 2)
        (by positivity))
  have hc := V02FlowProof.norm_fderiv_sub_le_of_cauchy isOpen_univ
    ((polynomial_contDiff P).differentiable (by simp)).differentiableOn
    ((polynomial_contDiff (linearPoly P.linearPart)).differentiable (by simp)).differentiableOn
    hr (by positivity : 0 ≤ 2 * P.coeffNorm * (2 * r) ^ 2)
    (by intro z hz; trivial : Metric.closedBall (0 : ComplexVector n) (2 * r) ⊆ Set.univ)
    hbound hy
  rw [hL, L.fderiv] at hc
  apply hc.trans_eq
  field_simp [hr.ne']
  ring

end Yau.NodeProofs.U02Proof
