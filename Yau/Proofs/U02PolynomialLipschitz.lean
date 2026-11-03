import Yau.Proofs.U02PolynomialRemainder

/-! Integrate only the nonlinear error and retain the fixed linear part.
This supplies both the inverse tube bound and the raw separation argument. -/

open scoped Topology ContDiff Matrix
open Metric

noncomputable section
namespace Yau.NodeProofs.U02Proof

open Yau Blueprint

theorem polynomial_linear_error_difference {n : ℕ} (P : PolyMap n) (hP : P.FixesZero)
    {r : ℝ} (hr : 0 < r) (hr1 : 2 * r ≤ 1)
    {u v : ComplexVector n} (hu : u ∈ closedBall 0 r) (hv : v ∈ closedBall 0 r) :
    ‖P.eval u - P.eval v -
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) P.linearPart (u - v)‖ ≤
      (8 * P.coeffNorm * r) * ‖u - v‖ := by
  exact (convex_closedBall (0 : ComplexVector n) r).norm_image_sub_le_of_norm_fderiv_le'
    (fun x _ => (polynomial_contDiff P).differentiable (by simp) x)
    (fun x hx => polynomial_derivative_error P hP hr hr1 hx) hv hu

theorem polynomial_lipschitz_small_ball {n : ℕ} (P : PolyMap n) (hP : P.FixesZero)
    {r : ℝ} (hr : 0 < r) (hr1 : 2 * r ≤ 1)
    {u v : ComplexVector n} (hu : u ∈ closedBall 0 r) (hv : v ∈ closedBall 0 r) :
    ‖P.eval u - P.eval v‖ ≤
      (matOpNorm P.linearPart + 8 * P.coeffNorm * r) * ‖u - v‖ := by
  have hder : ∀ x ∈ closedBall (0 : ComplexVector n) r,
      ‖fderiv ℂ P.eval x‖ ≤ matOpNorm P.linearPart + 8 * P.coeffNorm * r := by
    intro x hx
    have hd := polynomial_derivative_error P hP hr hr1 hx
    have ht := norm_le_norm_sub_add (fderiv ℂ P.eval x)
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) P.linearPart)
    change ‖fderiv ℂ P.eval x‖ ≤ _
    dsimp [matOpNorm]
    linarith
  exact (convex_closedBall (0 : ComplexVector n) r).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => (polynomial_contDiff P).differentiable (by simp) x) hder hv hu

theorem polynomial_lower_distance {n : ℕ} (P : PolyMap n) (hP : P.FixesZero)
    (hdet : P.linearPart.det ≠ 0) {r : ℝ} (hr : 0 < r) (hr1 : 2 * r ≤ 1)
    (hsmall : matOpNorm P.linearPart⁻¹ * (8 * P.coeffNorm * r) ≤ 1 / 2)
    {u v : ComplexVector n} (hu : u ∈ closedBall 0 r) (hv : v ∈ closedBall 0 r) :
    ‖u - v‖ ≤ 2 * matOpNorm P.linearPart⁻¹ * ‖P.eval u - P.eval v‖ := by
  let A := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) P.linearPart
  let Ai := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) P.linearPart⁻¹
  let K := matOpNorm P.linearPart⁻¹
  have hK : 0 ≤ K := norm_nonneg Ai
  have hmul : Ai * A = 1 := by
    change Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) P.linearPart⁻¹ *
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) P.linearPart = 1
    rw [← map_mul, Matrix.nonsing_inv_mul P.linearPart (isUnit_iff_ne_zero.mpr hdet), map_one]
  have hrecover : Ai (A (u - v)) = u - v := by
    change (Ai * A) (u - v) = u - v
    rw [hmul]
    rfl
  have hlower : ‖u - v‖ ≤ K * ‖A (u - v)‖ := by
    calc
      ‖u - v‖ = ‖Ai (A (u - v))‖ := congrArg norm hrecover.symm
      _ ≤ K * ‖A (u - v)‖ := Ai.le_opNorm (A (u - v))
  have he := polynomial_linear_error_difference P hP hr hr1 hu hv
  have htri : ‖A (u - v)‖ ≤ ‖P.eval u - P.eval v‖ +
      ‖P.eval u - P.eval v - A (u - v)‖ := by
    have hh := norm_sub_le (P.eval u - P.eval v)
      (P.eval u - P.eval v - A (u - v))
    have heq : P.eval u - P.eval v - (P.eval u - P.eval v - A (u - v)) =
        A (u - v) := by abel
    simpa only [heq] using hh
  have hbound := mul_le_mul_of_nonneg_left (htri.trans (add_le_add le_rfl he)) hK
  have hpaid := mul_le_mul_of_nonneg_right hsmall (norm_nonneg (u - v))
  change ‖u - v‖ ≤ 2 * K * ‖P.eval u - P.eval v‖
  dsimp only [K] at hK hlower hbound ⊢
  nlinarith

end Yau.NodeProofs.U02Proof
