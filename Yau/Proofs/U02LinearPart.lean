import Yau.Proofs.U02PolynomialRemainder

/-! Identify the actual derivative and the inverse linear matrix of a
polynomial automorphism from its coefficients. -/

open scoped Topology ContDiff Matrix
open Filter Asymptotics

noncomputable section
namespace Yau.NodeProofs.U02Proof

open Yau Blueprint
open Yau.Proofs.Y02Aux

theorem polynomial_fixesZero_iff_eval_zero {n : ℕ} (P : PolyMap n) :
    P.FixesZero ↔ P.eval 0 = 0 := by
  constructor
  · intro h
    ext i
    simpa [PolyMap.eval, MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq] using h i
  · intro h i
    have hh := congrArg (fun z : ComplexVector n => z i) h
    simpa [PolyMap.eval, MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq] using hh

theorem polynomial_hasFDerivAt_zero {n : ℕ} (P : PolyMap n) (hP : P.FixesZero) :
    HasFDerivAt P.eval (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) P.linearPart) 0 := by
  let A := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) P.linearPart
  have hbound : (fun z : ComplexVector n => P.eval z - A z) =O[𝓝 0]
      (fun z => ‖z‖ ^ 2) := by
    apply isBigO_iff.mpr
    refine ⟨2 * P.coeffNorm, ?_⟩
    filter_upwards [Metric.ball_mem_nhds (0 : ComplexVector n) zero_lt_one] with z hz
    have hnorm : ‖z‖ ≤ 1 :=
      (show ‖z‖ < 1 by simpa only [Metric.mem_ball, dist_zero_right] using hz).le
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖z‖)] using
      polynomial_quadratic_error P hP hnorm
  have hlittle := hbound.trans_isLittleO (isLittleO_norm_pow_id one_lt_two)
  have hzero : P.eval 0 = 0 := (polynomial_fixesZero_iff_eval_zero P).mp hP
  simpa only [hasFDerivAt_iff_isLittleO_nhds_zero, zero_add, hzero, sub_zero]
    using! hlittle

theorem polynomial_fderiv_zero {n : ℕ} (P : PolyMap n) (hP : P.FixesZero) :
    fderiv ℂ P.eval 0 = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) P.linearPart :=
  (polynomial_hasFDerivAt_zero P hP).fderiv

theorem polynomial_comp_fixesZero {n : ℕ} {P Q : PolyMap n}
    (hP : P.FixesZero) (hQ : Q.FixesZero) : (P.comp Q).FixesZero := by
  apply (polynomial_fixesZero_iff_eval_zero _).mpr
  rw [polynomial_eval_comp, (polynomial_fixesZero_iff_eval_zero Q).mp hQ,
    (polynomial_fixesZero_iff_eval_zero P).mp hP]

theorem polynomial_linearPart_comp {n : ℕ} (P Q : PolyMap n)
    (hP : P.FixesZero) (hQ : Q.FixesZero) :
    (P.comp Q).linearPart = P.linearPart * Q.linearPart := by
  let A := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
  have hQzero := (polynomial_fixesZero_iff_eval_zero Q).mp hQ
  have hderP : HasFDerivAt P.eval (A P.linearPart) (Q.eval 0) := by
    rw [hQzero]
    exact polynomial_hasFDerivAt_zero P hP
  have hc := hderP.comp 0 (polynomial_hasFDerivAt_zero Q hQ)
  have hd := polynomial_hasFDerivAt_zero (P.comp Q) (polynomial_comp_fixesZero hP hQ)
  have heval : (P.comp Q).eval = P.eval ∘ Q.eval := funext (polynomial_eval_comp P Q)
  rw [heval] at hd
  have heq := hd.unique hc
  apply A.injective
  rw [map_mul]
  exact heq

theorem automorphism_inverse_fixesZero {n : ℕ} {P Q : PolyMap n}
    (h : IsPolyAutomorphism P Q) (hP : P.FixesZero) : Q.FixesZero := by
  apply (polynomial_fixesZero_iff_eval_zero Q).mpr
  have hh : Q.eval (P.eval 0) = 0 := by
    rw [← polynomial_eval_comp, h.2, polynomial_eval_id]
  rwa [(polynomial_fixesZero_iff_eval_zero P).mp hP] at hh

theorem automorphism_inverse_linearPart {n : ℕ} {P Q : PolyMap n}
    (h : IsPolyAutomorphism P Q) (hP : P.FixesZero) :
    Q.linearPart = P.linearPart⁻¹ := by
  have hQ := automorphism_inverse_fixesZero h hP
  have hid : (PolyMap.id : PolyMap n).linearPart = 1 := by
    rw [← linearPoly_one, linearPoly_linearPart]
  have hleft : Q.linearPart * P.linearPart = 1 := by
    rw [← polynomial_linearPart_comp Q P hQ hP, h.2, hid]
  exact (Matrix.inv_eq_left_inv hleft).symm

end Yau.NodeProofs.U02Proof
