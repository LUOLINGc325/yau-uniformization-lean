import Yau.Proofs.C01TraceQuadraticAlgebra

/-! A nonnegative Ricci matrix is bounded by its actual metric trace.
The argument includes zero vectors, zero trace, and dimension zero. -/

noncomputable section

open scoped Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

theorem quadratic_le_traceWith_mul_metric {n : ℕ} (H A : Herm n)
    (hH : H.PosDef) (hA : A.PosSemidef) (v : Fin n → ℂ) :
    (star v ⬝ᵥ (A *ᵥ v)).re ≤ traceWith H A * (star v ⬝ᵥ (H *ᵥ v)).re := by
  let C : Herm n := (((star v ⬝ᵥ (H *ᵥ v)).re : ℝ) : ℂ) • H⁻¹ -
    Matrix.vecMulVec v (star v)
  have hunit : IsUnit H.det := hH.isUnit.map Matrix.detMonoidHom
  have hreal : (((star v ⬝ᵥ (H *ᵥ v)).re : ℝ) : ℂ) = star v ⬝ᵥ (H *ᵥ v) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im, RCLike.im_to_complex] using
        (hH.isHermitian.im_star_dotProduct_mulVec_self v).symm
  have hcross (u : Fin n → ℂ) : star (H *ᵥ v) ⬝ᵥ (H⁻¹ *ᵥ u) = star v ⬝ᵥ u := by
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      hH.isHermitian.eq, Matrix.mul_nonsing_inv H hunit, Matrix.vecMul_one]
  have hnorm : star (H *ᵥ v) ⬝ᵥ (H⁻¹ *ᵥ (H *ᵥ v)) =
      star v ⬝ᵥ (H *ᵥ v) := hcross (H *ᵥ v)
  have hC (u : Fin n → ℂ) : 0 ≤ (star u ⬝ᵥ (C *ᵥ u)).re := by
    have hcs := hH.inv.star_dotProduct_mulVec_mul_le (H *ᵥ v) u
    rw [hcross u, hnorm] at hcs
    have hnonneg := (Complex.nonneg_iff.mp (sub_nonneg.mpr hcs)).1
    have heq : star u ⬝ᵥ (C *ᵥ u) =
        (star v ⬝ᵥ (H *ᵥ v)) * (star u ⬝ᵥ (H⁻¹ *ᵥ u)) -
          star (star v ⬝ᵥ u) * (star v ⬝ᵥ u) := by
      dsimp only [C]
      rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul,
        smul_eq_mul, hreal, Matrix.vecMulVec_mulVec, op_smul_eq_smul,
        dotProduct_smul, smul_eq_mul, Matrix.star_dotProduct u v]
      ring
    rw [heq]
    exact hnonneg
  have hp := trace_mul_nonneg_of_real_quadratics A C hA hC
  have htrace : Matrix.trace (A * C) =
      (((star v ⬝ᵥ (H *ᵥ v)).re : ℝ) : ℂ) * Matrix.trace (H⁻¹ * A) -
        star v ⬝ᵥ (A *ᵥ v) := by
    dsimp only [C]
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul,
      Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, Matrix.trace_mul_comm A H⁻¹,
      dotProduct_comm (A *ᵥ v) (star v)]
  rw [htrace] at hp
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hp
  exact (sub_nonneg.mp hp).trans_eq (mul_comm _ _)

end Yau.NodeProofs.C01Aux
