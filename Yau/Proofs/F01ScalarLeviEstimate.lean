import Yau.Proofs.F01ScaledLeviChain
import Yau.Proofs.F01GradientQuadratic

/-! A quadratic estimate from the actual Levi and gradient of u; the
composition is differentiated by the genuine Hessian chain rule. -/
noncomputable section
open scoped ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ}

theorem scaled_scalar_levi_quadratic_bound
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    {u : ComplexVector n → ℝ} {F : ℝ → ℝ} {z : ComplexVector n}
    {L C r : ℝ} (hL : 0 < L) (hu : ContDiffAt ℝ 2 u z)
    (hF : ContDiffAt ℝ 2 F (u z / L))
    (hgrad : dualNormMat H (WithLp.toLp 2
      (fun i => wirt (fun w => (u w : ℂ)) z (stdVec i))) ≤ C ^ 2)
    (hlevi : ∀ v : ComplexVector n,
      |LeafProofs.L22Aux.complexLeviQuadratic u z v| ≤
        (C / r) * (star (WithLp.ofLp v) ⬝ᵥ (H *ᵥ WithLp.ofLp v)).re)
    (v : ComplexVector n) :
    |LeafProofs.L22Aux.complexLeviQuadratic (fun w => F (u w / L)) z v| ≤
      (|deriv F (u z / L)| / L * (C / r) +
        |deriv (deriv F) (u z / L)| / L ^ 2 * C ^ 2) *
          (star (WithLp.ofLp v) ⬝ᵥ (H *ᵥ WithLp.ofLp v)).re := by
  let q : ℝ := (star (WithLp.ofLp v) ⬝ᵥ (H *ᵥ WithLp.ofLp v)).re
  let A : ℝ := ((fderiv ℝ u z v) ^ 2 + (fderiv ℝ u z (Complex.I • v)) ^ 2) / 4
  have hq : 0 ≤ q := (Complex.nonneg_iff.mp
    (hH.posSemidef.dotProduct_mulVec_nonneg (WithLp.ofLp v))).1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hAb : A ≤ C ^ 2 * q :=
    (gradient_quadratic_cauchy H hH (hu.differentiableAt (by norm_num)) v).trans
      (mul_le_mul_of_nonneg_right hgrad hq)
  rw [complexLeviQuadratic_scaled_scalar_comp L hu hF]
  change |deriv F (u z / L) / L * LeafProofs.L22Aux.complexLeviQuadratic u z v +
    deriv (deriv F) (u z / L) / L ^ 2 * A| ≤ _
  calc
    _ ≤ |deriv F (u z / L) / L * LeafProofs.L22Aux.complexLeviQuadratic u z v| +
      |deriv (deriv F) (u z / L) / L ^ 2 * A| := abs_add_le _ _
    _ = (|deriv F (u z / L)| / L) *
        |LeafProofs.L22Aux.complexLeviQuadratic u z v| +
      (|deriv (deriv F) (u z / L)| / L ^ 2) * A := by
      rw [abs_mul, abs_mul, abs_div, abs_div, abs_of_pos hL,
        abs_of_nonneg (sq_nonneg L), abs_of_nonneg hA]
    _ ≤ (|deriv F (u z / L)| / L) * ((C / r) * q) +
      (|deriv (deriv F) (u z / L)| / L ^ 2) * (C ^ 2 * q) :=
      add_le_add (mul_le_mul_of_nonneg_left (hlevi v) (by positivity))
        (mul_le_mul_of_nonneg_left hAb (by positivity))
    _ = _ := by dsimp [q]; ring

end Yau.NodeProofs.F01Aux
