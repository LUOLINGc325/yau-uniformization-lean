import Yau.Proofs.F03TraceOrder
import Mathlib.Analysis.Normed.Lp.Matrix

/-! The actual Hermitian dual norm has a fixed linear square-root factor, hence the genuine integral triangle inequality. -/
noncomputable section
open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder
namespace Yau.Proofs.F03Aux
open Yau
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def dualNormFactor (H : Matrix (Fin n) (Fin n) ℂ) : ComplexVector n →L[ℝ] ComplexVector n := by
  let L : ComplexVector n →ₗ[ℝ] ComplexVector n :=
    (Matrix.toLpLin 2 2 (CFC.sqrt ((H⁻¹)ᵀ))).restrictScalars ℝ
  exact L.toContinuousLinearMap

theorem dualNormFactor_norm_sq (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) (ξ : ComplexVector n) :
    ‖dualNormFactor H ξ‖^2=dualNormMat H ξ := by
  let S := CFC.sqrt ((H⁻¹)ᵀ)
  have hS : S.IsHermitian :=
    ((Matrix.nonneg_iff_posSemidef).mp (CFC.sqrt_nonneg ((H⁻¹)ᵀ))).1
  have hSS : S*S=(H⁻¹)ᵀ := CFC.sqrt_mul_sqrt_self _ hH.inv.posSemidef.transpose.nonneg
  change ‖WithLp.toLp 2 (S *ᵥ WithLp.ofLp ξ)‖^2=dualNormMat H ξ
  rw [@norm_sq_eq_re_inner ℂ,EuclideanSpace.inner_eq_star_dotProduct]
  simp only [WithLp.ofLp_toLp]
  rw [dotProduct_comm,Matrix.star_mulVec,hS.eq,← Matrix.dotProduct_mulVec,Matrix.mulVec_mulVec,hSS]
  rfl

theorem dualNormFactor_norm (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) (ξ : ComplexVector n) :
    ‖dualNormFactor H ξ‖=Real.sqrt (dualNormMat H ξ) := by
  rw [← dualNormFactor_norm_sq H hH ξ,Real.sqrt_sq (norm_nonneg _)]

theorem sqrt_dualNormMat_integral_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (ξ : α → ComplexVector n) (hξ : Integrable ξ μ) :
    Real.sqrt (dualNormMat H (∫ a,ξ a ∂μ)) ≤ ∫ a,Real.sqrt (dualNormMat H (ξ a)) ∂μ := by
  rw [← dualNormFactor_norm H hH,← (dualNormFactor H).integral_comp_comm hξ]
  simpa only [dualNormFactor_norm H hH] using
    (norm_integral_le_integral_norm (f := fun a => dualNormFactor H (ξ a)))

end Yau.Proofs.F03Aux
