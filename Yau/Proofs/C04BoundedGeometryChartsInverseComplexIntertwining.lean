import Yau.Proofs.C04BoundedGeometryChartsNormalizedInverseParameter
import Yau.Geometry.Basic

/-! The same inverse and its normalized parameter preserve the actual complex structure. -/
noncomputable section
open scoped Topology ContDiff
namespace Yau.Proofs.C04ChartsAux
open Yau
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

theorem inverse_fderiv_intertwines (e : OpenPartialHomeomorph (ComplexVector n) (ComplexVector n))
    (F : ComplexVector n → ComplexVector n) (he : (e : ComplexVector n → ComplexVector n) = F)
    (hF : ContDiff ℝ ∞ F) (J : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n)
    (w : ComplexVector n) (hw : w ∈ e.target)
    (hi : (fderiv ℝ F (e.symm w)).IsInvertible)
    (hrel : ∀ v, fderiv ℝ F (e.symm w) (J (e.symm w) v) = Complex.I • fderiv ℝ F (e.symm w) v)
    (v : ComplexVector n) :
    fderiv ℝ e.symm w (Complex.I • v) = J (e.symm w) (fderiv ℝ e.symm w v) := by
  obtain ⟨D, hD⟩ := hi
  have hDF : HasFDerivAt e (D : ComplexVector n →L[ℝ] ComplexVector n) (e.symm w) := by
    rw [he, hD]
    exact (hF.differentiable (by simp) _).hasFDerivAt
  have hψ := e.hasFDerivAt_symm hw hDF
  rw [hψ.fderiv]
  apply D.injective
  simp only [ContinuousLinearEquiv.coe_coe]
  rw [D.apply_symm_apply]
  have H := hrel (D.symm v)
  rw [← hD] at H
  simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using H.symm

section Generic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem normalizedInverseParameter_fderiv (e : OpenPartialHomeomorph E E) (L : E →L[ℝ] E)
    {d : ℝ} (hd : d ≠ 0) (z : E)
    (hψ : DifferentiableAt ℝ e.symm (d⁻¹ • L z)) :
    fderiv ℝ (normalizedInverseParameter e L d) z = (fderiv ℝ e.symm (d⁻¹ • L z)).comp L := by
  let T : E →L[ℝ] E := d⁻¹ • L
  have hT : HasFDerivAt (fun y => d⁻¹ • L y) T z := T.hasFDerivAt
  have H := (hψ.hasFDerivAt.comp z hT).const_smul d
  have hder : d • ((fderiv ℝ e.symm (d⁻¹ • L z)).comp T) =
      (fderiv ℝ e.symm (d⁻¹ • L z)).comp L := by
    apply ContinuousLinearMap.ext
    intro v
    change d • fderiv ℝ e.symm (d⁻¹ • L z) (d⁻¹ • L v) = fderiv ℝ e.symm (d⁻¹ • L z) (L v)
    rw [map_smul, smul_smul, mul_inv_cancel₀ hd, one_smul]
  rw [hder] at H
  exact H.fderiv
end Generic

theorem normalizedInverseParameter_intertwines
    (e : OpenPartialHomeomorph (ComplexVector n) (ComplexVector n))
    (F : ComplexVector n → ComplexVector n) (he : (e : ComplexVector n → ComplexVector n) = F)
    (hF : ContDiff ℝ ∞ F) (J : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n)
    (L : ComplexVector n →L[ℝ] ComplexVector n)
    (hL : ∀ v, L (Complex.I • v) = Complex.I • L v) {d : ℝ} (hd : d ≠ 0)
    (z : ComplexVector n) (hw : d⁻¹ • L z ∈ e.target)
    (hi : (fderiv ℝ F (e.symm (d⁻¹ • L z))).IsInvertible)
    (hrel : ∀ v, fderiv ℝ F (e.symm (d⁻¹ • L z)) (J (e.symm (d⁻¹ • L z)) v) =
      Complex.I • fderiv ℝ F (e.symm (d⁻¹ • L z)) v)
    (v : ComplexVector n) :
    fderiv ℝ (normalizedInverseParameter e L d) z (Complex.I • v) =
      J (e.symm (d⁻¹ • L z)) (fderiv ℝ (normalizedInverseParameter e L d) z v) := by
  obtain ⟨D, hD⟩ := hi
  have hDF : HasFDerivAt e (D : ComplexVector n →L[ℝ] ComplexVector n) (e.symm (d⁻¹ • L z)) := by
    rw [he, hD]
    exact (hF.differentiable (by simp) _).hasFDerivAt
  have hψ := (e.hasFDerivAt_symm hw hDF).differentiableAt
  rw [normalizedInverseParameter_fderiv e L hd z hψ]
  simp only [ContinuousLinearMap.comp_apply, hL]
  exact inverse_fderiv_intertwines e F he hF J _ hw ⟨D, hD⟩ hrel (L v)

end Yau.Proofs.C04ChartsAux
