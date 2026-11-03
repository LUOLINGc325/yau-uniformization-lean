import Yau.Proofs.C04BoundedGeometryChartsActualTangent

/-! The actual chart differential is invertible, using the derivative of the same inverse. -/
noncomputable section
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

theorem normalizedInverseParameter_deriv_invertible
    (e : OpenPartialHomeomorph (ComplexVector n) (ComplexVector n))
    (F : ComplexVector n → ComplexVector n) (he : (e : ComplexVector n → ComplexVector n) = F)
    (hF : ContDiff ℝ ∞ F) (L : ComplexVector n →L[ℝ] ComplexVector n)
    (hL : L.IsInvertible) {d : ℝ} (hd : d ≠ 0) (z : ComplexVector n)
    (hw : d⁻¹ • L z ∈ e.target)
    (hi : (fderiv ℝ F (e.symm (d⁻¹ • L z))).IsInvertible) :
    (fderiv ℝ (normalizedInverseParameter e L d) z).IsInvertible := by
  obtain ⟨D, hD⟩ := hi
  have hDF : HasFDerivAt e (D : ComplexVector n →L[ℝ] ComplexVector n)
      (e.symm (d⁻¹ • L z)) := by
    rw [he, hD]
    exact (hF.differentiable (by simp) _).hasFDerivAt
  have hψ := e.hasFDerivAt_symm hw hDF
  rw [normalizedInverseParameter_fderiv e L hd z hψ.differentiableAt, hψ.fderiv]
  exact ContinuousLinearMap.isInvertible_equiv.comp hL

theorem normalChartMap_real_deriv_invertible (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (e : OpenPartialHomeomorph (ComplexVector n) (ComplexVector n))
    (L : ComplexVector n →L[ℝ] ComplexVector n) (d : ℝ) (z : ComplexVector n)
    (hparam : DifferentiableAt ℝ (normalizedInverseParameter e L d) z)
    (hα : (fderiv ℝ (normalizedInverseParameter e L d) z).IsInvertible)
    (hE : (realMapDeriv (unitaryExponential g p U) (normalizedInverseParameter e L d z)).IsInvertible) :
    (realMapDeriv (normalChartMap g p U e L d) z).IsInvertible := by
  letI := manifold_realSmooth M
  change (realMapDeriv (fun y => unitaryExponential g p U (normalizedInverseParameter e L d y)) z).IsInvertible
  rw [realMapDeriv_comp _ _ z ((unitaryExponential_smooth g p U).mdifferentiableAt (by simp)) hparam]
  exact hE.comp hα

theorem normalChartMap_complex_deriv_bijective (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (e : OpenPartialHomeomorph (ComplexVector n) (ComplexVector n))
    (L : ComplexVector n →L[ℝ] ComplexVector n) (d : ℝ) (z : ComplexVector n)
    (hf : MDifferentiableAt (ComplexModel n) (ComplexModel n) (normalChartMap g p U e L d) z)
    (hparam : DifferentiableAt ℝ (normalizedInverseParameter e L d) z)
    (hα : (fderiv ℝ (normalizedInverseParameter e L d) z).IsInvertible)
    (hE : (realMapDeriv (unitaryExponential g p U) (normalizedInverseParameter e L d z)).IsInvertible) :
    Function.Bijective (mfderiv (ComplexModel n) (ComplexModel n) (normalChartMap g p U e L d) z) :=
  complex_mfderiv_bijective_of_real _ z hf
    (normalChartMap_real_deriv_invertible g p U e L d z hparam hα hE)

end Yau.Proofs.C04ChartsAux
