import Yau.Proofs.C04BoundedGeometryChartsActualMetric

/-! The same inverse parameter gives exactly the identity Hermitian matrix at the center. -/
noncomputable section
open scoped Topology Manifold ContDiff InnerProductSpace
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.Blueprint Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5

theorem stdVec_inner (a b : Fin n) :
    ⟪stdVec a, stdVec b⟫_ℂ = (1 : Matrix (Fin n) (Fin n) ℂ) a b := by
  simp [stdVec, EuclideanSpace.inner_single_left,
    Matrix.one_apply]

theorem normalChartMap_unitary_center (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (hU : ∀ i j, (g.form p).toFun (U (stdVec i)) (U (stdVec j)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) i j)
    (e : OpenPartialHomeomorph (ComplexVector n) (ComplexVector n))
    (F : ComplexVector n → ComplexVector n) (he : (e : ComplexVector n → ComplexVector n) = F)
    (hF : ContDiff ℝ ∞ F) (h0 : e.symm 0 = 0) (ht : (0 : ComplexVector n) ∈ e.target)
    (hi : (fderiv ℝ F 0).IsInvertible) {d : ℝ} (hd : d ≠ 0)
    (hf : MDifferentiableAt (ComplexModel n) (ComplexModel n)
      (normalChartMap g p U e (fderiv ℝ F 0) d) 0) :
    pullbackMat g.form (normalChartMap g p U e (fderiv ℝ F 0) d) 0 = 1 := by
  have hα := normalizedInverseParameter_hasFDerivAt_zero e F he hF h0 ht hi hd
  ext a b
  rw [normalChartMap_pullback_entry g p U hU e (fderiv ℝ F 0) d 0 a b hα.differentiableAt hf,
    normalizedInverseParameter_zero e _ d h0, radialCoframe_zero,
    hα.fderiv]
  simp only [ContinuousLinearMap.id_apply, C04Aux.normalModelMetric_apply,
    complexVector_real_inner, inner_smul_right, stdVec_inner]
  by_cases hab : a = b
  · subst b
    norm_num [Matrix.one_apply]
  · norm_num [Matrix.one_apply, hab]

end Yau.Proofs.C04ChartsAux
