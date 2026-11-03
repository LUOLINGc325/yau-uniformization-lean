import Yau.Proofs.C04BoundedGeometryChartsActualTangent
import Yau.Blueprint.Stages

/-! The Gram model is the actual pullback metric of the same normalized chart. -/
noncomputable section
open scoped Topology Manifold ContDiff InnerProductSpace
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.Blueprint Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5

theorem normalChartMap_realMetric (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (hU : ∀ i j, (g.form p).toFun (U (stdVec i)) (U (stdVec j)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) i j)
    (e : OpenPartialHomeomorph (ComplexVector n) (ComplexVector n))
    (L : ComplexVector n →L[ℝ] ComplexVector n) (d : ℝ) (z u v : ComplexVector n)
    (hparam : DifferentiableAt ℝ (normalizedInverseParameter e L d) z) :
    (underlyingRealRiemannianMetric g.form).inner (normalChartMap g p U e L d z)
      (realMapDeriv (normalChartMap g p U e L d) z u)
      (realMapDeriv (normalChartMap g p U e L d) z v) =
      C04Aux.normalModelMetric (radialCoframe g p U (normalizedInverseParameter e L d z))
        (fderiv ℝ (normalizedInverseParameter e L d) z u)
        (fderiv ℝ (normalizedInverseParameter e L d) z v) := by
  letI := manifold_realSmooth M
  have hD := realMapDeriv_comp (unitaryExponential g p U)
    (normalizedInverseParameter e L d) z
    ((unitaryExponential_smooth g p U).mdifferentiableAt (by simp)) hparam
  change realMapDeriv (normalChartMap g p U e L d) z = _ at hD
  have hpoint (w : ComplexVector n) : realMapDeriv (normalChartMap g p U e L d) z w =
      radialParallelFrame g p U (normalizedInverseParameter e L d z)
        (radialCoframe g p U (normalizedInverseParameter e L d z)
          (fderiv ℝ (normalizedInverseParameter e L d) z w)) := by
    calc
      _ = realMapDeriv (unitaryExponential g p U) (normalizedInverseParameter e L d z)
          (fderiv ℝ (normalizedInverseParameter e L d) z w) :=
        congrArg (fun T : ComplexVector n →L[ℝ]
          TangentSpace 𝓘(ℝ, ComplexVector n) (normalChartMap g p U e L d z) => T w) hD
      _ = _ := (radialParallelFrame_radialCoframe g p U _ _).symm
  change (underlyingRealRiemannianMetric g.form).inner
    (unitaryExponential g p U (normalizedInverseParameter e L d z)) _ _ = _
  rw [hpoint u, hpoint v]
  rw [radialParallelFrame_metric g p U hU]
  rw [C04Aux.normalModelMetric_apply, complexVector_real_inner]

theorem normalChartMap_pullback_re (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (hU : ∀ i j, (g.form p).toFun (U (stdVec i)) (U (stdVec j)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) i j)
    (e : OpenPartialHomeomorph (ComplexVector n) (ComplexVector n))
    (L : ComplexVector n →L[ℝ] ComplexVector n) (d : ℝ) (z u v : ComplexVector n)
    (hparam : DifferentiableAt ℝ (normalizedInverseParameter e L d) z)
    (hf : MDifferentiableAt (ComplexModel n) (ComplexModel n) (normalChartMap g p U e L d) z) :
    2 * ((g.form (normalChartMap g p U e L d z)).toFun
      (mfderiv (ComplexModel n) (ComplexModel n) (normalChartMap g p U e L d) z u)
      (mfderiv (ComplexModel n) (ComplexModel n) (normalChartMap g p U e L d) z v)).re =
      C04Aux.normalModelMetric (radialCoframe g p U (normalizedInverseParameter e L d z))
        (fderiv ℝ (normalizedInverseParameter e L d) z u)
        (fderiv ℝ (normalizedInverseParameter e L d) z v) := by
  rw [← realMetric_of_complex_derivative g.form _ z u v hf]
  exact normalChartMap_realMetric g p U hU e L d z u v hparam

theorem normalChartMap_pullback_entry (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (hU : ∀ i j, (g.form p).toFun (U (stdVec i)) (U (stdVec j)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) i j)
    (e : OpenPartialHomeomorph (ComplexVector n) (ComplexVector n))
    (L : ComplexVector n →L[ℝ] ComplexVector n) (d : ℝ) (z : ComplexVector n) (a b : Fin n)
    (hparam : DifferentiableAt ℝ (normalizedInverseParameter e L d) z)
    (hf : MDifferentiableAt (ComplexModel n) (ComplexModel n) (normalChartMap g p U e L d) z) :
    pullbackMat g.form (normalChartMap g p U e L d) z a b =
      (C04Aux.normalModelMetric (radialCoframe g p U (normalizedInverseParameter e L d z))
        (fderiv ℝ (normalizedInverseParameter e L d) z (stdVec a))
        (fderiv ℝ (normalizedInverseParameter e L d) z (stdVec b)) / 2 : ℝ) -
      Complex.I * (C04Aux.normalModelMetric (radialCoframe g p U (normalizedInverseParameter e L d z))
        (fderiv ℝ (normalizedInverseParameter e L d) z (stdVec a))
        (fderiv ℝ (normalizedInverseParameter e L d) z (Complex.I • stdVec b)) / 2 : ℝ) := by
  have hr := normalChartMap_pullback_re g p U hU e L d z (stdVec a) (stdVec b) hparam hf
  have hi := normalChartMap_pullback_re g p U hU e L d z (stdVec a) (Complex.I • stdVec b) hparam hf
  simp only [map_smul, HermitianInnerProduct.map_smul_right, smul_eq_mul,
    Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, mul_zero, mul_one, zero_sub] at hi
  apply Complex.ext
  · change (pullbackMat g.form (normalChartMap g p U e L d) z a b).re = _
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
    change 2 * (pullbackMat g.form (normalChartMap g p U e L d) z a b).re = _ at hr
    linarith
  · change (pullbackMat g.form (normalChartMap g p U e L d) z a b).im = _
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add, zero_sub]
    change 2 * -(pullbackMat g.form (normalChartMap g p U e L d) z a b).im = _ at hi
    linarith

end Yau.Proofs.C04ChartsAux
