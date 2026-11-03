import Yau.Proofs.C04BoundedGeometryChartsEllipticFrameTrace
import Yau.Proofs.C04BoundedGeometryChartsScaledConnection
import Yau.Proofs.C04BoundedGeometryChartsCoordinateComponents

/-! Every component of the same normal complex coordinates solves the actual uniformly elliptic operator. -/
noncomputable section
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs.L21Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5

theorem normal_coordinate_component_elliptic (g : SmoothMetric M) (hk : KahlerClosed g.form)
    (p : M.Carrier) (U : ComplexVector n ≃L[ℂ] TangentVector M p) (d : ℝ)
    (F : ComplexVector n → ComplexVector n) (hF : ContDiff ℝ ∞ F)
    (hi : ∀ x ∈ Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ),
      (scaledRadialCoframe g p U d x).IsInvertible)
    (hcomplex : ∀ x ∈ Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ), ∀ v,
      fderiv ℝ F x (realPullbackJ (unitaryExponential g p U) (d • x) v) =
        Complex.I • fderiv ℝ F x v)
    (k : Fin n) (x : ComplexVector n) (hx : x ∈ Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ)) :
    Yau.LeafCandidates.ellipticOp
      (fun y => framePrincipalCoefficients (scaledRadialCoframe g p U d y).inverse)
      (fun y => frameDriftCoefficients (scaledRadialCoframe g p U d y).inverse
        (C04Aux.coframeModelConnection (scaledRadialCoframe g p U d) (scaledRadialConnection g p U d) y))
      (fun y => F y k) x = 0 := by
  have hcomponent : ContDiff ℝ ∞ (fun y => F y k) := by
    let pr : ComplexVector n →L[ℝ] ℂ := (EuclideanSpace.proj k).restrictScalars ℝ
    change ContDiff ℝ ∞ (pr ∘ F)
    exact pr.contDiff.comp hF
  have hmodel : ∀ y ∈ Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ), ∀ v,
      fderiv ℝ F y (scaledNormalComplex g p U d y v) = Complex.I • fderiv ℝ F y v := by
    intro y hy v
    rw [scaledNormalComplex_eq_actual g hk]
    exact hcomplex y hy v
  apply ellipticOp_zero_of_covariant_complex
    (fun y => (scaledRadialCoframe g p U d y).inverse)
    (C04Aux.coframeModelConnection (scaledRadialCoframe g p U d) (scaledRadialConnection g p U d))
    (scaledNormalComplex g p U d) (fun y => F y k) x
    (hcomponent.contDiffAt.of_le (by simp))
  · exact (C04Aux.coframe_model_complex_contDiffAt (scaledRadialCoframe g p U d) (stdComplex n) x
      (scaledRadialCoframe_smooth g p U d) (hi x hx)).differentiableAt (by simp)
  · exact scaledNormalComplex_parallel g hk p U d x
      (hi := hi x hx)
  · exact coordinate_component_complex F hF _ Metric.isOpen_ball hmodel hx k
  · exact scaledNormalConnection_symm g p U d x
  · exact scaledNormalComplex_inverse_frame g p U d x
      (hi := hi x hx)

end Yau.Proofs.C04ChartsAux
