import Yau.Proofs.C04BoundedGeometryChartsCoordinateFunction
import Yau.Proofs.C04BoundedGeometryChartsUniformNormalJets
import Yau.Proofs.C04BoundedGeometryChartsNormalModels

/-! The same normalized coordinates for every genuine bounded-geometry normal parametrization. -/
noncomputable section
open scoped Topology Manifold ContDiff Matrix.Norms.Elementwise
namespace Yau.Proofs.C04ChartsAux
open Yau
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5

theorem exists_uniform_normal_coordinate_function (n : ℕ) (hn : 0 < n)
    (r : ℝ) (K : ℕ → ℝ) (hr : 0 < r) (hK : ∀ m, 0 < K m) :
    ∃ R : ℝ, 0 < R ∧ ∃ B : ℕ → ℝ, (∀ m, 0 < B m) ∧
      ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧ d ≤ R / 4 ∧
      ∀ (M : ComplexManifold n) (g : SmoothMetric M), KahlerClosed g.form →
      ∀ (p : M.Carrier) (U : ComplexVector n ≃L[ℂ] TangentVector M p),
        (∀ i j, (g.form p).toFun (U (stdVec i)) (U (stdVec j)) =
          (1 : Matrix (Fin n) (Fin n) ℂ) i j) →
        (∀ m x, x ∈ distBall g.form p (2 * r) → curvatureJetNorm g.form m x ≤ K m) →
        (∀ x ∈ Metric.closedBall (0 : ComplexVector n) R,
          unitaryExponential g p U x ∈ distBall g.form p (2 * r) ∧
          ‖radialCoframe g p U x - ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ (1 / 4 : ℝ) ∧
          (realMapDeriv (unitaryExponential g p U) x).IsInvertible) ∧
        (∀ m x, x ∈ Metric.closedBall (0 : ComplexVector n) R →
          ‖iteratedFDeriv ℝ m (radialCoframe g p U) x‖ ≤ B m ∧
          ‖iteratedFDeriv ℝ m (radialConnection g p U) x‖ ≤ B m ∧
          ‖iteratedFDeriv ℝ m (radialCurvatureOperator g p U) x‖ ≤ B m) ∧
        ∃ F : ComplexVector n → ComplexVector n, ContDiff ℝ ∞ F ∧ F 0 = 0 ∧
          (∀ x ∈ Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ),
            ‖fderiv ℝ F x - ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ (1 / 4 : ℝ)) ∧
          (∀ x ∈ Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ), ∀ v,
            fderiv ℝ F x (realPullbackJ (unitaryExponential g p U) (d • x) v) =
              Complex.I • fderiv ℝ F x v) ∧
          ∀ x ∈ Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ), ‖F x‖ ≤ 1 := by
  obtain ⟨R, hR, B, hB, hnormal⟩ := exists_uniform_normal_coframe_jet_bounds n hn r K hr hK
  obtain ⟨d, hd, hd1, hdR, hcoordinates⟩ := exists_uniform_coframe_coordinate_function n R hR B hB
  refine ⟨R, hR, B, hB, d, hd, hd1, hdR, ?_⟩
  intro M g hk p U hU hcurv
  obtain ⟨hseed, hjets⟩ := hnormal M g p U hU hcurv
  have heq : realPullbackJ (unitaryExponential g p U) =
      fun y => coframeComplexModel n (radialCoframe g p U y) :=
    realPullbackJ_eq_normalModelComplex g hk p U
  have hJ2 : ∀ x ∈ Metric.ball (0 : ComplexVector n) R, ∀ v,
      coframeComplexModel n (radialCoframe g p U x)
        (coframeComplexModel n (radialCoframe g p U x) v) = -v := by
    intro x hx v
    have hi := (hseed x (Metric.ball_subset_closedBall hx)).2.2
    simpa only [heq] using realPullbackJ_square g p U x v hi
  have hN : ∀ x ∈ Metric.ball (0 : ComplexVector n) R, ∀ v w,
      Yau.LeafCandidates.nijenhuis (fun y => coframeComplexModel n (radialCoframe g p U y)) x v w = 0 := by
    intro x hx v w
    rw [← heq]
    exact realPullbackJ_nijenhuis_zero g hk p U x v w (hseed x (Metric.ball_subset_closedBall hx)).2.2
  obtain ⟨F, hF, hF0, hclose, hcomplex, hnorm⟩ := hcoordinates (radialCoframe g p U)
    (radialCoframe_smooth g p U) (radialCoframe_zero g p U)
    (fun m x hx => (hjets m x hx).1) hJ2 hN
  refine ⟨hseed, hjets, F, hF, hF0, hclose, ?_, hnorm⟩
  intro x hx v
  simpa only [heq] using hcomplex x hx v

end Yau.Proofs.C04ChartsAux
