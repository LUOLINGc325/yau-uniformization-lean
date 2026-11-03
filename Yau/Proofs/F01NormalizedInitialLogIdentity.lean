import Yau.Proofs.F01NormalizedComplexFlowMatrix
import Yau.Proofs.F01PotentialSpatialLinearization

/-! The logarithm in the zero-extended spatial-word equation is the
actual normalized native flow determinant ratio, including zero and both
closed time faces. No nonlinear equation is supplied independently. -/
noncomputable section
open Set Metric
open scoped ContDiff Manifold Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem normalized_initial_log_identity
    (hg : MetricSmooth g) (A : BoundedChartFamily g)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) {T ρ : ℝ}
    (hρ : 0 < ρ) (hρr : ρ ≤ A.radius) (hρT : ρ ^ 2 ≤ T)
    (hU : SmoothSpaceTime U (Icc 0 T)) (hh0 : h 0 = g)
    (hpot : ∀ s ∈ Icc 0 T, ∀ x,
      gMat (h s) x = gMat g x - (s : ℂ) • ricci g x + levi (fun y => U y s) x)
    (a : M.Carrier) {p : Point n} (hp : p ∈ ball 0 1 ×ˢ Icc (-1) 1) :
    forwardZeroSpaceTime
      (fun q : Point n => flowLogDetRatio g h (A.chart a (ρ • q.1)) (ρ ^ 2 * q.2)) p =
      Real.log (chartPotentialMatrix (normalizedComplexBackground A a ρ)
        (forwardZeroSpaceTime (parabolicRescalePotential ρ
          (fun q : Point n => U (A.chart a q.1) q.2))) p).det.re -
        Real.log (pullbackMatrix g (A.chart a) (ρ • p.1)).det.re := by
  have hzero (x : Space n) (hx : x ∈ ball 0 1) :
      flowLogDetRatio g h (A.chart a (ρ • x)) (ρ ^ 2 * 0) = 0 := by
    rw [mul_zero]
    exact flowLogDetRatio_initial g h hh0 _
  have hScalar : forwardZeroSpaceTime
      (fun q : Point n => flowLogDetRatio g h (A.chart a (ρ • q.1)) (ρ ^ 2 * q.2)) p =
      flowLogDetRatio g h (A.chart a (ρ • p.1)) (ρ ^ 2 * max p.2 0) :=
    forwardZeroSpaceTime_eq_clamped hzero hp.1 p.2
  have hMatrix : chartPotentialMatrix (normalizedComplexBackground A a ρ)
      (forwardZeroSpaceTime (parabolicRescalePotential ρ
        (fun q : Point n => U (A.chart a q.1) q.2))) p =
      pullbackMatrix (h (ρ ^ 2 * max p.2 0)) (A.chart a) (ρ • p.1) :=
    normalized_complex_flow_matrix hg A h U hρ hρr hρT hU hh0 hpot a hp
  have hz := spatialDilation_mem_ball hρ hρr hp.1
  have hs : ρ • p.1 ∈ (A.chart a).source := A.closedBall_source a (ball_subset_closedBall hz)
  rw [hScalar, hMatrix]
  exact flowLogDetRatio_pullback_difference g h (A.chart a) (A.differentiable a)
    (A.inverse_differentiable a) hs _

end Yau.NodeProofs.F01Aux
