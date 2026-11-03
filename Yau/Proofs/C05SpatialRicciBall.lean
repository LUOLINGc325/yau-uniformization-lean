import Yau.Proofs.C05SpatialRicciBallCoordinates
import Yau.Proofs.C05RicciPinchingCoercivity
import Yau.Proofs.C05RicciPropagation

/-! A uniform radius propagates actual center Ricci pinching to real coercivity. -/
noncomputable section
open scoped Topology Manifold Matrix
namespace Yau.Proofs.C05SpatialRicciBallAux
open Yau Yau.LeafProofs.L12Aux Yau.Proofs.C05Aux
open Yau.Proofs.C05GradientFlowAux Yau.Proofs.C05RicciPropagationAux

theorem exists_uniform_coercive_ricci_ball (n : ℕ) (μ B b : ℝ)
    (hμ : 0 < μ) (hB : 0 ≤ B) (hb : 0 < b) :
    ∃ r : ℝ, 0 < r ∧ r ≤ b ∧
      ∀ (M : ComplexManifold n) (g : SmoothMetric M) (o : M.Carrier),
      μ ≤ relMinEigenvalue (gMat g.form o) (ricci g.form o) →
      (∀ x ∈ distBall g.form o (2*b), realRicciJetNorm g.form 1 x ≤ B) →
      ∀ x ∈ distBall g.form o r, ∀ v : RIdx n → ℝ,
      (μ/2)*(v ⬝ᵥ (realMetricFn g.form x (chartPt x x)*ᵥv)) ≤
        v ⬝ᵥ (Matrix.of (realRicciCoeff g.form x (chartPt x x))*ᵥv) := by
  let r : ℝ := min b (μ/(2*(B+1)))
  have hr : 0 < r := lt_min hb (by positivity)
  have hrb : r ≤ b := min_le_left _ _
  have hsmall : B*r ≤ μ/2 := by
    have H := (le_div_iff₀ (show 0 < 2*(B+1) by positivity)).mp
      (min_le_right b (μ/(2*(B+1))))
    change r*(2*(B+1)) ≤ μ at H
    nlinarith
  refine ⟨r,hr,hrb,?_⟩
  intro M g o hpin hD x hx v
  have hcenter (w : TangentVector M o) :
      μ*realNormSq g.form o w ≤ ricciQuad g.form o w := by
    have H := realRicci_coercive_of_relative_pinching g.form
      (metricSmooth_of_smoothMetric g) g.kahler_equations o hμ hpin
      (realCoord (tangentCoords o o w))
    rwa [← realNormSq_coordinates,← ricciQuad_coordinates] at H
  have hDsmall (y : M.Carrier) (hy : y ∈ distBall g.form o r) :
      realRicciJetNorm g.form 1 y ≤ B := by
    apply hD y
    apply (mem_distBall_iff g o y (show 0 < 2*b by positivity)).mpr
    exact ((mem_distBall_iff g o y hr).mp hy).trans (hrb.trans_lt (by linarith))
  exact row_coercivity_of_tangent_coercivity g.form x (μ/2)
    (ricciQuad_coercive_on_ball g o hB hr hμ hDsmall hcenter hsmall x hx) v

end Yau.Proofs.C05SpatialRicciBallAux
