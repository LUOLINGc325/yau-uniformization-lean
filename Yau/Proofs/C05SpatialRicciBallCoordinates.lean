import Yau.Proofs.C05RicciPropagationDefinitions

/-! The actual tangent quadratic forms are exactly their real-coordinate matrices. -/
noncomputable section
open scoped Topology Manifold Matrix
namespace Yau.Proofs.C05SpatialRicciBallAux
open Yau Yau.LeafProofs.L12Aux
open Yau.Proofs.C05GradientFlowAux Yau.Proofs.C05RicciPropagationAux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem row_quadratic_sum (A : Matrix (RIdx n) (RIdx n) ℝ) (v : RIdx n → ℝ) :
    v ⬝ᵥ (A*ᵥv) = ∑ a : RIdx n, ∑ b : RIdx n, A a b*v a*v b := by
  simp only [dotProduct,Matrix.mulVec,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem realNormSq_coordinates (k : HermitianField M) (x : M.Carrier)
    (w : TangentVector M x) :
    realNormSq k x w = realCoord (tangentCoords x x w) ⬝ᵥ
      (realMetricFn k x (chartPt x x)*ᵥrealCoord (tangentCoords x x w)) := by
  rw [row_quadratic_sum]
  exact (realMetricTensor_quadratic k x w).symm

theorem ricciQuad_coordinates (k : HermitianField M) (x : M.Carrier)
    (w : TangentVector M x) :
    ricciQuad k x w = realCoord (tangentCoords x x w) ⬝ᵥ
      (Matrix.of (realRicciCoeff k x (chartPt x x))*ᵥrealCoord (tangentCoords x x w)) := by
  rw [row_quadratic_sum]
  rfl

theorem row_coercivity_of_tangent_coercivity (k : HermitianField M) (x : M.Carrier)
    (μ : ℝ) (h : ∀ w : TangentVector M x,
      μ*realNormSq k x w ≤ ricciQuad k x w) (v : RIdx n → ℝ) :
    μ*(v ⬝ᵥ (realMetricFn k x (chartPt x x)*ᵥv)) ≤
      v ⬝ᵥ (Matrix.of (realRicciCoeff k x (chartPt x x))*ᵥv) := by
  let w : TangentVector M x := chartVec x x (∑ a : RIdx n, v a • realVec a)
  have hw : realCoord (tangentCoords x x w) = v := by
    dsimp only [w]
    rw [tangentCoords_chartVec x x (mem_extChartAt_source x)]
    exact funext (realCoord_sum_realVec v)
  have H := h w
  rwa [realNormSq_coordinates,ricciQuad_coordinates,hw] at H

end Yau.Proofs.C05SpatialRicciBallAux
