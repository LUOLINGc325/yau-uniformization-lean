import Yau.Proofs.C05GeodesicScalarJets
import Yau.Proofs.C05ScalarLaplacianJets
import Yau.Proofs.C05MetricInverseBound
import Yau.LeafProofs.L12GaussLemma

/-! Genuine unit-energy tangent frames and the complex Laplacian trace. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff Matrix
namespace Yau.Proofs.C05GeometricNearMinimumAux
open Yau Yau.Blueprint Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
open Yau.Proofs.C05Aux Yau.Proofs.C05GradientFlowAux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

def frameColumn (D : Matrix (RIdx n) (RIdx n) ℝ) (j : RIdx n) : ComplexVector n :=
  ∑ a : RIdx n, D a j • realVec a

def framePhase (o : M.Carrier) (D : Matrix (RIdx n) (RIdx n) ℝ) (j : RIdx n) :
    TangentBundle 𝓘(ℝ,ComplexVector n) M.Carrier :=
  ⟨o, realFrameCLM o o (frameColumn D j)⟩

theorem framePhase_energy (g : SmoothMetric M) (o : M.Carrier)
    (D : Matrix (RIdx n) (RIdx n) ℝ)
    (hGram : Dᵀ * realMetricFn g.form o (chartPt o o) * D = 1) (j : RIdx n) :
    realTangentEnergy g.form (framePhase o D j) = 1 := by
  change (underlyingRealRiemannianMetric g.form).inner o
    (realFrameCLM o o (frameColumn D j)) (realFrameCLM o o (frameColumn D j)) = 1
  rw [← realMetricInChart_self_frame, realBilin_eq_sum]
  simp_rw [frameColumn, realCoord_sum_realVec,
    realMetricInChart_basis g.form o (chartPt o o) (mem_extChartAt_target o)]
  have he := congrArg (fun A : Matrix (RIdx n) (RIdx n) ℝ => A j j) hGram
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at he
  rw [Finset.sum_comm]
  simpa only [Finset.sum_mul, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using he

theorem frame_hessian (k : HermitianField M) (f : M.Carrier → ℝ)
    (o : M.Carrier) (D : Matrix (RIdx n) (RIdx n) ℝ) (j : RIdx n) :
    realHess k f o (realTangentEquiv o (framePhase o D j).2)
      (realTangentEquiv o (framePhase o D j).2) =
      ∑ a : RIdx n, ∑ b : RIdx n,
        realHessInChart k f o (chartPt o o) a b * D a j * D b j := by
  unfold realHess
  simp only [framePhase, tangentCoords_realTangentEquiv_self,
    realTangentCoords_realFrameCLM o o (mem_chart_source _ _), frameColumn,
    realCoord_sum_realVec]

theorem matrix_frame_trace (D H : Matrix (RIdx n) (RIdx n) ℝ) :
    (∑ j : RIdx n, ∑ a : RIdx n, ∑ b : RIdx n,
      H a b * D a j * D b j) =
      ∑ a : RIdx n, ∑ b : RIdx n, (D * Dᵀ) a b * H a b := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem laplacian_frame_trace (g : SmoothMetric M) (f : M.Carrier → ℝ)
    (hf : SmoothFn f) (o : M.Carrier) (D : Matrix (RIdx n) (RIdx n) ℝ)
    (hD : (realMetricFn g.form o (chartPt o o))⁻¹ = D * Dᵀ) :
    laplacian g.form f o = (1/2:ℝ) * ∑ j : RIdx n,
      realHess g.form f o (realTangentEquiv o (framePhase o D j).2)
        (realTangentEquiv o (framePhase o D j).2) := by
  simp_rw [frame_hessian]
  rw [matrix_frame_trace, ← hD]
  have he := Yau.NodeProofs.G04Aux.scalarLaplacian g.form
    (metricSmooth_of_smoothMetric g) g.kahler_equations f hf o (chartPt o o)
    (mem_extChartAt_target o)
  change (∑ a : RIdx n, ∑ b : RIdx n,
    (realMetricFn g.form o (chartPt o o))⁻¹ a b *
      realHessInChart g.form f o (chartPt o o) a b) =
    2 * laplacian g.form f (chartInv o (chartPt o o)) at he
  have hc : chartInv o (chartPt o o) = o :=
    (extChartAt (ComplexModel n) o).left_inv (mem_extChartAt_source o)
  rw [hc] at he
  linarith

end Yau.Proofs.C05GeometricNearMinimumAux
