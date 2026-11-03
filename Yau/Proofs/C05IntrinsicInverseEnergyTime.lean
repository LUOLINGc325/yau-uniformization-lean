import Yau.Proofs.C05InverseEnergyTimeBound
import Yau.Proofs.C05HarnackSourceJetBounds

/-! The genuine intrinsic inverse-energy time expression for a KRF slice.
Its only temporal source is the computed scalar KRF source. -/
noncomputable section
open scoped Topology Manifold ContDiff Matrix
namespace Yau.Proofs.C05Aux
open Yau Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

def intrinsicInverseEnergyTime (k : HermitianField M) (x : M.Carrier) : ℝ :=
  let A := Matrix.of (realRicciCoeff k x (chartPt x x))
  let B := (2:ℝ) • Yau.NodeProofs.G01Aux.rawReal (levi (scalarCurvature k) x)
  let p := fun a => scalarJet k (scalarCurvature k) x 1 (chartPt x x) ![a]
  let q := fun a => scalarJet k (scalarHarnackSource k 0) x 1 (chartPt x x) ![a]
  (1/2:ℝ)*(-(p ⬝ᵥ ((A⁻¹*B*A⁻¹)*ᵥp)) + q ⬝ᵥ (A⁻¹*ᵥp) + p ⬝ᵥ (A⁻¹*ᵥq))

theorem intrinsicInverseEnergyTime_abs_le (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (x : M.Carrier) :
    |intrinsicInverseEnergyTime k x| ≤
      (1/2:ℝ)*(2*n:ℕ)*
        metricTensorNorm (realMetricFn k x (chartPt x x))
          (ricciInverseTensor k x (chartPt x x)) ^ 2 *
        scalarJetNorm k (scalarCurvature k) 2 x * scalarJetNorm k (scalarCurvature k) 1 x ^ 2 +
      metricTensorNorm (realMetricFn k x (chartPt x x))
        (ricciInverseTensor k x (chartPt x x)) *
        scalarJetNorm k (scalarCurvature k) 1 x * scalarJetNorm k (scalarHarnackSource k 0) 1 x := by
  let G := realMetricFn k x (chartPt x x)
  let A := Matrix.of (realRicciCoeff k x (chartPt x x))
  let B := (2:ℝ) • Yau.NodeProofs.G01Aux.rawReal (levi (scalarCurvature k) x)
  let p := scalarJet k (scalarCurvature k) x 1 (chartPt x x)
  let q := scalarJet k (scalarHarnackSource k 0) x 1 (chartPt x x)
  have H := inverseEnergyTime_abs_le G A B (realMetricFn_posDef k x _
    (mem_extChartAt_target x)) p q
  have hB := realLevi_norm_le_scalarHessian k hk hK (scalarCurvature k)
    (scalarCurvature_smoothFn k hk hK) x
  have hc : 0 ≤ (1/2:ℝ)*(2*n:ℕ)*
      metricTensorNorm G (matrixCovTensor (loweredInverseMatrix G A))^2*
        metricTensorNorm G p^2 := by positivity
  have hb := mul_le_mul_of_nonneg_left hB hc
  change |intrinsicInverseEnergyTime k x| ≤ _ at H
  apply H.trans
  dsimp only [G,A,p,q,B,scalarJetNorm,metricTensorNorm,ricciInverseTensor] at hb ⊢
  nlinarith [hb]

end Yau.Proofs.C05Aux
