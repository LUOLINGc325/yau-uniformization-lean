import Yau.Proofs.C05HermitianHessianProjection
import Yau.Proofs.C05LaplacianTimeDerivative
import Yau.Proofs.C05MatrixTensorContraction

/-! The actual Ricci--Levi pairing is one-half the metric pairing with
the full real scalar Hessian, in every fixed chart. -/
noncomputable section
open scoped Topology Manifold ContDiff Matrix
namespace Yau.Proofs.C05Aux
open Yau Blueprint Matrix Yau.Proofs.C05GradientFlowAux
open Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux Yau.NodeProofs.G01Aux
variable {n r : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem rawReal_realHessian_trace (D : Matrix (Fin n) (Fin n) ℂ)
    (B : Matrix (RIdx n) (RIdx n) ℝ) :
    (rawReal D * B).trace = 4 * (D * hessianMixed B).trace.re := by
  have he (i j : Fin n) :
      (rawReal D (i,0) (j,0)*B (j,0) (i,0) + rawReal D (i,0) (j,1)*B (j,1) (i,0)) +
      (rawReal D (i,1) (j,0)*B (j,0) (i,1) + rawReal D (i,1) (j,1)*B (j,1) (i,1)) =
      4 * (D i j * hessianMixed B j i).re := by
    simp [rawReal,hessianMixed,Complex.mul_re,Complex.mul_im]
    ring
  calc
    _ = ∑ i, ∑ j,
        ((rawReal D (i,0) (j,0)*B (j,0) (i,0) + rawReal D (i,0) (j,1)*B (j,1) (i,0)) +
        (rawReal D (i,1) (j,0)*B (j,0) (i,1) + rawReal D (i,1) (j,1)*B (j,1) (i,1))) := by
      simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Fintype.sum_prod_type,
        Fin.sum_univ_two,Finset.sum_add_distrib]
      ring
    _ = ∑ i, ∑ j, 4 * (D i j * hessianMixed B j i).re := by simp_rw [he]
    _ = _ := by
      simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Complex.re_sum,Finset.mul_sum]

theorem ricciLeviPairing_eq_half_hessian_pair (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (f : M.Carrier → ℝ) (hf : SmoothFn f) (x : M.Carrier) :
    ricciLeviPairing k f x = (1/2:ℝ) * covTensorPair (realMetricFn k x (chartPt x x))
      (realRicciJet k x 0 (chartPt x x)) (scalarJet k f x 2 (chartPt x x)) := by
  let z := chartPt x x
  let G := realMetricFn k x z
  let A := Matrix.of (realRicciCoeff k x z)
  let B := Matrix.of (realHessInChart k f x z)
  have hz : z ∈ chartTarget x := mem_extChartAt_target x
  have hfz : ContDiffAt ℝ 2 (inChart x f) z :=
    ((hf x).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).of_le (by simp)
  have hR : A = (2:ℝ) • rawReal (ricci k x) := by
    ext a b
    exact Yau.NodeProofs.G04Aux.realRicciCoeff_center_raw k hk hK x a b
  have hG : G⁻¹ = (1/2:ℝ) • rawReal (gMat k x)⁻¹ := realMetricFn_inverse_eq k x z hz
  have hp : G⁻¹*A*G⁻¹ = (1/2:ℝ) • rawReal ((gMat k x)⁻¹*ricci k x*(gMat k x)⁻¹) := by
    rw [hG,hR]
    simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul]
    norm_num
    simp only [← rawReal_mul]
  have hb : B.IsSymm := realHessInChart_isSymm k f x z hfz
  rw [scalarJet_two_matrix]
  change ricciLeviPairing k f x = (1/2:ℝ) * covTensorPair G (matrixCovTensor A) (matrixCovTensor B)
  rw [covTensorPair_matrix G A B (Yau.LeafProofs.L18Aux.realMetricFn_isSymm k x z) hb,
    hp,Matrix.smul_mul,Matrix.trace_smul,smul_eq_mul,rawReal_realHessian_trace]
  have hm : hessianMixed B = levi f x := hessianMixed_realHessInChart k hk hK f x hz hfz
  rw [hm]
  simp only [ricciLeviPairing,traceWith,Matrix.mul_assoc]
  ring

theorem covTensorPair_frameTransform (Gc Gd J : Matrix (RIdx n) (RIdx n) ℝ)
    (hInv : J*Gc⁻¹*Jᵀ=Gd⁻¹) (A B : CovTensor n r) :
    covTensorPair Gc (tensorFrameTransform J A) (tensorFrameTransform J B) = covTensorPair Gd A B := by
  unfold covTensorPair
  rw [tensor_contraction_frameTransform,hInv]

theorem ricciLeviPairing_inChart (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (f : M.Carrier → ℝ) (hf : SmoothFn f) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    inChart c (ricciLeviPairing k f) z = (1/2:ℝ) * covTensorPair (realMetricFn k c z)
      (realRicciJet k c 0 z) (scalarJet k f c 2 z) := by
  let d := chartInv c z
  have hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source := mem_extChartAt_source d
  change ricciLeviPairing k f d = _
  rw [ricciLeviPairing_eq_half_hessian_pair k hk hK f hf d,
    realRicciJet_chart_change k hk 0 c d hz hy,scalarJet_chart_change k hk f hf 2 c d hz hy,
    covTensorPair_frameTransform _ _ _ (inverseMetric_chart_change k c d hz hy)]
  rfl

theorem ricciLeviPairing_smoothFn (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (f : M.Carrier → ℝ) (hf : SmoothFn f) :
    SmoothFn (ricciLeviPairing k f) := by
  intro c
  have hA := realRicciJet_contDiffOn k hk c 0
  have hB := Yau.Proofs.C05HessianPropagationAux.scalarJet_contDiffOn k hk f hf c 2
  have he := chartTensorPair_contDiffOn k hk c (realRicciJet k c 0) (scalarJet k f c 2) hA hB
  exact (contDiffOn_const.mul he).congr (fun z hz => ricciLeviPairing_inChart k hk hK f hf c hz)

end Yau.Proofs.C05Aux
