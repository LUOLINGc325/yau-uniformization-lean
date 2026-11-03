import Yau.Proofs.C05HessianFrameEnergyBindingAlgebra
import Yau.Proofs.C05HessianEnergyBlocks
import Yau.Proofs.C05HessianEnergyActual
import Yau.Proofs.C05CovariantHessianBlocks
import Yau.Proofs.G04FlowNormalization

/-! The computed Hessian energy in one actual metric/Ricci unitary frame. -/
noncomputable section
open scoped Matrix BigOperators ContDiff Manifold
namespace Yau.Proofs.C05HessianFrameEnergyBindingAux
open Yau Yau.Proofs.C05Aux Yau.Proofs.C05GradientFlowAux
open Yau.NodeProofs.G01Aux Yau.Proofs.C05HessianEnergyAux Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

def frameHessian (k : HermitianField M) (f : M.Carrier → ℝ) (x : M.Carrier)
    (W : Matrix (Fin n) (Fin n) ℂ) : Matrix (RIdx n) (RIdx n) ℝ :=
  (rawReal W)ᵀ * Matrix.of (realHessInChart k f x (chartPt x x)) * rawReal W

theorem frameHessian_mixed (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (f : M.Carrier → ℝ) (hf : SmoothFn f)
    (x : M.Carrier) (W : Matrix (Fin n) (Fin n) ℂ) :
    hessianMixed (frameHessian k f x W) = Wᴴ * levi f x * W := by
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target (I := ComplexModel n) x
  have h2 : ContDiffAt ℝ 2 (inChart x f) (chartPt x x) :=
    ((hf x).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).of_le (by simp)
  rw [frameHessian, hessianMixed_congruence]
  change Wᴴ * hessianMixed (realHessInChart k f x (chartPt x x)) * W = _
  rw [hessianMixed_realHessInChart k hk hK f x hz h2]
  rfl

theorem half_inverseEnergyHessianSquare_frame (k : HermitianField M)
    (hk : MetricSmooth k) (hK : KahlerClosed k) (f : M.Carrier → ℝ)
    (hf : SmoothFn f) (x : M.Carrier) (W : Matrix (Fin n) (Fin n) ℂ)
    (hdetW : W.det ≠ 0) (hGram : Wᴴ * gMat k x * W = 1)
    (lam : Fin n → ℝ)
    (hDiag : Wᴴ * ricci k x * W = Matrix.diagonal (fun j => (lam j : ℂ)))
    (hLam : ∀ j, 0 < lam j) :
    (1/2 : ℝ) * inverseEnergyHessianSquare k f x (chartPt x x) =
      weightedHessianSquare lam (Wᴴ * levi f x * W) +
      weightedHessianSquare lam (hessianPure (frameHessian k f x W)) := by
  let J := rawReal W
  let B := Matrix.of (realHessInChart k f x (chartPt x x))
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target (I := ComplexModel n) x
  have h2 : ContDiffAt ℝ 2 (inChart x f) (chartPt x x) :=
    ((hf x).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).of_le (by simp)
  have hB : B.IsSymm := realHessInChart_isSymm k f x (chartPt x x) h2
  have hBF : (Jᵀ * B * J).IsSymm := by
    change (Jᵀ * B * J)ᵀ = Jᵀ * B * J
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hB.eq, Matrix.mul_assoc]
  have hG : Jᵀ * realMetricFn k x (chartPt x x) * J = (2 : ℝ) • 1 := by
    rw [realMetricFn_eq_rawReal, Matrix.mul_smul, Matrix.smul_mul]
    change (2 : ℝ) • ((rawReal W)ᵀ * rawReal (gMat k x) * rawReal W) = _
    rw [rawReal_congruence, hGram, rawReal_one]
  have hA : Jᵀ * Matrix.of (realRicciCoeff k x (chartPt x x)) * J =
      (2 : ℝ) • Matrix.diagonal (fun a : RIdx n => lam a.1) := by
    have he : Matrix.of (realRicciCoeff k x (chartPt x x)) = (2 : ℝ) • rawReal (ricci k x) := by
      ext a b
      exact Yau.NodeProofs.G04Aux.realRicciCoeff_center_raw k hk hK x a b
    rw [he, Matrix.mul_smul, Matrix.smul_mul]
    change (2 : ℝ) • ((rawReal W)ᵀ * rawReal (ricci k x) * rawReal W) = _
    rw [rawReal_congruence, hDiag, rawReal_diagonal]
  rw [half_inverseEnergyHessianSquare_eq k f x hz,
    ← hessianEnergy_congruence _ _ B J (rawReal_det_ne_zero W hdetW), hG, hA,
    hessianEnergy_diagonal_blocks lam hLam (Jᵀ * B * J) hBF]
  change weightedHessianSquare lam (hessianMixed (frameHessian k f x W)) + _ = _
  rw [frameHessian_mixed k hk hK f hf x W]
  rfl

end Yau.Proofs.C05HessianFrameEnergyBindingAux
