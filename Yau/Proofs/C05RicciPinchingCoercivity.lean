import Yau.Proofs.C05UnitaryFrame
import Yau.Proofs.C05RealRicciPositive
import Yau.Proofs.C05MetricInverseBound
import Yau.Proofs.C05IntrinsicTensorNorm
import Yau.Proofs.G01Realification

/-! The frozen relative Ricci pinching is actual real coercivity and bounds
the genuine lowered inverse in its own metric norm. -/
noncomputable section
open scoped Topology Manifold ContDiff Matrix ComplexOrder
namespace Yau.Proofs.C05Aux
open Yau Yau.NodeProofs.G01Aux Yau.LeafProofs.L12Aux
open Yau.Proofs.C05UnitaryFrameAux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem relative_rayleigh_coercivity (g A : Matrix (Fin n) (Fin n) ℂ) (hg : g.PosDef)
    {μ : ℝ} (hμ : 0 < μ) (hpin : μ ≤ relMinEigenvalue g A) (v : Fin n → ℂ) :
    μ*(star v ⬝ᵥ (g*ᵥv)).re ≤ (star v ⬝ᵥ (A*ᵥv)).re := by
  by_cases hv : v=0
  · simp [hv]
  let V : ComplexVector n := WithLp.toLp 2 v
  have hV : V ≠ 0 := by
    intro h
    apply hv
    simpa only [V,WithLp.ofLp_toLp,WithLp.ofLp_zero] using congrArg WithLp.ofLp h
  have hden : 0 < (star v ⬝ᵥ (g*ᵥv)).re :=
    (Complex.pos_iff.mp (hg.dotProduct_mulVec_pos hv)).1
  have H := hpin.trans (relMin_le_rayleigh_of_pos (hμ.trans_le hpin) V hV)
  change μ ≤ (star v ⬝ᵥ (A*ᵥv)).re / (star v ⬝ᵥ (g*ᵥv)).re at H
  exact (le_div_iff₀ hden).mp H

theorem realRicci_coercive_of_relative_pinching (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (x : M.Carrier) {μ : ℝ} (hμ : 0 < μ)
    (hpin : μ ≤ relMinEigenvalue (gMat k x) (ricci k x)) (v : RIdx n → ℝ) :
    μ*(v ⬝ᵥ (realMetricFn k x (chartPt x x)*ᵥv)) ≤
      v ⬝ᵥ ((Matrix.of (realRicciCoeff k x (chartPt x x)))*ᵥv) := by
  let V : ComplexVector n := ∑ a, v a • realVec a
  have hcoords : realCoord V = v := funext (realCoord_sum_realVec v)
  have H := relative_rayleigh_coercivity (gMat k x) (ricci k x)
    (Yau.LeafProofs.L18Aux.hMat_posDef k x _ (mem_extChartAt_target x)) hμ hpin (WithLp.ofLp V)
  rw [←rawReal_quadratic_coords (gMat k x) V,
    ←rawReal_quadratic_coords (ricci k x) V,hcoords] at H
  have hA : Matrix.of (realRicciCoeff k x (chartPt x x)) = (2:ℝ) • rawReal (ricci k x) := by
    ext a b
    exact Yau.NodeProofs.G04Aux.realRicciCoeff_center_raw k hk hK x a b
  rw [hA,realMetricFn_eq_rawReal]
  change μ*(v ⬝ᵥ (((2:ℝ) • rawReal (gMat k x))*ᵥv)) ≤ _
  simp only [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]
  linarith

theorem ricciInverseTensor_norm_le_of_relative_pinching (k : HermitianField M)
    (hk : MetricSmooth k) (hK : KahlerClosed k) (x : M.Carrier)
    (hA : (ricci k x).PosDef) {μ : ℝ} (hμ : 0 < μ)
    (hpin : μ ≤ relMinEigenvalue (gMat k x) (ricci k x)) :
    metricTensorNorm (realMetricFn k x (chartPt x x))
      (ricciInverseTensor k x (chartPt x x)) ≤ Real.sqrt (2*n:ℕ) / μ := by
  have H := loweredInverseMatrix_metric_normSq_bound
    (realMetricFn k x (chartPt x x)) (Matrix.of (realRicciCoeff k x (chartPt x x)))
    (realMetricFn_posDef k x _ (mem_extChartAt_target x))
    (realRicciMatrix_posDef k hk hK x hA).det_pos.ne' μ hμ
    (realRicci_coercive_of_relative_pinching k hk hK x hμ hpin)
  have hnorm := Real.sq_sqrt (Yau.LeafProofs.L23Aux.covTensorNormSq_nonneg
    (realMetricFn k x (chartPt x x)) (realMetricFn_posDef k x _ (mem_extChartAt_target x))
    (ricciInverseTensor k x (chartPt x x)))
  have hs := Real.sq_sqrt (Nat.cast_nonneg (2*n) : (0:ℝ)≤(2*n:ℕ))
  have hn := metricTensorNorm_nonneg (realMetricFn k x (chartPt x x))
    (ricciInverseTensor k x (chartPt x x))
  apply (le_div_iff₀ hμ).mpr
  have hsn := Real.sqrt_nonneg (2*n:ℕ)
  change μ^2*Yau.covTensorNormSq
    (realMetricFn k x (chartPt x x)) (ricciInverseTensor k x (chartPt x x)) ≤ (2*n:ℕ) at H
  dsimp only [metricTensorNorm] at hn ⊢
  nlinarith

end Yau.Proofs.C05Aux
