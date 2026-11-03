import Yau.Proofs.C05HessianFrameEnergyBindingEnergy

/-! The same frame identifies the actual tangent Hessian and the physical real norm. -/
noncomputable section
open scoped Matrix BigOperators ContDiff Manifold
namespace Yau.Proofs.C05HessianFrameEnergyBindingAux
open Yau Yau.Proofs.C05Aux Yau.Proofs.C05GradientFlowAux
open Yau.NodeProofs.G01Aux Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

def frameVector (x : M.Carrier) (W : Matrix (Fin n) (Fin n) ℂ)
    (w : ComplexVector n) : TangentVector M x :=
  chartVec x x (WithLp.toLp 2 (W *ᵥ WithLp.ofLp w))

theorem frameVector_coordinates (x : M.Carrier) (W : Matrix (Fin n) (Fin n) ℂ)
    (w : ComplexVector n) :
    realCoord (tangentCoords x x (frameVector x W w)) = rawReal W *ᵥ realCoord w := by
  rw [frameVector, tangentCoords_chartVec x x (mem_extChartAt_source x), rawReal_mulVec]

theorem realHess_frame (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (f : M.Carrier → ℝ) (hf : SmoothFn f)
    (x : M.Carrier) (W : Matrix (Fin n) (Fin n) ℂ) (w : ComplexVector n) :
    realHess k f x (frameVector x W w) (frameVector x W w) =
      unitaryHessianQuadratic (Wᴴ * levi f x * W)
        (hessianPure (frameHessian k f x W)) (WithLp.ofLp w) := by
  rw [← frameHessian_mixed k hk hK f hf x W, hessianBlocks_quadratic]
  unfold realHess
  simp_rw [frameVector_coordinates]
  change (∑ a, ∑ b, Matrix.of (realHessInChart k f x (chartPt x x)) a b *
      (rawReal W *ᵥ realCoord w) a * (rawReal W *ᵥ realCoord w) b) = _
  rw [real_double_sum_quadratic, real_double_sum_quadratic]
  exact real_quadratic_congruence _ _ _

theorem realNormSq_frame (k : HermitianField M) (x : M.Carrier)
    (W : Matrix (Fin n) (Fin n) ℂ) (hGram : Wᴴ * gMat k x * W = 1)
    (w : ComplexVector n) :
    realNormSq k x (frameVector x W w) = 2 * ∑ j, ‖WithLp.ofLp w j‖ ^ 2 := by
  have hG : (rawReal W)ᵀ * realMetricFn k x (chartPt x x) * rawReal W =
      (2 : ℝ) • 1 := by
    rw [realMetricFn_eq_rawReal, Matrix.mul_smul, Matrix.smul_mul]
    change (2 : ℝ) • ((rawReal W)ᵀ * rawReal (gMat k x) * rawReal W) = _
    rw [rawReal_congruence, hGram, rawReal_one]
  rw [realNormSq, ← realMetricTensor_quadratic k x (frameVector x W w)]
  simp_rw [frameVector_coordinates]
  rw [real_double_sum_quadratic, real_quadratic_congruence, hG]
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
  congr 1
  simp only [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, realCoord,
    Complex.sq_norm, Complex.normSq_apply, ↓reduceIte, Fin.one_eq_zero_iff]
  apply Finset.sum_congr rfl
  intro j _
  norm_num


end Yau.Proofs.C05HessianFrameEnergyBindingAux
