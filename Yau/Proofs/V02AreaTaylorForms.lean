import Yau.Proofs.V02AreaTaylorKernel
import Yau.Proofs.V03AreaFamilySmoothness
import Yau.Proofs.V03EuclideanAreaVariation
import Yau.Proofs.V03AmbientBaseTensor
import Yau.Proofs.V03AmbientGaussTensor

/-! The sum of the three original spatial area forms in a fixed genuine
cotangent chart. These are the original metric, Euclidean immersion and Gauss forms. -/

open scoped Topology ContDiff Matrix Manifold

noncomputable section
namespace Yau.Blueprint.V02AreaTaylorProof
open Yau Yau.Blueprint V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

def spatialChartBilinear (G : CotangentPoint X.manifold → ComplexVector q)
    (g : HermitianField X.manifold) (x : Pt X) (z : CotangentCoord n) :
    CotangentCoord n →L[ℝ] CotangentCoord n →L[ℝ] ℝ :=
  pullbackBilinear (matrixKahlerBilinear (hMat g x z.1))
      (ContinuousLinearMap.fst ℝ (ComplexVector n) (ComplexVector n)) +
    pullbackBilinear (matrixKahlerBilinear (1 : Matrix (Fin q) (Fin q) ℂ))
      ((fderiv ℂ (fun w => G (cotangentChartInv x w)) z).restrictScalars ℝ) +
    scalarLeviBilinear (gaussPotential G x) z

theorem spatialChartBilinear_contDiffOn {G : CotangentPoint X.manifold → ComplexVector q}
    (hG : CotangentImmersion G) (x : Pt X) :
    ContDiffOn ℝ ∞ (spatialChartBilinear G X.metric.form x) (cotangentTarget x) := by
  have hopen : IsOpen (cotangentTarget x) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ
  have hbase : ContDiffOn ℝ ∞
      (fun z : CotangentCoord n => matrixKahlerBilinear (hMat X.metric.form x z.1))
      (cotangentTarget x) := matrixKahlerBilinear_contDiffOn (fun a b =>
    (hMat_contDiffOn X.metric x a b).comp contDiff_fst.contDiffOn (fun p hp => hp.1))
  have hbasePull := pullbackBilinear_contDiffOn hbase
    (contDiffOn_const (c := ContinuousLinearMap.fst ℝ (ComplexVector n) (ComplexVector n)))
  have hD := (cotangentHolomorphic_chart_contDiffOn hG.1 x).fderiv_of_isOpen hopen
    (m := ∞) (by simp)
  have hDR : ContDiffOn ℝ ∞ (fun z =>
      (fderiv ℂ (fun w => G (cotangentChartInv x w)) z).restrictScalars ℝ) (cotangentTarget x) := by
    apply contDiffOn_clm_apply.mpr
    intro v
    exact (hD.clm_apply (contDiffOn_const (c := v))).restrict_scalars ℝ
  have heuclidean := pullbackBilinear_contDiffOn
    (contDiffOn_const (c := matrixKahlerBilinear (1 : Matrix (Fin q) (Fin q) ℂ))) hDR
  have hpot : ContDiffOn ℝ ∞ (gaussPotential G x) (cotangentTarget x) :=
    fun z hz => (gaussPotential_contDiffAt hG x hz).contDiffWithinAt
  exact (hbasePull.add heuclidean).add (scalarLeviBilinear_contDiffOn hopen hpot)

theorem complexDiagonal_add (A B : CotangentCoord n →L[ℝ] CotangentCoord n →L[ℝ] ℝ)
    (v : CotangentCoord n) :
    complexDiagonal (A + B) v = complexDiagonal A v + complexDiagonal B v := by
  simp only [complexDiagonal, add_apply]
  ring

theorem complexDiagonal_pullback {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
    (A : F →L[ℝ] F →L[ℝ] ℝ) (T : E →L[ℂ] F) (v : E) :
    complexDiagonal (pullbackBilinear A (T.restrictScalars ℝ)) v = complexDiagonal A (T v) := by
  simp only [complexDiagonal, pullbackBilinear_apply, ContinuousLinearMap.coe_restrictScalars', map_smul]

theorem euclidean_complexDiagonal (v : ComplexVector q) :
    complexDiagonal (matrixKahlerBilinear (1 : Matrix (Fin q) (Fin q) ℂ)) v = 2 * ‖v‖ ^ 2 := by
  rw [complexDiagonal_eq_twoForm, ← matrixKahlerTwoForm,
    matrixKahlerTwoForm_diagonal Matrix.isHermitian_one]
  rw [Matrix.one_mulVec, dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
  simp [inner_self_eq_norm_sq_to_K, pow_two]

theorem spatialChartBilinear_diagonal {G : CotangentPoint X.manifold → ComplexVector q}
    (hG : CotangentImmersion G) (x : Pt X) {z : CotangentCoord n} (hz : z ∈ cotangentTarget x)
    (v : CotangentCoord n) :
    complexDiagonal (spatialChartBilinear G X.metric.form x z) v =
      2 * hermitianChartNormSq X.metric.form x z.1 v.1 +
        2 * ‖fderiv ℂ (fun w => G (cotangentChartInv x w)) z v‖ ^ 2 +
          2 * realLeviValue (gaussPotential G x) z v := by
  rw [spatialChartBilinear, complexDiagonal_add, complexDiagonal_add]
  have hfst := complexDiagonal_pullback (matrixKahlerBilinear (hMat X.metric.form x z.1))
    (ContinuousLinearMap.fst ℂ (ComplexVector n) (ComplexVector n)) v
  have hfstEq : (ContinuousLinearMap.fst ℂ (ComplexVector n) (ComplexVector n)).restrictScalars ℝ =
      ContinuousLinearMap.fst ℝ (ComplexVector n) (ComplexVector n) := by
    apply ContinuousLinearMap.ext
    intro w
    rfl
  rw [hfstEq] at hfst
  rw [hfst, complexDiagonal_pullback, euclidean_complexDiagonal]
  rw [complexDiagonal_eq_twoForm, ← matrixKahlerTwoForm,
    matrixKahlerTwoForm_diagonal (hMat_isHermitian X.metric.form x z.1)]
  rw [complexDiagonal_eq_twoForm, ← scalarLeviTwoForm,
    scalarLeviTwoForm_diagonal ((gaussPotential_contDiffAt hG x hz).of_le (by simp))]
  rfl

end Yau.Blueprint.V02AreaTaylorProof
