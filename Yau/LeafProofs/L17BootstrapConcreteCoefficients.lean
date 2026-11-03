import Yau.LeafProofs.L17BootstrapBackgroundDifference
import Yau.LeafProofs.L17BootstrapPositiveBaseHolderAffine

/-! The actual shifted background coefficient, as a smooth Hölder Banach element. -/

noncomputable section
open Set Metric
open scoped Classical Topology ContDiff Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

namespace Yau.LeafProofs.L17BootstrapConcreteCoefficientsAux
open L17Aux L17HolderAux L17SchauderAux L17SmallTranslationAux L17BootstrapPatchAux
open L17LocalHolderBanachAlgebraAux L17BootstrapBackgroundDifferenceAux
open L17BootstrapPositiveBaseHolderAux

local instance concreteCoefficientsMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {T beta : ℝ} {x : M.Carrier}
variable (D : BootstrapPatch P x) (h2rho : 2*P.radius < P.charts.radius)
variable (hT : 0 < T) (hTime : T ≤ P.radius^2) (hb0 : 0 < beta) (hb1 : beta < 1)
  (hr : P.radius ≤ 1)

/-- Evaluation at the actual zero potential uses the affine definition of Hstar. -/
theorem Hstar_zero_value (q : LocalCylinder P T) :
    Hstar P hT hTime hb0.le hb1.le hr 0 q =
      pullbackMatrix g (P.charts.chart q.1) q.2.1 -
        (q.2.2 : ℂ) • pullbackRicci g (P.charts.chart q.1) q.2.1 := by
  rw [Hstar,(potentialLeviBanachCLM P T beta hT).map_zero,add_zero]
  change backgroundMatrixBanach P hTime hb1.le hr q -
    timeScalarActionCLM P hT hb0.le (hb1.le.trans (by norm_num)) hr
      (ricciMatrixBanach P hTime hb1.le hr) q = _
  rw [backgroundMatrixBanach_value,timeScalarActionCLM_value,
    ricciMatrixBanach_value,matrixRealScalar_eq_complexScalar]

/-- A concrete coefficient; no Hölder element or smoothness proof is supplied by the caller. -/
def c0Hat (θ : ComplexVector n) :
    LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T beta :=
  Hstar P hT hTime hb0.le hb1.le hr 0 +
    (backgroundDifferences D h2rho hT hTime hb0 hb1).matrixHat θ

theorem c0Hat_contDiffOn :
    ContDiffOn ℝ ∞ (c0Hat D h2rho hT hTime hb0 hb1 hr)
      (ball 0 (D.smallRadius/2)) :=
  contDiffOn_const.add (backgroundDifferences D h2rho hT hTime hb0 hb1).matrix_contDiff

theorem c0Hat_zero :
    c0Hat D h2rho hT hTime hb0 hb1 hr 0 = Hstar P hT hTime hb0.le hb1.le hr 0 := by
  simp only [c0Hat,(backgroundDifferences D h2rho hT hTime hb0 hb1).matrix_zero,add_zero]

/-- The selected chart is translated; every other chart retains its actual background. -/
theorem c0Hat_value {θ : ComplexVector n} (hθ : θ ∈ ball 0 (D.smallRadius/2))
    (q : LocalCylinder P T) :
    c0Hat D h2rho hT hTime hb0 hb1 hr θ q =
      if q.1 = D.center then
        pullbackMatrix g (P.charts.chart q.1) (cutoffTranslation D.bump θ q.2.1) -
          (q.2.2 : ℂ) • pullbackRicci g (P.charts.chart q.1) (cutoffTranslation D.bump θ q.2.1)
      else pullbackMatrix g (P.charts.chart q.1) q.2.1 -
        (q.2.2 : ℂ) • pullbackRicci g (P.charts.chart q.1) q.2.1 := by
  change Hstar P hT hTime hb0.le hb1.le hr 0 q +
    localFun _ ((backgroundDifferences D h2rho hT hTime hb0 hb1).matrixHat θ).value q = _
  rw [Hstar_zero_value hT hTime hb0 hb1 hr,
    (backgroundDifferences D h2rho hT hTime hb0 hb1).matrix_value θ hθ q]
  by_cases hq : q.1 = D.center
  · simp only [matrixFamily,hq,↓reduceIte,matrixSpecial,smul_sub]
    abel
  · simp only [matrixFamily,ite_eq_right hq,add_zero]

theorem c0Hat_collar {θ : ComplexVector n} (hθ : θ ∈ ball 0 (D.smallRadius/2))
    (q : LocalCylinder P T)
    (hq : q.1 ≠ D.center ∨ (q.2.1 : ComplexVector n) ∉ tsupport D.bump) :
    c0Hat D h2rho hT hTime hb0 hb1 hr θ q = Hstar P hT hTime hb0.le hb1.le hr 0 q := by
  change Hstar P hT hTime hb0.le hb1.le hr 0 q +
    localFun _ ((backgroundDifferences D h2rho hT hTime hb0 hb1).matrixHat θ).value q = _
  rw [(backgroundDifferences D h2rho hT hTime hb0 hb1).matrix_collar θ hθ q hq,add_zero]

end Yau.LeafProofs.L17BootstrapConcreteCoefficientsAux
