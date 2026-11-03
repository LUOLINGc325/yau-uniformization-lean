import Yau.LeafProofs.L17BootstrapPatch
import Yau.LeafProofs.L17BackgroundLogDetJets
import Yau.LeafProofs.L17MatrixHolderReconstruction
import Yau.LeafProofs.L17BackgroundFunctionSmooth

/-! Ordinary smoothness of the actual background differences, in Frobenius norm. -/

noncomputable section
open Set Metric
open scoped Topology ContDiff Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

namespace Yau.LeafProofs.L17BootstrapBackgroundDifferenceAux
open L17Aux L17HolderAux L17SchauderAux L17SmallTranslationAux L17BootstrapPatchAux

local instance backgroundDifferenceMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem backgroundMatrix_contDiffOn (A : BoundedChartFamily g) (p : M.Carrier) :
    ContDiffOn ℝ ∞ (pullbackMatrix g (A.chart p)) (ball 0 A.radius) := by
  have hs : ContDiffOn ℝ ∞
      (fun z => ∑ i, ∑ j, matrixSingleCLM i j (pullbackMatrix g (A.chart p) z i j))
      (ball 0 A.radius) := by
    apply ContDiffOn.sum
    intro i hi
    apply ContDiffOn.sum
    intro j hj
    exact (matrixSingleCLM i j).contDiff.comp_contDiffOn (A.coefficient_smooth p i j)
  apply hs.congr
  intro z hz
  exact (Matrix.sum_sum_single _).symm

theorem backgroundRicci_contDiffOn (A : BoundedChartFamily g) (p : M.Carrier) :
    ContDiffOn ℝ ∞ (pullbackRicci g (A.chart p)) (ball 0 A.radius) := by
  apply ((leviHessianCLM n).contDiff.comp_contDiffOn
    (A.backgroundLogDet_hessian_smooth p)).neg.congr
  intro z hz
  change -leviC (A.backgroundLogDet p) z =
    -leviHessianCLM n (fderiv ℝ (fderiv ℝ (A.backgroundLogDet p)) z)
  rw [leviC_eq_leviHessianCLM (((A.backgroundLogDet_smooth p).contDiffAt
    (isOpen_ball.mem_nhds hz)).of_le (by simp))]

variable {P : UniformChartPartition g} {x : M.Carrier} (D : BootstrapPatch P x)

def differenceRadius : ℝ := D.smallRadius/2

theorem differenceRadius_pos : 0 < differenceRadius D := by
  unfold differenceRadius
  exact div_pos D.smallRadius_pos (by norm_num)

theorem differenceRadius_lt : differenceRadius D < D.smallRadius := by
  unfold differenceRadius
  linarith [D.smallRadius_pos]

def specialDomain : Set (ComplexVector n × (ComplexVector n × ℝ)) :=
  ball 0 D.smallRadius ×ˢ (ball 0 (2*P.radius) ×ˢ univ)

theorem coordinate_mapsTo_double {θ : ComplexVector n} (hθ : θ ∈ ball 0 D.smallRadius) :
    MapsTo (cutoffTranslation D.bump θ) (ball 0 (2*P.radius)) (ball 0 (2*P.radius)) :=
  D.coordinate_mapsTo (by simpa only [mem_ball,dist_zero_right] using hθ) _
    (D.bump_support_ball_quarter.trans (ball_subset_ball (by linarith [P.radius_pos])))

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem background_joint_contDiffOn {f : ComplexVector n → F}
    (h2rho : 2*P.radius < P.charts.radius)
    (hf : ContDiffOn ℝ ∞ f (ball 0 P.charts.radius)) :
    ContDiffOn ℝ ∞ (fun a : ComplexVector n × (ComplexVector n × ℝ) => f a.2.1)
      (specialDomain D) :=
  hf.comp (contDiff_snd.fst.contDiffOn) (fun _a ha => (ball_subset_ball h2rho.le) ha.2.1)

theorem translated_joint_contDiffOn {f : ComplexVector n → F}
    (h2rho : 2*P.radius < P.charts.radius)
    (hf : ContDiffOn ℝ ∞ f (ball 0 P.charts.radius)) :
    ContDiffOn ℝ ∞
      (fun a : ComplexVector n × (ComplexVector n × ℝ) => f (cutoffTranslation D.bump a.1 a.2.1))
      (specialDomain D) := by
  apply hf.comp ((cutoffTranslation_joint_contDiff D.bump_smooth).comp
    (contDiff_fst.prodMk contDiff_snd.fst)).contDiffOn
  intro a ha
  exact (ball_subset_ball h2rho.le) (coordinate_mapsTo_double D ha.1 ha.2.1)

def matrixSpecial (θ z : ComplexVector n) (t : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  pullbackMatrix g (P.charts.chart D.center) (cutoffTranslation D.bump θ z) -
    pullbackMatrix g (P.charts.chart D.center) z -
    (t : ℂ) • (pullbackRicci g (P.charts.chart D.center) (cutoffTranslation D.bump θ z) -
      pullbackRicci g (P.charts.chart D.center) z)

def logSpecial (θ z : ComplexVector n) (_t : ℝ) : ℝ :=
  P.charts.backgroundLogDet D.center (cutoffTranslation D.bump θ z) -
    P.charts.backgroundLogDet D.center z

def normalizationSpecial (_θ z : ComplexVector n) (_t : ℝ) : ℝ :=
  chartWeightSum P.charts P.centers P.radius P.radius_pos (P.charts.chart D.center z)

theorem matrixSpecial_contDiffOn (h2rho : 2*P.radius < P.charts.radius) :
    ContDiffOn ℝ ∞ (fun a : ComplexVector n × (ComplexVector n × ℝ) =>
      matrixSpecial D a.1 a.2.1 a.2.2) (specialDomain D) := by
  have hG := backgroundMatrix_contDiffOn P.charts D.center
  have hRic := backgroundRicci_contDiffOn P.charts D.center
  exact ((translated_joint_contDiffOn D h2rho hG).sub (background_joint_contDiffOn D h2rho hG)).sub
    (((Complex.ofRealCLM.contDiff.comp contDiff_snd.snd).contDiffOn).smul
      ((translated_joint_contDiffOn D h2rho hRic).sub (background_joint_contDiffOn D h2rho hRic)))

theorem logSpecial_contDiffOn (h2rho : 2*P.radius < P.charts.radius) :
    ContDiffOn ℝ ∞ (fun a : ComplexVector n × (ComplexVector n × ℝ) =>
      logSpecial D a.1 a.2.1 a.2.2) (specialDomain D) :=
  (translated_joint_contDiffOn D h2rho (P.charts.backgroundLogDet_smooth D.center)).sub
    (background_joint_contDiffOn D h2rho (P.charts.backgroundLogDet_smooth D.center))

theorem normalizationSpecial_contDiffOn (h2rho : 2*P.radius < P.charts.radius) :
    ContDiffOn ℝ ∞ (fun a : ComplexVector n × (ComplexVector n × ℝ) =>
      normalizationSpecial D a.1 a.2.1 a.2.2) (specialDomain D) :=
  background_joint_contDiffOn D h2rho
    (smoothFn_comp_backgroundChart_contDiffOn P.charts P.chartWeightSum_smoothFn D.center)

end Yau.LeafProofs.L17BootstrapBackgroundDifferenceAux
