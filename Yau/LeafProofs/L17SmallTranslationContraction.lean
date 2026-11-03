import Yau.LeafProofs.L17SmallTranslationBlock
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.MetricSpace.Contracting

open Set Metric
open scoped Topology NNReal ContDiff
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17SmallTranslationAux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def smallTranslationRadius (L : ℝ) : ℝ := 1/(4*(1+L))

theorem smallTranslationRadius_pos {L : ℝ} (hL : 0 ≤ L) : 0 < smallTranslationRadius L := by
  unfold smallTranslationRadius
  positivity

def cutoffTranslation (χ : E → ℝ) (θ z : E) : E := z+χ z • θ

def cutoffInverseStep (χ : E → ℝ) (θ y z : E) : E := y-χ z • θ

theorem cutoffTranslation_zero_parameter (χ : E → ℝ) (z : E) : cutoffTranslation χ 0 z=z := by
  simp [cutoffTranslation]

theorem cutoffTranslation_fixed_of_zero (χ : E → ℝ) (θ : E) {z : E} (hz : χ z=0) :
    cutoffTranslation χ θ z=z := by simp [cutoffTranslation,hz]

theorem cutoffTranslation_of_one (χ : E → ℝ) (θ : E) {z : E} (hz : χ z=1) :
    cutoffTranslation χ θ z=z+θ := by simp [cutoffTranslation,hz]

theorem cutoffTranslation_joint_contDiff {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (fun p : E × E => cutoffTranslation χ p.1 p.2) :=
  contDiff_snd.add ((hχ.comp contDiff_snd).smul contDiff_fst)

theorem cutoffTranslation_contDiff {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) (θ : E) :
    ContDiff ℝ ∞ (cutoffTranslation χ θ) := contDiff_id.add (hχ.smul contDiff_const)

theorem cutoff_lipschitz {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) {L : ℝ}
    (hDf : ∀ z, ‖fderiv ℝ χ z‖ ≤ L) (z w : E) : |χ z-χ w| ≤ L*‖z-w‖ := by
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun x (_ : x ∈ (Set.univ : Set E)) => (hχ.differentiable (by simp)) x)
    (fun x (_ : x ∈ (Set.univ : Set E)) => hDf x) convex_univ (mem_univ w) (mem_univ z)

theorem smallTranslation_parameter_bound {L : ℝ} (hL : 0 ≤ L) {θ : E}
    (hθ : ‖θ‖ < smallTranslationRadius L) : L*‖θ‖ < 1/4 := by
  have hp : 0 < 1+L := by linarith
  calc
    L*‖θ‖ ≤ (1+L)*‖θ‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < (1+L)*(1/(4*(1+L))) := mul_lt_mul_of_pos_left hθ hp
    _ = 1/4 := by field_simp

theorem cutoffInverseStep_sub_norm_le {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) {L : ℝ}
    (hL : 0 ≤ L) (hDf : ∀ z, ‖fderiv ℝ χ z‖ ≤ L) {θ : E}
    (hθ : ‖θ‖ < smallTranslationRadius L) (y z w : E) :
    ‖cutoffInverseStep χ θ y z-cutoffInverseStep χ θ y w‖ ≤ (1/4 : ℝ)*‖z-w‖ := by
  have hid : cutoffInverseStep χ θ y z-cutoffInverseStep χ θ y w=(χ w-χ z) • θ := by
    simp only [cutoffInverseStep,sub_smul]
    abel
  rw [hid,norm_smul,Real.norm_eq_abs]
  calc
    |χ w-χ z| * ‖θ‖ ≤ (L*‖w-z‖)*‖θ‖ :=
      mul_le_mul_of_nonneg_right (cutoff_lipschitz hχ hDf w z) (norm_nonneg _)
    _ = (L*‖θ‖)*‖z-w‖ := by rw [norm_sub_rev]; ring
    _ ≤ (1/4 : ℝ)*‖z-w‖ :=
      mul_le_mul_of_nonneg_right (smallTranslation_parameter_bound hL hθ).le (norm_nonneg _)

theorem cutoffInverseStep_contracting {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) {L : ℝ}
    (hL : 0 ≤ L) (hDf : ∀ z, ‖fderiv ℝ χ z‖ ≤ L) {θ : E}
    (hθ : ‖θ‖ < smallTranslationRadius L) (y : E) :
    ContractingWith (1/4 : ℝ≥0) (cutoffInverseStep χ θ y) := by
  refine ⟨by norm_num,LipschitzWith.of_dist_le_mul ?_⟩
  intro z w
  simpa only [dist_eq_norm,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat] using
    cutoffInverseStep_sub_norm_le hχ hL hDf hθ y z w

end Yau.LeafProofs.L17SmallTranslationAux
