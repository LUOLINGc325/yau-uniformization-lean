import Yau.LeafProofs.L10Exact
import Yau.Proofs.D05ScalarCauchyGreenLinear

/-! The source's fixed-disc dbar solution is four times the actual within
Wirtinger derivative of the canonical Dirichlet Green solution. -/

open scoped Topology ContDiff
open Filter MeasureTheory

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.LeafProofs

def discDbarSolution (b : ℂ → ℂ) (z : ℂ) : ℂ :=
  2 * (discEnergyPartial (discGreenSolution b) 1 z -
    Complex.I * discEnergyPartial (discGreenSolution b) Complex.I z)

theorem discDbarSolution_contDiffOn {b : ℂ → ℂ}
    (hb : ContDiffOn ℝ ∞ b (Metric.closedBall (0 : ℂ) 1)) :
    ContDiffOn ℝ ∞ (discDbarSolution b) (Metric.closedBall (0 : ℂ) 1) := by
  have hu := discGreenSolution_contDiffOn hb
  exact contDiffOn_const.mul ((discEnergyPartial_contDiffOn hu 1).sub
    (contDiffOn_const.mul (discEnergyPartial_contDiffOn hu Complex.I)))

theorem discDbarSolution_eq_four_wirt (b : ℂ → ℂ) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    discDbarSolution b z = 4 * wirt (discGreenSolution b) z 1 := by
  simp only [discDbarSolution, discEnergyPartial_eq_fderiv _ _ hz,
    wirt, smul_eq_mul, mul_one]
  ring

theorem discDbarSolution_dbar {b : ℂ → ℂ}
    (hb : ContDiffOn ℝ ∞ b (Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    wirtBar (discDbarSolution b) z 1 = b z := by
  have hu := discEnergy_contDiffAt (discGreenSolution_contDiffOn hb) hz
  have hD := hu.fderiv_right (m := ∞) (by simp)
  have hw : DifferentiableAt ℝ (fun w => wirt (discGreenSolution b) w 1) z := by
    unfold wirt
    exact ((contDiffAt_const.mul ((hD.clm_apply contDiffAt_const).sub
      (contDiffAt_const.mul (hD.clm_apply contDiffAt_const))))).differentiableAt (by simp)
  have he : discDbarSolution b =ᶠ[𝓝 z] fun w => 4 * wirt (discGreenSolution b) w 1 := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
    exact discDbarSolution_eq_four_wirt b hw
  have hscale : wirtBar (discDbarSolution b) z 1 =
      4 * wirtBar (fun w => wirt (discGreenSolution b) w 1) z 1 := by
    simp only [wirtBar, he.fderiv_eq, fderiv_const_mul hw, smul_apply, smul_eq_mul]
    ring
  rw [hscale, D05Proof.wirtBar_wirt_eq_planarLaplacian (hu.of_le (by simp)),
    discGreenSolution_laplacian hb hz]
  ring

theorem discDbarSolution_smul {b : ℂ → ℂ}
    (hb : ContDiffOn ℝ ∞ b (Metric.closedBall (0 : ℂ) 1))
    (c : ℂ) {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    discDbarSolution (c • b) z = c * discDbarSolution b z := by
  have hu := discGreenSolution_contDiffOn hb
  have he : discGreenSolution (c • b) = fun w => c * discGreenSolution b w := by
    funext w
    exact discGreenSolution_smul c b w
  have hp (v : ℂ) :
      discEnergyPartial (discGreenSolution (c • b)) v z =
        c * discEnergyPartial (discGreenSolution b) v z := by
    rw [he]
    exact discEnergyPartial_clm ((ContinuousLinearMap.mul ℝ ℂ) c) hu v hz
  simp only [discDbarSolution, hp]
  ring

theorem discDbarSolution_neg {b : ℂ → ℂ}
    (hb : ContDiffOn ℝ ∞ b (Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    discDbarSolution (-b) z = -discDbarSolution b z := by
  simpa only [neg_one_smul, neg_one_mul] using discDbarSolution_smul hb (-1) hz

end Yau.Blueprint.V02Proof
