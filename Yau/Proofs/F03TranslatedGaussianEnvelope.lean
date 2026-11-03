import Yau.Proofs.F03TerminalEnvelopeGaussian
import Yau.Proofs.F03GaussianSingleCenter
import Yau.Proofs.F03CoarseKernelBound

/-! The genuine terminal-density Gaussian envelope may be centered at any actual point. -/
noncomputable section
open MeasureTheory Set
namespace Yau.Proofs.F03Aux
open Yau Blueprint LeafProofs.L18Aux LeafProofs.L24Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem localizedFlow_translated_gaussian_envelope_integrable
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 ≤ T)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (x : Pt X) {c : ℝ} (hc : 0 < c) :
    Integrable (fun y => Real.exp (-c*(inducedDistance X.metric.form x y)^2)*(1+ρ y T)) μ := by
  let R := inducedDistance X.metric.form o x+1
  have hR : 1 ≤ R := by dsimp [R];linarith [X.metric.induced_distance_nonneg o x]
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hInt := (localizedFlow_terminal_envelope_gaussian_integrable X o h U P ρ hf hT μ hμ
    (half_pos hc) hR).const_mul (Real.exp c)
  apply hInt.mono'
    ((Real.continuous_exp.comp (((LeafProofs.L12Aux.continuous_distFrom X.metric x).pow 2).const_mul (-c))).aestronglyMeasurable.mul
      (continuous_const.add (continuous_of_smoothFn (LeafProofs.L19Aux.smoothSpaceTime_slice hf.2.2.2.1 hT))).aestronglyMeasurable)
  apply ae_of_all μ
  intro y
  have hρ0 := (hf.2.2.2.2.2.2.2.2.2.1 y T hT).2
  change |Real.exp (-c*inducedDistance X.metric.form x y^2)*(1+ρ y T)| ≤ _
  rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (by linarith))]
  have hExponent := nearby_gaussian_exponent (c := c)
    (d := inducedDistance X.metric.form x y) (D := inducedDistance X.metric.form o y)
    (t := R^2) (s := 1) (r := R) hc.le (sq_pos_of_pos hR0) zero_lt_one
    (by nlinarith) hR0.le rfl (X.metric.induced_distance_nonneg x y)
    (X.metric.induced_distance_nonneg o y)
    (by dsimp [R];linarith [X.metric.induced_distance_triangle o x y])
  have hExp : Real.exp (-c*inducedDistance X.metric.form x y^2) ≤
      Real.exp c*Real.exp (-(c/2)*(inducedDistance X.metric.form o y/R)^2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    convert hExponent using 1 <;> simp only [div_pow,div_one] <;> ring
  convert mul_le_mul_of_nonneg_right hExp (show 0 ≤ 1+ρ y T by linarith) using 1 <;> ring

end Yau.Proofs.F03Aux
