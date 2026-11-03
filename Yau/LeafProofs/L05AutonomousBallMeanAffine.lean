import Yau.LeafProofs.L05AutonomousBallMeanTranslation

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic

theorem auto_ballMean_affine_hasFDerivAt {n : ℕ} (S : Space n →L[ℝ] Space n)
    (x y : Space n) : HasFDerivAt (fun z : Space n => x+S z) S y := by
  convert! (hasFDerivAt_const x y).add (S.hasFDerivAt (x := y)) using 1 <;> simp only [Pi.add_apply,zero_add]

theorem auto_ballMean_affine_second {n : ℕ} {f : Space n → ℝ}
    (S : Space n →L[ℝ] Space n) (x y : Space n)
    (hf : ContDiffAt ℝ 2 f (x+S y)) (e : Space n) :
    (fderiv ℝ (fderiv ℝ (fun z : Space n => f (x+S z))) y) e e=
      (fderiv ℝ (fderiv ℝ f) (x+S y)) (S e) (S e) := by
  have hAff (z : Space n) := auto_ballMean_affine_hasFDerivAt S x z
  have hC : ContDiffAt ℝ 2 (fun z : Space n => f (x+S z)) y :=
    hf.comp y (contDiffAt_const.add S.contDiff.contDiffAt)
  have hCont : Continuous (fun z : Space n => x+S z) := continuous_const.add S.continuous
  have hNear : ∀ᶠ z : Space n in 𝓝 y, ContDiffAt ℝ 2 f (x+S z) :=
    hCont.continuousAt.tendsto.eventually (hf.eventually (by norm_num))
  have hEq : (fun z : Space n => fderiv ℝ (fun w : Space n => f (x+S w)) z e)=ᶠ[𝓝 y]
      (fun z : Space n => fderiv ℝ f (x+S z) (S e)) := by
    filter_upwards [hNear] with z hz
    have hD := (hz.differentiableAt (by norm_num)).hasFDerivAt.comp z (hAff z)
    change (fderiv ℝ (f ∘ (fun w : Space n => x+S w)) z) e=_
    rw [hD.fderiv]
    rfl
  have hF : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) (x+S y)) (x+S y) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hD := ((hF.comp y (hAff y)).clm_apply (hasFDerivAt_const (S e) y)).fderiv
  simp only [Function.comp_def] at hD
  have h := congrArg (fun L : Space n →L[ℝ] ℝ => L e) hEq.fderiv_eq
  rw [auto_ballMean_direction_second hC e,hD] at h
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,ContinuousLinearMap.comp_zero,zero_apply,add_zero,zero_add] using h

end Yau.LeafProofs.L05AutonomousAux
