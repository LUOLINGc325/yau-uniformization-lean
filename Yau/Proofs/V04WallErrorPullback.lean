import Yau.Proofs.V03LeviLinear

/-! Local linear pullbacks of the actual Wirtinger operators. -/

open Filter
open scoped Topology ContDiff Matrix
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux
open Yau Yau.Blueprint V03Proof

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem wirt_comp_clm (L : E →L[ℂ] F) {f : F → ℂ} {z : E}
    (hf : DifferentiableAt ℝ f (L z)) (v : E) :
    wirt (fun y => f (L y)) z v = wirt f (L z) (L v) := by
  have hd := (hf.hasFDerivAt.comp z (L.restrictScalars ℝ).hasFDerivAt).fderiv
  simp only [Function.comp_def] at hd
  simp only [wirt, hd, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', map_smul]

theorem wirtBar_comp_clm (L : E →L[ℂ] F) {f : F → ℂ} {z : E}
    (hf : DifferentiableAt ℝ f (L z)) (v : E) :
    wirtBar (fun y => f (L y)) z v = wirtBar f (L z) (L v) := by
  have hd := (hf.hasFDerivAt.comp z (L.restrictScalars ℝ).hasFDerivAt).fderiv
  simp only [Function.comp_def] at hd
  simp only [wirtBar, hd, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', map_smul]

theorem mixedWirt_comp_clm (L : E →L[ℂ] F) {f : F → ℂ} {z : E}
    (hf : ContDiffAt ℝ 2 f (L z)) (v w : E) :
    wirt (fun y => wirtBar (fun x => f (L x)) y v) z w =
      wirt (fun y => wirtBar f y (L v)) (L z) (L w) := by
  have hnear : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ 2 f (L y) :=
    L.continuous.tendsto z (hf.eventually (by norm_num))
  have heq : (fun y => wirtBar (fun x => f (L x)) y v) =ᶠ[𝓝 z]
      (fun y => wirtBar f (L y) (L v)) := by
    filter_upwards [hnear] with y hy
    exact wirtBar_comp_clm L (hy.differentiableAt (by norm_num)) v
  calc
    _ = wirt (fun y => wirtBar f (L y) (L v)) z w := by
      simp only [wirt, heq.fderiv_eq (𝕜 := ℝ)]
    _ = _ := wirt_comp_clm L (wirtBar_differentiableAt hf (L v)) w

theorem leviMatrix_comp_clm (L : E →L[ℂ] F) {f : F → ℝ} {z : E}
    (hf : ContDiffAt ℝ 2 f (L z)) (dir : ι → E) :
    leviMatrix (fun y => f (L y)) z dir = leviMatrix f (L z) (fun i => L (dir i)) := by
  ext a b
  exact mixedWirt_comp_clm L (hf.continuousLinearMap_comp Complex.ofRealCLM) (dir a) (dir b)

end Yau.Blueprint.V04Proof.WallErrorAux
