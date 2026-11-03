import Yau.Proofs.E02PeanoUnique

open Set Filter Asymptotics
open scoped Topology ContDiff Asymptotics
noncomputable section
namespace Yau.NodeProofs.E02Aux

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual expansion along an affine chart/time slice. Only its
linear part acts on the jet, with a genuine operator-norm remainder bound. -/
theorem realSecondJet_comp_affine {f : F → ℝ} {x : E} {p : F →L[ℝ] ℝ}
    {A : F →L[ℝ] F →L[ℝ] ℝ} (a : F) (L : E →L[ℝ] F)
    (hf : RealSecondJet f (a+L x) p A) :
    RealSecondJet (fun y => f (a+L y)) x (p.comp L) (A.bilinearComp L L) := by
  refine ⟨?_,?_⟩
  · intro v w
    exact hf.1 (L v) (L w)
  · have hDelta (y : E) : a+L y-(a+L x) = L (y-x) := by rw [map_sub]; abel
    have hComp := hf.2.comp_tendsto (continuous_const.add L.continuous).continuousAt.tendsto
    have hBound : (fun y => ‖a+L y-(a+L x)‖^2) =O[𝓝 x] (fun y => ‖y-x‖^2) := by
      simpa only [hDelta] using norm_square_comp_continuousLinearMap_bigO L x
    convert hComp.trans_isBigO hBound using 1
    funext y
    simp only [Function.comp_def,Pi.add_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.bilinearComp_apply,hDelta]

theorem affinePullback_second_fderiv {f : F → ℝ} {x : E} (a : F) (L : E →L[ℝ] F)
    (hf : ContDiffAt ℝ 2 f (a+L x)) :
    fderiv ℝ (fderiv ℝ (fun y => f (a+L y))) x =
      (fderiv ℝ (fderiv ℝ f) (a+L x)).bilinearComp L L := by
  have hAff : ContDiffAt ℝ 2 (fun y => a+L y) x :=
    (contDiff_const.add L.contDiff).contDiffAt
  exact realSecondJet_second_fderiv_eq
    (realSecondJet_comp_affine a L (realSecondJet_of_contDiffAt_two hf)) (hf.comp x hAff)

end Yau.NodeProofs.E02Aux
