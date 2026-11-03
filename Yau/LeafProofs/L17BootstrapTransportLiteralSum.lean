import Yau.LeafProofs.L17BootstrapPatch
import Yau.LeafProofs.L17BootstrapTransportProfiles
import Yau.LeafProofs.L17LocalizedSchauderTimeTransport

open Set Metric
open scoped Topology ContDiff Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapTransportAux
open L17Aux L17HolderAux L17SchauderAux L17BootstrapPatchAux L17SmallTranslationAux
open L17LocalizedSchauderAux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier} {T gamma : ℝ} {hT : 0 < T}
variable (D : BootstrapPatch P x) (theta : ComplexVector n) (u : SchauderSpace P T gamma hT)

theorem globalSum_correctionFamily_single (q : Cylinder M T) :
    globalSum P T (correctionFamily D theta u) q=
      localizedTerm P T D.center (correctionValue D theta u) q := by
  rw [globalSum,finsum_eq_single _ D.center (fun p hp => by
    simp only [correctionFamily,ite_eq_right hp,localizedTerm,Pi.zero_apply,mul_zero])]
  simp only [correctionFamily,ite_true]

theorem localized_correction_eq_pullback_difference (q : Cylinder M T) :
    localizedTerm P T D.center (correctionValue D theta u) q=
      schauderFun u (D.forward theta q.1,q.2)-schauderFun u q := by
  let e := P.charts.chart D.center
  by_cases hq : q.1 ∈ e.target
  · by_cases hz : e.symm q.1 ∈ tsupport D.bump
    · have hSmall := D.bump_support_ball_quarter hz
      have hn : ‖e.symm q.1‖ < P.radius/4 := by
        simpa only [mem_ball,dist_zero_right] using hSmall
      have hHalf : e.symm q.1 ∈ closedBall (0 : ComplexVector n) (P.radius/2) := by
        apply mem_closedBall.mpr
        rw [dist_zero_right]
        linarith [P.radius_pos]
      have hLambda : P.localization D.center q.1=1 :=
        P.charts.chartLocalization_one D.center P.radius_pos P.radius_lt
          ⟨e.symm q.1,hHalf,e.right_inv hq⟩
      rw [localizedTerm,hLambda,one_mul,correctionValue,chartFunction,chartFunction]
      rw [D.forward_of_mem_target theta hq,e.right_inv hq]
    · have hChi : D.bump (e.symm q.1)=0 := by
        by_contra hn
        exact hz (subset_closure hn)
      rw [localizedTerm,correctionValue_zero_of_not_mem_support D theta u hz,mul_zero]
      rw [D.forward_of_mem_target theta hq,cutoffTranslation_fixed_of_zero D.bump theta hChi,
        e.right_inv hq,sub_self]
  · rw [localizedTerm_eq_formula,ite_eq_right hq]
    have hForward : D.forward theta q.1=q.1 := ite_eq_right hq
    rw [hForward,sub_self]

theorem globalSum_correctionFamily_value (q : Cylinder M T) :
    globalSum P T (correctionFamily D theta u) q=
      schauderFun u (D.forward theta q.1,q.2)-schauderFun u q := by
  rw [globalSum_correctionFamily_single]
  exact localized_correction_eq_pullback_difference D theta u q

end Yau.LeafProofs.L17BootstrapTransportAux
