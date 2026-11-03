import Yau.LeafProofs.L17GaussianLaplacian
import Yau.LeafProofs.L17GaussianResidualSum

/-! Each actual transported Gaussian satisfies its original metric equation with its actual residual. -/

open Set Metric Filter
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux

open Yau.Parabolic L17HolderAux L17SourceLocalizationAux L17LocalizedSchauderAux L17ParabolicOperatorAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem gaussianTerm_equation (P : UniformChartPartition g) (T : ℝ) (hT : 0 < T)
    (hSmall : T ≤ P.radius^2) (hRadius : 2*P.radius < P.charts.radius)
    {γ C : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1) (f : HolderSpace P T γ) (p : P.centers)
    (hf : HolderBound γ Set.univ (rescaledSource P T hT.le f p) C)
    (x : M.Carrier) (t : Time T) :
    gaussianTimeTerm P T hT.le f p (x,t)-laplacian g (fun y => gaussianTerm P T hT.le f p (y,t)) x =
      P.weight p x*holderFun f (x,t)+rawLocalizedTerm P T p (physicalGaussianResidual P T hT.le f p) (x,t) := by
  classical
  have hu := localGaussian_c2_of_source_holder P T hT hSmall hγ hγ1 f p hf
  by_cases hx : x ∈ P.charts.chart p '' closedBall 0 P.radius
  · let e := P.charts.chart p
    let z : Space n := e.symm x
    obtain ⟨hxT,hzClosed⟩ := inverseChart_mem_of_cover P p hx
    have hzSource : z ∈ e.source := chart_closedBall_source P p hzClosed
    have hzTwo : z ∈ ball (0 : Space n) (2*P.radius) :=
      (closedBall_subset_ball (by have := P.radius_pos; linarith)) hzClosed
    have hEZ : e z=x := e.right_inv hxT
    have hNative := gaussianTerm_native_contDiffAt P T hT.le f p hu x t
    rw [← hEZ] at hNative
    have hLap := laplacian_eq_backgroundChart_scalarSymbol g e (P.charts.differentiable p)
      (P.charts.inverse_differentiable p) (fun y => gaussianTerm P T hT.le f p (y,t)) hzSource hNative
    rw [hEZ] at hLap
    have hGerm : (fun w => gaussianTerm P T hT.le f p (e w,t)) =ᶠ[𝓝 z]
        (fun w => P.localization p (e w)*localGaussian P T hT.le f p (w,(t : ℝ))) := by
      filter_upwards [e.open_source.mem_nhds hzSource] with w hw
      change P.localization p (e w)*localGaussian P T hT.le f p (e.symm (e w),(t : ℝ)) = _
      rw [e.left_inv hw]
    rw [realHessianContraction_congr_of_eventuallyEq hGerm] at hLap
    change laplacian g (fun y => gaussianTerm P T hT.le f p (y,t)) x =
      realHessianContraction (chartCoefficient P.charts p z)
        (fun w => P.localization p (e w)*localGaussian P T hT.le f p (w,(t : ℝ))) z at hLap
    have hCoupling := localizedSource_partition_coupling P T hT.le f p (x,t)
    change P.localization p x*(if x ∈ e.target then localizedSource P T hT.le f p (z,(t : ℝ)) else 0) = _ at hCoupling
    rw [ite_eq_left hxT] at hCoupling
    have hRaw : rawLocalizedTerm P T p (physicalGaussianResidual P T hT.le f p) (x,t) =
        localGaussianResidual P T hT.le f p (z,(t : ℝ)) := by
      rw [rawLocalizedTerm,ite_eq_left hx,physicalGaussianResidual,ite_eq_left hzTwo]
    have hPDE := localGaussianResidual_equation P T hT hSmall hRadius hγ hγ1 f p hf
      (q := (z,(t : ℝ))) ⟨hzTwo,t.property⟩
    simp only [linearOp,zero_mul,Finset.sum_const_zero,sub_zero] at hPDE
    change timeD (cylinder Set.univ 0 T)
      (fun r => P.localization p (e r.1)*localGaussian P T hT.le f p r) (z,(t : ℝ)) -
      realHessianContraction (chartCoefficient P.charts p z)
        (fun w => P.localization p (e w)*localGaussian P T hT.le f p (w,(t : ℝ))) z =
      P.localization p (e z)*localizedSource P T hT.le f p (z,(t : ℝ))+
        localGaussianResidual P T hT.le f p (z,(t : ℝ)) at hPDE
    rw [timeD_spatial_mul hu (fun w : Space n => P.localization p (e w))
      (show (z,(t : ℝ)) ∈ cylinder Set.univ 0 T from ⟨mem_univ _,t.property⟩)] at hPDE
    rw [hEZ,hCoupling] at hPDE
    change P.localization p x*timeD (cylinder Set.univ 0 T) (localGaussian P T hT.le f p) (z,(t : ℝ)) - _ = _
    rw [hLap,hRaw]
    exact hPDE
  · have hTime : gaussianTimeTerm P T hT.le f p (x,t) = 0 :=
      localizedTerm_zero_of_not_cover P T p _ (x,t) hx
    have hLap := gaussianTerm_laplacian_zero_of_not_cover P T hT.le f p x t hx
    have hRaw := rawLocalizedTerm_zero_of_not_cover P T p (physicalGaussianResidual P T hT.le f p) (x,t) hx
    have hWeight : P.weight p x=0 := by
      have h := P.localization_mul_weight p x
      rw [localization_zero_of_not_cover P p hx,zero_mul] at h
      exact h.symm
    simp only [hTime,hLap,hRaw,hWeight,zero_mul,sub_self,add_zero]

end Yau.LeafProofs.L17Aux
