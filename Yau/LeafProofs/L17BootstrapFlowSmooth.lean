import Yau.LeafProofs.L17BootstrapFlowSmoothScalar
import Yau.LeafProofs.L17BootstrapFlowSmoothMetric
import Yau.LeafProofs.L17BootstrapFlowPullback

noncomputable section
open Set Metric
open scoped Topology ContDiff
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapFlowSmoothAux
open L17Aux L17HolderAux L17SchauderAux L17BootstrapPositiveBaseHolderAux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
    {P : UniformChartPartition g} {T : ℝ} {hT : 0<T}

theorem potentialFlow_smooth_of_local_jets
    (hg : MetricSmooth g) (hTime : T≤P.radius^2) (hr : P.radius≤1)
    (u : SchauderSpace P T (1/4) hT)
    (hSmall : ‖u‖+T*backgroundLogDetHessianBudget P.charts≤(P.charts.bound 0)⁻¹)
    (hJets : ∀ y : M.Carrier, ∃ p : P.centers, ∃ z0 : ComplexVector n, ∃ r : ℝ,
      0<r ∧ z0∈ball 0 P.radius ∧ P.charts.chart p z0=y ∧
      ∃ hCoord : MapsTo (fun theta : ComplexVector n => z0+theta)
        (ball 0 r) (ball 0 P.radius),
      ∃ f : ComplexVector n × ℝ → ℝ, ∃ Q : ComplexVector n × ℝ → D2 n,
        ContDiffOn ℝ ∞ f (ball 0 r ×ˢ Icc (0:ℝ) T) ∧
        ContDiffOn ℝ ∞ Q (ball 0 r ×ˢ Icc (0:ℝ) T) ∧
        EqOn f (fun q : ComplexVector n × ℝ =>
          potentialFunction u (P.charts.chart p (z0+q.1)) q.2)
          (ball 0 r ×ˢ Icc (0:ℝ) T) ∧
        ∀ (theta : ComplexVector n) (htheta : theta∈ball 0 r), ∀ t : Time T,
          Q (theta,(t:ℝ))=hessianFun u ⟨p,(⟨z0+theta,hCoord htheta⟩,t)⟩) :
    SmoothSpaceTime (potentialFunction u) (Icc (0:ℝ) T) ∧
      MetricFamilySmooth (potentialFlowField hg u hSmall) (Icc (0:ℝ) T) := by
  constructor
  · apply potentialFunction_smooth_of_local_profiles u (Icc (0:ℝ) T)
    intro y
    obtain ⟨p,z0,r,hr0,hz,hzy,hCoord,f,Q,hf,hQ,hVal,hStored⟩ := hJets y
    exact ⟨p,z0,r,hr0,hz,hzy,f,hf,hVal⟩
  · apply potentialFlow_metricSmooth_of_local_profiles hg u hSmall
    intro y
    obtain ⟨p,z0,r,hr0,hz,hzy,hCoord,f,Q,hf,hQ,hVal,hStored⟩ := hJets y
    refine ⟨p,z0,r,hr0,hz,hzy,hCoord,Q,hQ,?_⟩
    intro theta htheta t
    let z : ↥(ball (0 : ComplexVector n) P.radius) := ⟨z0+theta,hCoord htheta⟩
    let q : LocalCylinder P T := ⟨p,(z,t)⟩
    have hLevi : leviC (chartFunction u p t) z =
        leviHessianCLM n (hessianFun u q) := by
      exact (potentialLeviHolderCLM_value P T (1/4) hT u p z t).symm
    have hPull := L17BootstrapSmoothAux.potentialFlowField_background_pullback
      (P := P) hg hTime (by norm_num : (0:ℝ)≤1/4)
      (by norm_num : (1/4:ℝ)≤1) hr u hSmall p z t
    rw [Hstar_value,coordinateMetricError_eq,hLevi,←hStored theta htheta t] at hPull
    exact hPull
end Yau.LeafProofs.L17BootstrapFlowSmoothAux
