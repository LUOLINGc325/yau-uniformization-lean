import Yau.LeafProofs.L17BootstrapFlowSmoothProfiles
import Yau.LeafProofs.L17BootstrapScalarSmooth
import Yau.LeafProofs.L17PotentialHermitianField

noncomputable section
open Set Metric
open scoped Topology ContDiff
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.LeafProofs.L17BootstrapFlowSmoothAux
open L17Aux L17SchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
    {P : UniformChartPartition g} {T gamma : ℝ} {hT : 0<T}

/-- The produced local scalar profiles describe the original clamped potential
on precisely the original time set. Only spatial coordinates are translated. -/
theorem potentialFunction_smooth_of_local_profiles
    (u : SchauderSpace P T gamma hT) (I : Set ℝ)
    (hProfiles : ∀ y : M.Carrier, ∃ p : P.centers, ∃ z0 : ComplexVector n, ∃ r : ℝ,
      0<r ∧ z0∈ball 0 P.radius ∧ P.charts.chart p z0=y ∧
      ∃ f : ComplexVector n × ℝ → ℝ,
        ContDiffOn ℝ ∞ f (ball 0 r ×ˢ I) ∧
        EqOn f (fun q : ComplexVector n × ℝ =>
          potentialFunction u (P.charts.chart p (z0+q.1)) q.2) (ball 0 r ×ˢ I)) :
    SmoothSpaceTime (potentialFunction u) I := by
  apply L17BootstrapSmoothAux.smoothSpaceTime_of_local_background_charts P
  intro y
  obtain ⟨p,z0,r,hr,hz,hzy,f,hf,hVal⟩ := hProfiles y
  refine ⟨p,z0,r,hr,hz,hzy,?_⟩
  apply (translated_profile_contDiffOn z0 r I hf).congr
  intro a ha
  have hTheta : a.1-z0 ∈ ball 0 r := by
    simpa only [mem_ball,dist_eq_norm,sub_zero] using ha.1
  have hCancel : z0+(a.1-z0)=a.1 := by abel
  simpa only [hCancel] using
    (hVal (show (a.1-z0,a.2)∈ball 0 r ×ˢ I from ⟨hTheta,ha.2⟩)).symm

end Yau.LeafProofs.L17BootstrapFlowSmoothAux
