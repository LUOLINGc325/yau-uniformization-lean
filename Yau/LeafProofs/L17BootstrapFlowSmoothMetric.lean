import Yau.LeafProofs.L17BootstrapFlowSmoothProfiles
import Yau.LeafProofs.L17BootstrapMetricSmooth
import Yau.LeafProofs.L17PotentialHermitianField

noncomputable section
open Set Metric
open scoped Topology ContDiff
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.LeafProofs.L17BootstrapFlowSmoothAux
open L17Aux L17HolderAux L17SchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
    {P : UniformChartPartition g} {T gamma : ℝ} {hT : 0<T}

/-- Apply the proved metric chart bridge to the actual local coefficient
formula. Its pointwise value identity will be supplied by the fixed pullback
theorem and the produced stored-Hessian identification in the final binding. -/
theorem potentialFlow_metricSmooth_of_local_profiles
    (hg : MetricSmooth g) (u : SchauderSpace P T gamma hT)
    (hSmall : ‖u‖+T*backgroundLogDetHessianBudget P.charts≤(P.charts.bound 0)⁻¹)
    (hProfiles : ∀ y : M.Carrier, ∃ p : P.centers, ∃ z0 : ComplexVector n, ∃ r : ℝ,
      0<r ∧ z0∈ball 0 P.radius ∧ P.charts.chart p z0=y ∧
      ∃ hCoord : MapsTo (fun theta : ComplexVector n => z0+theta)
        (ball 0 r) (ball 0 P.radius),
      ∃ Q : ComplexVector n × ℝ → D2 n,
        ContDiffOn ℝ ∞ Q (ball 0 r ×ˢ Icc (0:ℝ) T) ∧
        ∀ theta∈ball 0 r, ∀ t : Time T,
          pullbackMatrix (potentialFlowField hg u hSmall (t:ℝ))
            (P.charts.chart p) (z0+theta)=
          pullbackMatrix g (P.charts.chart p) (z0+theta)+
            (leviHessianCLM n (Q (theta,(t:ℝ)))-
              ((t:ℝ):ℂ) • pullbackRicci g (P.charts.chart p) (z0+theta))) :
    MetricFamilySmooth (potentialFlowField hg u hSmall) (Icc (0:ℝ) T) := by
  apply L17BootstrapMetricSmoothAux.metricFamilySmooth_of_local_pullback P
  intro y
  obtain ⟨p,z0,r,hr,hz,hzy,hCoord,Q,hQ,hVal⟩ := hProfiles y
  refine ⟨p,z0,r,hr,hz,hzy,?_⟩
  intro i j
  have hParam : ContDiffOn ℝ ∞ (fun a : ComplexVector n × ℝ =>
      pullbackMatrix (potentialFlowField hg u hSmall a.2)
        (P.charts.chart p) (z0+a.1) i j) (ball 0 r ×ˢ Icc (0:ℝ) T) := by
    apply (metric_profile_entry_contDiffOn P p z0 r (Icc (0:ℝ) T) hCoord hQ i j).congr
    intro a ha
    have hEntry := congrArg (fun H : Matrix (Fin n) (Fin n) ℂ => H i j)
      (hVal a.1 ha.1 ⟨a.2,ha.2⟩)
    simpa only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul] using hEntry
  apply (translated_profile_contDiffOn z0 r (Icc (0:ℝ) T) hParam).congr
  intro a ha
  have hCancel : z0+(a.1-z0)=a.1 := by abel
  change pullbackMatrix (potentialFlowField hg u hSmall a.2) (P.charts.chart p) a.1 i j =
    pullbackMatrix (potentialFlowField hg u hSmall a.2) (P.charts.chart p)
      (z0+(a.1-z0)) i j
  rw [hCancel]

end Yau.LeafProofs.L17BootstrapFlowSmoothAux
