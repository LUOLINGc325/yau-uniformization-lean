import Yau.LeafProofs.L17BootstrapCandidateSelectedResidual
import Yau.LeafProofs.L17BootstrapCandidateDifferenceSupport
import Yau.LeafProofs.L17BootstrapCandidateResidualAssembly
import Yau.LeafProofs.L17BootstrapResidualLocality

noncomputable section
open Set Metric
open scoped Classical Topology ContDiff Matrix.Norms.Frobenius ComplexOrder
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapMetricAux
open L17Aux L17HolderAux L17SchauderAux L17ParabolicOperatorAux
open L17BootstrapPositiveBaseHolderAux L17LocalHolderBanachAlgebraAux L17BootstrapPatchAux
open L17BootstrapInverseHessianCoefficientsAux L17SmallTranslationAux
open L17BootstrapResidualLocalityAux
local instance candidateZeroMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier} {T gamma : ℝ} {hT : 0<T}

/-- The genuinely transported element solves the actual conjugated equation.
Its ordinary metric positivity comes from the actual branch domain; no stronger
norm bound on the transported element is imposed. -/
theorem conjugatedResidual_zero_of_transport_values (D : BootstrapPatch P x)
    {theta : ComplexVector n} (htheta : ‖theta‖<D.smallRadius)
    (hg : MetricSmooth g) (hTime : T≤P.radius^2)
    (hgamma0 : 0≤gamma) (hgamma1 : gamma≤1) (hr : P.radius≤1)
    (J : LocalHolderSpace ℝ P T gamma →L[ℝ] HolderSpace P T gamma)
    (hJ : ∀ w, holderFun (J w)=L17LocalScalarAssemblyAux.scalarAssemblyFunction P w)
    (u v : SchauderSpace P T gamma hT)
    (huZ : ‖normalizedMetricPerturbation P T gamma hT hTime hgamma0 hgamma1 hr u‖<1)
    (hvZ : ‖normalizedMetricPerturbation P T gamma hT hTime hgamma0 hgamma1 hr v‖<1)
    (huPos : ∀q : LocalCylinder P T, (Hstar P hT hTime hgamma0 hgamma1 hr u q).PosDef)
    (hvPos : ∀q : LocalCylinder P T, (Hstar P hT hTime hgamma0 hgamma1 hr v q).PosDef)
    (hEquation : scalarParabolicCLM P T gamma hT hTime hgamma1 hr u=
      globalNonlinearMap P T gamma hT hTime hgamma0 hgamma1 hr J u)
    (hValue : ∀(y : M.Carrier)(t : Time T),
      schauderFun v (y,t)=schauderFun u (D.forward theta y,t))
    (hTimeValue : ∀q : Cylinder M T, timeFun v q=timeFun u (D.forward theta q.1,q.2))
    (hInverse : ∀(z : ↥(ball (0 : ComplexVector n) P.radius))(t : Time T),
      c1 D theta z (gradientFun v ⟨D.center,(z,t)⟩)+
      c2 D theta z (hessianFun v ⟨D.center,(z,t)⟩)=
        leviC (chartFunction u D.center t) (cutoffTranslation D.bump theta z))
    (K H : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma)
    (c0 : LocalCylinder P T → Matrix (Fin n) (Fin n) ℂ)
    (dLog sigma : LocalHolderSpace ℝ P T gamma)
    (hC0 : ∀q, c0 q=shiftedBackgroundValue D theta q)
    (hH : ∀q, H q=c0 q+c1Family D theta q.1 q.2.1 q.2.2 (gradientFun v q)+
      c2Family D theta q.1 q.2.1 q.2.2 (hessianFun v q))
    (hK : ∀q : LocalCylinder P T, K q=(Hstar P hT hTime hgamma0 hgamma1 hr u q)⁻¹)
    (hSmallt : ‖relativeMetricPerturbation P T gamma K (Hstar P hT hTime hgamma0 hgamma1 hr u) H‖<1)
    (hSmall0 : ‖relativeMetricPerturbation P T gamma K (Hstar P hT hTime hgamma0 hgamma1 hr u)
      (Hstar P hT hTime hgamma0 hgamma1 hr v)‖<1)
    (hLogPoint : ∀(z : ↥(ball (0 : ComplexVector n) P.radius))(t : Time T),
      localFun ℝ dLog ⟨D.center,(z,t)⟩=
        Real.log ((pullbackMatrix g (P.charts.chart D.center) (cutoffTranslation D.bump theta z)).det.re)-
        Real.log ((pullbackMatrix g (P.charts.chart D.center) z).det.re))
    (hLogCollar : ∀q : LocalCylinder P T,
      q.1≠D.center ∨ (q.2.1 : ComplexVector n)∉tsupport D.bump → localFun ℝ dLog q=0)
    (hsigma : ∀q : LocalCylinder P T, localFun ℝ sigma q=
      if q.1=D.center then chartWeightSum P.charts P.centers P.radius P.radius_pos
        (P.charts.chart D.center q.2.1) else 0)
    (hcancel : ∀z∈tsupport D.bump, P.weight D.center (P.charts.chart D.center z)*
      chartWeightSum P.charts P.centers P.radius P.radius_pos (P.charts.chart D.center z)=1) :
    scalarNonlinearResidualMap P T gamma hT hTime hgamma0 hgamma1 hr J v-
      assembledLogCorrection P T gamma J sigma K (Hstar P hT hTime hgamma0 hgamma1 hr u)
        H (Hstar P hT hTime hgamma0 hgamma1 hr v) dLog=0 := by
  have hHPos := shiftedMetric_posDef_of_inverse D htheta hTime hgamma0 hgamma1 hr
    u v H c0 hC0 hH hInverse huPos hvPos
  have hd := candidateLogDifference_zero_on_collar D htheta hTime hgamma0 hgamma1 hr
    v K (Hstar P hT hTime hgamma0 hgamma1 hr u) H c0 dLog hC0 hH hSmallt hSmall0 hLogCollar
  have huCoord : ∀q : LocalCylinder P T,
      (pullbackMatrix g (P.charts.chart q.1) q.2.1+coordinateMetricError u q).PosDef := by
    intro q
    simpa only [Hstar_value] using huPos q
  have hvCoord : ∀q : LocalCylinder P T,
      (pullbackMatrix g (P.charts.chart q.1) q.2.1+coordinateMetricError v q).PosDef := by
    intro q
    simpa only [Hstar_value] using hvPos q
  apply conjugatedResidual_zero_of_point_values D hTime hgamma0 hgamma1 hr J hJ sigma K
    (Hstar P hT hTime hgamma0 hgamma1 hr u) H (Hstar P hT hTime hgamma0 hgamma1 hr v)
    dLog v hd hsigma hcancel
  · intro q hq
    exact scalarResidual_zero_off_patch P T gamma hT hTime hgamma0 hgamma1 hr hg J hJ
      u v huZ hvZ huCoord hvCoord D theta hValue hTimeValue hEquation q.1 hq q.2
  · intro z t
    apply candidateResidual_selected_value D htheta hg hTime hgamma0 hgamma1 hr J hJ
      u v huZ hvZ huPos hvPos hEquation K H dLog hK hHPos hSmallt hSmall0 z t
    · exact shiftedMetric_on_center D htheta hTime hgamma0 hgamma1 hr u v H c0 hC0 hH hInverse z t
    · have hzSource : (z : ComplexVector n)∈(P.charts.chart D.center).source :=
        P.charts.closedBall_source D.center
          (ball_subset_closedBall ((ball_subset_ball P.radius_lt.le) z.property))
      have h := hTimeValue (P.charts.chart D.center z,t)
      rw [D.forward_chart theta hzSource] at h
      exact h
    · exact hLogPoint z t

end Yau.LeafProofs.L17BootstrapMetricAux
