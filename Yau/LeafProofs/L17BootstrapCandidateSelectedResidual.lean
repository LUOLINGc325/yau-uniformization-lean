import Yau.LeafProofs.L17BootstrapCandidateCoordinateResidual
import Yau.LeafProofs.L17BootstrapRelativeLogValues
import Yau.LeafProofs.L17BootstrapPatchBounds

noncomputable section
open Set Metric
open scoped Topology ContDiff Matrix.Norms.Frobenius ComplexOrder
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapMetricAux
open L17Aux L17HolderAux L17SchauderAux L17ParabolicOperatorAux
open L17BootstrapPositiveBaseHolderAux L17LocalHolderBanachAlgebraAux L17BootstrapPatchAux
open L17SmallTranslationAux
local instance candidateSelectedResidualMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier} {T gamma : ℝ} {hT : 0<T}

/-- On the selected chart the actual original equation cancels the conjugated
logarithmic difference. Every time is in the original closed interval. -/
theorem candidateResidual_selected_value (D : BootstrapPatch P x) {theta : ComplexVector n}
    (htheta : ‖theta‖<D.smallRadius) (hg : MetricSmooth g) (hTime : T≤P.radius^2)
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
    (K H : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma)
    (dLog : LocalHolderSpace ℝ P T gamma)
    (hK : ∀q : LocalCylinder P T, K q=(Hstar P hT hTime hgamma0 hgamma1 hr u q)⁻¹)
    (hHPos : ∀q : LocalCylinder P T, (H q).PosDef)
    (hSmallt : ‖relativeMetricPerturbation P T gamma K (Hstar P hT hTime hgamma0 hgamma1 hr u) H‖<1)
    (hSmall0 : ‖relativeMetricPerturbation P T gamma K (Hstar P hT hTime hgamma0 hgamma1 hr u)
      (Hstar P hT hTime hgamma0 hgamma1 hr v)‖<1)
    (z : ↥(ball (0 : ComplexVector n) P.radius)) (t : Time T)
    (hHpoint : H ⟨D.center,(z,t)⟩=Hstar P hT hTime hgamma0 hgamma1 hr u
      ⟨D.center,(⟨cutoffTranslation D.bump theta z,D.coordinate_mapsTo_ball htheta z.property⟩,t)⟩)
    (hTimePoint : timeFun v (P.charts.chart D.center z,t)=timeFun u
      (P.charts.chart D.center (cutoffTranslation D.bump theta z),t))
    (hLogPoint : localFun ℝ dLog ⟨D.center,(z,t)⟩=
      Real.log ((pullbackMatrix g (P.charts.chart D.center) (cutoffTranslation D.bump theta z)).det.re)-
      Real.log ((pullbackMatrix g (P.charts.chart D.center) z).det.re)) :
    holderFun (scalarNonlinearResidualMap P T gamma hT hTime hgamma0 hgamma1 hr J v)
      (P.charts.chart D.center z,t)=
      localFun ℝ (relativeLogDifference P T gamma K (Hstar P hT hTime hgamma0 hgamma1 hr u)
        H (Hstar P hT hTime hgamma0 hgamma1 hr v) dLog) ⟨D.center,(z,t)⟩ := by
  let q : LocalCylinder P T := ⟨D.center,(z,t)⟩
  let qt : LocalCylinder P T := ⟨D.center,
    (⟨cutoffTranslation D.bump theta z,D.coordinate_mapsTo_ball htheta z.property⟩,t)⟩
  have hTimeEq := timeFun_eq_coordinate_logratio_of_equation P T gamma hT hTime hgamma0 hgamma1 hr
    hg J hJ u huZ huPos hEquation qt
  have hPhi := scalarResidual_value_in_chart P T gamma hT hTime hgamma0 hgamma1 hr hg J hJ v hvZ hvPos q
  have hRel := relativeLogDifference_logratio P T gamma K
    (Hstar P hT hTime hgamma0 hgamma1 hr u) H (Hstar P hT hTime hgamma0 hgamma1 hr v) dLog
    hK huPos hHPos hvPos hSmallt hSmall0 q
  have hGa (r : LocalCylinder P T) : (pullbackMatrix g (P.charts.chart r.1) r.2.1).PosDef :=
    pullbackMatrix_posDef g (P.charts.chart r.1) (P.charts.differentiable r.1)
      (P.charts.inverse_differentiable r.1) (P.charts.closedBall_source r.1
        (ball_subset_closedBall ((ball_subset_ball P.radius_lt.le) r.2.1.property)))
  have ha := (Complex.pos_iff.mp (huPos qt).det_pos).1.ne'
  have hb := (Complex.pos_iff.mp (hvPos q).det_pos).1.ne'
  have hc := (Complex.pos_iff.mp (hGa qt).det_pos).1.ne'
  have hd := (Complex.pos_iff.mp (hGa q).det_pos).1.ne'
  change _=localFun ℝ _ q
  rw [hRel,hHpoint,hLogPoint]
  change holderFun (scalarNonlinearResidualMap P T gamma hT hTime hgamma0 hgamma1 hr J v)
    (P.charts.chart D.center z,t)=timeFun v (P.charts.chart D.center z,t)-
      Real.log ((Hstar P hT hTime hgamma0 hgamma1 hr v q).det.re/
        (pullbackMatrix g (P.charts.chart D.center) z).det.re) at hPhi
  change timeFun u (P.charts.chart D.center (cutoffTranslation D.bump theta z),t)=
    Real.log ((Hstar P hT hTime hgamma0 hgamma1 hr u qt).det.re/
      (pullbackMatrix g (P.charts.chart D.center) (cutoffTranslation D.bump theta z)).det.re) at hTimeEq
  rw [hPhi,hTimePoint,hTimeEq]
  exact coordinate_logratio_cancellation ha hb hc hd

end Yau.LeafProofs.L17BootstrapMetricAux
