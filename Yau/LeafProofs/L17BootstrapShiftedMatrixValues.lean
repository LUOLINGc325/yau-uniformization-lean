import Yau.LeafProofs.L17BootstrapInverseHessianCoefficients
import Yau.LeafProofs.L17BootstrapMetricBase

noncomputable section
open Set Metric
open scoped Classical Topology ContDiff Matrix.Norms.Frobenius ComplexOrder
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapMetricAux
open L17Aux L17HolderAux L17SchauderAux L17BootstrapPatchAux
open L17BootstrapInverseHessianCoefficientsAux L17SmallTranslationAux
open L17BootstrapPositiveBaseHolderAux L17LocalHolderBanachAlgebraAux
local instance shiftedMatrixValuesTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier} {T gamma : ℝ} {hT : 0<T}

def shiftedBackgroundValue (D : BootstrapPatch P x) (theta : ComplexVector n)
    (q : LocalCylinder P T) : Matrix (Fin n) (Fin n) ℂ :=
  if q.1=D.center then
    pullbackMatrix g (P.charts.chart q.1) (cutoffTranslation D.bump theta q.2.1)-
      (q.2.2 : ℂ) • pullbackRicci g (P.charts.chart q.1) (cutoffTranslation D.bump theta q.2.1)
  else pullbackMatrix g (P.charts.chart q.1) q.2.1-
    (q.2.2 : ℂ) • pullbackRicci g (P.charts.chart q.1) q.2.1

theorem shiftedMetric_on_center (D : BootstrapPatch P x) {theta : ComplexVector n}
    (htheta : ‖theta‖<D.smallRadius) (hTime : T≤P.radius^2)
    (hgamma0 : 0≤gamma) (hgamma1 : gamma≤1) (hr : P.radius≤1)
    (u v : SchauderSpace P T gamma hT)
    (H c0 : LocalCylinder P T → Matrix (Fin n) (Fin n) ℂ)
    (hC0 : ∀q, c0 q=shiftedBackgroundValue D theta q)
    (hH : ∀q, H q=c0 q+c1Family D theta q.1 q.2.1 q.2.2 (gradientFun v q)+
      c2Family D theta q.1 q.2.1 q.2.2 (hessianFun v q))
    (hInverse : ∀ (z : ↥(ball (0 : ComplexVector n) P.radius)) (t : Time T),
      c1 D theta z (gradientFun v ⟨D.center,(z,t)⟩)+
      c2 D theta z (hessianFun v ⟨D.center,(z,t)⟩)=
        leviC (chartFunction u D.center t) (cutoffTranslation D.bump theta z))
    (z : ↥(ball (0 : ComplexVector n) P.radius)) (t : Time T) :
    H ⟨D.center,(z,t)⟩=Hstar P hT hTime hgamma0 hgamma1 hr u
      ⟨D.center,(⟨cutoffTranslation D.bump theta z,D.coordinate_mapsTo_ball htheta z.property⟩,t)⟩ := by
  let q : LocalCylinder P T := ⟨D.center,(z,t)⟩
  let qt : LocalCylinder P T :=
    ⟨D.center,(⟨cutoffTranslation D.bump theta z,D.coordinate_mapsTo_ball htheta z.property⟩,t)⟩
  have hFirst : H q=c0 q+
      (c1 D theta z (gradientFun v q)+c2 D theta z (hessianFun v q)) := by
    simpa [q,c1Family,c2Family,add_assoc] using hH q
  have hBg : c0 q=pullbackMatrix g (P.charts.chart D.center) (cutoffTranslation D.bump theta z)-
      (t : ℂ) • pullbackRicci g (P.charts.chart D.center) (cutoffTranslation D.bump theta z) := by
    simpa [q,shiftedBackgroundValue] using hC0 q
  have hEnd := Hstar_value P hT hTime hgamma0 hgamma1 hr u qt
  rw [coordinateMetricError_eq u qt] at hEnd
  change H q=Hstar P hT hTime hgamma0 hgamma1 hr u qt
  rw [hFirst,hBg,hInverse z t,hEnd]
  abel

theorem shiftedMetric_off_center (D : BootstrapPatch P x) (theta : ComplexVector n)
    (hTime : T≤P.radius^2) (hgamma0 : 0≤gamma) (hgamma1 : gamma≤1) (hr : P.radius≤1)
    (v : SchauderSpace P T gamma hT)
    (H c0 : LocalCylinder P T → Matrix (Fin n) (Fin n) ℂ)
    (hC0 : ∀q, c0 q=shiftedBackgroundValue D theta q)
    (hH : ∀q, H q=c0 q+c1Family D theta q.1 q.2.1 q.2.2 (gradientFun v q)+
      c2Family D theta q.1 q.2.1 q.2.2 (hessianFun v q))
    (q : LocalCylinder P T) (hq : q.1≠D.center) :
    H q=Hstar P hT hTime hgamma0 hgamma1 hr v q := by
  have h := hH q
  rw [hC0 q] at h
  simp only [shiftedBackgroundValue,c1Family,c2Family,ite_eq_right hq,_root_.zero_apply,add_zero] at h
  have hLevi : leviHessianCLM n (hessianFun v q)=leviC (chartFunction v q.1 q.2.2) q.2.1 :=
    potentialLeviBanachCLM_value P T gamma hT v q
  have hEnd := Hstar_value P hT hTime hgamma0 hgamma1 hr v q
  rw [coordinateMetricError_eq v q] at hEnd
  rw [h,hLevi,hEnd]
  abel

end Yau.LeafProofs.L17BootstrapMetricAux
