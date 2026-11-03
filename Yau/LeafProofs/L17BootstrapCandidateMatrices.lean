import Yau.LeafProofs.L17BootstrapShiftedMatrixValues

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
local instance candidateMatricesTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier} {T gamma : ℝ} {hT : 0<T}

/-- The actual shifted coefficients reduce to the ordinary ones on the zero collar. -/
theorem shiftedMetric_collar (D : BootstrapPatch P x) {theta : ComplexVector n}
    (htheta : ‖theta‖<D.smallRadius) (hTime : T≤P.radius^2)
    (hgamma0 : 0≤gamma) (hgamma1 : gamma≤1) (hr : P.radius≤1)
    (v : SchauderSpace P T gamma hT)
    (H c0 : LocalCylinder P T → Matrix (Fin n) (Fin n) ℂ)
    (hC0 : ∀q, c0 q=shiftedBackgroundValue D theta q)
    (hH : ∀q, H q=c0 q+c1Family D theta q.1 q.2.1 q.2.2 (gradientFun v q)+
      c2Family D theta q.1 q.2.1 q.2.2 (hessianFun v q))
    (q : LocalCylinder P T)
    (hq : q.1≠D.center ∨ (q.2.1 : ComplexVector n)∉tsupport D.bump) :
    H q=Hstar P hT hTime hgamma0 hgamma1 hr v q := by
  rcases hq with hp | hz
  · exact shiftedMetric_off_center D theta hTime hgamma0 hgamma1 hr v H c0 hC0 hH q hp
  · by_cases hp : q.1=D.center
    · have h := hH q
      rw [hC0 q] at h
      simp only [shiftedBackgroundValue,c1Family,c2Family,ite_eq_left hp,
        c1_of_not_mem_tsupport D theta hz,c2_of_not_mem_tsupport D htheta hz,
        _root_.zero_apply,add_zero] at h
      have hfix := cutoffTranslation_fixed_of_zero D.bump theta (image_eq_zero_of_notMem_tsupport hz)
      rw [hfix] at h
      have hLevi : leviHessianCLM n (hessianFun v q)=leviC (chartFunction v q.1 q.2.2) q.2.1 :=
        potentialLeviBanachCLM_value P T gamma hT v q
      have hEnd := Hstar_value P hT hTime hgamma0 hgamma1 hr v q
      rw [coordinateMetricError_eq v q] at hEnd
      rw [h,hLevi,hEnd]
      abel
    · exact shiftedMetric_off_center D theta hTime hgamma0 hgamma1 hr v H c0 hC0 hH q hp

/-- The genuinely transported element has a positive shifted metric throughout
all selected chart cylinders, using only the actual ordinary branch domain. -/
theorem shiftedMetric_posDef_of_inverse (D : BootstrapPatch P x) {theta : ComplexVector n}
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
    (huPos : ∀q : LocalCylinder P T, (Hstar P hT hTime hgamma0 hgamma1 hr u q).PosDef)
    (hvPos : ∀q : LocalCylinder P T, (Hstar P hT hTime hgamma0 hgamma1 hr v q).PosDef)
    (q : LocalCylinder P T) : (H q).PosDef := by
  by_cases hp : q.1=D.center
  · rcases q with ⟨p,z,t⟩
    change p=D.center at hp
    subst p
    rw [shiftedMetric_on_center D htheta hTime hgamma0 hgamma1 hr u v H c0 hC0 hH hInverse]
    exact huPos _
  · rw [shiftedMetric_off_center D theta hTime hgamma0 hgamma1 hr v H c0 hC0 hH q hp]
    exact hvPos q

end Yau.LeafProofs.L17BootstrapMetricAux
