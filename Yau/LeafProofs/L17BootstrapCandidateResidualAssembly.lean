import Yau.LeafProofs.L17BootstrapScalarCorrection
import Yau.LeafProofs.L17BootstrapConjugatedResidual
import Yau.LeafProofs.L17BootstrapPatchBounds

noncomputable section
open Set Metric
open scoped Classical Topology ContDiff Matrix.Norms.Frobenius ComplexOrder
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapMetricAux
open L17Aux L17HolderAux L17SchauderAux L17LocalHolderBanachAlgebraAux
open L17BootstrapPatchAux L17BootstrapScalarCorrectionAux
local instance candidateResidualAssemblyMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier} {T gamma : ℝ} {hT : 0<T}

/-- The two actual pointwise branches identify the original residual with the
literal selected-chart zero extension. -/
theorem residualFunction_eq_patch (D : BootstrapPatch P x)
    (F : Cylinder M T → ℝ) (d : LocalHolderSpace ℝ P T gamma)
    (hd : ∀q : LocalCylinder P T,
      q.1≠D.center ∨ (q.2.1 : ComplexVector n)∉tsupport D.bump → localFun ℝ d q=0)
    (hOutside : ∀q : Cylinder M T, q.1∉D.supportSet → F q=0)
    (hInside : ∀(z : ↥(ball (0 : ComplexVector n) P.radius)) (t : Time T),
      F (P.charts.chart D.center z,t)=localFun ℝ d ⟨D.center,(z,t)⟩) :
    F=patchScalarValue D d := by
  funext q
  by_cases hq : q.1∈D.supportSet
  · rcases q with ⟨y,t⟩
    rcases hq with ⟨z,hz,hzy⟩
    have hzR : z∈ball (0 : ComplexVector n) P.radius :=
      (ball_subset_ball (by linarith [P.radius_pos] : P.radius/4≤P.radius))
        (D.bump_support_ball_quarter hz)
    change P.charts.chart D.center z=y at hzy
    subst y
    exact (hInside ⟨z,hzR⟩ t).trans (patchScalarValue_chart D d ⟨z,hzR⟩ t).symm
  · rw [hOutside q hq,patchScalarValue_zero_off_support D d hd q hq]

/-- Actual normalized scalar assembly, rather than a caller-chosen global
correction, converts the pointwise identities into the conjugated equation. -/
theorem conjugatedResidual_zero_of_point_values (D : BootstrapPatch P x)
    (hTime : T≤P.radius^2) (hgamma0 : 0≤gamma) (hgamma1 : gamma≤1) (hr : P.radius≤1)
    (J : LocalHolderSpace ℝ P T gamma →L[ℝ] HolderSpace P T gamma)
    (hJ : ∀ w, holderFun (J w)=L17LocalScalarAssemblyAux.scalarAssemblyFunction P w)
    (sigma : LocalHolderSpace ℝ P T gamma)
    (K Hbase Htheta Hzero : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma)
    (dLog : LocalHolderSpace ℝ P T gamma) (v : SchauderSpace P T gamma hT)
    (hd : ∀q : LocalCylinder P T,
      q.1≠D.center ∨ (q.2.1 : ComplexVector n)∉tsupport D.bump →
        localFun ℝ (relativeLogDifference P T gamma K Hbase Htheta Hzero dLog) q=0)
    (hsigma : ∀q : LocalCylinder P T, localFun ℝ sigma q=
      if q.1=D.center then chartWeightSum P.charts P.centers P.radius P.radius_pos
        (P.charts.chart D.center q.2.1) else 0)
    (hcancel : ∀z∈tsupport D.bump, P.weight D.center (P.charts.chart D.center z)*
      chartWeightSum P.charts P.centers P.radius P.radius_pos (P.charts.chart D.center z)=1)
    (hOutside : ∀q : Cylinder M T, q.1∉D.supportSet →
      holderFun (scalarNonlinearResidualMap P T gamma hT hTime hgamma0 hgamma1 hr J v) q=0)
    (hInside : ∀(z : ↥(ball (0 : ComplexVector n) P.radius)) (t : Time T),
      holderFun (scalarNonlinearResidualMap P T gamma hT hTime hgamma0 hgamma1 hr J v)
        (P.charts.chart D.center z,t)=
        localFun ℝ (relativeLogDifference P T gamma K Hbase Htheta Hzero dLog) ⟨D.center,(z,t)⟩) :
    scalarNonlinearResidualMap P T gamma hT hTime hgamma0 hgamma1 hr J v-
      assembledLogCorrection P T gamma J sigma K Hbase Htheta Hzero dLog=0 := by
  apply sub_eq_zero.mpr
  apply holderFun_injective P T gamma
  exact (residualFunction_eq_patch D _ _ hd hOutside hInside).trans
    (scalarCorrection_holderFun D J hJ _ sigma hd hsigma hcancel).symm

end Yau.LeafProofs.L17BootstrapMetricAux
