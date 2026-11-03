import Yau.LeafProofs.L17BootstrapInverseHessianCoefficientsGeometry
import Yau.LeafProofs.L17PotentialLeviMap

/-! Actual real inverse-Hessian coefficients in the original Frobenius matrix space. -/

noncomputable section
open Set Metric
open scoped Classical Topology ContDiff Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000

namespace Yau.LeafProofs.L17BootstrapInverseHessianCoefficientsAux
open L17Aux L17SchauderAux L17BootstrapPatchAux L17SmallTranslationAux

local instance inverseHessianCoefficientMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier} (D : BootstrapPatch P x)

def c2 (theta z : ComplexVector n) : D2 n →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  (leviHessianCLM n).comp (hessianPrecompositionCLM (inverseDifferential D theta z))

def c1 (theta z : ComplexVector n) : D1 n →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  (leviHessianCLM n).comp
    (gradientCorrectionCLM (inverseDifferential D theta z) (translationHessian D theta z))

theorem c2_apply (theta z : ComplexVector n) (Q : D2 n) :
    c2 D theta z Q = leviHessianCLM n (hessianPrecompositionCLM (inverseDifferential D theta z) Q) := rfl

theorem c1_apply (theta z : ComplexVector n) (p : D1 n) :
    c1 D theta z p = leviHessianCLM n
      (gradientCorrectionCLM (inverseDifferential D theta z) (translationHessian D theta z) p) := rfl

theorem c2_contDiffAt {theta : ComplexVector n} (htheta : ‖theta‖ < D.smallRadius)
    (z : ComplexVector n) :
    ContDiffAt ℝ ∞ (fun a : ComplexVector n × ComplexVector n => c2 D a.1 a.2) (theta,z) := by
  have hpre := (hessianPrecompositionCLM_contDiff (E := ComplexVector n) (F := ℝ)).contDiffAt.comp
    (theta,z) (inverseDifferential_contDiffAt D htheta z)
  exact contDiffAt_const.clm_comp hpre

theorem c1_contDiffAt {theta : ComplexVector n} (htheta : ‖theta‖ < D.smallRadius)
    (z : ComplexVector n) :
    ContDiffAt ℝ ∞ (fun a : ComplexVector n × ComplexVector n => c1 D a.1 a.2) (theta,z) := by
  have hpair := (inverseDifferential_contDiffAt D htheta z).prodMk (translationHessian_contDiff D).contDiffAt
  have hcor := (gradientCorrectionCLM_contDiff (E := ComplexVector n) (F := ℝ)).contDiffAt.comp (theta,z) hpair
  exact contDiffAt_const.clm_comp hcor

theorem c2_contDiffOn :
    ContDiffOn ℝ ∞ (fun a : ComplexVector n × ComplexVector n => c2 D a.1 a.2)
      (ball (0:ComplexVector n) D.smallRadius ×ˢ (univ : Set (ComplexVector n))) := by
  intro a ha
  exact (c2_contDiffAt D (by simpa only [mem_ball,dist_zero_right] using ha.1) a.2).contDiffWithinAt

theorem c1_contDiffOn :
    ContDiffOn ℝ ∞ (fun a : ComplexVector n × ComplexVector n => c1 D a.1 a.2)
      (ball (0:ComplexVector n) D.smallRadius ×ˢ (univ : Set (ComplexVector n))) := by
  intro a ha
  exact (c1_contDiffAt D (by simpa only [mem_ball,dist_zero_right] using ha.1) a.2).contDiffWithinAt

/-- The actual inverse-coordinate Levi identity retains the first derivative term. -/
theorem inverseComposition_levi {theta : ComplexVector n} (htheta : ‖theta‖ < D.smallRadius)
    (z : ComplexVector n) (v : ComplexVector n → ℝ) (hv : ContDiffAt ℝ 2 v z) :
    c2 D theta z (fderiv ℝ (fderiv ℝ v) z) + c1 D theta z (fderiv ℝ v z) =
      leviC (fun y => v (cutoffInverse D.bump D.bump_smooth D.bound
        (zero_le_one.trans D.bound_ge_one) D.derivative_bound theta y))
          (cutoffTranslation D.bump theta z) := by
  rw [leviC_eq_leviHessianCLM (inverseComposition_contDiffAt_two D htheta z v hv),
    inverseComposition_hessian D htheta z v hv,map_add]
  rfl

theorem c2_zero (z : ComplexVector n) : c2 D 0 z = leviHessianCLM n := by
  simp only [c2,inverseDifferential_zero,hessianPrecompositionCLM_id,ContinuousLinearMap.comp_id]

theorem c1_zero (z : ComplexVector n) : c1 D 0 z = 0 := by
  simp only [c1,translationHessian_zero,gradientCorrectionCLM_zero,ContinuousLinearMap.comp_zero]

theorem c2_of_not_mem_tsupport {theta z : ComplexVector n} (htheta : ‖theta‖ < D.smallRadius)
    (hz : z ∉ tsupport D.bump) : c2 D theta z = leviHessianCLM n := by
  simp only [c2,inverseDifferential_of_not_mem_tsupport D htheta hz,
    hessianPrecompositionCLM_id,ContinuousLinearMap.comp_id]

theorem c1_of_not_mem_tsupport (theta : ComplexVector n) {z : ComplexVector n}
    (hz : z ∉ tsupport D.bump) : c1 D theta z = 0 := by
  simp only [c1,translationHessian_of_not_mem_tsupport D theta hz,
    gradientCorrectionCLM_zero,ContinuousLinearMap.comp_zero]

def c2Family (theta : ComplexVector n) (q : P.centers) (z : ComplexVector n) (_t : ℝ) :
    D2 n →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  if q = D.center then c2 D theta z else leviHessianCLM n

def c1Family (theta : ComplexVector n) (q : P.centers) (z : ComplexVector n) (_t : ℝ) :
    D1 n →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  if q = D.center then c1 D theta z else 0

theorem c2Family_contDiffOn (q : P.centers) :
    ContDiffOn ℝ ∞
      (fun a : ComplexVector n × (ComplexVector n × ℝ) => c2Family D a.1 q a.2.1 a.2.2)
      (ball 0 D.smallRadius ×ˢ (ball 0 (2*P.radius) ×ˢ Set.univ)) := by
  by_cases hq : q = D.center
  · simp only [c2Family,ite_eq_left hq]
    intro a ha
    have hcurve : ContDiffAt ℝ ∞
        (fun b : ComplexVector n × (ComplexVector n × ℝ) => (b.1,b.2.1)) a :=
      contDiffAt_fst.prodMk contDiffAt_snd.fst
    exact ((c2_contDiffAt D
      (by simpa only [mem_ball,dist_zero_right] using ha.1) a.2.1).comp a hcurve).contDiffWithinAt
  · simp only [c2Family,ite_eq_right hq]
    exact contDiffOn_const

theorem c1Family_contDiffOn (q : P.centers) :
    ContDiffOn ℝ ∞
      (fun a : ComplexVector n × (ComplexVector n × ℝ) => c1Family D a.1 q a.2.1 a.2.2)
      (ball 0 D.smallRadius ×ˢ (ball 0 (2*P.radius) ×ˢ Set.univ)) := by
  by_cases hq : q = D.center
  · simp only [c1Family,ite_eq_left hq]
    intro a ha
    have hcurve : ContDiffAt ℝ ∞
        (fun b : ComplexVector n × (ComplexVector n × ℝ) => (b.1,b.2.1)) a :=
      contDiffAt_fst.prodMk contDiffAt_snd.fst
    exact ((c1_contDiffAt D
      (by simpa only [mem_ball,dist_zero_right] using ha.1) a.2.1).comp a hcurve).contDiffWithinAt
  · simp only [c1Family,ite_eq_right hq]
    exact contDiffOn_const

theorem c2_background_mixed_bounds (z : ComplexVector n) (t : ℝ) :
    ‖leviHessianCLM n‖ ≤ ‖leviHessianCLM n‖ ∧
    ‖fderiv ℝ (fun _ : ComplexVector n => leviHessianCLM n) z‖ ≤ 0 ∧
    ‖deriv (fun _ : ℝ => leviHessianCLM n) t‖ ≤ 0 := by
  refine ⟨le_rfl,?_,?_⟩
  · rw [fderiv_const_apply,ContinuousLinearMap.opNorm_zero]
  · rw [deriv_const,ContinuousLinearMap.opNorm_zero]

theorem c1_background_mixed_bounds (z : ComplexVector n) (t : ℝ) :
    ‖(0 : D1 n →L[ℝ] Matrix (Fin n) (Fin n) ℂ)‖ ≤ 0 ∧
    ‖fderiv ℝ (fun _ : ComplexVector n => (0 : D1 n →L[ℝ] Matrix (Fin n) (Fin n) ℂ)) z‖ ≤ 0 ∧
    ‖deriv (fun _ : ℝ => (0 : D1 n →L[ℝ] Matrix (Fin n) (Fin n) ℂ)) t‖ ≤ 0 := by
  refine ⟨?_,?_,?_⟩
  · rw [ContinuousLinearMap.opNorm_zero]
  · rw [fderiv_const_apply,ContinuousLinearMap.opNorm_zero]
  · rw [deriv_const,ContinuousLinearMap.opNorm_zero]

end Yau.LeafProofs.L17BootstrapInverseHessianCoefficientsAux
