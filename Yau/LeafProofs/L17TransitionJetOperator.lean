import Yau.LeafProofs.L17JetGlobalComposition

/-! A fixed smooth finite-dimensional polynomial for the actual transition acceleration. -/

noncomputable section

open Set Metric
open scoped ContDiff

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

local instance acceleration_firstGroup :
    NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance acceleration_firstSpace :
    NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance acceleration_secondGroup :
    NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance acceleration_secondSpace :
    NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance

abbrev TransitionJetInput (n : ℕ) := (ComplexVector n →L[ℝ] ComplexVector n) ×
  (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) ×
  (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n)

def transitionAcceleration (a : TransitionJetInput n) :
    ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n :=
  (ContinuousLinearMap.compL ℝ (ComplexVector n) (ComplexVector n) (ComplexVector n) a.1).comp
      a.2.1 -
    ((ContinuousLinearMap.compL ℝ (ComplexVector n) (ComplexVector n) (ComplexVector n)).flip
      a.1).comp (a.2.2.comp a.1)

theorem transitionAcceleration_contDiff : ContDiff ℝ ∞ (transitionAcceleration (n := n)) := by
  unfold transitionAcceleration
  fun_prop

def BoundedChartFamily.transitionMap (A : BoundedChartFamily g) (a : M.Carrier × M.Carrier) :
    ComplexVector n → ComplexVector n := fun z => (A.chart a.2).symm (A.chart a.1 z)

def BoundedChartFamily.transitionBallDomain (A : BoundedChartFamily g)
    (a : M.Carrier × M.Carrier) : Set (ComplexVector n) :=
  ball 0 A.radius ∩ (transitionDomain (A.chart a.1) (A.chart a.2) ∩
    A.transitionMap a ⁻¹' ball 0 A.radius)

theorem BoundedChartFamily.transitionBallDomain_isOpen (A : BoundedChartFamily g)
    (a : M.Carrier × M.Carrier) : IsOpen (A.transitionBallDomain a) :=
  isOpen_ball.inter ((transition_real_contDiffOn (A.chart a.1) (A.chart a.2)
    (A.differentiable a.1) (A.inverse_differentiable a.2)).continuousOn.isOpen_inter_preimage
      (transitionDomain_isOpen _ _) isOpen_ball)

theorem BoundedChartFamily.transitionMap_contDiffOn (A : BoundedChartFamily g)
    (a : M.Carrier × M.Carrier) :
    ContDiffOn ℝ ∞ (A.transitionMap a) (A.transitionBallDomain a) :=
  (transition_real_contDiffOn (A.chart a.1) (A.chart a.2) (A.differentiable a.1)
    (A.inverse_differentiable a.2)).mono (fun _ hz => hz.2.1)

theorem BoundedChartFamily.transitionBallDomain_image (A : BoundedChartFamily g)
    (a : M.Carrier × M.Carrier) {z : ComplexVector n} (hz : z ∈ A.transitionBallDomain a) :
    A.chart a.1 z ∈ A.chart a.2 '' ball 0 A.radius :=
  ⟨A.transitionMap a z, hz.2.2, (A.chart a.2).right_inv hz.2.1.2⟩

theorem BoundedChartFamily.transition_acceleration_eq (A : BoundedChartFamily g)
    (a : M.Carrier × M.Carrier) {z : ComplexVector n} (hz : z ∈ A.transitionBallDomain a) :
    fderiv ℝ (fderiv ℝ (A.transitionMap a)) z =
      transitionAcceleration (fderiv ℝ (A.transitionMap a) z,
        backgroundConnection g (A.chart a.1) z,
        backgroundConnection g (A.chart a.2) (A.transitionMap a z)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change (fderiv ℝ (fderiv ℝ (A.transitionMap a)) z u) v =
    fderiv ℝ (A.transitionMap a) z (backgroundConnection g (A.chart a.1) z u v) -
      backgroundConnection g (A.chart a.2) (A.transitionMap a z)
        (fderiv ℝ (A.transitionMap a) z u) (fderiv ℝ (A.transitionMap a) z v)
  have h := A.transition_secondDerivative a.1 a.2 hz.1 (A.transitionBallDomain_image a hz) u v
  exact eq_sub_iff_add_eq.mpr h.symm

end Yau.LeafProofs.L17Aux
