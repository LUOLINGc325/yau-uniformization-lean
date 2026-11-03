import Yau.Proofs.F03ClassicalCaloricOperator

/-! Actual affine second-derivative transport, reusing the native Hessian chain rule. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau Parabolic LeafProofs.L18Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem affine_secondFDeriv (L : E →L[ℝ] F) (c : F) (f : F → ℝ) (x : E)
    (hf : ContDiffAt ℝ 2 f (L x+c)) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => f (L y+c))) x v w=
      fderiv ℝ (fderiv ℝ f) (L x+c) (L v) (L w) := by
  have hFirst : ∀ y : E,fderiv ℝ (fun z => L z+c) y=L := fun y =>
    (L.hasFDerivAt.add_const c).fderiv
  have hSecond : fderiv ℝ (fderiv ℝ (fun y => L y+c)) x=0 := by
    rw [funext hFirst]
    exact fderiv_const_apply L
  have h := secondFDeriv_comp ((L.contDiff.add contDiff_const).contDiffAt) hf v w
  change fderiv ℝ (fderiv ℝ (fun y => f (L y+c))) x v w=_ at h
  simpa only [hFirst,hSecond,ContinuousLinearMap.zero_apply,map_zero,add_zero] using h

theorem spatialDD_eq_joint_second {d : ℕ} (f : Point d → ℝ) (p : Point d)
    (hf : ContDiffAt ℝ 2 f p) (v w : Space d) :
    spatialDD f p v w=fderiv ℝ (fderiv ℝ f) p (v,0) (w,0) := by
  let L : Space d →L[ℝ] Point d := (ContinuousLinearMap.id ℝ (Space d)).prod 0
  have h := affine_secondFDeriv L (0,p.2) f p.1 (by simpa only [L,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.zero_apply,Prod.mk_add_mk,add_zero,zero_add,Prod.mk.eta] using hf) v w
  simpa only [L,ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.zero_apply,Prod.mk_add_mk,add_zero,zero_add,Prod.mk.eta,spatialDD] using h

end Yau.Proofs.F03Aux
