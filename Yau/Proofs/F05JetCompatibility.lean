import Yau.Proofs.F05JetOverlap

/-! The closed overlap graph enforces the actual value, time, gradient and
full second derivative chain rules at every physical overlap point. -/

open Set
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

theorem F05CompatibleJetGraph_value (A : AtlasData M) (α : ℝ) {T : ℝ}
    (hT : 0 ≤ T) (u : F05CompatibleJetGraph A α hT) (p : F05OverlapPoint A T) :
    (u.val p.left).val.1 p.leftPoint = (u.val p.right).val.1 p.rightPoint := by
  have h : u.val ∈ F05ValueOverlapGraph A α hT := u.property.1.1.1
  have hh := (Submodule.mem_iInf _).mp h p
  change F05ValueOverlapResidual A α hT p u.val = 0 at hh
  exact sub_eq_zero.mp hh

theorem F05CompatibleJetGraph_time (A : AtlasData M) (α : ℝ) {T : ℝ}
    (hT : 0 ≤ T) (u : F05CompatibleJetGraph A α hT) (p : F05OverlapPoint A T) :
    (u.val p.left).val.2.2.2.val.1 p.leftPoint =
      (u.val p.right).val.2.2.2.val.1 p.rightPoint := by
  have h : u.val ∈ F05TimeOverlapGraph A α hT := u.property.1.1.2
  have hh := (Submodule.mem_iInf _).mp h p
  change F05TimeOverlapResidual A α hT p u.val = 0 at hh
  exact sub_eq_zero.mp hh

theorem F05CompatibleJetGraph_gradient (A : AtlasData M) (α : ℝ) {T : ℝ}
    (hT : 0 ≤ T) (u : F05CompatibleJetGraph A α hT) (p : F05OverlapPoint A T)
    (v : Space n) :
    (u.val p.left).val.2.1 p.leftPoint v = (u.val p.right).val.2.1 p.rightPoint
      (fderiv ℝ (F05Transition A p.left p.right) p.leftCoord.val v) := by
  have h : u.val ∈ F05GradientOverlapGraph A α hT := u.property.1.2
  have hh := (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp h p) v
  change F05GradientOverlapResidual A α hT p v u.val = 0 at hh
  exact sub_eq_zero.mp hh

theorem F05CompatibleJetGraph_hessian (A : AtlasData M) (α : ℝ) {T : ℝ}
    (hT : 0 ≤ T) (u : F05CompatibleJetGraph A α hT) (p : F05OverlapPoint A T)
    (v w : Space n) :
    (u.val p.left).val.2.2.1.val.1 p.leftPoint v w =
      (u.val p.right).val.2.2.1.val.1 p.rightPoint
        (fderiv ℝ (F05Transition A p.left p.right) p.leftCoord.val v)
        (fderiv ℝ (F05Transition A p.left p.right) p.leftCoord.val w) +
      (u.val p.right).val.2.1 p.rightPoint
        (fderiv ℝ (fderiv ℝ (F05Transition A p.left p.right)) p.leftCoord.val v w) := by
  have h : u.val ∈ F05HessianOverlapGraph A α hT := u.property.2
  have hh := (Submodule.mem_iInf _).mp
    ((Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp h p) v) w
  change F05HessianOverlapResidual A α hT p v w u.val = 0 at hh
  simp only [F05HessianOverlapResidual,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply] at hh
  change (u.val p.left).val.2.2.1.val.1 p.leftPoint v w -
    (u.val p.right).val.2.2.1.val.1 p.rightPoint
      (fderiv ℝ (F05Transition A p.left p.right) p.leftCoord.val v)
      (fderiv ℝ (F05Transition A p.left p.right) p.leftCoord.val w) -
    (u.val p.right).val.2.1 p.rightPoint
      (fderiv ℝ (fderiv ℝ (F05Transition A p.left p.right)) p.leftCoord.val v w) = 0 at hh
  linarith

end Yau.Proofs.F05Aux
