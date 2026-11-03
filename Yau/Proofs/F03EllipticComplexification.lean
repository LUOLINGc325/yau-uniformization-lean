import Yau.Proofs.F03ComplexTensorTransport

/-! The same computed real nondivergence operator embeds in the native complex elliptic operator. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau LeafCandidates LeafProofs.L16Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

def realEllipticOp (a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
    (b : ComplexVector n → RIdx n → ℝ) (u : ComplexVector n → ℝ) (z : ComplexVector n) : ℝ :=
  (∑ i,∑ j,a z i j*fderiv ℝ (fderiv ℝ u) z (realVec i) (realVec j))+
    ∑ i,b z i*fderiv ℝ u z (realVec i)

theorem ellipticOp_ofReal (a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
    (b : ComplexVector n → RIdx n → ℝ) {u : ComplexVector n → ℝ} {z : ComplexVector n}
    (hu : ContDiffAt ℝ ∞ u z) :
    ellipticOp a b (fun w => (u w : ℂ)) z=(realEllipticOp a b u z : ℂ) := by
  have hComplex : ContDiffAt ℝ ∞ (fun w => (u w : ℂ)) z :=
    hu.continuousLinearMap_comp Complex.ofRealCLM
  have hD : DifferentiableAt ℝ (fderiv ℝ (fun w => (u w : ℂ))) z :=
    (hComplex.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  unfold ellipticOp realEllipticOp
  simp_rw [fderiv_clm_const_eval hD,
    secondFDeriv_ofReal (hu.of_le (by simp)),fderiv_ofReal_apply (hu.differentiableAt (by simp))]
  push_cast
  rfl

end Yau.Proofs.F03Aux
