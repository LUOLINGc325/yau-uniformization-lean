import Yau.Proofs.F03EllipticChart

/-! Translating the original elliptic operator transports all actual powers and tensor norms. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau LeafCandidates
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

theorem ellipticOp_translate
    (a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
    (b : ComplexVector n → RIdx n → ℝ) (u : ComplexVector n → ℂ)
    (c z : ComplexVector n) :
    ellipticOp (fun w => a (w+c)) (fun w => b (w+c)) (fun w => u (w+c)) z=
      ellipticOp a b u (z+c) := by
  have hFirst : fderiv ℝ (fun w => u (w+c))=(fun w => fderiv ℝ u (w+c)) :=
    funext (fun w => fderiv_comp_add_right (𝕜 := ℝ) (f := u) (x := w) c)
  have hSecond (i j : RIdx n) :
      fderiv ℝ (fun w => fderiv ℝ u (w+c) (realVec j)) z (realVec i)=
        fderiv ℝ (fun w => fderiv ℝ u w (realVec j)) (z+c) (realVec i) :=
    congrArg (fun A : ComplexVector n →L[ℝ] ℂ => A (realVec i))
      (fderiv_comp_add_right (𝕜 := ℝ) (f := fun w => fderiv ℝ u w (realVec j)) (x := z) c)
  simp only [ellipticOp,hFirst,hSecond]

theorem ellipticOp_power_translate
    (a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
    (b : ComplexVector n → RIdx n → ℝ) (u : ComplexVector n → ℂ)
    (c : ComplexVector n) (m : ℕ) :
    (ellipticOp (fun w => a (w+c)) (fun w => b (w+c)))^[m] (fun w => u (w+c))=
      (fun w => ((ellipticOp a b)^[m] u) (w+c)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply',ih]
    funext z
    rw [ellipticOp_translate,Function.iterate_succ_apply']

end Yau.Proofs.F03Aux
