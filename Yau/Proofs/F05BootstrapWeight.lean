import Yau.Proofs.F05BootstrapDefinitions

/-! The actual parabolic Hölder weight is a continuous modulus vanishing on
the diagonal, independently of the member of a function family. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux

theorem F05_holderWeight_diagonal {n : ℕ} {α : ℝ} (hα : 0 < α) (p : Point n) :
    holderWeight α p p = 0 := by
  simp only [holderWeight,sub_self,norm_zero,abs_zero,Real.zero_rpow hα.ne',
    Real.zero_rpow (by positivity : α/2 ≠ 0),add_zero]

theorem F05_holderWeight_fixed_continuous {n : ℕ} {α : ℝ} (hα : 0 ≤ α)
    (p : Point n) (Q : Set (Point n)) : Continuous (fun q : Q => holderWeight α p q.val) := by
  unfold holderWeight
  fun_prop (disch := positivity)

end Yau.Proofs.F05Aux
