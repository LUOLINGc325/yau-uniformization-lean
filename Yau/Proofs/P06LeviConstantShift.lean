import Yau.Proofs.P06Scalar

noncomputable section
open scoped Manifold Topology ContDiff Matrix

namespace Yau.NodeProofs.P06Aux
open Yau

theorem leviC_sub_constant {n : ℕ} (f : ComplexVector n → ℝ) (c : ℝ) (z : ComplexVector n) :
    leviC (fun w => f w - c) z = leviC f z := by
  ext a b
  simp only [leviC, leviMatrix, wirt, wirtBar, Complex.ofReal_sub, fderiv_sub_const]

theorem levi_sub_constant {n : ℕ} {M : ComplexManifold n}
    (f : M.Carrier → ℝ) (c : ℝ) (x : M.Carrier) :
    levi (fun y => f y - c) x = levi f x := by
  exact leviC_sub_constant (inChart x f) c (chartPt x x)

end Yau.NodeProofs.P06Aux
