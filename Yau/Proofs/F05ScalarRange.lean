import Yau.Proofs.F05ExponentialHolder
import Yau.Proofs.F05Scalar

/-! On an actual bounded value range, the nonlinear scalar RHS has a fixed
one-sided Lipschitz constant without assuming the solution nonnegative. -/

noncomputable section
namespace Yau.Proofs.F05Aux

theorem F05_scalar_rhs_sub_le_lower (R D K A : ℝ) {u w : ℝ}
    (hu : -K ≤ u) (huw : u ≤ w) (hA : |R-D| ≤ A) :
    scalarNonlinearRHS R D w-scalarNonlinearRHS R D u ≤ (Real.exp K*A)*(w-u) := by
  have hMono : Real.exp (-w) ≤ Real.exp (-u) := Real.exp_le_exp.mpr (by linarith)
  have hLip := F05_exp_lipschitz_upper (B := K) (x := -u) (y := -w) (by linarith) (by linarith)
  have hNegDiff : -u-(-w) = w-u := by ring
  rw [abs_of_nonneg (sub_nonneg.mpr hMono),hNegDiff,abs_of_nonneg (sub_nonneg.mpr huw)] at hLip
  have hEq : scalarNonlinearRHS R D w-scalarNonlinearRHS R D u =
      (Real.exp (-u)-Real.exp (-w))*(R-D) := by unfold scalarNonlinearRHS; ring
  calc
    _ ≤ |scalarNonlinearRHS R D w-scalarNonlinearRHS R D u| := le_abs_self _
    _ = (Real.exp (-u)-Real.exp (-w))*|R-D| := by rw [hEq,abs_mul,abs_of_nonneg (sub_nonneg.mpr hMono)]
    _ ≤ (Real.exp K*(w-u))*A := mul_le_mul hLip hA (abs_nonneg _) (by positivity)
    _ = (Real.exp K*A)*(w-u) := by ring

end Yau.Proofs.F05Aux
