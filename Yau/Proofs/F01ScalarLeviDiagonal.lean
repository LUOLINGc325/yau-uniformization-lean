import Yau.Proofs.F01ScalarChain
import Yau.Proofs.F01GradientQuadratic
import Yau.Proofs.F01DiagonalRayleigh

/-! Actual diagonal Levi chain rules, including the logarithm with its
precise negative gradient square. -/
noncomputable section
open scoped ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs
variable {n : ℕ}

theorem leviC_diagonal_eq_quadratic {q : ComplexVector n → ℝ} {z : ComplexVector n}
    (hq : ContDiffAt ℝ 2 q z) (i : Fin n) :
    (leviC q z i i).re = L22Aux.complexLeviQuadratic q z (stdVec i) := by
  have hh := L22Aux.leviC_quadratic_re hq (stdVec i)
  change matrixQuadraticValue (leviC q z) (Pi.single i 1) = _ at hh
  rw [matrixQuadraticValue_single] at hh
  exact hh

theorem scalar_levi_diagonal_comp {q : ComplexVector n → ℝ} {F : ℝ → ℝ}
    {z : ComplexVector n} (hq : ContDiffAt ℝ 2 q z)
    (hF : ContDiffAt ℝ 2 F (q z)) (i : Fin n) :
    (leviC (fun w => F (q w)) z i i).re =
      deriv F (q z) * (leviC q z i i).re +
        deriv (deriv F) (q z) * Complex.normSq (wirt (fun w => (q w : ℂ)) z (stdVec i)) := by
  have hcomp : ContDiffAt ℝ 2 (fun w => F (q w)) z := hF.comp z hq
  have hdiag := leviC_diagonal_eq_quadratic hcomp i
  have hchain := complexLeviQuadratic_scalar_comp hq hF (stdVec i)
  change L22Aux.complexLeviQuadratic (fun w => F (q w)) z (stdVec i) = _ at hchain
  rw [hdiag, hchain, ← leviC_diagonal_eq_quadratic hq]
  have hn := norm_wirt_ofReal_sq (hq.differentiableAt (by norm_num)) (stdVec i)
  rw [Complex.sq_norm] at hn
  rw [hn]
  ring

theorem leviC_log_diagonal {q : ComplexVector n → ℝ} {z : ComplexVector n}
    (hq : ContDiffAt ℝ 2 q z) (hpos : 0 < q z) (i : Fin n) :
    (leviC (fun w => Real.log (q w)) z i i).re =
      (q z)⁻¹ * (leviC q z i i).re -
        ((q z) ^ 2)⁻¹ * Complex.normSq (wirt (fun w => (q w : ℂ)) z (stdVec i)) := by
  rw [scalar_levi_diagonal_comp hq (Real.contDiffAt_log.mpr hpos.ne'),
    Real.deriv_log, Real.deriv_log', deriv_inv]
  ring

end Yau.NodeProofs.F01Aux
