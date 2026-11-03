import Yau.Proofs.F01ScalarLeviDiagonal
import Yau.Proofs.F01LogLaplacianDiagonal
import Yau.LeafProofs.L16

/-! The actual complex heat operator is nonnegative at a space-time
maximum, retaining the within derivative on the terminal time face. -/
noncomputable section
open scoped ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ}

theorem traceWith_leviC_nonpos_at_localMax (values : Fin n → ℝ)
    (hv : ∀ i, 0 < values i) {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (hmax : IsLocalMax f z) :
    traceWith (Matrix.diagonal (fun i => (values i : ℂ))) (leviC f z) ≤ 0 := by
  rw [traceWith_real_diagonal values (fun i => (hv i).ne')]
  apply Finset.sum_nonpos
  intro i hi
  have hreal := Yau.LeafProofs.L16Aux.secondFDeriv_nonpos_of_isLocalMax hf hmax (stdVec i)
  have himag := Yau.LeafProofs.L16Aux.secondFDeriv_nonpos_of_isLocalMax hf hmax (Complex.I • stdVec i)
  have hlevi : (leviC f z i i).re ≤ 0 := by
    rw [leviC_diagonal_eq_quadratic hf]
    unfold Yau.LeafProofs.L22Aux.complexLeviQuadratic
    linarith
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (hv i).le) hlevi

theorem complex_heat_nonneg_at_max (values : Fin n → ℝ) (hv : ∀ i, 0 < values i)
    (F : ComplexVector n × ℝ → ℝ) {z : ComplexVector n} {t T : ℝ}
    (ht : 0 < t) (htT : t ≤ T)
    (hspace : ContDiffAt ℝ 2 (fun w => F (w, t)) z)
    (hmaxSpace : IsLocalMax (fun w => F (w, t)) z)
    (htime : DifferentiableWithinAt ℝ (fun s => F (z, s)) (Set.Icc 0 T) t)
    (hmaxTime : IsMaxOn (fun s => F (z, s)) (Set.Icc 0 T) t) :
    0 ≤ derivWithin (fun s => F (z, s)) (Set.Icc 0 T) t -
      traceWith (Matrix.diagonal (fun i => (values i : ℂ))) (leviC (fun w => F (w, t)) z) := by
  have hs := traceWith_leviC_nonpos_at_localMax values hv hspace hmaxSpace
  have htimeD := Yau.LeafProofs.L16Aux.derivWithin_nonneg_at_Icc_max ht htT htime hmaxTime
  linarith

end Yau.NodeProofs.F01Aux
