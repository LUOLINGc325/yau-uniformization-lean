import Yau.Proofs.F04CovectorMatrix
import Yau.Proofs.F04GradientCauchy

open scoped Matrix ComplexOrder

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint Yau.LeafProofs.L18Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem traceWith_covector_rankOne (H : Herm n) (c : Fin n → ℂ) :
    traceWith H (Matrix.vecMulVec (star c) c) = dualNormMat H (WithLp.toLp 2 c) := by
  unfold traceWith dualNormMat
  simp only [WithLp.ofLp_toLp, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec, Matrix.transpose_apply, Pi.star_apply,
    Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem dualNormMat_le_trace_product (H G : Herm n) (hH : H.PosDef) (hG : G.PosDef)
    (c : Fin n → ℂ) :
    dualNormMat H (WithLp.toLp 2 c) ≤
      traceWith H G * dualNormMat G (WithLp.toLp 2 c) := by
  have hh := Yau.Proofs.F02Aux.traceWith_mono H
    (Matrix.vecMulVec (star c) c) ((dualNormMat G (WithLp.toLp 2 c) : ℂ) • G)
    hH.posSemidef (covector_rankOne_bound G hG c)
  rw [traceWith_covector_rankOne, Yau.Proofs.F02Aux.traceWith_real_smul] at hh
  simpa only [mul_comm] using hh

/-- The intrinsic trace controls all scalar cotangent energies at once. -/
theorem scalarGradientPair_le_trace (H G : HermitianField M)
    {f : M.Carrier → ℝ} (hf : SmoothFn f) (x : M.Carrier) :
    scalarGradientPair H f f x ≤
      traceWith (gMat H x) (gMat G x) * scalarGradientPair G f f x := by
  rw [scalarGradientPair_eq_twice_gradNormSq H hf x,
    scalarGradientPair_eq_twice_gradNormSq G hf x]
  have hh := dualNormMat_le_trace_product (gMat H x) (gMat G x)
    (hMat_posDef H x (chartPt x x) (mem_extChartAt_target x))
    (hMat_posDef G x (chartPt x x) (mem_extChartAt_target x))
    (fun i => wirt (fun z => (Complex.ofReal (inChart x f z))) (chartPt x x) (stdVec i))
  change gradNormSq H f x ≤ traceWith (gMat H x) (gMat G x) * gradNormSq G f x at hh
  nlinarith

end Yau.F04Proof
