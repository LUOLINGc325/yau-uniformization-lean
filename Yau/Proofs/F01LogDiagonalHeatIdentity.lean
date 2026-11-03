import Yau.Proofs.F01LogLaplacianDiagonal
import Yau.Proofs.F01LogDetDiagonalHessian
import Yau.Proofs.F01MixedJetLocality

/-! The exact logarithmic diagonal heat identity from the actual
log-determinant metric evolution, before any curvature or error estimate. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix ComplexOrder Topology
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ}

theorem log_diagonal_heat_identity
    (H : ComplexVector n → Matrix (Fin n) (Fin n) ℂ) {S : Set (ComplexVector n)}
    (hS : IsOpen S) (hH : ∀ i j, ContDiffOn ℝ ∞ (fun w => H w i j) S)
    (hpos : ∀ w ∈ S, (H w).PosDef) {z : ComplexVector n} (hz : z ∈ S)
    (values : Fin n → ℝ) (hdiag : H z = Matrix.diagonal (fun i => (values i : ℂ)))
    (a : Fin n) (qcurve : ℝ → ℝ) (t : ℝ)
    (hvalue : qcurve t = (H z a a).re)
    (hevolution : HasDerivAt qcurve (leviC (fun w => Real.log (H w).det.re) z a a).re t) :
    let q := (H z a a).re
    deriv (fun s => Real.log (qcurve s)) t -
        traceWith (H z) (leviC (fun w => Real.log (H w a a).re) z) =
      -q⁻¹ * (∑ i, ∑ j, (values i)⁻¹ * (values j)⁻¹ *
          Complex.normSq (wirt (fun w => H w j i) z (stdVec a))) +
        q⁻¹ * (∑ i, (values i)⁻¹ *
          ((wirt (fun w => wirtBar (fun y => H y i i) w (stdVec a)) z (stdVec a)).re -
            (wirt (fun w => wirtBar (fun y => H y a a) w (stdVec i)) z (stdVec i)).re)) +
        dualNormMat (H z) (WithLp.toLp 2
          (fun i => wirt (fun w => (Real.log (H w a a).re : ℂ)) z (stdVec i))) := by
  have hv (i : Fin n) : 0 < values i := by
    have hsingle : (Pi.single i (1 : ℂ) : Fin n → ℂ) ≠ 0 := by
      intro hh
      have hh' := congrFun hh i
      simpa using hh'
    have hh := matrixQuadraticValue_pos (hpos z hz) hsingle
    simpa only [matrixQuadraticValue_single, hdiag, Matrix.diagonal_apply_eq,
      Complex.ofReal_re] using hh
  have hq : 0 < (H z a a).re := by
    simpa only [hdiag, Matrix.diagonal_apply_eq, Complex.ofReal_re] using hv a
  have hqd : ContDiffAt ℝ 2 (fun w => (H w a a).re) z :=
    Complex.reCLM.contDiff.contDiffAt.comp z
      (((hH a a).contDiffAt (hS.mem_nhds hz)).of_le (by simp))
  have hreal : EqOn (fun w => (((H w a a).re : ℝ) : ℂ)) (fun w => H w a a) S := by
    intro w hw
    have hh := congrArg Complex.im ((hpos w hw).isHermitian.apply a a)
    simp only [Complex.star_def, Complex.conj_im] at hh
    apply Complex.ext
    · rfl
    · simp only [Complex.ofReal_im]
      linarith
  have hmix (i : Fin n) : (leviC (fun w => (H w a a).re) z i i).re =
      (wirt (fun w => wirtBar (fun y => H y a a) w (stdVec i)) z (stdVec i)).re := by
    exact congrArg Complex.re (mixed_wirtinger_eq_of_eqOn hS hreal hz (stdVec i) (stdVec i))
  have htrace := traceWith_leviC_log_real_diagonal values (fun i => (hv i).ne') hqd hq
  rw [traceWith_real_diagonal values (fun i => (hv i).ne')
    (leviC (fun w => (H w a a).re) z), ← hdiag] at htrace
  simp only [hmix] at htrace
  have htlog : deriv (fun s => Real.log (qcurve s)) t =
      (leviC (fun w => Real.log (H w).det.re) z a a).re / (H z a a).re := by
    have hp : qcurve t ≠ 0 := by rw [hvalue]; exact hq.ne'
    simpa only [hvalue] using (hevolution.log hp).deriv
  dsimp only
  rw [htlog, htrace, logdet_diagonal_levi_formula H hS hH hpos hz values hdiag a]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  ring

end Yau.NodeProofs.F01Aux
