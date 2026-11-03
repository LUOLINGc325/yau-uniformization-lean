import Yau.Proofs.V03HilbertQuadratic

/-! For a genuine holomorphic Hilbert-valued map the mixed parameter
acceleration cancels, leaving exactly the squared first derivative. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau

theorem mixedReal_holomorphic_norm_sq {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {U : ℂ → H} (hU : ContDiffAt ℂ 2 U 0) :
    mixedReal (fun z => ‖U z‖ ^ 2) = ‖fderiv ℂ U 0 1‖ ^ 2 := by
  letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  rw [mixedReal_norm_sq (hU.restrict_scalars ℝ)]
  have hd := hU.differentiableAt (by norm_num)
  have hreal (v : ℂ) : fderiv ℝ U 0 v = fderiv ℂ U 0 v :=
    congrArg (fun A : ℂ →L[ℝ] H => A v) (hd.fderiv_restrictScalars ℝ)
  have hII := secondFDeriv_complex_I_I hU (1 : ℂ) (1 : ℂ)
  simp only [smul_eq_mul, mul_one] at hII
  rw [hII, add_neg_cancel]
  simp only [inner_zero_right, mul_zero, add_zero, hreal]
  have hI : fderiv ℂ U 0 Complex.I = Complex.I • fderiv ℂ U 0 1 := by
    simpa only [smul_eq_mul, mul_one] using (fderiv ℂ U 0).map_smul Complex.I (1 : ℂ)
  rw [hI, norm_smul, Complex.norm_I, one_mul]
  ring

end Yau.Blueprint.V03Proof
