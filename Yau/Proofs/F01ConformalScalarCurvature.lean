import Yau.Proofs.F01ConformalRicci
import Yau.Proofs.F01ConformalDual
import Yau.Proofs.F01TraceOrder
import Yau.Proofs.F01PotentialLaplacian

/-! The actual conformal scalar curvature has its exact initial lower
bound from the original scalar curvature and the true conformal Levi budget. -/
noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem traceWith_real_smul_left (H A : Matrix (Fin n) (Fin n) ℂ)
    (hH : IsUnit H.det) {c : ℝ} (hc : c ≠ 0) :
    traceWith ((c : ℂ) • H) A = c⁻¹ * traceWith H A := by
  rw [traceWith, matrix_inv_smul_of_ne_zero H hH (c : ℂ) (Complex.ofReal_ne_zero.mpr hc),
    Matrix.smul_mul, Matrix.trace_smul]
  simp only [← Complex.ofReal_inv, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, traceWith]

theorem conformalField_scalarCurvature (g : HermitianField M) (hg : MetricSmooth g)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (x : M.Carrier) :
    scalarCurvature (conformalField g f) x =
      Real.exp (-f x) * scalarCurvature g x -
        (n : ℝ) * laplacian (conformalField g f) f x := by
  unfold scalarCurvature
  rw [conformalField_ricci g hg f hf x, traceWith_sub]
  have hn : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_cast
  rw [hn, traceWith_real_smul]
  have hdet : IsUnit (gMat g x).det := (Yau.LeafProofs.L12Aux.hMat_posDef g x (chartPt x x)
    (mem_extChartAt_target x)).isUnit.map Matrix.detMonoidHom
  conv_lhs => arg 1; rw [conformalField_gMat, traceWith_real_smul_left _ _ hdet (Real.exp_pos _).ne']
  rw [Real.exp_neg]
  rfl

theorem conformalField_negative_scalar_upper (g : HermitianField M) (hg : MetricSmooth g)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (x : M.Carrier) {B : ℝ}
    (hscalar : 0 ≤ scalarCurvature g x)
    (hLevi : ((B : ℂ) • gMat (conformalField g f) x - levi f x).PosSemidef) :
    -scalarCurvature (conformalField g f) x ≤ (n : ℝ) ^ 2 * B := by
  have hpos : (gMat (conformalField g f) x).PosDef := Yau.LeafProofs.L12Aux.hMat_posDef (conformalField g f) x (chartPt x x)
    (mem_extChartAt_target x)
  have htrace := traceWith_mono hpos hLevi
  rw [traceWith_real_smul, traceWith_self_posDef hpos] at htrace
  have hnonneg := mul_nonneg (Real.exp_pos (-f x)).le hscalar
  have hmul := mul_le_mul_of_nonneg_left htrace (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  rw [conformalField_scalarCurvature g hg f hf x]
  change (n : ℝ) * laplacian (conformalField g f) f x ≤ _ at hmul
  nlinarith

end Yau.NodeProofs.F01Aux
