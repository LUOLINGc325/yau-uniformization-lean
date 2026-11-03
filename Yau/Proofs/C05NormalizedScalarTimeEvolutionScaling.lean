import Yau.Proofs.C05NormalizedScalarTimeEvolutionDefinitions

/-! Constant metric rescaling of the actual trace polynomials, with their exact weights. -/
noncomputable section
open scoped Manifold Topology ContDiff Matrix
namespace Yau.Proofs.C05NormalizedScalarTimeEvolutionAux
open Yau Yau.Blueprint Yau.Proofs.C04Aux Yau.Proofs.C05Aux Yau.Proofs.C05ThirdScalarTimeAux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem inverseMetric_scaleField (R : ℝ) (hR : 0 < R) (k : HermitianField M)
    (x : M.Carrier) :
    (gMat (scaleField R hR k) x)⁻¹ = ((R⁻¹ : ℝ) : ℂ) • (gMat k x)⁻¹ := by
  have hg := Yau.LeafProofs.L18Aux.hMat_posDef k x (chartPt x x) (mem_extChartAt_target x)
  rw [gMat_scaleField]
  simpa only [Complex.ofReal_inv] using inverse_real_smul R hR (gMat k x) hg

theorem ricciEndomorphism_scaleField (R : ℝ) (hR : 0 < R) (k : HermitianField M)
    (x : M.Carrier) :
    (gMat (scaleField R hR k) x)⁻¹ * ricci (scaleField R hR k) x =
      ((R⁻¹ : ℝ) : ℂ) • ((gMat k x)⁻¹ * ricci k x) := by
  rw [inverseMetric_scaleField, ricci_scaleField, Matrix.smul_mul]

theorem scalarLeviEndomorphism_scaleField (R : ℝ) (hR : 0 < R)
    (k : HermitianField M) (hs : SmoothFn (scalarCurvature k)) (x : M.Carrier) :
    (gMat (scaleField R hR k) x)⁻¹ * levi (scalarCurvature (scaleField R hR k)) x =
      (((R⁻¹)^2 : ℝ) : ℂ) • ((gMat k x)⁻¹ * levi (scalarCurvature k) x) := by
  have he : scalarCurvature (scaleField R hR k) = fun y => R⁻¹ * scalarCurvature k y := by
    funext y
    exact scalar_scaleField R hR k y
  rw [inverseMetric_scaleField, he, levi_const_mul _ hs]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  push_cast
  ring

theorem ricciLeviPairing_scaled_function (R : ℝ) (hR : 0 < R) (k : HermitianField M)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (a : ℝ) (x : M.Carrier) :
    ricciLeviPairing (scaleField R hR k) (fun y => a * f y) x =
      R⁻¹ ^ 2 * a * ricciLeviPairing k f x := by
  unfold ricciLeviPairing traceWith
  rw [inverseMetric_scaleField, ricci_scaleField, levi_const_mul f hf a]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_smul, smul_eq_mul,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, add_zero]
  ring

theorem ricciCube_scaleField (R : ℝ) (hR : 0 < R) (k : HermitianField M) (x : M.Carrier) :
    ricciCube (scaleField R hR k) x = R⁻¹ ^ 3 * ricciCube k x := by
  unfold ricciCube
  simp only [ricciEndomorphism_scaleField, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.trace_smul, smul_eq_mul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  ring

theorem ricciSquareLevi_scaleField (R : ℝ) (hR : 0 < R) (k : HermitianField M)
    (hs : SmoothFn (scalarCurvature k)) (x : M.Carrier) :
    ricciSquareLevi (scaleField R hR k) x = R⁻¹ ^ 4 * ricciSquareLevi k x := by
  unfold ricciSquareLevi
  simp only [ricciEndomorphism_scaleField, scalarLeviEndomorphism_scaleField R hR k hs,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul, smul_eq_mul,
    Complex.mul_re, Complex.mul_im, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, add_zero]
  ring

theorem leviScalarSquare_scaleField (R : ℝ) (hR : 0 < R) (k : HermitianField M)
    (hs : SmoothFn (scalarCurvature k)) (x : M.Carrier) :
    leviScalarSquare (scaleField R hR k) x = R⁻¹ ^ 4 * leviScalarSquare k x := by
  unfold leviScalarSquare
  simp only [scalarLeviEndomorphism_scaleField R hR k hs, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Matrix.trace_smul, smul_eq_mul, Complex.mul_re, Complex.mul_im,
    ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, add_zero]
  ring

theorem ricciQuartic_scaleField (R : ℝ) (hR : 0 < R) (k : HermitianField M) (x : M.Carrier) :
    ricciQuartic (scaleField R hR k) x = R⁻¹ ^ 4 * ricciQuartic k x := by
  unfold ricciQuartic
  simp only [ricciEndomorphism_scaleField, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.trace_smul, smul_eq_mul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  ring

end Yau.Proofs.C05NormalizedScalarTimeEvolutionAux
