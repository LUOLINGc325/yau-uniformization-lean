import Yau.Proofs.F01LeviChartNaturality
import Yau.Proofs.F01ConformalLeviBound
import Yau.Proofs.F01GradientChartNaturality
import Yau.Proofs.F01ConformalRayleighContact

/-! The intrinsic conformal gradient and Levi budgets give the actual
coordinate budgets in a genuine g-normal holomorphic chart. -/
noncomputable section
open scoped Manifold ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem levi_holomorphic_chart_sandwich (α : HermitianField M)
    (f : M.Carrier → ℝ) (hf : SmoothFn f)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    {z : ComplexVector n} (hz : z ∈ e.source) (B : ℝ)
    (hlo : (levi f (e z) - ((-B : ℝ) : ℂ) • gMat α (e z)).PosSemidef)
    (hhi : ((B : ℂ) • gMat α (e z) - levi f (e z)).PosSemidef) :
    (leviC (fun w => f (e w)) z - ((-B : ℝ) : ℂ) • pullbackMatrix α e z).PosSemidef ∧
      ((B : ℂ) • pullbackMatrix α e z - leviC (fun w => f (e w)) z).PosSemidef := by
  let J := linearMatrix (coordinateDifferential e (e z) z)
  have hα : pullbackMatrix α e z = Jᴴ * gMat α (e z) * J :=
    pullbackMatrix_eq_congruence α e (e z) z (mem_extChartAt_source (e z))
  rw [leviC_holomorphic_chart f hf e he hz, hα]
  constructor
  · simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_assoc] using hlo.conjTranspose_mul_mul_same J
  · simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_assoc] using hhi.conjTranspose_mul_mul_same J

theorem conformal_normal_coordinate_gradient_bound (g : HermitianField M)
    (f : M.Carrier → ℝ) (hf : SmoothFn f)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {z : ComplexVector n} (hz : z ∈ e.source) (hvalue : pullbackMatrix g e z = 1)
    {G : ℝ} (hgrad : gradNormSq (conformalField g f) f (e z) ≤ G) (i : Fin n) :
    Complex.normSq (wirt (fun w => (f (e w) : ℂ)) z (stdVec i)) ≤
      G * Real.exp (f (e z)) := by
  have hfd : DifferentiableAt ℝ (fun w => f (e w)) z :=
    ((smoothFn_comp_holomorphic_chart f hf e he).contDiffAt
      (e.open_source.mem_nhds hz)).differentiableAt (by simp)
  have hc := gradient_quadratic_cauchy (pullbackMatrix (conformalField g f) e z)
    (pullbackMatrix_posDef (conformalField g f) e he hei hz) hfd (stdVec i)
  rw [← norm_wirt_ofReal_sq hfd, Complex.sq_norm,
    dualNormMat_holomorphic_chart_gradient (conformalField g f) f hf e he hei hz] at hc
  have hquad : (star (WithLp.ofLp (stdVec i)) ⬝ᵥ
      (pullbackMatrix (conformalField g f) e z *ᵥ WithLp.ofLp (stdVec i))).re =
        Real.exp (f (e z)) := by
    change matrixQuadraticValue (pullbackMatrix (conformalField g f) e z) (Pi.single i 1) = _
    rw [matrixQuadraticValue_single, conformalField_pullbackMatrix, hvalue]
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
      Complex.ofReal_re]
  rw [hquad] at hc
  exact hc.trans (mul_le_mul_of_nonneg_right hgrad (Real.exp_pos _).le)

theorem conformal_normal_coordinate_levi_bound (g : HermitianField M)
    (f : M.Carrier → ℝ) (hf : SmoothFn f)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    {z : ComplexVector n} (hz : z ∈ e.source) (hvalue : pullbackMatrix g e z = 1)
    (B : ℝ)
    (hlo : (levi f (e z) - ((-B : ℝ) : ℂ) • gMat (conformalField g f) (e z)).PosSemidef)
    (hhi : ((B : ℂ) • gMat (conformalField g f) (e z) - levi f (e z)).PosSemidef)
    (i : Fin n) :
    |(leviC (fun w => f (e w)) z i i).re| ≤ B * Real.exp (f (e z)) := by
  obtain ⟨hl, hh⟩ := levi_holomorphic_chart_sandwich (conformalField g f) f hf e he hz B hlo hhi
  have hl' := matrixQuadraticValue_nonneg hl (Pi.single i 1)
  have hh' := matrixQuadraticValue_nonneg hh (Pi.single i 1)
  rw [matrixQuadraticValue_single] at hl' hh'
  simp only [Matrix.sub_apply, Matrix.smul_apply, conformalField_pullbackMatrix,
    hvalue, Matrix.one_apply_eq, smul_eq_mul, mul_one, Complex.sub_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero,
    Complex.ofReal_neg, Complex.neg_re] at hl' hh'
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Yau.NodeProofs.F01Aux
