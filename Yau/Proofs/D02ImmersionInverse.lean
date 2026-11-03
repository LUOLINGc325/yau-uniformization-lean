import Yau.Proofs.D02RelativeQuadratic
import Yau.Proofs.D02ImmersionTrace

/-! The actual immersion derivative has the inverse bound determined by
the same metric norm u and Jacobian potential ψ. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof
set_option backward.isDefEq.respectTransparency false

variable {n N : ℕ} {M : ComplexManifold n}

theorem immersionGram_tangentCoords_quadratic {F : M.Carrier → ComplexVector N}
    (hF : IsHolomorphicVecMap F) (y : M.Carrier) (v : TangentVector M y) :
    (star (WithLp.ofLp (tangentCoords y y v)) ⬝ᵥ
      (immersionGram F y (chartPt y y) *ᵥ WithLp.ofLp (tangentCoords y y v))).re =
        ‖(NormedSpace.fromTangentSpace (𝕜 := ℂ) (F y))
          (mfderiv (ComplexModel n) (ComplexModel N) F y v)‖ ^ 2 := by
  have hround : chartInv y (chartPt y y) = y :=
    (extChartAt (ComplexModel n) y).left_inv (mem_extChartAt_source y)
  have hderiv := immersionInChart_fderiv_apply hF y (z := chartPt y y)
    (mem_extChartAt_target y) (tangentCoords y y v)
  rw [hround, chartVec_tangentCoords y y (mem_extChartAt_source y) v] at hderiv
  have hJ := immersionDerivativeMatrix_mulVec F y (chartPt y y) (tangentCoords y y v)
  rw [hderiv] at hJ
  rw [immersionGram, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, hJ]
  rw [EuclideanSpace.norm_sq_eq]
  simp only [dotProduct, Complex.re_sum, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro i _
  change (star ((NormedSpace.fromTangentSpace (𝕜 := ℂ) (F y))
      (mfderiv (ComplexModel n) (ComplexModel N) F y v) i) *
    ((NormedSpace.fromTangentSpace (𝕜 := ℂ) (F y))
      (mfderiv (ComplexModel n) (ComplexModel N) F y v) i)).re = _
  rw [star_mul_self_eq_norm_sq, Complex.ofReal_re]

theorem immersionJacobianWeight_eq_exp (g : HermitianField M)
    {F : M.Carrier → ComplexVector N} (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F)
    (y : M.Carrier) : immersionJacobianWeight g F y = Real.exp (immersionPotential g F y) :=
  (Real.exp_log (immersionJacobianWeight_pos g hF hImm y)).symm

/-- This compares the actual same-metric tangent norm to the actual dF
image; no singular values or comparison metric are supplied as hypotheses. -/
theorem immersionDerivative_inverse_bound (g : HermitianField M)
    {F : M.Carrier → ComplexVector N} (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F)
    (B : ℝ) (y : M.Carrier) (hy : immersionDifferentialNormSq g F y ≤ B)
    (v : TangentVector M y) :
    hermitianNormSq (g y) v ≤ max 1 B ^ (n - 1) * Real.exp (-immersionPotential g F y) *
      ‖(NormedSpace.fromTangentSpace (𝕜 := ℂ) (F y))
        (mfderiv (ComplexModel n) (ComplexModel N) F y v)‖ ^ 2 := by
  have htrace : ((gMat g y)⁻¹ * immersionGram F y (chartPt y y)).trace.re ≤ B := by
    rwa [← immersionDifferentialNormSq_eq_trace g hF y]
  have hb := relative_gram_quadratic_bound (gMat g y) (immersionGram F y (chartPt y y))
    (gMat_posDef g y) (immersionGram_posDef hF hImm y (mem_extChartAt_target y))
    B htrace (WithLp.ofLp (tangentCoords y y v))
  rw [gMat_tangentCoords_quadratic g y v, immersionGram_tangentCoords_quadratic hF y v] at hb
  change hermitianNormSq (g y) v ≤
    max 1 B ^ (n - 1) / immersionJacobianWeight g F y * _ at hb
  rw [immersionJacobianWeight_eq_exp g hF hImm y, div_eq_mul_inv, ← Real.exp_neg] at hb
  exact hb

end Yau.NodeProofs.D02Aux
