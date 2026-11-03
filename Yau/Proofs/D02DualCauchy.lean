import Yau.Proofs.D02DifferentialNorm
import Yau.Proofs.D02PotentialLevi
import Yau.Proofs.D02Pullback

/-! Exact same-metric Cauchy--Schwarz and the actual dF operator bound.
These estimates use the inverse-transpose dual quadratic form. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof
set_option backward.isDefEq.respectTransparency false

variable {n N : ℕ} {M : ComplexManifold n}

/-- The ordinary covector pairing is controlled by the actual dual quadratic form. -/
theorem dualNormMat_cauchy {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosDef)
    (η v : Fin n → ℂ) :
    ‖η ⬝ᵥ v‖ ^ 2 ≤ dualNormMat H (WithLp.toLp 2 η) * (star v ⬝ᵥ H *ᵥ v).re := by
  let u : Fin n → ℂ := H⁻¹ *ᵥ star η
  have hHu : H *ᵥ u = star η := by
    dsimp only [u]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv H (hH.isUnit.map Matrix.detMonoidHom),
      Matrix.one_mulVec]
  have hstar : star u = η ᵥ* H⁻¹ := by
    dsimp only [u]
    rw [Matrix.star_mulVec, star_star, hH.inv.isHermitian.eq]
  have hcross : star u ⬝ᵥ H *ᵥ v = η ⬝ᵥ v := by
    rw [hstar, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul H (hH.isUnit.map Matrix.detMonoidHom), Matrix.one_mulVec]
  have hself : (star u ⬝ᵥ H *ᵥ u).re = dualNormMat H (WithLp.toLp 2 η) := by
    rw [hstar, hHu]
    change (η ᵥ* H⁻¹ ⬝ᵥ star η).re = (star η ⬝ᵥ H⁻¹ᵀ *ᵥ η).re
    rw [dotProduct_comm]
    have hv : η ᵥ* H⁻¹ = H⁻¹ᵀ *ᵥ η := by
      simpa only [Matrix.transpose_transpose] using Matrix.vecMul_transpose H⁻¹ᵀ η
    rw [hv]
  have hCS := hH.star_dotProduct_mulVec_mul_le u v
  rw [hcross, star_mul_self_eq_norm_sq] at hCS
  have him : (star u ⬝ᵥ H *ᵥ u).im = 0 :=
    (Complex.nonneg_iff.mp (hH.posSemidef.dotProduct_mulVec_nonneg u)).2.symm
  have hc := (Complex.nonneg_iff.mp (sub_nonneg.mpr hCS)).1
  simp only [Complex.sub_re, Complex.mul_re, him, zero_mul, sub_zero, Complex.ofReal_re,
    hself] at hc
  linarith

/-- Actual tangent coordinates evaluate the actual Hermitian metric. -/
theorem gMat_tangentCoords_quadratic (g : HermitianField M) (x : M.Carrier)
    (v : TangentVector M x) :
    (star (WithLp.ofLp (tangentCoords x x v)) ⬝ᵥ
      (gMat g x *ᵥ WithLp.ofLp (tangentCoords x x v))).re = hermitianNormSq (g x) v := by
  have h := hMat_quadratic g x (chartPt x x) (WithLp.ofLp (tangentCoords x x v))
  have hround : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  rw [hround, Yau.LeafProofs.L17Aux.chartVec_basis_sum,
    chartVec_tangentCoords x x (mem_extChartAt_source x) v] at h
  exact congrArg Complex.re h

theorem covector_apply_norm_sq_le (g : HermitianField M) (x : M.Carrier)
    (ξ : Covector n) (v : TangentVector M x) :
    ‖ξ (show ComplexVector n from v)‖ ^ 2 ≤ dualNorm g x ξ * hermitianNormSq (g x) v := by
  have hf : chartVec x x (tangentCoords x x v) = v :=
    chartVec_tangentCoords x x (mem_extChartAt_source x) v
  have he := covector_apply_chartVec x x ξ (tangentCoords x x v)
  rw [hf] at he
  have he' : ξ (show ComplexVector n from v) =
      WithLp.ofLp (covectorCoords x x ξ) ⬝ᵥ WithLp.ofLp (tangentCoords x x v) := by
    simpa only [dotProduct, mul_comm] using he
  have h := dualNormMat_cauchy (gMat_posDef g x)
    (WithLp.ofLp (covectorCoords x x ξ)) (WithLp.ofLp (tangentCoords x x v))
  rw [← he', gMat_tangentCoords_quadratic g x v] at h
  exact h

/-- This is the exact squared operator estimate for the same actual differential. -/
theorem immersionDifferentialNorm_bound (g : HermitianField M) (F : M.Carrier → ComplexVector N)
    (x : M.Carrier) (v : TangentVector M x) :
    ‖(NormedSpace.fromTangentSpace (𝕜 := ℂ) (F x))
      (mfderiv (ComplexModel n) (ComplexModel N) F x v)‖ ^ 2 ≤
        immersionDifferentialNormSq g F x * hermitianNormSq (g x) v := by
  rw [EuclideanSpace.norm_sq_eq]
  calc
    _ = ∑ a, ‖immersionComponentDifferential F a x (show ComplexVector n from v)‖ ^ 2 := rfl
    _ ≤ ∑ a, dualNorm g x (immersionComponentDifferential F a x) * hermitianNormSq (g x) v :=
      Finset.sum_le_sum fun a _ => covector_apply_norm_sq_le g x (immersionComponentDifferential F a x) v
    _ = _ := by rw [← Finset.sum_mul]; rfl

/-- A bound for the computed u gives the bound for the actual pullback map A=dF. -/
theorem tangentPullbackMap_bounded {B : ComplexManifold 1} (g : HermitianField M)
    (F : M.Carrier → ComplexVector N)
    (f : ContMDiffMap (ComplexModel 1) (ComplexModel n) B.Carrier M.Carrier ⊤)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, immersionDifferentialNormSq g F (f x) ≤ C) :
    BundlePresentation.BoundedMap (tangentPullbackFiber f) (tangentPullbackMetric g f)
      (tangentPullbackMap F f) := by
  refine ⟨C, hC, fun x v => ?_⟩
  exact (immersionDifferentialNorm_bound g F (f x) v).trans
    (mul_le_mul_of_nonneg_right (hbound x) (hermitianNormSq_nonneg (g (f x)) v))

end Yau.NodeProofs.D02Aux
