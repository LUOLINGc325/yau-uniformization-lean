import Yau.Proofs.C02Frames
import Yau.LeafProofs.L23FieldMetric

/-! The Loewner inequalities in the original flow control the actual intrinsic
tangent norm, rather than only a separately supplied coordinate matrix. -/

noncomputable section
open scoped Manifold Matrix ComplexOrder
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

theorem hMat_quadratic_chartVec (k : HermitianField M) (a : M.Carrier)
    (z u : ComplexVector n) :
    star (WithLp.ofLp u) ⬝ᵥ (hMat k a z *ᵥ WithLp.ofLp u) =
      (k (chartInv a z)).toFun (chartVec a (chartInv a z) u)
        (chartVec a (chartInv a z) u) := by
  rw [L12Aux.hMat_quadratic]
  have hsum : (∑ i, u i • chartVec a (chartInv a z) (stdVec i)) =
      chartVec a (chartInv a z) u := by
    exact chartVectorInFrame_eq_chartVec a (chartInv a z) u
  rw [hsum]

theorem gMat_quadratic_tangent (k : HermitianField M) (x : M.Carrier)
    (v : TangentVector M x) :
    (star (WithLp.ofLp (tangentCoords x x v)) ⬝ᵥ
      (gMat k x *ᵥ WithLp.ofLp (tangentCoords x x v))).re =
      hermitianNormSq (k x) v := by
  let u := tangentCoords x x v
  have hp : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hG : gMat k x = fun i j => (k x).toFun
      (chartVec x x (stdVec i)) (chartVec x x (stdVec j)) := by
    ext i j
    change coordinateCoefficientInChart k x (chartInv x (chartPt x x)) i j =
      coordinateCoefficientInChart k x x i j
    exact congrArg (fun y => coordinateCoefficientInChart k x y i j) hp
  have hGram : star (WithLp.ofLp u) ⬝ᵥ (gMat k x *ᵥ WithLp.ofLp u) =
      (k x).toFun (∑ i, u i • chartVec x x (stdVec i))
        (∑ i, u i • chartVec x x (stdVec i)) := by
    rw [L12Aux.hermitian_sum_left]
    simp only [L12Aux.hermitian_sum_right, HermitianInnerProduct.map_smul_left,
      HermitianInnerProduct.map_smul_right, dotProduct, Matrix.mulVec,
      Pi.star_apply, Finset.mul_sum, hG]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hsum : (∑ i, u i • chartVec x x (stdVec i)) = v :=
    (chartVectorInFrame_eq_chartVec x x u).trans
      (L12Aux.chartVec_tangentCoords x x (mem_extChartAt_source x) v)
  rw [hsum] at hGram
  exact congrArg Complex.re hGram

theorem tangentNormSq_le_of_gMat_order (k₀ k₁ : HermitianField M) (x : M.Carrier)
    (hle : HermLE (gMat k₀ x) (gMat k₁ x)) (v : TangentVector M x) :
    hermitianNormSq (k₀ x) v ≤ hermitianNormSq (k₁ x) v := by
  have h := hle.dotProduct_mulVec_nonneg (WithLp.ofLp (tangentCoords x x v))
  have hr := (Complex.nonneg_iff.mp h).1
  rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re,
    gMat_quadratic_tangent k₁ x v, gMat_quadratic_tangent k₀ x v] at hr
  exact sub_nonneg.mp hr

theorem curveSpeed_le_of_gMat_order (k₀ k₁ : HermitianField M)
    (hle : ∀ x, HermLE (gMat k₀ x) (gMat k₁ x))
    {x y : M.Carrier} (γ : PiecewiseC1Curve x y) (s : ℝ) :
    curveSpeed k₀ γ s ≤ curveSpeed k₁ γ s := by
  exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
    (tangentNormSq_le_of_gMat_order k₀ k₁ (γ s) (hle (γ s))
      (realTangentDerivative γ s)) (by norm_num))

end Yau.Blueprint.C02Proof
