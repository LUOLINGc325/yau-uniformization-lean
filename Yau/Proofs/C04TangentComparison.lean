import Yau.Proofs.C04RayleighScaling

/-! The Loewner bounds in C01 control the genuine path speeds. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

namespace Yau.Proofs.C04Aux
open Yau Blueprint
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem gMat_quadratic_tangent (k : HermitianField M) (x : M.Carrier)
    (v : TangentVector M x) :
    matrixQuadratic (gMat k x) (tangentCoords x x v) = hermitianNormSq (k x) v := by
  have hx : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  let u := tangentCoords x x v
  have hsum : ∑ i, u i • stdVec i = u := by
    ext i
    simp [stdVec, EuclideanSpace.single, Pi.single_apply]
  have hrec : ∑ i, u i • chartVec x x (stdVec i) = v := by
    calc
      ∑ i, u i • chartVec x x (stdVec i) = chartVec x x (∑ i, u i • stdVec i) := by
        rw [LeafProofs.L18Aux.chartVec_sum]
        apply Finset.sum_congr rfl
        intro i _
        exact (LeafProofs.L18Aux.chartVec_smul x x _ _).symm
      _ = v := by rw [hsum]; exact LeafProofs.L12Aux.chartVec_tangentCoords x x (mem_extChartAt_source x) v
  have heq := congrArg Complex.re
    (LeafProofs.L18Aux.hMat_quadratic k x (chartPt x x) (WithLp.ofLp u))
  rw [hx, hrec] at heq
  exact heq

theorem tangent_norm_le_of_HermLE (k g : HermitianField M) (x : M.Carrier)
    (c : ℝ) (hkg : HermLE (gMat k x) ((c : ℂ) • gMat g x))
    (v : TangentVector M x) : hermitianNormSq (k x) v ≤ c * hermitianNormSq (g x) v := by
  let u := tangentCoords x x v
  have hh := hkg.re_dotProduct_nonneg (WithLp.ofLp u)
  change 0 ≤ matrixQuadratic (((c : ℂ) • gMat g x) - gMat k x) u at hh
  have hsub : matrixQuadratic (((c : ℂ) • gMat g x) - gMat k x) u =
      c * matrixQuadratic (gMat g x) u - matrixQuadratic (gMat k x) u := by
    simp only [matrixQuadratic, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re,
      Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hsub, gMat_quadratic_tangent, gMat_quadratic_tangent] at hh
  linarith

theorem curveSpeed_le_of_HermLE (k g : HermitianField M) {x y : M.Carrier}
    (γ : PiecewiseC1Curve x y) (t c : ℝ) (hc : 0 ≤ c)
    (hkg : HermLE (gMat k (γ t)) ((c : ℂ) • gMat g (γ t))) :
    curveSpeed k γ t ≤ Real.sqrt c * curveSpeed g γ t := by
  have hnorm := tangent_norm_le_of_HermLE k g (γ t) c hkg (realTangentDerivative γ t)
  have hh := Real.sqrt_le_sqrt (show 2 * hermitianNormSq (k (γ t)) (realTangentDerivative γ t) ≤
      c * (2 * hermitianNormSq (g (γ t)) (realTangentDerivative γ t)) by nlinarith)
  rw [Real.sqrt_mul hc] at hh
  exact hh

theorem curveLength_le_of_HermLE (k g : HermitianField M) {x y : M.Carrier}
    (γ : PiecewiseC1Curve x y) (c : ℝ) (hc : 0 ≤ c)
    (hk : IntegrableOn (curveSpeed k γ) (Set.Icc (0 : ℝ) 1))
    (hg : IntegrableOn (curveSpeed g γ) (Set.Icc (0 : ℝ) 1))
    (hkg : ∀ t ∈ Set.Icc (0 : ℝ) 1, HermLE (gMat k (γ t)) ((c : ℂ) • gMat g (γ t))) :
    curveLength k γ ≤ Real.sqrt c * curveLength g γ := by
  unfold curveLength
  rw [← integral_const_mul]
  exact setIntegral_mono_on hk (hg.const_mul _) measurableSet_Icc
    (fun t ht => curveSpeed_le_of_HermLE k g γ t c hc (hkg t ht))

end Yau.Proofs.C04Aux
