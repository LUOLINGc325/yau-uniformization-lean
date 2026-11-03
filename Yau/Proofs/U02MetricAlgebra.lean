import Yau.Proofs.U02ModelSeparation
import Yau.LeafProofs.L12

/-! The original matrix inequalities act on the actual tangent vectors.
The chart pullback estimate uses its actual manifold derivative. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Matrix

noncomputable section
namespace Yau.NodeProofs.U02Proof
open Yau Blueprint
open Yau.LeafProofs.L12Aux

theorem hermitian_gram_quadratic {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (h : HermitianInnerProduct V) (L : ComplexVector n →ₗ[ℂ] V) (u : ComplexVector n) :
    star (fun i => u i) ⬝ᵥ
        ((fun i j => h.toFun (L (stdVec i)) (L (stdVec j))) *ᵥ fun i => u i) =
      h.toFun (L u) (L u) := by
  classical
  have hu : (∑ i, u i • stdVec i) = u := by
    ext i
    simp [stdVec, EuclideanSpace.single, Pi.single_apply]
  have hL : (∑ i, u i • L (stdVec i)) = L u := by
    simpa only [map_sum, map_smul] using congrArg L hu
  calc
    _ = h.toFun (∑ i, u i • L (stdVec i)) (∑ i, u i • L (stdVec i)) := by
      rw [hermitian_sum_left]
      simp only [hermitian_sum_right, HermitianInnerProduct.map_smul_left,
        HermitianInnerProduct.map_smul_right, dotProduct, mulVec, Pi.star_apply,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [hL]

theorem gMat_tangent_quadratic {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x : M.Carrier) (v : TangentVector M x) :
    (star (fun i => tangentCoords x x v i) ⬝ᵥ
      (gMat h x *ᵥ fun i => tangentCoords x x v i)).re = hermitianNormSq (h x) v := by
  have hx : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hq := hermitian_gram_quadratic (h x)
    (mfderiv (ComplexModel n) (ComplexModel n)
      (extChartAt (ComplexModel n) x).symm (chartPt x x)).toLinearMap (tangentCoords x x v)
  change (star (fun i => tangentCoords x x v i) ⬝ᵥ
    ((fun i j => (h x).toFun (chartVec x x (stdVec i))
      (chartVec x x (stdVec j))) *ᵥ fun i => tangentCoords x x v i)) =
        (h x).toFun (chartVec x x (tangentCoords x x v))
          (chartVec x x (tangentCoords x x v)) at hq
  rw [chartVec_tangentCoords x x (mem_extChartAt_source x)] at hq
  unfold gMat Yau.hMat
  rw [hx]
  exact congrArg Complex.re hq

theorem hermLE_quadratic {n : ℕ} {A B : Herm n} (h : HermLE A B) (u : Fin n → ℂ) :
    (star u ⬝ᵥ (A *ᵥ u)).re ≤ (star u ⬝ᵥ (B *ᵥ u)).re := by
  have hh := (Complex.nonneg_iff.mp (h.dotProduct_mulVec_nonneg u)).1
  simpa only [sub_mulVec, dotProduct_sub, Complex.sub_re, sub_nonneg] using hh

theorem hermLE_tangent_normSq {n : ℕ} {M : ComplexManifold n}
    (h0 h1 : HermitianField M) (x : M.Carrier) (a : ℝ)
    (h : HermLE ((a : ℂ) • gMat h0 x) (gMat h1 x)) (v : TangentVector M x) :
    a * hermitianNormSq (h0 x) v ≤ hermitianNormSq (h1 x) v := by
  have hh := hermLE_quadratic h (fun i => tangentCoords x x v i)
  simpa only [smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, gMat_tangent_quadratic] using hh

set_option backward.isDefEq.respectTransparency false in
theorem unitaryChart_tangent_normSq {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (p : M.Carrier) (Phi : ComplexVector n → M.Carrier)
    {r c C : ℝ} (hc : UnitaryChart h p Phi r c C)
    {z : ComplexVector n} (hz : z ∈ Metric.ball 0 r) (v : ComplexVector n) :
    hermitianNormSq (h (Phi z))
      (mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Phi z v) ≤ C * ‖v‖ ^ 2 := by
  have hh := hermLE_quadratic (hc.2.2.2 z hz).2 (fun i => v i)
  have hq := hermitian_gram_quadratic (h (Phi z))
    (mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Phi z).toLinearMap v
  change (star (fun i => v i) ⬝ᵥ (pullbackMat h Phi z *ᵥ fun i => v i)) = _ at hq
  rw [hq] at hh
  have hnorm : (star (fun i => v i) ⬝ᵥ (fun i => v i)).re = ‖v‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ) v, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct_comm]
    rfl
  simp only [ContinuousLinearMap.coe_coe, hermitianNormSq, smul_mulVec, one_mulVec,
    dotProduct_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, hnorm] at hh
  convert! hh using 1 <;> rfl

end Yau.NodeProofs.U02Proof
