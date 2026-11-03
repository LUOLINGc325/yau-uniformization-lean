import Yau.Proofs.Y03CenterFrame

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint
open Yau.Blueprint.Alignment.Y03Proof

variable {n : ℕ} {M : ComplexManifold n}

/-- The displayed pullback matrix is the quadratic form of the actual
manifold differential on every vector, beyond the standard basis vectors. -/
theorem pullback_quadratic (k : HermitianField M)
    (Φ : ComplexVector n → M.Carrier) (z v : ComplexVector n) :
    (star (WithLp.ofLp v) ⬝ᵥ (pullbackMat k Φ z *ᵥ WithLp.ofLp v)).re =
      hermitianNormSq (k (Φ z))
        (mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ z v) := by
  let L : ComplexVector n →L[ℂ] TangentVector M (Φ z) :=
    (mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ z).comp
      (NormedSpace.fromTangentSpace (𝕜 := ℂ) z).symm.toContinuousLinearMap
  have hL : L v = ∑ i, v i • L (stdVec i) := by
    calc
      L v = L (∑ i, v i • stdVec i) := congrArg L (sum_stdVec v).symm
      _ = _ := by simp only [map_sum, map_smul]
  change _ = ((k (Φ z)).toFun (L v) (L v)).re
  rw [hL, hermitian_sum_left]
  apply congrArg Complex.re
  simp only [hermitian_sum_right, HermitianInnerProduct.map_smul_left,
    HermitianInnerProduct.map_smul_right, Matrix.mulVec, dotProduct,
    Finset.mul_sum, pullbackMat, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change star (v i) * ((k (Φ z)).toFun
      ((mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ z) (stdVec i))
      ((mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ z) (stdVec j)) * v j) =
    star (v i) * (k (Φ z)).toFun
      ((mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ z) (stdVec i))
      ((mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ z) (stdVec j)) * v j
  ring

/-- The chart's Loewner bounds control the speed of its genuine differential.
This is the metric estimate used to prevent short lifted paths from escaping
through the Euclidean boundary. -/
theorem unitaryChart_derivative_bounds {k : HermitianField M} {p : M.Carrier}
    {Φ : ComplexVector n → M.Carrier} {r c C : ℝ}
    (hΦ : UnitaryChart k p Φ r c C) {z : ComplexVector n}
    (hz : z ∈ Metric.ball 0 r) (v : ComplexVector n) :
    c * ‖v‖ ^ 2 ≤ hermitianNormSq (k (Φ z))
      (mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ z v) ∧
    hermitianNormSq (k (Φ z))
      (mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ z v) ≤ C * ‖v‖ ^ 2 := by
  let q : Herm n → ℝ := fun A => (star (WithLp.ofLp v) ⬝ᵥ (A *ᵥ WithLp.ofLp v)).re
  have hq {A B : Herm n} (hAB : HermLE A B) : q A ≤ q B := by
    have h := (Complex.nonneg_iff.mp (hAB.dotProduct_mulVec_nonneg (WithLp.ofLp v))).1
    simpa only [q, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, sub_nonneg] using h
  have hq1 : q 1 = ‖v‖ ^ 2 := by
    have hh := inner_self_eq_norm_sq (𝕜 := ℂ) v
    rw [EuclideanSpace.inner_eq_star_dotProduct, RCLike.re_eq_complex_re] at hh
    simpa only [q, Matrix.one_mulVec, dotProduct_comm] using hh
  have hscale (a : ℝ) : q ((a : ℂ) • (1 : Herm n)) = a * ‖v‖ ^ 2 := by
    simp only [q, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    exact congrArg (a * ·) (by simpa only [q, Matrix.one_mulVec] using hq1)
  rcases hΦ.2.2.2 z hz with ⟨hlo, hhi⟩
  have hlo' := hq hlo
  have hhi' := hq hhi
  rw [hscale] at hlo' hhi'
  rw [← pullback_quadratic]
  exact ⟨hlo', hhi'⟩

end Yau.Proofs.C07Aux
