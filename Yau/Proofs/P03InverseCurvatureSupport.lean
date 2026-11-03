import Yau.LeafProofs.L14

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar Yau.LeafProofs.L14Aux

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (Bundle.TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- The variational inverse norm vanishes at an actual zero of the source
under the computed nonnegative weighted curvature. -/
theorem inverseCurvatureNormSq_zero_at (g : HermitianField M) (h : Metric (M := M) E)
    (φ : M.Carrier → ℝ) (hN : WeightedNakanoNonnegative (r := r) E h φ)
    (f : NQForm E 1) (x : M.Carrier) (hfx : f x = (0 : NQForm E 1) x) :
    inverseCurvatureNormSq (r := r) E g h φ f x = 0 := by
  have hnorm : BundleDbar.formNormSq (r := r) E g h f x = 0 :=
    (formNormSq_one_eq_zero_iff E g h f x).mpr hfx
  have hcoeff := (formNormSq_one_eq_zero_iff_coefficients E g h f x).mp hnorm
  have hpair (V : Fin n → Fin r → ℂ) :
      coefficientInner (r := r) E g h x
        (fun i α => coefficients (r := r) E f x (chartPt x x) (fun _ => i) α) V = 0 := by
    unfold coefficientInner
    simp only [hcoeff, star_zero, zero_mul, Finset.sum_const_zero, mul_zero]
  have hle : inverseCurvatureNormSq (r := r) E g h φ f x ≤ ENNReal.ofReal 0 := by
    apply (inverseCurvatureNormSq_le_iff E g h φ hN f x (le_refl 0)).mpr
    intro V
    simp only [hpair, Complex.normSq_zero, zero_mul, le_refl]
  exact le_antisymm (by simpa only [ENNReal.ofReal_zero] using hle) (by positivity)

end Yau.NodeProofs.P03Aux
