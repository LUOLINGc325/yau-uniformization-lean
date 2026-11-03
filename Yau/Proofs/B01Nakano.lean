import Yau.Proofs.B01Levi

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Bundle

noncomputable section

namespace Yau.Proofs.B01Aux
open Yau Yau.Blueprint Yau.Blueprint.BundlePresentation

variable {M : ComplexManifold 1} {r : ℕ}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem curveWeightedNakanoTransport : CurveWeightedNakanoTransport (r := r) E := by
  intro c hc k φ _ _ hG hφ hl a z hz U
  let R := BundleDbar.curvature (r := r) E k a z 0 0
  let H := BundleDbar.metricMatrix (r := r) E k a z
  let Q (B : Matrix (Fin r) (Fin r) ℂ) : ℂ :=
    ∑ α, ∑ β, B α β * star (U 0 α) * U 0 β
  let l : ℝ := discLeviScalar c φ (chartInv a z) *
    Complex.normSq (wirt (fun w => c (chartInv a w)) z (stdVec 0))
  have hR : 0 ≤ (Q R).re := by
    have h := hG a z hz (stdVec 0) (WithLp.toLp 2 (U 0))
    simpa [BundleDbar.griffithsQuadratic, stdVec, Q, R] using h
  have hH : 0 ≤ (Q H).re := by
    have h := (LeafProofs.L14Aux.metricMatrix_posDef (r := r) E k a z hz).posSemidef.dotProduct_mulVec_nonneg (U 0)
    have he : Q H = star (U 0) ⬝ᵥ (H *ᵥ (U 0)) := by
      simp only [Q, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro α _
      apply Finset.sum_congr rfl
      intro β _
      ring
    rw [he]
    exact (Complex.nonneg_iff.mp h).1
  have hl' : 0 ≤ l := mul_nonneg (hl _) (Complex.normSq_nonneg _)
  have hlev : leviC (inChart a φ) z 0 0 = (l : ℂ) := discLevi_inChart (r := r) E c hc φ hφ a hz.1
  have hsum : (∑ α : Fin r, ∑ β : Fin r,
      (R α β + (l : ℂ) * H α β) * star (U 0 α) * U 0 β) = Q R + (l : ℂ) * Q H := by
    simp only [Q, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  have he : BundleDbar.nakanoQuadratic (BundleDbar.weightedCurvature (r := r) E k φ a z) U =
      (Q R).re + l * (Q H).re := by
    unfold BundleDbar.nakanoQuadratic BundleDbar.weightedCurvature
    simp only [Fin.sum_univ_one, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hlev]
    rw [hsum]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
  rw [he]
  exact add_nonneg hR (mul_nonneg hl' hH)

end Yau.Proofs.B01Aux
