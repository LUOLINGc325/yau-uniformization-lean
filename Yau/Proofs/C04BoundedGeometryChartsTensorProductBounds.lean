import Yau.Proofs.C04BoundedGeometryChartsCurvatureFrame

/-! Intrinsic tensor estimates retaining the length of each individual slot. -/

noncomputable section
open scoped Matrix Manifold

namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n r : ℕ}

theorem tensorEvaluation_abs_le_product
    (G : Matrix (RIdx n) (RIdx n) ℝ) (hG : G.PosDef) (A : CovTensor n r)
    (V : Fin r → RIdx n → ℝ) (B : Fin r → ℝ) {K : ℝ}
    (hK : 0 ≤ K) (hB : ∀ j, 0 ≤ B j)
    (hA : Real.sqrt (covTensorNormSq G A) ≤ K)
    (hV : ∀ j, V j ⬝ᵥ (G *ᵥ V j) ≤ B j ^ 2) :
    |tensorEvaluation A V| ≤ K * ∏ j, B j := by
  have hnorm := covTensorNormSq_nonneg G hG A
  have hsq : covTensorNormSq G A ≤ K ^ 2 := by
    nlinarith [Real.sq_sqrt hnorm, Real.sqrt_nonneg (covTensorNormSq G A)]
  have hV₀ (j : Fin r) : 0 ≤ V j ⬝ᵥ (G *ᵥ V j) := by
    simpa only [star_trivial] using hG.posSemidef.dotProduct_mulVec_nonneg (V j)
  have hp : (∏ j : Fin r, V j ⬝ᵥ (G *ᵥ V j)) ≤ (∏ j, B j) ^ 2 := by
    rw [← Finset.prod_pow]
    exact Finset.prod_le_prod₀ (s := Finset.univ) (fun j _ => hV₀ j) (fun j _ => hV j)
  have heval := tensorEvaluation_sq_le G hG A V
  have hprod₀ : 0 ≤ ∏ j : Fin r, V j ⬝ᵥ (G *ᵥ V j) :=
    Finset.prod_nonneg fun j _ => hV₀ j
  have hh : tensorEvaluation A V ^ 2 ≤ (K * ∏ j, B j) ^ 2 := by
    calc
      _ ≤ covTensorNormSq G A * ∏ j : Fin r, V j ⬝ᵥ (G *ᵥ V j) := heval
      _ ≤ K ^ 2 * (∏ j, B j) ^ 2 := mul_le_mul hsq hp hprod₀ (sq_nonneg K)
      _ = _ := (mul_pow _ _ _).symm
  exact (sq_le_sq₀ (abs_nonneg _)
    (mul_nonneg hK (Finset.prod_nonneg fun j _ => hB j))).mp
      (by simpa only [sq_abs] using hh)

theorem curvature_jet_evaluation_le_product {M : ComplexManifold n}
    (k : HermitianField M) (p : M.Carrier) (m : ℕ)
    (V : Fin (4 + m) → TangentSpace 𝓘(ℝ, ComplexVector n) p)
    (B : Fin (4 + m) → ℝ) {K : ℝ} (hK : 0 ≤ K) (hB : ∀ j, 0 ≤ B j)
    (hcurv : curvatureJetNorm k m p ≤ K)
    (hV : ∀ j, (underlyingRealRiemannianMetric k).inner p (V j) (V j) ≤ B j ^ 2) :
    |tensorEvaluation (rmJet k p m (chartPt p p))
      (fun j => realCoord (realTangentCoords p p (V j)))| ≤ K * ∏ j, B j := by
  apply tensorEvaluation_abs_le_product _
    (realMetricFn_posDef k p (chartPt p p) (mem_extChartAt_target p)) _ _ B hK hB hcurv
  intro j
  rw [real_tangent_metric_coordinates]
  exact hV j

end Yau.Proofs.C04ChartsAux
