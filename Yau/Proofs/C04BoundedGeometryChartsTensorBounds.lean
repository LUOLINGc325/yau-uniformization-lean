import Yau.LeafProofs.L23JetNaturality

/-! Intrinsic covariant curvature bounds control actual frame evaluations. -/

noncomputable section
open scoped Matrix

namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n r : ℕ}

theorem tensorEvaluation_abs_le_of_norm_bound
    (G : Matrix (RIdx n) (RIdx n) ℝ) (hG : G.PosDef) (A : CovTensor n r)
    (V : Fin r → RIdx n → ℝ) {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hA : Real.sqrt (covTensorNormSq G A) ≤ K)
    (hV : ∀ j, V j ⬝ᵥ (G *ᵥ V j) ≤ B ^ 2) :
    |tensorEvaluation A V| ≤ K * B ^ r := by
  have hnorm := covTensorNormSq_nonneg G hG A
  have hsq : covTensorNormSq G A ≤ K ^ 2 := by
    nlinarith [Real.sq_sqrt hnorm, Real.sqrt_nonneg (covTensorNormSq G A)]
  have hV0 (j : Fin r) : 0 ≤ V j ⬝ᵥ (G *ᵥ V j) := by
    simpa only [star_trivial] using hG.posSemidef.dotProduct_mulVec_nonneg (V j)
  have hp : (∏ j : Fin r, V j ⬝ᵥ (G *ᵥ V j)) ≤ (B ^ 2) ^ r := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      Finset.prod_le_prod₀ (s := Finset.univ) (fun j _ => hV0 j) (fun j _ => hV j)
  have heval := tensorEvaluation_sq_le G hG A V
  have hprod0 : 0 ≤ ∏ j : Fin r, V j ⬝ᵥ (G *ᵥ V j) :=
    Finset.prod_nonneg fun j _ => hV0 j
  have hh : tensorEvaluation A V ^ 2 ≤ (K * B ^ r) ^ 2 := by
    calc
      _ ≤ covTensorNormSq G A * ∏ j : Fin r, V j ⬝ᵥ (G *ᵥ V j) := heval
      _ ≤ K ^ 2 * (B ^ 2) ^ r := mul_le_mul hsq hp hprod0 (sq_nonneg K)
      _ = _ := by rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm r 2]
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hK (pow_nonneg hB r))).mp
    (by simpa only [sq_abs] using hh)

theorem curvature_jet_frame_evaluation_le {M : ComplexManifold n}
    (k : HermitianField M) (p : M.Carrier) (m : ℕ)
    (V : Fin (4 + m) → RIdx n → ℝ) {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hcurv : curvatureJetNorm k m p ≤ K)
    (hV : ∀ j, V j ⬝ᵥ (realMetricFn k p (chartPt p p) *ᵥ V j) ≤ B ^ 2) :
    |tensorEvaluation (rmJet k p m (chartPt p p)) V| ≤ K * B ^ (4 + m) := by
  exact tensorEvaluation_abs_le_of_norm_bound _
    (realMetricFn_posDef k p (chartPt p p) (mem_extChartAt_target p)) _ _ hK hB hcurv hV

end Yau.Proofs.C04ChartsAux
