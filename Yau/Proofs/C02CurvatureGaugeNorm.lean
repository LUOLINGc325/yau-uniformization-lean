import Yau.Proofs.C02CurvatureGauge
import Yau.Proofs.C02ParallelMetricQuadratic

/-! The norm of an actual covariant curvature jet in the genuine parallel
frame is bounded by the original metric contraction norm, with constant one. -/

noncomputable section
open scoped Manifold InnerProductSpace ContDiff Matrix
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem normalCurvatureJet_norm_le (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (j : ℕ) (x : ComplexVector n) :
    ‖normalCurvatureJet g p U hU j x‖ ≤ curvatureJetNorm g.form j (normalRealMap g p U x) := by
  let c := normalRealMap g p U x
  let G := realMetricFn g.form c (chartPt c c)
  let A := rmJet g.form c j (chartPt c c)
  let Q := normalParallelCoefficients g p U hU c x
  let K := curvatureJetNorm g.form j c
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  have hKsq : K ^ 2 = covTensorNormSq G A := curvatureJetNorm_sq g.form j c
  apply ContinuousMultilinearMap.opNorm_le_bound hK
  intro V
  have he := tensorEvaluation_sq_le G
    (realMetricFn_posDef g.form c _ (mem_extChartAt_target c)) A (fun i => realCoord (Q (V i)))
  have hEval : tensorEvaluation A (fun i => realCoord (Q (V i))) =
      normalCurvatureJet g p U hU j x V := by
    change tensorEvaluation A (fun i => realCoord (Q (V i))) = tensorEvalCLM A (fun i => Q (V i))
    rw [tensorEvalCLM_apply]
    rfl
  have hProd : (∏ i : Fin (4 + j), realCoord (Q (V i)) ⬝ᵥ (G *ᵥ realCoord (Q (V i)))) =
      (∏ i : Fin (4 + j), ‖V i‖) ^ 2 := by
    calc
      _ = ∏ i : Fin (4 + j), ‖V i‖ ^ 2 := by
        apply Finset.prod_congr rfl
        intro i hi
        exact normalParallelCoefficients_metric_quadratic g p U hU c x (V i) (mem_chart_source _ _)
      _ = _ := by rw [Finset.prod_pow]
  rw [hEval, hProd, ← hKsq] at he
  have hBound : 0 ≤ K * ∏ i : Fin (4 + j), ‖V i‖ :=
    mul_nonneg hK (Finset.prod_nonneg (fun i hi => norm_nonneg (V i)))
  apply (sq_le_sq₀ (norm_nonneg _) hBound).mp
  simpa only [Real.norm_eq_abs, sq_abs, mul_pow] using he

end Yau.Blueprint.C02Proof
