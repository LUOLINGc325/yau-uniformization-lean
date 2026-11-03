import Yau.Proofs.C02CurvatureGauge
import Yau.Proofs.C02NormalConnection
import Yau.Proofs.C02NormalDifferentialCoords
import Yau.Proofs.C02TensorSlotComposition

/-! The head and connection slots of actual covariant curvature jets,
proved separately so their dependent tensor ranks remain explicit. -/

noncomputable section
open scoped Manifold InnerProductSpace ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem normalCurvatureJet_succ_coords (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (c : M.Carrier) (j : ℕ) (x u : ComplexVector n) (V : Fin (4 + j) → ComplexVector n)
    (hx : normalRealMap g p U x ∈ (chartAt (ComplexVector n) c).source) :
    normalCurvatureJet g p U hU (j + 1) x (Fin.cons (normalDifferential g p U hU x u) V) =
      tensorEvalCLM (covariantD g.form c (rmJet g.form c j) (normalCoordinateMap g p U c x))
        (Fin.cons (fderiv ℝ (normalCoordinateMap g p U c) x u)
          (fun i => normalParallelCoefficients g p U hU c x (V i))) := by
  let Q := normalParallelCoefficients g p U hU c x
  let T : RealTensorForm n ((4 + j) + 1) := tensorEvalCLM
    (covariantD g.form c (rmJet g.form c j) (normalCoordinateMap g p U c x))
  have hc := congrArg (fun S : RealTensorForm n (4 + (j + 1)) =>
    S (Fin.cons (normalDifferential g p U hU x u) V))
    (normalCurvatureJet_eq_chart g p U hU c (j + 1) x hx)
  calc
    _ = (T.compContinuousLinearMap (fun _ => Q))
        (Fin.cons (normalDifferential g p U hU x u) V) := hc
    _ = T (Fin.cons (Q (normalDifferential g p U hU x u)) (fun i => Q (V i))) := tensor_comp_cons _ _ _ _
    _ = _ := congrArg (fun w : ComplexVector n => T (Fin.cons w (fun i => Q (V i))))
      (normalDifferential_coords g p U hU c x u hx)

theorem normalCurvatureJet_update_coords (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (c : M.Carrier) (j : ℕ) (x u : ComplexVector n) (V : Fin (4 + j) → ComplexVector n)
    (s : Fin (4 + j)) (hx : normalRealMap g p U x ∈ (chartAt (ComplexVector n) c).source) :
    normalCurvatureJet g p U hU j x (Function.update V s (normalConnection g p U hU x u (V s))) =
      tensorEvalCLM (rmJet g.form c j (normalCoordinateMap g p U c x))
        (Function.update (fun i => normalParallelCoefficients g p U hU c x (V i)) s
          (fderiv ℝ (normalParallelCoefficients g p U hU c) x u (V s) +
            chartChristoffelBilin g.form c (normalCoordinateMap g p U c x)
              (fderiv ℝ (normalCoordinateMap g p U c) x u)
              (normalParallelCoefficients g p U hU c x (V s)))) := by
  rw [normalCurvatureJet_eq_chart g p U hU c j x hx]
  change tensorEvalCLM (rmJet g.form c j (normalCoordinateMap g p U c x))
    (fun i => normalParallelCoefficients g p U hU c x
      (Function.update V s (normalConnection g p U hU x u (V s)) i)) = _
  rw [linearMap_map_update, normalConnection_eq_chart g p U hU c x hx,
    normalConnectionInChart_reconstruct g p U hU c x u (V s) hx]

end Yau.Blueprint.C02Proof
