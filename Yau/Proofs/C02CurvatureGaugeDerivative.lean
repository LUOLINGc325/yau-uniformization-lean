import Yau.Proofs.C02CurvatureGauge
import Yau.Proofs.C02NormalConnection
import Yau.Proofs.C02NormalDifferentialCoords
import Yau.Proofs.C02TensorGaugeDerivative
import Yau.Proofs.C02CurvatureGaugeSlotIdentities

/-! The actual transported curvature jets satisfy the triangular covariant
derivative identity. Each slot term has the genuine frame connection A. -/

noncomputable section
open Set Filter
open scoped Manifold InnerProductSpace ContDiff Topology
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem normalCurvatureJet_fderiv (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (j : ℕ) (x u : ComplexVector n) (V : Fin (4 + j) → ComplexVector n) :
    fderiv ℝ (normalCurvatureJet g p U hU j) x u V =
      normalCurvatureJet g p U hU (j + 1) x (Fin.cons (normalDifferential g p U hU x u) V) +
        ∑ s : Fin (4 + j), normalCurvatureJet g p U hU j x
          (Function.update V s (normalConnection g p U hU x u (V s))) := by
  letI := manifold_realSmooth M
  let c := normalRealMap g p U x
  let φ := normalCoordinateMap g p U c
  let Q := normalParallelCoefficients g p U hU c
  have hx : normalRealMap g p U x ∈ (chartAt (ComplexVector n) c).source := mem_chart_source _ _
  have hO := (normalRealMap_smooth g p U hU).continuous.continuousAt.preimage_mem_nhds
    ((chartAt (ComplexVector n) c).open_source.mem_nhds hx)
  have hφ : DifferentiableAt ℝ φ x :=
    ((normalCoordinateMap_smooth g p U hU c).contDiffAt hO).differentiableAt (by simp)
  have hQ : DifferentiableAt ℝ Q x :=
    ((normalParallelCoefficients_smooth g p U hU c).contDiffAt hO).differentiableAt (by simp)
  have hz : φ x ∈ chartTarget c := mem_extChartAt_target c
  have hR : ∀ v, DifferentiableAt ℝ (fun y => rmJet g.form c j y v) (φ x) := by
    intro v
    exact ((rmJet_contDiffOn g.form (metricSmooth_of_smoothMetric g) c j v).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have heq : normalCurvatureJet g p U hU j =ᶠ[𝓝 x] normalCurvatureJetInChart g p U hU c j := by
    filter_upwards [hO] with y hy
    exact normalCurvatureJet_eq_chart g p U hU c j y hy
  rw [heq.fderiv_eq]
  change fderiv ℝ (fun y => (tensorEvalCLM (rmJet g.form c j (φ y))).compContinuousLinearMap
    (fun _ : Fin (4 + j) => Q y)) x u V = _
  rw [tensorGauge_fderiv g.form c (rmJet g.form c j) φ Q x u V hR hφ hQ]
  apply congrArg₂ (fun a b : ℝ => a + b)
  · exact (normalCurvatureJet_succ_coords g p U hU c j x u V hx).symm
  · apply Finset.sum_congr rfl
    intro s hs
    exact (normalCurvatureJet_update_coords g p U hU c j x u V s hx).symm

end Yau.Blueprint.C02Proof
