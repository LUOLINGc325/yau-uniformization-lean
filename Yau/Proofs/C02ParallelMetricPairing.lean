import Yau.Proofs.C02NormalDifferentialCoords

noncomputable section
open scoped Manifold InnerProductSpace ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem normalParallelCoefficients_metric_pairing (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (c : M.Carrier) (x u v : ComplexVector n)
    (hx : normalRealMap g p U x ∈ (chartAt (ComplexVector n) c).source) :
    realMetricInChart g.form c (normalCoordinateMap g p U c x)
      (normalParallelCoefficients g p U hU c x u) (normalParallelCoefficients g p U hU c x v) =
        ⟪u, v⟫_ℝ := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  have ht := realMetricInChart_tangentCoords g.form c (normalRealMap g p U x) hx
    (normalParallelIsometry g p U hU x u) (normalParallelIsometry g p U hU x v)
  change realMetricInChart g.form c (normalCoordinateMap g p U c x)
      (normalParallelCoefficients g p U hU c x u) (normalParallelCoefficients g p U hU c x v) =
    ⟪normalParallelIsometry g p U hU x u, normalParallelIsometry g p U hU x v⟫_ℝ at ht
  exact ht.trans ((normalParallelIsometry g p U hU x).inner_map_map u v)

end Yau.Blueprint.C02Proof
