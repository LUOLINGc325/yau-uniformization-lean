import Yau.Proofs.C02ParallelCoefficients

/-! The actual coordinate metric evaluated on parallel-frame coefficients
is exactly the fixed Euclidean norm, with the physical factor 2 already
included in the genuine tangent inner product. -/

noncomputable section
open scoped Manifold InnerProductSpace ContDiff Matrix
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem realMetricInChart_quadratic (h : HermitianField M) (c : M.Carrier)
    (y : ComplexVector n) (hy : y ∈ chartTarget c) (v : ComplexVector n) :
    realMetricInChart h c y v v = realCoord v ⬝ᵥ (realMetricFn h c y *ᵥ realCoord v) := by
  rw [realBilin_eq_sum]
  simp_rw [realMetricInChart_basis h c y hy]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem normalParallelCoefficients_metric_quadratic (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (c : M.Carrier) (x u : ComplexVector n)
    (hx : normalRealMap g p U x ∈ (chartAt (ComplexVector n) c).source) :
    realCoord (normalParallelCoefficients g p U hU c x u) ⬝ᵥ
      (realMetricFn g.form c (chartPt c (normalRealMap g p U x)) *ᵥ
        realCoord (normalParallelCoefficients g p U hU c x u)) = ‖u‖ ^ 2 := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  have hy : chartPt c (normalRealMap g p U x) ∈ chartTarget c :=
    (extChartAt (ComplexModel n) c).map_source (by simpa only [extChartAt_source] using hx)
  rw [← realMetricInChart_quadratic g.form c _ hy]
  have ht := realMetricInChart_tangentCoords g.form c (normalRealMap g p U x) hx
    (normalParallelIsometry g p U hU x u) (normalParallelIsometry g p U hU x u)
  change realMetricInChart g.form c (chartPt c (normalRealMap g p U x))
      (normalParallelCoefficients g p U hU c x u) (normalParallelCoefficients g p U hU c x u) =
    ⟪normalParallelIsometry g p U hU x u, normalParallelIsometry g p U hU x u⟫_ℝ at ht
  rw [ht, (normalParallelIsometry g p U hU x).inner_map_map, real_inner_self_eq_norm_sq]

end Yau.Blueprint.C02Proof
