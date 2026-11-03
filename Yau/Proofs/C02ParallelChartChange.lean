import Yau.Proofs.C02NormalDifferentialSmooth

/-! Exact changes of target chart for the actual normal map and radial frame. -/

noncomputable section
open Set
open scoped Manifold InnerProductSpace ContDiff Topology
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem normalCoordinateMap_chartChange (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p) (a b : M.Carrier)
    (x : ComplexVector n) (ha : normalRealMap g p U x ∈ (chartAt (ComplexVector n) a).source) :
    realChartChange a b (normalCoordinateMap g p U a x) = normalCoordinateMap g p U b x := by
  change chartPt b (chartInv a (chartPt a (normalRealMap g p U x))) = _
  have hinv : chartInv a (chartPt a (normalRealMap g p U x)) = normalRealMap g p U x :=
    (extChartAt (ComplexModel n) a).left_inv (by simpa only [extChartAt_source] using ha)
  rw [hinv]
  rfl

theorem normalParallelCoefficients_chartChange (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (a b : M.Carrier) (x : ComplexVector n)
    (ha : normalRealMap g p U x ∈ (chartAt (ComplexVector n) a).source)
    (hb : normalRealMap g p U x ∈ (chartAt (ComplexVector n) b).source) :
    (fderiv ℝ (realChartChange a b) (normalCoordinateMap g p U a x)).comp
      (normalParallelCoefficients g p U hU a x) = normalParallelCoefficients g p U hU b x := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  have ha' : normalRealMap g p U x ∈ (extChartAt (ComplexModel n) a).source := by
    simpa only [extChartAt_source] using ha
  have hz : normalCoordinateMap g p U a x ∈ chartTarget a :=
    (extChartAt (ComplexModel n) a).map_source ha'
  have hinv : chartInv a (normalCoordinateMap g p U a x) = normalRealMap g p U x :=
    (extChartAt (ComplexModel n) a).left_inv ha'
  have hb' : chartInv a (normalCoordinateMap g p U a x) ∈
      (extChartAt (ComplexModel n) b).source := by
    rw [hinv]
    simpa only [extChartAt_source] using hb
  apply ContinuousLinearMap.ext
  intro z
  have hc := realChartChange_fderiv a b hz hb' (normalParallelCoefficients g p U hU a x z)
  rw [hinv, ← realFrameCLM_apply a _ ha] at hc
  change fderiv ℝ (realChartChange a b) (normalCoordinateMap g p U a x)
      (normalParallelCoefficients g p U hU a x z) =
    realTangentCoords b (normalRealMap g p U x) (normalParallelIsometry g p U hU x z)
  rw [hc]
  congr 1
  exact realFrameCLM_realTangentCoords a _ ha _

end Yau.Blueprint.C02Proof
