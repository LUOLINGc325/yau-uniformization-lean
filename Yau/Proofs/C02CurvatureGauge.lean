import Yau.Proofs.C02ParallelChartChange
import Yau.LeafProofs.L23JetNaturality
import Yau.Proofs.C02TensorCompositionSmooth

/-! Actual iterated covariant curvature tensors in the genuine radial
parallel frame, with chart independence before any differential estimate. -/

noncomputable section
open Set Filter
open scoped Manifold InnerProductSpace ContDiff Topology
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}

def normalCurvatureJetInChart (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (c : M.Carrier) (j : ℕ) (x : ComplexVector n) : RealTensorForm n (4 + j) :=
  (tensorEvalCLM (rmJet g.form c j (normalCoordinateMap g p U c x))).compContinuousLinearMap
    (fun _ : Fin (4 + j) => normalParallelCoefficients g p U hU c x)

theorem normalCurvatureJetInChart_smooth (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (c : M.Carrier) (j : ℕ) :
    ContDiffOn ℝ ∞ (normalCurvatureJetInChart g p U hU c j)
      ((normalRealMap g p U) ⁻¹' (chartAt (ComplexVector n) c).source) := by
  let O := (normalRealMap g p U) ⁻¹' (chartAt (ComplexVector n) c).source
  have hy := normalCoordinateMap_smooth g p U hU c
  have hQ := normalParallelCoefficients_smooth g p U hU c
  apply contDiffOn_tensor_composition (Q := normalParallelCoefficients g p U hU c) ?_ hQ
  intro v
  apply (rmJet_contDiffOn g.form (metricSmooth_of_smoothMetric g) c j v).comp hy
  intro x hx
  have hx' : normalRealMap g p U x ∈ (chartAt (ComplexVector n) c).source := hx
  exact (extChartAt (ComplexModel n) c).map_source
    (by simpa only [extChartAt_source] using hx')

theorem normalCurvatureJetInChart_chartChange (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (a b : M.Carrier) (j : ℕ) (x : ComplexVector n)
    (ha : normalRealMap g p U x ∈ (chartAt (ComplexVector n) a).source)
    (hb : normalRealMap g p U x ∈ (chartAt (ComplexVector n) b).source) :
    normalCurvatureJetInChart g p U hU a j x = normalCurvatureJetInChart g p U hU b j x := by
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
  have hJet := rmJet_eval_chart_change g.form (metricSmooth_of_smoothMetric g) j a b hz hb'
  rw [normalCoordinateMap_chartChange g p U a b x ha] at hJet
  have hQ := normalParallelCoefficients_chartChange g p U hU a b x ha hb
  apply ContinuousMultilinearMap.ext
  intro V
  have he := congrArg (fun T : RealTensorForm n (4 + j) =>
    T (fun i => normalParallelCoefficients g p U hU a x (V i))) hJet
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply] at he
  change tensorEvalCLM (rmJet g.form a j (normalCoordinateMap g p U a x))
    (fun i => normalParallelCoefficients g p U hU a x (V i)) =
      tensorEvalCLM (rmJet g.form b j (normalCoordinateMap g p U b x))
        (fun i => normalParallelCoefficients g p U hU b x (V i))
  convert he using 1
  congr 1
  funext i
  exact (congrArg (fun L : ComplexVector n →L[ℝ] ComplexVector n => L (V i)) hQ).symm

def normalCurvatureJet (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (j : ℕ) (x : ComplexVector n) : RealTensorForm n (4 + j) :=
  normalCurvatureJetInChart g p U hU (normalRealMap g p U x) j x

theorem normalCurvatureJet_eq_chart (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (c : M.Carrier) (j : ℕ) (x : ComplexVector n)
    (hx : normalRealMap g p U x ∈ (chartAt (ComplexVector n) c).source) :
    normalCurvatureJet g p U hU j x = normalCurvatureJetInChart g p U hU c j x :=
  normalCurvatureJetInChart_chartChange g p U hU (normalRealMap g p U x) c j x
    (mem_chart_source _ _) hx

theorem normalCurvatureJet_smooth (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (j : ℕ) :
    ContDiff ℝ ∞ (normalCurvatureJet g p U hU j) := by
  letI := manifold_realSmooth M
  rw [contDiff_iff_contDiffAt]
  intro x
  let c := normalRealMap g p U x
  have hO := (normalRealMap_smooth g p U hU).continuous.continuousAt.preimage_mem_nhds
    ((chartAt (ComplexVector n) c).open_source.mem_nhds (mem_chart_source _ _))
  have heq : normalCurvatureJet g p U hU j =ᶠ[𝓝 x] normalCurvatureJetInChart g p U hU c j := by
    filter_upwards [hO] with y hy
    exact normalCurvatureJet_eq_chart g p U hU c j y hy
  exact ((normalCurvatureJetInChart_smooth g p U hU c j).contDiffAt hO).congr_of_eventuallyEq heq

end Yau.Blueprint.C02Proof
