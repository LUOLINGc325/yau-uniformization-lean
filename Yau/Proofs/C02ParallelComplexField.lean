import Yau.Proofs.C02ParallelChartChange
import Yau.Proofs.C02ComplexChartTransition

/-! The actual target complex structure transported into the radial
parallel frame. Chart independence precedes its smoothness and parallelity. -/

noncomputable section
open Set Filter
open scoped Manifold InnerProductSpace ContDiff Topology
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

def normalParallelComplexInChart (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (c : M.Carrier) (x : ComplexVector n) : ComplexVector n →L[ℝ] ComplexVector n :=
  (normalParallelCoefficientInverse g p U hU c x).comp
    ((complexStructureCLM n).comp (normalParallelCoefficients g p U hU c x))

theorem normalParallelComplex_reconstruct (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (c : M.Carrier) (x z : ComplexVector n)
    (hx : normalRealMap g p U x ∈ (chartAt (ComplexVector n) c).source) :
    normalParallelCoefficients g p U hU c x (normalParallelComplexInChart g p U hU c x z) =
      Complex.I • normalParallelCoefficients g p U hU c x z := by
  have h := congrArg (fun L : ComplexVector n →L[ℝ] ComplexVector n =>
    L (Complex.I • normalParallelCoefficients g p U hU c x z))
    (normalParallelCoefficient_inverse_identities g p U hU c x hx).1
  exact h

theorem normalParallelComplexInChart_chartChange (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (a b : M.Carrier) (x : ComplexVector n)
    (ha : normalRealMap g p U x ∈ (chartAt (ComplexVector n) a).source)
    (hb : normalRealMap g p U x ∈ (chartAt (ComplexVector n) b).source) :
    normalParallelComplexInChart g p U hU a x = normalParallelComplexInChart g p U hU b x := by
  have ha' : normalRealMap g p U x ∈ (extChartAt (ComplexModel n) a).source := by
    simpa only [extChartAt_source] using ha
  have hz : normalCoordinateMap g p U a x ∈ chartTarget a := (extChartAt (ComplexModel n) a).map_source ha'
  have hInv : chartInv a (normalCoordinateMap g p U a x) = normalRealMap g p U x :=
    (extChartAt (ComplexModel n) a).left_inv ha'
  have hb' : chartInv a (normalCoordinateMap g p U a x) ∈ (extChartAt (ComplexModel n) b).source := by
    rw [hInv]
    simpa only [extChartAt_source] using hb
  have hQ0 (z : ComplexVector n) := congrArg (fun L : ComplexVector n →L[ℝ] ComplexVector n => L z)
    (normalParallelCoefficients_chartChange g p U hU a b x ha hb)
  have hQ (z : ComplexVector n) :
      fderiv ℝ (realChartChange a b) (normalCoordinateMap g p U a x)
        (normalParallelCoefficients g p U hU a x z) = normalParallelCoefficients g p U hU b x z := by
    simpa only [ContinuousLinearMap.comp_apply] using hQ0 z
  apply ContinuousLinearMap.ext
  intro z
  apply (normalParallelCoefficients_isInvertible g p U hU b x hb).bijective.injective
  calc
    _ = fderiv ℝ (realChartChange a b) (normalCoordinateMap g p U a x)
        (normalParallelCoefficients g p U hU a x (normalParallelComplexInChart g p U hU a x z)) := (hQ _).symm
    _ = fderiv ℝ (realChartChange a b) (normalCoordinateMap g p U a x)
        (Complex.I • normalParallelCoefficients g p U hU a x z) := by rw [normalParallelComplex_reconstruct g p U hU a x z ha]
    _ = Complex.I • normalParallelCoefficients g p U hU b x z := by
      rw [realChartChange_fderiv_I a b hz hb', hQ z]
    _ = _ := (normalParallelComplex_reconstruct g p U hU b x z hb).symm

theorem normalParallelComplexInChart_smooth (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (c : M.Carrier) :
    ContDiffOn ℝ ∞ (normalParallelComplexInChart g p U hU c)
      ((normalRealMap g p U) ⁻¹' (chartAt (ComplexVector n) c).source) :=
  (normalParallelCoefficientInverse_smooth g p U hU c).clm_comp
    (contDiffOn_const.clm_comp (normalParallelCoefficients_smooth g p U hU c))

def normalParallelComplex (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (x : ComplexVector n) : ComplexVector n →L[ℝ] ComplexVector n :=
  normalParallelComplexInChart g p U hU (normalRealMap g p U x) x

theorem normalParallelComplex_eq_chart (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (c : M.Carrier) (x : ComplexVector n)
    (hx : normalRealMap g p U x ∈ (chartAt (ComplexVector n) c).source) :
    normalParallelComplex g p U hU x = normalParallelComplexInChart g p U hU c x :=
  normalParallelComplexInChart_chartChange g p U hU (normalRealMap g p U x) c x (mem_chart_source _ _) hx

theorem normalParallelComplex_smooth (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) :
    ContDiff ℝ ∞ (normalParallelComplex g p U hU) := by
  letI := manifold_realSmooth M
  rw [contDiff_iff_contDiffAt]
  intro x
  let c := normalRealMap g p U x
  have hO := (normalRealMap_smooth g p U hU).continuous.continuousAt.preimage_mem_nhds
    ((chartAt (ComplexVector n) c).open_source.mem_nhds (mem_chart_source _ _))
  have heq : normalParallelComplex g p U hU =ᶠ[𝓝 x] normalParallelComplexInChart g p U hU c := by
    filter_upwards [hO] with y hy
    exact normalParallelComplex_eq_chart g p U hU c y hy
  exact ((normalParallelComplexInChart_smooth g p U hU c).contDiffAt hO).congr_of_eventuallyEq heq

end Yau.Blueprint.C02Proof
