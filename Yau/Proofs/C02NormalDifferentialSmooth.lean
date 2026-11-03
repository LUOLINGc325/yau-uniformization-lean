import Yau.Proofs.C02ParallelCoefficientInverse
import Yau.Proofs.C02NormalDifferential
import Yau.LeafProofs.L12JacobiMatrix

/-! Smoothness of the genuine normal differential in the parallel gauge.
The coordinate formula uses the inverse parallel frame, independently of
whether the normal parametrization is an immersion. -/

noncomputable section
open Set
open scoped Manifold InnerProductSpace ContDiff Topology
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

def normalCoordinateMap (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p) (c : M.Carrier)
    (x : ComplexVector n) : ComplexVector n := chartPt c (normalRealMap g p U x)

theorem normalCoordinateMap_smooth (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (c : M.Carrier) :
    ContDiffOn ℝ ∞ (normalCoordinateMap g p U c)
      ((normalRealMap g p U) ⁻¹' (chartAt (ComplexVector n) c).source) := by
  letI := manifold_realSmooth M
  intro x hx
  have hc : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) ∞
      (chartPt c) (normalRealMap g p U x) := contMDiffAt_extChartAt' hx
  exact ((hc.comp x (normalRealMap_smooth g p U hU).contMDiffAt).contDiffAt).contDiffWithinAt

theorem normalDifferential_eq_coordinates (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (c : M.Carrier) (x : ComplexVector n)
    (hx : normalRealMap g p U x ∈ (chartAt (ComplexVector n) c).source) :
    normalDifferential g p U hU x =
      (normalParallelCoefficientInverse g p U hU c x).comp
        (fderiv ℝ (normalCoordinateMap g p U c) x) := by
  letI := manifold_realSmooth M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  apply ContinuousLinearMap.ext
  intro z
  have hc := realTangentCoords_mfderiv (normalRealMap g p U) x c hx z
    ((normalRealMap_smooth g p U hU).mdifferentiable (by simp) x)
  change realTangentCoords c (normalRealMap g p U x) (rawNormalDifferential g p U x z) =
    fderiv ℝ (normalCoordinateMap g p U c) x z at hc
  change (normalParallelIsometry g p U hU x).symm (rawNormalDifferential g p U x z) =
    (normalParallelIsometry g p U hU x).symm
      (realFrameCLM c (normalRealMap g p U x) (fderiv ℝ (normalCoordinateMap g p U c) x z))
  apply congrArg (normalParallelIsometry g p U hU x).symm
  change rawNormalDifferential g p U x z = _
  rw [← hc]
  exact (realFrameCLM_realTangentCoords c _ hx _).symm

theorem normalDifferential_smooth (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) :
    ContDiff ℝ ∞ (normalDifferential g p U hU) := by
  letI := manifold_realSmooth M
  rw [contDiff_iff_contDiffAt]
  intro x
  let c := normalRealMap g p U x
  let O := (normalRealMap g p U) ⁻¹' (chartAt (ComplexVector n) c).source
  have hO : IsOpen O :=
    (chartAt (ComplexVector n) c).open_source.preimage (normalRealMap_smooth g p U hU).continuous
  have hx : x ∈ O := mem_chart_source _ _
  have hDy : ContDiffOn ℝ ∞ (fderiv ℝ (normalCoordinateMap g p U c)) O :=
    (normalCoordinateMap_smooth g p U hU c).fderiv_of_isOpen hO (by simp)
  have hComp := (normalParallelCoefficientInverse_smooth g p U hU c).clm_comp hDy
  have hB : ContDiffOn ℝ ∞ (normalDifferential g p U hU) O :=
    (contDiffOn_congr (fun y hy => normalDifferential_eq_coordinates g p U hU c y hy)).mpr hComp
  exact hB.contDiffAt (hO.mem_nhds hx)

end Yau.Blueprint.C02Proof
