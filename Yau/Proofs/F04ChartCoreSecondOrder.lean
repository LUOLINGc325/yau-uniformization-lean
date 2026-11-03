import Yau.Proofs.F04ChartLaplacianIntegral
import Yau.Proofs.F04ChartCoefficients
import Yau.Proofs.F04ChartEnergyTest
import Yau.LeafProofs.L19HeatRegularityDensityTest

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace
noncomputable section
namespace Yau.F04Proof
open Yau.Parabolic Yau.Proofs.F03Aux Yau.LeafProofs.L19Aux Yau.LeafProofs.L18Aux
variable {n : ℕ} {M : ComplexManifold n}

/-- Testing the actual fixed-volume form by the density-corrected compact
 chart test gives exactly the actual nondivergence second-order operator.
 The fixed volume density cancels inside the proof. -/
theorem localCoreForm_chart_secondOrder
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (h : ℝ → HermitianField M) (t : ℝ) (hH : MetricSmooth (h t))
    (B : DirichletEnergy g μ hμ Ω →L[ℝ] DirichletEnergy g μ hμ Ω →L[ℝ] ℝ)
    (hB : ∀ f v : dirichletCore g μ hμ Ω,
      B (dirichletCoreToEnergy g μ hμ Ω f) (dirichletCoreToEnergy g μ hμ Ω v) =
        -(∫ y in Ω, v.val y * laplacian (h t) f.val y ∂μ))
    (c : M.Carrier) {O : Set (Space n)} (hO : IsOpen O) (hOt : O ⊆ chartTarget c)
    (hMap : chartInv c '' O ⊆ Ω) {I : Set ℝ}
    {φ : Point n → ℝ} (hφ : Test (O ×ˢ I) φ) (f : dirichletCore g μ hμ Ω) :
    B (dirichletCoreToEnergy g μ hμ Ω f)
      (dirichletCoreToEnergy g μ hμ Ω (chartSupportedTestCore g μ hμ Ω c hOt hMap
        (scalarChart_densityInverseTest g c hOt hφ) t)) =
      -(∫ z in O, φ (z, t) * ∑ i, ∑ j, flowChartPrincipal h c (z, t) i j *
        spatialDD (fun p : Point n => f.val (chartInv c p.1)) (z, t) (realVec i) (realVec j)) := by
  let θ : Point n → ℝ := fun p => φ p / Real.sqrt (realMetricFn g.form c p.1).det
  have hθ : Test (O ×ˢ I) θ := scalarChart_densityInverseTest g c hOt hφ
  let k := chartSupportedTestCore g μ hμ Ω c hOt hMap hθ t
  change B (dirichletCoreToEnergy g μ hμ Ω f) (dirichletCoreToEnergy g μ hμ Ω k) = _
  rw [hB]
  have hAll : (∫ y in Ω, k.val y * laplacian (h t) f.val y ∂μ) =
      ∫ y, k.val y * laplacian (h t) f.val y ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport (fun hh => hy (k.property hh)), zero_mul]
  rw [hAll]
  change -(∫ y, chartPushforwardZero c (fun z => θ (z, t)) y * laplacian (h t) f.val y ∂μ) = _
  have hSlice := scalarChartTest_slice hθ t
  rw [chartPushforward_laplacian_integral g μ hμ (h t) hH c hOt f.val.2.1
    hSlice.1 hSlice.2.1 hSlice.2.2]
  congr 1
  apply setIntegral_congr_fun hO.measurableSet
  intro z hz
  change Real.sqrt (realMetricFn g.form c z).det *
    (φ (z, t) / Real.sqrt (realMetricFn g.form c z).det) * laplacian (h t) f.val (chartInv c z) = _
  rw [flowChartPrincipal_operator h c f.val.2.1 z (hOt hz) t]
  field_simp [ne_of_gt (Yau.LeafProofs.L12Aux.volumeDensity_pos g.form c z (hOt hz))]

end Yau.F04Proof
