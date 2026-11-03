import Yau.Proofs.F04ChartCoreSecondOrder
import Yau.Proofs.F04ChartMatrixIntegration
import Yau.Proofs.F04DirichletCore

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace
noncomputable section
namespace Yau.F04Proof
open Yau.Parabolic Yau.Proofs.F03Aux Yau.LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}

/-- Spatial smoothness of the actual inverse evolving Hermitian metric
 uses its actual smooth coefficient field; completeness is not an inlet. -/
theorem flowChartPrincipal_slice_smooth
    (h : ℝ → HermitianField M) (c : M.Carrier) (t : ℝ) (hH : MetricSmooth (h t)) (i j : RIdx n) :
    ContDiffOn ℝ ∞ (fun z => flowChartPrincipal h c (z, t) i j) (chartTarget c) :=
  contDiffOn_const.mul (Adjoint.realMetricFn_inverse_contDiffOn (h t) hH c i j)

/-- The actual nonsymmetric fixed-volume form, against a density-corrected
 compact chart test, has the literal flux-plus-coefficient-drift formula
 on EVERY supported energy vector. The extension is proved using the
 genuine compact core density and bounded chart differential maps. -/
theorem localCoreForm_chart_gradient_integral
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (h : ℝ → HermitianField M) (t : ℝ) (hH : MetricSmooth (h t))
    (B : DirichletEnergy g μ hμ Ω →L[ℝ] DirichletEnergy g μ hμ Ω →L[ℝ] ℝ)
    (hB : ∀ f v : dirichletCore g μ hμ Ω,
      B (dirichletCoreToEnergy g μ hμ Ω f) (dirichletCoreToEnergy g μ hμ Ω v) =
        -(∫ y in Ω, v.val y * laplacian (h t) f.val y ∂μ))
    (c : M.Carrier) {O : Set (Space n)} (hO : IsOpen O) (hOC : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget c) (hMap : chartInv c '' O ⊆ Ω) {I : Set ℝ}
    {φ : Point n → ℝ} (hφ : Test (O ×ˢ I) φ) (v : DirichletEnergy g μ hμ Ω) :
    B v (dirichletCoreToEnergy g μ hμ Ω (chartSupportedTestCore g μ hμ Ω c
      (subset_closure.trans hOt) hMap (scalarChart_densityInverseTest g c (subset_closure.trans hOt) hφ) t)) =
      ∫ z in O, ∑ i, ∑ j, scalarEnergy_chartDerivativeCLM g μ hμ c hO hOC hOt j v.val z *
        chartWeakTestEntry (fun w => flowChartPrincipal h c (w, t)) (fun w => φ (w, t)) i j z := by
  let a := fun z => flowChartPrincipal h c (z, t)
  let η := fun z => φ (z, t)
  have ha : ∀ i j, ContDiffOn ℝ 1 (fun z => a z i j) O := fun i j =>
    ((flowChartPrincipal_slice_smooth h c t hH i j).mono (subset_closure.trans hOt)).of_le (by simp)
  have hηS := scalarChartTest_slice hφ t
  have hη : ContDiff ℝ 1 η := hηS.1.of_le (by simp)
  let Q := fun i j => chartWeakTestEntryLp hO ha hη hηS.2.1 hηS.2.2 i j
  let D := fun j => scalarEnergy_chartDerivativeCLM g μ hμ c hO hOC hOt j
  let k := chartSupportedTestCore g μ hμ Ω c (subset_closure.trans hOt) hMap
    (scalarChart_densityInverseTest g c (subset_closure.trans hOt) hφ) t
  let K := dirichletCoreToEnergy g μ hμ Ω k
  have hInt (w : DirichletEnergy g μ hμ Ω) :
      (∑ i, ∑ j, inner ℝ (D j w.val) (Q i j)) =
        ∫ z in O, ∑ i, ∑ j, D j w.val z * chartWeakTestEntry a η i j z :=
    scalarEnergy_chartWeakTest_integral g μ hμ c hO hOC hOt ha w.val hη hηS.2.1 hηS.2.2
  have hCore (f : dirichletCore g μ hμ Ω) :
      B (dirichletCoreToEnergy g μ hμ Ω f) K =
        ∑ i, ∑ j, inner ℝ (D j (dirichletCoreToEnergy g μ hμ Ω f).val) (Q i j) := by
    rw [hInt]
    have hStart := localCoreForm_chart_secondOrder g μ hμ Ω h t hH B hB c hO
      (subset_closure.trans hOt) hMap hφ f
    change B (dirichletCoreToEnergy g μ hμ Ω f) K =
      -(∫ z in O, η z * ∑ i, ∑ j, a z i j *
        spatialDD (fun p : Point n => f.val (chartInv c p.1)) (z, t) (realVec i) (realVec j)) at hStart
    rw [hStart]
    have hf : ContDiffOn ℝ 2 (inChart c f.val) O :=
      ((f.val.2.1 c).mono (subset_closure.trans hOt)).of_le (by simp)
    have hIP := integral_chart_matrix_hessian hO ha hη hηS.2.1 hηS.2.2 hf
    change (∫ z in O, η z * ∑ i, ∑ j, a z i j *
      spatialDD (fun p : Point n => f.val (chartInv c p.1)) (z, t) (realVec i) (realVec j)) = _ at hIP
    rw [hIP, neg_neg]
    apply integral_congr_ae
    have hd : ∀ᵐ z ∂volume.restrict O, ∀ j : RIdx n,
        D j (dirichletCoreToEnergy g μ hμ Ω f).val z = rDeriv (inChart c f.val) z j :=
      ae_all_iff.mpr (fun j => scalarEnergy_chartDerivativeCLM_coe g μ hμ c hO hOC hOt j f.val)
    filter_upwards [hd] with z hz
    simp_rw [hz]
  have hLC : Continuous (fun w : DirichletEnergy g μ hμ Ω => B w K) :=
    B.continuous.clm_apply continuous_const
  have hRC : Continuous (fun w : DirichletEnergy g μ hμ Ω =>
      ∑ i, ∑ j, inner ℝ (D j w.val) (Q i j)) :=
    continuous_finsetSum Finset.univ (fun i _ => continuous_finsetSum Finset.univ (fun j _ =>
      ((D j).continuous.comp (dirichletEnergySubmodule g μ hμ Ω).subtypeL.continuous).inner continuous_const))
  have hclosed : IsClosed {w : DirichletEnergy g μ hμ Ω |
      B w K = ∑ i, ∑ j, inner ℝ (D j w.val) (Q i j)} := isClosed_eq hLC hRC
  have hcore : Set.range (dirichletCoreEmbedding g μ hμ Ω) ⊆
      {w : DirichletEnergy g μ hμ Ω | B w K = ∑ i, ∑ j, inner ℝ (D j w.val) (Q i j)} := by
    rintro _ ⟨f, rfl⟩
    exact hCore f
  have hAll := (closure_minimal hcore hclosed) (dirichletCoreEmbedding_denseRange g μ hμ Ω v)
  exact hAll.trans (hInt v)

end Yau.F04Proof
