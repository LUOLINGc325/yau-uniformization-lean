import Yau.Proofs.F04ChartPushSupport

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint Yau.Parabolic Yau.Proofs.F03Aux Yau.HeatConcreteBindings Yau.LeafProofs.L18Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem chartPushforwardZero_scalarTest (c : M.Carrier)
    {O : Set (Space n)} (hOt : O ⊆ chartTarget c) {Ω : Set M.Carrier}
    (hMap : chartInv c '' O ⊆ Ω) {I : Set ℝ}
    {φ : Point n → ℝ} (hφ : Test (O ×ˢ I) φ) (t : ℝ) :
    ScalarTest Ω (chartPushforwardZero c (fun z => φ (z, t))) := by
  have hs := chartPushforwardZero_smoothSpaceTime c hOt hφ
  obtain ⟨K, hK, hKΩ, hSupp⟩ := chartPushforwardZero_spacetime_support c hOt hMap hφ
  refine ⟨?_, hK.of_isClosed_subset (isClosed_tsupport _) (hSupp t), (hSupp t).trans hKΩ⟩
  intro b
  exact (hs b).comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hz => ⟨hz, mem_univ t⟩)

def chartSupportedTestCore (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (Ω : Set M.Carrier) (c : M.Carrier)
    {O : Set (Space n)} (hOt : O ⊆ chartTarget c) (hMap : chartInv c '' O ⊆ Ω) {I : Set ℝ}
    {φ : Point n → ℝ} (hφ : Test (O ×ˢ I) φ) (t : ℝ) : dirichletCore g μ hμ Ω :=
  ⟨⟨chartPushforwardZero c (fun z => φ (z, t)),
    (chartPushforwardZero_scalarTest c hOt hMap hφ t).1,
    (chartPushforwardZero_scalarTest c hOt hMap hφ t).2.1⟩,
    (chartPushforwardZero_scalarTest c hOt hMap hφ t).2.2⟩

theorem chartSupportedTestCore_zero (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (Ω : Set M.Carrier) (c : M.Carrier)
    {O : Set (Space n)} (hOt : O ⊆ chartTarget c) (hMap : chartInv c '' O ⊆ Ω) {I : Set ℝ}
    {φ : Point n → ℝ} (hφ : Test (O ×ˢ I) φ) (t : ℝ) (hzero : ∀ z, φ (z, t) = 0) :
    dirichletCoreToEnergy g μ hμ Ω (chartSupportedTestCore g μ hμ Ω c hOt hMap hφ t) = 0 := by
  have hc : chartSupportedTestCore g μ hμ Ω c hOt hMap hφ t = 0 := by
    apply Subtype.ext
    apply Subtype.ext
    funext y
    change chartPushforwardZero c (fun z => φ (z, t)) y = 0
    by_cases hy : y ∈ (extChartAt (ComplexModel n) c).source
    · simp only [chartPushforwardZero, ite_eq_left hy, hzero]
    · simp only [chartPushforwardZero, ite_eq_right hy]
  rw [hc]
  apply Subtype.ext
  exact UniformSpace.Completion.coe_zero

end Yau.F04Proof
