import Yau.Proofs.F04ChartEnergyTime

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint Yau.Parabolic Yau.Proofs.F03Aux Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

local instance (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (Ω : Set M.Carrier) :
    CompleteSpace (DirichletEnergy g μ hμ Ω) := dirichletEnergy_completeSpace g μ hμ Ω

theorem chartSupportedTestCore_zero_germ
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (c : M.Carrier) {O : Set (Space n)} (hOt : O ⊆ chartTarget c)
    (hMap : chartInv c '' O ⊆ Ω) {S : ℝ} {φ : Point n → ℝ}
    (hφ : Test (O ×ˢ Ioo 0 S) φ) (t : ℝ) (ht : t ∉ Ioo 0 S) :
    (fun s => dirichletCoreToEnergy g μ hμ Ω (chartSupportedTestCore g μ hμ Ω c hOt hMap hφ s)) =ᶠ[𝓝 t]
      (fun _ => 0) := by
  let A := Prod.snd '' tsupport φ
  have hA : IsCompact A := hφ.2.1.image continuous_snd
  have htA : t ∉ A := by
    rintro ⟨p, hp, rfl⟩
    exact ht (hφ.2.2 hp).2
  filter_upwards [hA.isClosed.isOpen_compl.mem_nhds htA] with s hs
  apply chartSupportedTestCore_zero g μ hμ Ω c hOt hMap hφ s
  intro z
  exact image_eq_zero_of_notMem_tsupport (fun hp => hs ⟨(z, s), hp, rfl⟩)

/-- The actual supported chart test is a genuine global C1 energy-valued
 test with its actual time-derivative core. Compact time support handles
 both endpoints before the moving-test theorem is applied. -/
theorem chartSupportedTestCore_contDiff_one
    (g : SmoothMetric M) (hg : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (Ω K : Set M.Carrier)
    (hΩ : MeasurableSet Ω) (hK : IsCompact K) (hΩK : Ω ⊆ K)
    (c : M.Carrier) {O : Set (Space n)} (hOt : O ⊆ chartTarget c)
    (hMap : chartInv c '' O ⊆ Ω) {S : ℝ} (hS : 0 < S)
    {φ : Point n → ℝ} (hφ : Test (O ×ˢ Ioo 0 S) φ) :
    ContDiff ℝ 1 (fun t => dirichletCoreToEnergy g μ hμ Ω
      (chartSupportedTestCore g μ hμ Ω c hOt hMap hφ t)) ∧
      ∀ t : ℝ, HasDerivAt
        (fun s => dirichletCoreToEnergy g μ hμ Ω (chartSupportedTestCore g μ hμ Ω c hOt hMap hφ s))
        (dirichletCoreToEnergy g μ hμ Ω
          (chartSupportedTestCore g μ hμ Ω c hOt hMap (test_timeDerivative hφ) t)) t := by
  let V := fun t => dirichletCoreToEnergy g μ hμ Ω (chartSupportedTestCore g μ hμ Ω c hOt hMap hφ t)
  let W := fun t => dirichletCoreToEnergy g μ hμ Ω
    (chartSupportedTestCore g μ hμ Ω c hOt hMap (test_timeDerivative hφ) t)
  have hClosed := chartSupportedTestCore_contDiffOn_one g hg μ hμ Ω K hΩ hK hΩK c hOt hMap hS hφ
  have hClosedW := chartSupportedTestCore_contDiffOn_one g hg μ hμ Ω K hΩ hK hΩK c hOt hMap hS
    (test_timeDerivative hφ)
  have hDv (t : ℝ) : HasDerivAt V (W t) t := by
    by_cases ht : t ∈ Ioo 0 S
    · exact (hClosed.2 t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    · have hZero := (chartSupportedTestCore_zero_germ g μ hμ Ω c hOt hMap (test_timeDerivative hφ) t ht).eq_of_nhds
      change W t = 0 at hZero
      rw [hZero]
      exact (hasDerivAt_const t (0 : DirichletEnergy g μ hμ Ω)).congr_of_eventuallyEq
        (chartSupportedTestCore_zero_germ g μ hμ Ω c hOt hMap hφ t ht)
  have hWC : Continuous W := by
    apply continuous_iff_continuousAt.mpr
    intro t
    by_cases ht : t ∈ Ioo 0 S
    · exact hClosedW.1.continuousOn.continuousAt (Icc_mem_nhds ht.1 ht.2)
    · have he := chartSupportedTestCore_zero_germ g μ hμ Ω c hOt hMap (test_timeDerivative hφ) t ht
      change W =ᶠ[𝓝 t] (fun _ => 0) at he
      change Tendsto W (𝓝 t) (𝓝 (W t))
      rw [he.eq_of_nhds]
      exact tendsto_const_nhds.congr' he.symm
  refine ⟨?_, hDv⟩
  apply contDiff_one_iff_deriv.mpr
  exact ⟨fun t => (hDv t).differentiableAt, hWC.congr (fun t => (hDv t).deriv.symm)⟩

end Yau.F04Proof
