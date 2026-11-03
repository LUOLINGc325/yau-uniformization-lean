import Yau.LeafProofs.L14SquarePartition
import Yau.LeafProofs.L14RoughChartGraph

noncomputable section
open scoped Manifold Topology ContDiff ComplexOrder ENNReal Matrix
open MeasureTheory Bundle Filter Module

namespace Yau.LeafProofs.L14Aux
open BundleDbar

variable {n r : ℕ} {M : ComplexManifold n}

/-- A compact set has a smooth compactly supported cutoff with a unit plateau
on a neighborhood of the set and values between zero and one. -/
theorem exists_smooth_compact_plateau (g : Yau.SmoothMetric M)
    {K : Set M.Carrier} (hK : IsCompact K) :
    ∃ θ : M.Carrier → ℝ, SmoothFn θ ∧ HasCompactSupport θ ∧
      (∀ x, θ x ∈ Set.Icc (0 : ℝ) 1) ∧ K ⊆ interior {x | θ x = 1} := by
  classical
  letI : MetricSpace M.Carrier := L12Aux.inducedMetricSpace g
  letI := L12Aux.manifold_realSmooth M
  letI : LocallyCompactSpace M.Carrier := L12Aux.manifold_locallyCompact M
  obtain ⟨L, hL, hKL⟩ := exists_compact_superset hK
  obtain ⟨θ, hθone, hθzero, hθrange⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (I := 𝓘(ℝ, ComplexVector n)) (n := (⊤ : ℕ∞)) hK.isClosed hKL
  have hθs : SmoothFn (fun x => θ x) := L18Aux.smoothFn_of_contMDiff_real θ.contMDiff
  have hθsupp : Function.support θ ⊆ L := by
    intro x hx
    by_contra hn
    exact hx (hθzero x hn)
  have hθc : HasCompactSupport θ :=
    hL.of_isClosed_subset isClosed_closure (closure_minimal hθsupp hL.isClosed)
  refine ⟨θ, hθs, hθc, hθrange, ?_⟩
  intro x hx
  apply mem_interior_iff_mem_nhds.mpr
  exact hθone.filter_mono (nhds_le_nhdsSet hx)

variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- A compact model set in a bundle chart and in the inverse image of an open
manifold set has a compact neighborhood satisfying both constraints. -/
theorem exists_compact_model_set_in_open_preimage (a : M.Carrier)
    {K : Set (ComplexVector n)} (hK : IsCompact K)
    (hKO : K ⊆ localDomain (r := r) E a)
    {U : Set M.Carrier} (hU : IsOpen U) (hKU : K ⊆ chartInv a ⁻¹' U) :
    ∃ L : Set (ComplexVector n), IsCompact L ∧ L ⊆ localDomain (r := r) E a ∧
      K ⊆ interior L ∧ chartInv a '' L ⊆ U := by
  let O := localDomain (r := r) E a ∩ chartInv a ⁻¹' U
  have hO : IsOpen O :=
    ((continuousOn_extChartAt_symm (I := ComplexModel n) a).mono
      Set.inter_subset_left).isOpen_inter_preimage (localDomain_isOpen E a) hU
  have hKO' : K ⊆ O := Set.subset_inter hKO hKU
  obtain ⟨Ω, hΩ, hKΩ, hΩO, hcΩ⟩ := exists_open_between_and_isCompact_closure hK hO hKO'
  refine ⟨closure Ω, hcΩ, hΩO.trans Set.inter_subset_left, ?_, ?_⟩
  · exact hKΩ.trans (hΩ.subset_interior_closure)
  · rintro x ⟨z, hz, rfl⟩
    exact (hΩO hz).2

/-- The model support of a chart cutoff contained in the interior of a unit
plateau admits a common compact neighborhood on which the plateau equals one. -/
theorem exists_compact_chart_model_set_in_plateau (a : M.Carrier)
    (θ χ : M.Carrier → ℝ) (hχ : SmoothFn χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ bundleChartSource (r := r) E a)
    (hsθ : tsupport χ ⊆ interior {x | θ x = 1}) :
    ∃ L : Set (ComplexVector n), IsCompact L ∧ L ⊆ localDomain (r := r) E a ∧
      tsupport (L18Aux.chartPullbackZero a χ) ⊆ interior L ∧
      ∀ z ∈ L, θ (chartInv a z) = 1 := by
  obtain ⟨_, hcψ, hsψ⟩ := bundle_chartPullbackZero_properties E a χ hχ hcχ hsχ
  have hsψθ : tsupport (L18Aux.chartPullbackZero a χ) ⊆
      chartInv a ⁻¹' interior {x | θ x = 1} := by
    intro z hz
    rcases L18Aux.chartPullbackZero_tsupport_subset a hcχ
      (hsχ.trans Set.inter_subset_left) hz with ⟨x, hx, rfl⟩
    change chartInv a (chartPt a x) ∈ interior {x | θ x = 1}
    rw [chartInv_chartPt_of_mem a x
      (by simpa only [extChartAt_source] using (hsχ hx).1)]
    exact hsθ hx
  obtain ⟨L, hL, hLO, hψL, hLθ⟩ := exists_compact_model_set_in_open_preimage E a
    hcψ hsψ isOpen_interior hsψθ
  refine ⟨L, hL, hLO, hψL, ?_⟩
  intro z hz
  have hzθ : chartInv a z ∈ {x | θ x = 1} := interior_subset (hLθ ⟨z, hz, rfl⟩)
  exact hzθ

end Yau.LeafProofs.L14Aux
