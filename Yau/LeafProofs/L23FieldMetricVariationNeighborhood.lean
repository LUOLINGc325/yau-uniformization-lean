import Yau.LeafProofs.L23FieldMetricVariationLocal

/-! Compactness supplies one genuine variation neighborhood for the whole path. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 800000

theorem exists_unit_interval_thickening (U : Set ℝ) (hU : IsOpen U)
    (hunit : Set.Icc (0 : ℝ) 1 ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ Set.Ioo (-δ) (1+δ) ⊆ U := by
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (hunit (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)))
  obtain ⟨s,hs,hssub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (hunit (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1)))
  let δ := min r s / 2
  have hδ : 0 < δ := div_pos (lt_min hr hs) (by norm_num)
  have hδr : δ < r := by dsimp only [δ]; linarith [min_le_left r s]
  have hδs : δ < s := by dsimp only [δ]; linarith [min_le_right r s]
  refine ⟨δ,hδ,?_⟩
  intro t ht
  by_cases ht0 : t < 0
  · apply hrsub
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_neg ht0]
    linarith [ht.1]
  · by_cases ht1 : 1 < t
    · apply hssub
      rw [Metric.mem_ball,Real.dist_eq,abs_of_pos (sub_pos.mpr ht1)]
      linarith [ht.2]
    · exact hunit ⟨le_of_not_gt ht0,le_of_not_gt ht1⟩

theorem exists_parallelExpVariation_neighborhood
    (h : HermitianField M) (hh : MetricSmooth h) (γ : ℝ → M.Carrier)
    (P : (u : ℝ) → ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (γ u))
    (I : Set ℝ) (hI : IsOpen I) (hunit : Set.Icc (0 : ℝ) 1 ⊆ I)
    (HP : IsParallelFrameOn h γ P I) (O : Set M.Carrier) (hO : IsOpen O) :
    letI := manifold_realSmooth M
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 3 γ I →
    Set.MapsTo γ (Set.Icc (0 : ℝ) 1) O →
    ∃ (δ r : ℝ), 0 < δ ∧ 0 < r ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3
        (Function.uncurry (parallelExpVariation h γ P))
        (Set.Ioo (-δ) (1+δ) ×ˢ Metric.ball 0 r) ∧
      Set.MapsTo (Function.uncurry (parallelExpVariation h γ P))
        (Set.Ioo (-δ) (1+δ) ×ˢ Metric.ball 0 r) O := by
  letI := manifold_realSmooth M
  intro hγ hγO
  let A := Function.uncurry (parallelExpVariation h γ P)
  let 𝒰 := {U : Set (ℝ × ComplexVector n) | IsOpen U ∧
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3 A U ∧
    Set.MapsTo A U O}
  let W : Set (ℝ × ComplexVector n) := ⋃ U : 𝒰, U.val
  have hW : IsOpen W := isOpen_iUnion (fun U => U.property.1)
  have hzero : Set.Icc (0 : ℝ) 1 ×ˢ ({0} : Set (ComplexVector n)) ⊆ W := by
    intro p hp
    have hp0 : p.2 = 0 := Set.mem_singleton_iff.mp hp.2
    obtain ⟨U,hU,hpU,hAU,hmap⟩ := exists_parallelExpVariation_local h hh γ P I hI HP O hO hγ p.1 (hunit hp.1) (hγO hp.1)
    apply Set.mem_iUnion.mpr
    refine ⟨⟨U,hU,hAU,hmap⟩,?_⟩
    have Hp : p = (p.1,0) := Prod.ext rfl hp0
    rw [Hp]
    exact hpU
  have HAW : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3 A W := by
    intro p hp
    obtain ⟨U,hpU⟩ := Set.mem_iUnion.mp hp
    exact ((U.property.2.1 p hpU).contMDiffAt (U.property.1.mem_nhds hpU)).contMDiffWithinAt
  have hmapW : Set.MapsTo A W O := by
    intro p hp
    obtain ⟨U,hpU⟩ := Set.mem_iUnion.mp hp
    exact U.property.2.2 hpU
  obtain ⟨U,V,hU,hV,hUunit,hVzero,hprod⟩ := generalized_tube_lemma isCompact_Icc isCompact_singleton hW hzero
  obtain ⟨δ,hδ,hδsub⟩ := exists_unit_interval_thickening U hU hUunit
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds (hVzero (Set.mem_singleton 0)))
  have hsub : Set.Ioo (-δ) (1+δ) ×ˢ Metric.ball (0 : ComplexVector n) r ⊆ W :=
    fun p hp => hprod ⟨hδsub hp.1,hrsub hp.2⟩
  exact ⟨δ,r,hδ,hr,HAW.mono hsub,fun p hp => hmapW (hsub hp)⟩

end Yau.LeafProofs.L23Aux
