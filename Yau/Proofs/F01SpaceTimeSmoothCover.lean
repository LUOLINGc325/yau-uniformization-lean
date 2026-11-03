import Yau.Proofs.F01SpaceTimeChart

/-! Real joint smoothness in an actual holomorphic open cover recovers
the original fixed-chart SmoothSpaceTime predicate, even on closed time sets. -/
noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem smoothSpaceTime_of_holomorphic_cover
    (F : M.Carrier → ℝ → ℝ) (I : Set ℝ)
    (e : ℕ → OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (hei : ∀ j, MDifferentiableOn (ComplexModel n) (ComplexModel n) (e j).symm (e j).target)
    (V : ℕ → Set (ComplexVector n)) (hV : ∀ j, IsOpen (V j))
    (hVs : ∀ j, V j ⊆ (e j).source)
    (hcover : ∀ y : M.Carrier, ∃ j w, w ∈ V j ∧ e j w = y)
    (hlocal : ∀ j, ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => F (e j p.1) p.2) (V j ×ˢ I)) :
    SmoothSpaceTime F I := by
  intro a
  rintro ⟨z, t⟩ hzt
  obtain ⟨j, w, hw, hwy⟩ := hcover (chartInv a z)
  let D := inverseChartDomain (e j) a
  let T : ComplexVector n → ComplexVector n := fun q => (e j).symm (chartInv a q)
  have hDopen : IsOpen D := inverseChartDomain_isOpen (e j) a
  have hT : ContDiffOn ℝ ∞ T D := inverseChart_real_contDiffOn (e j) (hei j) a
  let O := D ∩ T ⁻¹' V j
  have hOopen : IsOpen O := hT.continuousOn.isOpen_inter_preimage hDopen (hV j)
  have hytarget : chartInv a z ∈ (e j).target := by
    rw [← hwy]
    exact (e j).map_source (hVs j hw)
  have hzD : z ∈ D := ⟨hzt.1, hytarget⟩
  have hTw : T z = w := by
    dsimp only [T]
    rw [← hwy]
    exact (e j).left_inv (hVs j hw)
  have hzO : z ∈ O := by
    refine ⟨hzD, ?_⟩
    change T z ∈ V j
    rw [hTw]
    exact hw
  have hprod : ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => (T p.1, p.2)) (O ×ˢ I) :=
    (((hT.mono inter_subset_left).comp contDiffOn_fst (fun p hp => hp.1)).prodMk contDiffOn_snd)
  have hactual : ContDiffOn ℝ ∞
      (fun p : ComplexVector n × ℝ => F (chartInv a p.1) p.2) (O ×ˢ I) := by
    have hnative := (hlocal j).comp hprod (fun p hp => ⟨hp.1.2, hp.2⟩)
    apply hnative.congr
    intro p hp
    change F (chartInv a p.1) p.2 = F (e j ((e j).symm (chartInv a p.1))) p.2
    exact (congrArg (fun y => F y p.2) ((e j).right_inv hp.1.1.2)).symm
  apply (hactual (z, t) ⟨hzO, hzt.2⟩).mono_of_mem_nhdsWithin
  have hn : {p : ComplexVector n × ℝ | p.1 ∈ O} ∈ 𝓝 (z, t) :=
    (hOopen.preimage continuous_fst).mem_nhds hzO
  filter_upwards [mem_nhdsWithin_of_mem_nhds hn, self_mem_nhdsWithin] with p hpO hp
  exact ⟨hpO, hp.2⟩

end Yau.NodeProofs.F01Aux
