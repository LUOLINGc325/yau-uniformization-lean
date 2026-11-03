import Yau.Proofs.F01MetricFamilyEntries
import Yau.LeafProofs.L17HolomorphicCharts

/-! Native jointly smooth scalar functions remain jointly smooth in an
actual fixed holomorphic chart, including every closed time face. -/
noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem smoothSpaceTime_slice {F : M.Carrier → ℝ → ℝ} {I : Set ℝ}
    (hF : SmoothSpaceTime F I) {t : ℝ} (ht : t ∈ I) : SmoothFn (fun x => F x t) := by
  intro a
  exact (hF a).comp (contDiffOn_id.prodMk contDiffOn_const) (fun z hz => ⟨hz, ht⟩)

theorem smoothSpaceTime_holomorphic_chart {F : M.Carrier → ℝ → ℝ} {I : Set ℝ}
    (hF : SmoothSpaceTime F I)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source) :
    ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => F (e p.1) p.2) (e.source ×ˢ I) := by
  rintro ⟨z, t⟩ hzt
  let a := e z
  let D := forwardChartDomain e a
  let T : ComplexVector n → ComplexVector n := fun w => chartPt a (e w)
  have hDopen : IsOpen D := forwardChartDomain_isOpen e a
  have hzD : z ∈ D := ⟨hzt.1, mem_extChartAt_source a⟩
  have hT : ContDiffOn ℂ ∞ T D := forwardChart_contDiffOn e he a
  have hprod : ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => (T p.1, p.2)) (D ×ˢ I) :=
    ((hT.restrict_scalars ℝ).comp contDiffOn_fst (fun _ hp => hp.1)).prodMk contDiffOn_snd
  have hactual : ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => F (e p.1) p.2) (D ×ˢ I) := by
    have hnative := (hF a).comp hprod (fun p hp =>
      ⟨(extChartAt (ComplexModel n) a).map_source hp.1.2, hp.2⟩)
    apply hnative.congr
    intro p hp
    change F (e p.1) p.2 = F (chartInv a (chartPt a (e p.1))) p.2
    exact (congrArg (fun y => F y p.2) ((extChartAt (ComplexModel n) a).left_inv hp.1.2)).symm
  apply (hactual (z, t) ⟨hzD, hzt.2⟩).mono_of_mem_nhdsWithin
  have hn : {p : ComplexVector n × ℝ | p.1 ∈ D} ∈ 𝓝 (z, t) :=
    (hDopen.preimage continuous_fst).mem_nhds hzD
  filter_upwards [mem_nhdsWithin_of_mem_nhds hn, self_mem_nhdsWithin] with p hpD hp
  exact ⟨hpD, hp.2⟩

end Yau.NodeProofs.F01Aux
