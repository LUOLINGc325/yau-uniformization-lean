import Yau.Proofs.F01OpenPotentialExtension
import Yau.Proofs.F01SpaceTimeChart

/-! Extending a potential by zero introduces no claimed boundary
regularity. On every genuine original chart contained in the open
manifold its closed-time smoothness follows from the native charts. -/
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} (M : ComplexManifold n) (S : Opens M.Carrier)
  (hS : IsConnected (S : Set M.Carrier))

theorem openExtendedPotential_holomorphic_chart_smooth
    (U : (openConnectedManifold M S hS).Carrier → ℝ → ℝ) {I : Set ℝ}
    (hU : SmoothSpaceTime U I)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    {O : Set (ComplexVector n)} (hOe : O ⊆ e.source)
    (hOS : ∀ z ∈ O, e z ∈ S) :
    ContDiffOn ℝ ∞
      (fun p : ComplexVector n × ℝ => openExtendedPotential M S hS U (e p.1) p.2)
      (O ×ˢ I) := by
  rintro ⟨z, t⟩ hzt
  let a : (openConnectedManifold M S hS).Carrier := ⟨e z, hOS z hzt.1⟩
  let D := forwardChartDomain e a.val
  let T : ComplexVector n → ComplexVector n := fun w => chartPt a.val (e w)
  have hDopen : IsOpen D := forwardChartDomain_isOpen e a.val
  have hzD : z ∈ D := ⟨hOe hzt.1, mem_extChartAt_source a.val⟩
  have hT : ContDiffOn ℂ ∞ T D := forwardChart_contDiffOn e he a.val
  have hTAt : ContDiffAt ℝ ∞ T z :=
    ((hT.contDiffAt (hDopen.mem_nhds hzD)).restrict_scalars ℝ)
  have hzTarget : T z ∈ chartTarget a := mem_extChartAt_target a
  let D' : Set (ComplexVector n) := D ∩ T ⁻¹' chartTarget a
  have hzD' : z ∈ D' := ⟨hzD, hzTarget⟩
  have hD' : D' ∈ 𝓝 z :=
    inter_mem (hDopen.mem_nhds hzD)
      (hTAt.continuousAt ((isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds hzTarget))
  have hprod : ContDiffOn ℝ ∞
      (fun p : ComplexVector n × ℝ => (T p.1, p.2)) (D' ×ˢ I) :=
    (((hT.restrict_scalars ℝ).mono inter_subset_left).comp
      contDiffOn_fst (fun _ hp => hp.1)).prodMk contDiffOn_snd
  have hactual : ContDiffOn ℝ ∞
      (fun p : ComplexVector n × ℝ => openExtendedPotential M S hS U (e p.1) p.2)
      (D' ×ˢ I) := by
    have hnative := (hU a).comp hprod (fun p hp => ⟨hp.1.2, hp.2⟩)
    apply hnative.congr
    intro p hp
    have hval : (chartInv a (T p.1)).val = e p.1 :=
      (openInclusion_chartInv M S hS a hp.1.2).trans
        ((extChartAt (ComplexModel n) a.val).left_inv hp.1.1.2)
    change openExtendedPotential M S hS U (e p.1) p.2 = U (chartInv a (T p.1)) p.2
    rw [← hval]
    exact openExtendedPotential_restrict M S hS U _ _
  apply (hactual (z, t) ⟨hzD', hzt.2⟩).mono_of_mem_nhdsWithin
  have hnear : {p : ComplexVector n × ℝ | p.1 ∈ D'} ∈ 𝓝 (z, t) :=
    continuous_fst.continuousAt.preimage_mem_nhds hD'
  filter_upwards [mem_nhdsWithin_of_mem_nhds hnear, self_mem_nhdsWithin] with p hpD hp
  exact ⟨hpD, hp.2⟩

end Yau.NodeProofs.F01Aux
