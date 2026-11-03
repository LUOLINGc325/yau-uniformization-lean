import Yau.Proofs.HeatSmoothExhaustionRegularFunction
import Yau.Proofs.HeatSmoothExhaustionLocalSides

noncomputable section
open Set Filter
open scoped Topology ContDiff Manifold

namespace Yau.Proofs.SmoothExhaustionAux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem component_negative_smoothPrecompact
    {f : M.Carrier → ℝ} (hf : SmoothFn f) (hc : IsCompact {p | f p ≤ 0})
    (hr : ChartRegularZero f) {o : M.Carrier} (ho : f o < 0) :
    HeatConcreteBindings.SmoothPrecompactDomain (connectedComponentIn {p | f p < 0} o) := by
  letI : LocallyConnectedSpace M.Carrier := ChartedSpace.locallyConnectedSpace (ComplexVector n) M.Carrier
  let S : Set M.Carrier := {p | f p < 0}
  let D := connectedComponentIn S o
  have hfc : Continuous f := continuous_of_smoothFn hf
  have hSo : IsOpen S := isOpen_lt hfc continuous_const
  have hDo : IsOpen D := hSo.connectedComponentIn
  have hoD : o ∈ D := mem_connectedComponentIn ho
  have hDS : D ⊆ S := connectedComponentIn_subset S o
  have hDsub : D ⊆ {p | f p ≤ 0} := fun p hp => (show f p < 0 from hDS hp).le
  have hclosure : closure D ⊆ {p | f p ≤ 0} :=
    closure_minimal hDsub (isClosed_le hfc continuous_const)
  have hDc : IsCompact (closure D) := hc.of_isClosed_subset isClosed_closure hclosure
  refine ⟨hDo,⟨o,hoD⟩,isConnected_connectedComponentIn_iff.mpr ho,hDc,?_⟩
  intro p hp
  have hpcl : p ∈ closure D := frontier_subset_closure hp
  have hpnot : p ∉ D := by
    have HH := hp
    rw [hDo.frontier_eq] at HH
    exact HH.2
  have hpzero : f p=0 := by
    have hle : f p ≤ 0 := hclosure hpcl
    have hn : ¬f p < 0 := by
      intro hneg
      let T := connectedComponentIn S p
      have hTo : IsOpen T := hSo.connectedComponentIn
      have hpT : p ∈ T := mem_connectedComponentIn hneg
      obtain ⟨q,hqT,hqD⟩ := mem_closure_iff.mp hpcl T hTo hpT
      have heq : T=D := (connectedComponentIn_eq hqT).trans (connectedComponentIn_eq hqD).symm
      exact hpnot (heq ▸ hpT)
    exact le_antisymm hle (le_of_not_gt hn)
  obtain ⟨a,hpa,hD⟩ := hr p hpzero
  have hpa' : p ∈ (extChartAt (ComplexModel n) a).source := by
    simpa only [extChartAt_source] using hpa
  have hz : chartPt a p ∈ chartTarget a := (extChartAt (ComplexModel n) a).map_source hpa'
  have hinv : chartInv a (chartPt a p)=p := (extChartAt (ComplexModel n) a).left_inv hpa'
  let ρ := inChart a f
  have hρ0 : ρ (chartPt a p)=0 := by change f (chartInv a (chartPt a p))=0;rw [hinv];exact hpzero
  obtain ⟨W,hWo,hpW,hWa,hWpre⟩ := regular_negative_local_preconnected
    (isOpen_extChartAt_target (I := ComplexModel n) a) (hf a) hz hρ0 hD
  let H : Set M.Carrier := chartInv a '' W
  have hHo : IsOpen H := isOpen_chartInv_image a hWo hWa
  have hpH : p ∈ H := ⟨chartPt a p,hpW,hinv⟩
  have hHS : H ∩ S = chartInv a '' (W ∩ {z | ρ z < 0}) := by
    ext y
    constructor
    · rintro ⟨⟨z,hzW,rfl⟩,hyS⟩
      exact ⟨z,⟨hzW,hyS⟩,rfl⟩
    · rintro ⟨z,⟨hzW,hzρ⟩,rfl⟩
      exact ⟨⟨z,hzW,rfl⟩,hzρ⟩
  have hHSpre : IsPreconnected (H ∩ S) := by
    rw [hHS]
    exact hWpre.image (chartInv a)
      ((continuousOn_extChartAt_symm (I := ComplexModel n) a).mono (inter_subset_left.trans hWa))
  obtain ⟨q,hqH,hqD⟩ := mem_closure_iff.mp hpcl H hHo hpH
  have hqHS : q ∈ H ∩ S := ⟨hqH,hDS hqD⟩
  have hHSD : H ∩ S ⊆ D := by
    have HH := hHSpre.subset_connectedComponentIn hqHS (inter_subset_right : H ∩ S ⊆ S)
    rwa [← connectedComponentIn_eq hqD] at HH
  refine ⟨a,W,ρ,hpa,hWo,hpW,hWa,(hf a).mono hWa,hρ0,hD,?_⟩
  intro z hzW
  constructor
  · intro hzD
    exact hDS hzD
  · intro hzρ
    exact hHSD ⟨⟨z,hzW,rfl⟩,hzρ⟩

end Yau.Proofs.SmoothExhaustionAux
