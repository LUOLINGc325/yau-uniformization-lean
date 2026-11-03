import Yau.Proofs.C03ShortLiftTopology
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-! Parameter continuity for actual lifts confined to an open domain. -/
noncomputable section
open scoped Topology
open Set unitInterval
namespace Yau.Proofs.C03Aux.ShortLift

theorem restricted_local_homeomorph
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    (p : E → X) (U : Set E) (hU : IsOpen U) (hz : U.Nonempty)
    (hloc : ∀ z ∈ U, ∃ e : OpenPartialHomeomorph E X,
      z ∈ e.source ∧ e.source ⊆ U ∧ EqOn e p e.source) :
    IsLocalHomeomorph (fun z : U => p z) := by
  let V : TopologicalSpace.Opens E := ⟨U, hU⟩
  have hV : Nonempty V := ⟨⟨hz.choose, hz.choose_spec⟩⟩
  apply isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
  apply IsLocalHomeomorphOn.mk
  intro z _
  obtain ⟨e, he, _, hep⟩ := hloc z z.2
  refine ⟨e.subtypeRestr hV, ?_, ?_⟩
  · simpa only [OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage] using he
  · intro y hy
    change p y = e y
    exact (hep (by simpa only [OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage] using hy)).symm

theorem continuous_lift_endpoints_on
    {E X A : Type*} [TopologicalSpace E] [T2Space E]
    [TopologicalSpace X] [TopologicalSpace A]
    (p : E → X) (U : Set E) (hU : IsOpen U) (hz : U.Nonempty)
    (hloc : ∀ z ∈ U, ∃ e : OpenPartialHomeomorph E X,
      z ∈ e.source ∧ e.source ⊆ U ∧ EqOn e p e.source)
    (f : C(I × A, X)) (g : I × A → E)
    (hmem : ∀ q, g q ∈ U) (hg : p ∘ g = f)
    (hstart : Continuous (fun a => g (0, a)))
    (hpaths : ∀ a, Continuous (fun t => g (t, a))) :
    Continuous (fun a => g (1, a)) := by
  let gU : I × A → U := fun q => ⟨g q, hmem q⟩
  have hproj : (fun z : U => p z) ∘ gU = f := hg
  have h0 : Continuous (fun a => gU (0, a)) := hstart.subtype_mk _
  have hA : ∀ a, Continuous (fun t => gU (t, a)) := fun a => (hpaths a).subtype_mk _
  exact continuous_subtype_val.comp
    (continuous_lift_endpoints (restricted_local_homeomorph p U hU hz hloc) f gU hproj h0 hA)

end Yau.Proofs.C03Aux.ShortLift
