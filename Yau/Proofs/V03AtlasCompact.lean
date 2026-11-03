import Yau.Proofs.V03Atlas

/-! The immersion is continuous in the actual induced atlas and embeds each
fixed intrinsic compact set. No global properness assertion is used. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {M : ComplexManifold n}

def nativeCotangentChartHomeomorph (x : M.Carrier) :
    OpenPartialHomeomorph (NativeCotangentPoint M) (CotangentCoord n) :=
  (nativeCotangentCore M).openPartialHomeomorph (nativeCotangentChart x) ⟨x, rfl⟩

theorem cotangentCompact_native_isCompact {K : Set (CotangentPoint M)}
    (hK : CotangentCompact K) : IsCompact (NativeCotangentPoint.mk '' K) := by
  obtain ⟨r, x, C, hC, hK⟩ := hK
  rw [hK, Set.image_iUnion]
  apply isCompact_iUnion
  intro i
  have hi := (hC i).1.image_of_continuousOn
    ((nativeCotangentChartHomeomorph (x i)).continuousOn_symm.mono (hC i).2)
  change IsCompact ((fun z : CotangentCoord n =>
    NativeCotangentPoint.mk (cotangentChartInv (x i) z)) '' C i) at hi
  simpa only [Set.image_image, Function.comp_def] using hi

theorem nativeCotangentMap_continuous
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentHolomorphic G) :
    Continuous (fun y : NativeCotangentPoint M => G y.val) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  let e := nativeCotangentChartHomeomorph y.val.1
  have hy : y ∈ e.source := mem_extChartAt_source y.val.1
  have htarget : e y ∈ e.target := e.map_source hy
  have hGc : ContinuousAt (fun z => G (cotangentChartInv y.val.1 z)) (e y) :=
    (hG y.val.1).continuousOn.continuousAt (e.open_target.mem_nhds htarget)
  have hcoord : ContinuousAt e y := e.continuousOn.continuousAt (e.open_source.mem_nhds hy)
  have hcomp := hGc.comp hcoord
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hy] with y' hy'
  exact congrArg G (cotangentChart_left_inv y.val.1 hy').symm

theorem nativeCotangent_t2_of_immersion
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G) :
    T2Space (NativeCotangentPoint M) := by
  apply T2Space.of_injective_continuous
    (f := fun y : NativeCotangentPoint M => G y.val) ?_
    (nativeCotangentMap_continuous hG.1)
  intro y y' h
  exact NativeCotangentPoint.ext (hG.2.1 h)

theorem cotangentImmersion_compact_isClosedEmbedding
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    {K : Set (CotangentPoint M)} (hK : CotangentCompact K) :
    Topology.IsClosedEmbedding (fun y : (NativeCotangentPoint.mk '' K) => G y.1.val) := by
  letI : CompactSpace (NativeCotangentPoint.mk '' K) :=
    isCompact_iff_compactSpace.mp (cotangentCompact_native_isCompact hK)
  apply ((nativeCotangentMap_continuous hG.1).comp continuous_subtype_val).isClosedEmbedding
  intro y y' h
  exact Subtype.ext (NativeCotangentPoint.ext (hG.2.1 h))

end Yau.Blueprint.V03Proof
