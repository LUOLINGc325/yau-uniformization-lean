import Yau.Proofs.V03NativeMaps
import Yau.Proofs.V03Coordinates
import Yau.Proofs.V03TransitionInverse
import Yau.Proofs.V03HolomorphicSmooth

/-! Calculus in the actual induced cotangent atlas. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.Blueprint.V02FlowProof
open Yau Yau.Blueprint V03Proof

variable {n : ℕ} {M : ComplexManifold n}

theorem nativeCotangent_proj_contMDiff :
    ContMDiff 𝓘(ℂ, CotangentCoord n) (ComplexModel n) ∞
      (fun y : NativeCotangentPoint M => y.val.1) := by
  intro y
  rw [contMDiffAt_iff_source]
  have hy : cotangentChart y.val.1 y.val ∈ cotangentTarget y.val.1 :=
    cotangentChart_mapsTo _ (mem_extChartAt_source _)
  have hi : ContMDiffAt 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞
      (chartInv y.val.1) (cotangentChart y.val.1 y.val).1 :=
    (contMDiffOn_extChartAt_symm (I := ComplexModel n) y.val.1).contMDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) y.val.1).mem_nhds hy.1)
  have hc := hi.comp (cotangentChart y.val.1 y.val)
    (contDiff_fst.contDiffAt.contMDiffAt)
  simp only [modelWithCornersSelf_coe, Set.range_id]
  change ContMDiffWithinAt 𝓘(ℂ, CotangentCoord n) (ComplexModel n) ∞
    (fun z => chartInv y.val.1 z.1) Set.univ (cotangentChart y.val.1 y.val)
  exact hc.contMDiffWithinAt

theorem native_contMDiffOn_cotangentHolomorphicOn
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    {S : Set P} {g : P → NativeCotangentPoint M}
    (hg : ContMDiffOn 𝓘(ℂ, P) 𝓘(ℂ, CotangentCoord n) ∞ g S) :
    CotangentHolomorphicOn (fun p => (g p).val) S := by
  refine ⟨nativeCotangent_proj_contMDiff.comp_contMDiffOn hg, fun p hp => ?_⟩
  have hself : g p ∈ (chartAt (CotangentCoord n) (g p)).source :=
    mem_chart_source _ _
  have hsource : ∀ᶠ q in 𝓝[S] p,
      g q ∈ (chartAt (CotangentCoord n) (g p)).source :=
    (hg p hp).continuousWithinAt.preimage_mem_nhdsWithin
      ((chartAt (CotangentCoord n) (g p)).open_source.mem_nhds hself)
  obtain ⟨A, hA, hpA, hmap⟩ := mem_nhdsWithin.mp hsource
  refine ⟨A, hA, hpA, fun q hq => hmap ⟨hq.2, hq.1⟩, ?_⟩
  intro q hq
  have hc := (contMDiffWithinAt_iff_target_of_mem_source
    (hmap ⟨hq.2, hq.1⟩)).mp (hg q hq.1)
  have hd := hc.2.contDiffWithinAt
  change ContDiffWithinAt ℂ ∞
    (fun z => cotangentChart (g p).val.1 (g z).val) S q at hd
  exact hd.mono Set.inter_subset_left

end Yau.Blueprint.V02FlowProof
