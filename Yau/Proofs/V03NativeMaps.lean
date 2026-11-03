import Yau.Proofs.V03AtlasSmooth
import Yau.Proofs.V03AtlasCompact
import Yau.Proofs.V03DiscSmooth

/-! The original cotangent holomorphic predicate gives smooth maps into the
constructed native cotangent manifold, including at closed-disc boundaries. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

theorem cotangentHolomorphicOn_native_contMDiffOn {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set E}
    {f : E → CotangentPoint M} (hf : CotangentHolomorphicOn f S) :
    ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, CotangentCoord n) ∞
      (fun z => NativeCotangentPoint.mk (f z)) S := by
  intro z hz
  obtain ⟨V, hV, hzV, hsource, hd⟩ := hf.2 z hz
  have hcoord : ContDiffWithinAt ℂ ∞ (fun y => cotangentChart (f z).1 (f y)) S z :=
    (contDiffWithinAt_inter (hV.mem_nhds hzV)).mp (hd z ⟨hz, hzV⟩)
  let e := nativeCotangentChartHomeomorph (f z).1
  have hself : NativeCotangentPoint.mk (f z) ∈ e.source := mem_extChartAt_source _
  have htarget : cotangentChart (f z).1 (f z) ∈ e.target := e.map_source hself
  have hInv : ContinuousAt e.symm (cotangentChart (f z).1 (f z)) :=
    e.continuousOn_symm.continuousAt (e.open_target.mem_nhds htarget)
  have hcomp : ContinuousWithinAt
      (fun y : E => e.symm (cotangentChart (f z).1 (f y))) S z :=
    hInv.tendsto.comp hcoord.continuousWithinAt
  have hC : ContinuousWithinAt (fun y => NativeCotangentPoint.mk (f y)) S z := by
    apply hcomp.congr_of_eventuallyEq_of_mem ?_ hz
    have hVnear : V ∈ 𝓝[S] z := mem_inf_of_left (hV.mem_nhds hzV)
    filter_upwards [self_mem_nhdsWithin, hVnear] with y hy hyV
    apply NativeCotangentPoint.ext
    exact (cotangentChart_left_inv (f z).1 (hsource y ⟨hy, hyV⟩)).symm
  apply contMDiffWithinAt_iff_target.mpr
  refine ⟨hC, ?_⟩
  change ContMDiffWithinAt 𝓘(ℂ, E) 𝓘(ℂ, CotangentCoord n) ∞
    (fun y => cotangentChart (f z).1 (f y)) S z
  exact hcoord.contMDiffWithinAt

theorem cotangentDisc_native_contMDiffOn {f : ℂ → CotangentPoint M} (hf : CotangentDisc f) :
    ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, CotangentCoord n) ∞
      (fun z => NativeCotangentPoint.mk (f z)) (Metric.closedBall 0 1) :=
  cotangentHolomorphicOn_native_contMDiffOn (cotangentDisc_holomorphicOn hf)

end Yau.Blueprint.V03Proof
