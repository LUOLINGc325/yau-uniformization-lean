import Yau.Proofs.V03CotangentSmooth

/-! A disc's centered coordinate regularity transports to each valid fixed
induced chart. This supplies the genuine joint local cotangent predicate. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

theorem cotangentDisc_centeredCoords_contDiffWithinAt
    {f : ℂ → CotangentPoint M} (hf : CotangentDisc f)
    {ζ : ℂ} (hζ : ζ ∈ Metric.closedBall 0 1) :
    ContDiffWithinAt ℂ ∞ (fun η => cotangentChart (f ζ).1 (f η))
      (Metric.closedBall 0 1) ζ := by
  have hb := (contMDiffWithinAt_iff_target.mp (hf.1 ζ hζ)).2.contDiffWithinAt
  exact hb.prodMk (hf.2 ζ hζ)

theorem cotangentDisc_coords_contDiffWithinAt {f : ℂ → CotangentPoint M}
    (hf : CotangentDisc f) {ζ : ℂ} (hζ : ζ ∈ Metric.closedBall 0 1)
    (x : M.Carrier) (hx : f ζ ∈ cotangentSource x) :
    ContDiffWithinAt ℂ ∞ (fun η => cotangentChart x (f η))
      (Metric.closedBall 0 1) ζ := by
  have hself : f ζ ∈ cotangentSource (f ζ).1 := mem_extChartAt_source _
  have htarget := cotangentChart_mapsTo (f ζ).1 hself
  have hbase : chartInv (f ζ).1 (cotangentChart (f ζ).1 (f ζ)).1 = (f ζ).1 :=
    (extChartAt (ComplexModel n) (f ζ).1).left_inv hself
  have htransition := cotangentChartTransition_contDiffAt (f ζ).1 x htarget
    (by rw [hbase]; exact hx)
  have hcomp := htransition.comp_contDiffWithinAt ζ
    (cotangentDisc_centeredCoords_contDiffWithinAt hf hζ)
  apply hcomp.congr_of_eventuallyEq_of_mem ?_ hζ
  have hsource : ∀ᶠ η in 𝓝[Metric.closedBall 0 1] ζ,
      f η ∈ cotangentSource (f ζ).1 :=
    (hf.1 ζ hζ).continuousWithinAt.preimage_mem_nhdsWithin
      ((isOpen_extChartAt_source (I := ComplexModel n) (f ζ).1).mem_nhds hself)
  filter_upwards [hsource] with η hη
  simp only [Function.comp_apply, cotangentChart_left_inv (f ζ).1 hη]

theorem cotangentDisc_holomorphicOn {f : ℂ → CotangentPoint M} (hf : CotangentDisc f) :
    CotangentHolomorphicOn f (Metric.closedBall 0 1) := by
  refine ⟨hf.1, fun ζ hζ => ?_⟩
  have hself : f ζ ∈ cotangentSource (f ζ).1 := mem_extChartAt_source _
  have hsource : ∀ᶠ η in 𝓝[Metric.closedBall 0 1] ζ,
      f η ∈ cotangentSource (f ζ).1 :=
    (hf.1 ζ hζ).continuousWithinAt.preimage_mem_nhdsWithin
      ((isOpen_extChartAt_source (I := ComplexModel n) (f ζ).1).mem_nhds hself)
  obtain ⟨V, hV, hζV, hmap⟩ := mem_nhdsWithin.mp hsource
  refine ⟨V, hV, hζV, fun η hη => hmap ⟨hη.2, hη.1⟩, ?_⟩
  intro η hη
  exact (cotangentDisc_coords_contDiffWithinAt hf hη.1 (f ζ).1
    (hmap ⟨hη.2, hη.1⟩)).mono Set.inter_subset_left

end Yau.Blueprint.V03Proof
