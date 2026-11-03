import Yau.Proofs.V02WallTaylorBoundaryRegularity

/-! The original reciprocal walls are actually jointly smooth on a family
whose original geometric boundary inequalities hold. No uniform zeroth bound is used. -/

open scoped Topology ContDiff Manifold

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof
open Yau Yau.Blueprint V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

theorem family_walls_contDiffOn_of_boundary {d : VariationData X q}
    (hd : VariationSetup d) (j : ℕ) {F : VariationDisc X}
    {fz : ℂ → ℂ → CotangentPoint X.manifold} {r : ℝ}
    (hfamily : HolomorphicDiscFamily F fz r)
    (hboundary : ∀ z ∈ Metric.ball (0 : ℂ) r, ∀ θ, fz z (circlePoint θ) ∈ boundaryRegion d j) :
    ContDiffOn ℝ ∞ (fun p : ℂ × ℝ => wallBase d j (fz p.1 (circlePoint p.2)).1 +
      wallFiber d j (fz p.1 (circlePoint p.2))) (Metric.ball (0 : ℂ) r ×ˢ Set.univ) := by
  have hdb : ContDiffOn ℝ ∞ (fun p : ℂ × ℂ => deltaBase d j (fz p.1 p.2).1)
      (Metric.ball (0 : ℂ) r ×ˢ Metric.closedBall (0 : ℂ) 1) :=
    cotangentHolomorphicOn_scalar_contDiffOn (b := fun y => deltaBase d j y.1) hfamily.2.2 (fun x => deltaBase_chart_contDiffOn hd j x)
  have hdf : ContDiffOn ℝ ∞ (fun p : ℂ × ℂ => deltaFiber d j (fz p.1 p.2))
      (Metric.ball (0 : ℂ) r ×ˢ Metric.closedBall (0 : ℂ) 1) :=
    cotangentHolomorphicOn_scalar_contDiffOn (b := deltaFiber d j) hfamily.2.2 (fun x => deltaFiber_chart_contDiffOn hd j x)
  have hc : ContDiff ℝ ∞ (fun p : ℂ × ℝ => (p.1, circlePoint p.2)) :=
    contDiff_fst.prodMk (circlePoint_contDiff.comp contDiff_snd)
  have hmap : Set.MapsTo (fun p : ℂ × ℝ => (p.1, circlePoint p.2))
      (Metric.ball (0 : ℂ) r ×ˢ Set.univ) (Metric.ball (0 : ℂ) r ×ˢ Metric.closedBall (0 : ℂ) 1) :=
    fun p hp => ⟨hp.1, circlePoint_mem_closedBall p.2⟩
  have hb := hdb.comp hc.contDiffOn hmap
  have hf := hdf.comp hc.contDiffOn hmap
  obtain ⟨hA, hB⟩ := setup_index_bounds hd j
  exact ((hb.inv (fun p hp => (deltaBase_pos (setup_wallProfiles hd) hA
    (hboundary p.1 hp.1 p.2).1).ne')).sub contDiffOn_const).add
    ((hf.inv (fun p hp => (deltaFiber_pos (setup_wallProfiles hd) hB
      (hboundary p.1 hp.1 p.2).2).ne')).sub contDiffOn_const)

end Yau.Blueprint.V02WallTaylorProof
