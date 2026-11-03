import Yau.Proofs.F01SublevelTopology

/-! A connected chart-ball image stays in the SAME base-point component.
Membership in the open sublevel alone is never substituted for this claim. -/
open Set
noncomputable section
namespace Yau.NodeProofs.F01Aux
variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace A]

theorem chart_ball_image_mem_component {V : Set A} {o p : A}
    (hp : p ∈ connectedComponentIn V o) {r : ℝ} (hr : 0 < r) {e : E → A}
    (he : ContinuousOn e (Metric.ball 0 r)) (he0 : e 0 = p)
    (hV : MapsTo e (Metric.ball 0 r) V) :
    MapsTo e (Metric.ball 0 r) (connectedComponentIn V o) := by
  have hpre : IsPreconnected (e '' Metric.ball 0 r) :=
    (convex_ball (0 : E) r).isPreconnected.image e he
  have hcenter : p ∈ e '' Metric.ball 0 r := ⟨0, Metric.mem_ball_self hr, he0⟩
  have hsub := hpre.subset_connectedComponentIn hcenter (Set.image_subset_iff.mpr hV)
  intro z hz
  rw [connectedComponentIn_eq hp]
  exact hsub (Set.mem_image_of_mem e hz)

end Yau.NodeProofs.F01Aux
