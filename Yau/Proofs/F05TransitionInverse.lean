import Yau.Proofs.F05TransitionDomains

/-! The actual transition map lifts back to the same manifold point on its
genuine open domain, before any function or derivative is considered. -/

open Set Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

theorem F05Coord_lift_ball {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (i : Fin A.count) {z : Space n} (hz : z ∈ Metric.ball 0 3) :
    F05Coord A i (lift A i z) = z := by
  have hTarget := (hA.1 i).2.1 ((hA.1 i).2.2.2.2.1 ⟨z,hz,rfl⟩)
  have hchart : chartPt (A.center i) (chartInv (A.center i) (A.inverse i z)) = A.inverse i z :=
    (extChartAt (ComplexModel n) (A.center i)).right_inv hTarget
  change A.forward i (chartPt (A.center i) (chartInv (A.center i) (A.inverse i z))) = z
  rw [hchart]
  exact (hA.1 i).2.2.2.2.2.1 z hz

theorem F05_lift_coord_image {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (i : Fin A.count) {x : M.Carrier}
    (hx : x ∈ lift A i '' Metric.ball 0 3) : lift A i (F05Coord A i x) = x := by
  obtain ⟨z,hz,rfl⟩ := hx
  rw [F05Coord_lift_ball hA i hz]

theorem F05Transition_lift {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (i j : Fin A.count) {z : Space n}
    (hz : z ∈ F05TransitionDomain A i j) : lift A j (F05Transition A i j z) = lift A i z :=
  F05_lift_coord_image hA j hz.2

theorem F05Transition_lift_near {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (i j : Fin A.count) {z : Space n}
    (hz : z ∈ F05TransitionDomain A i j) :
    ∀ᶠ w in 𝓝 z, lift A j (F05Transition A i j w) = lift A i w := by
  filter_upwards [(F05TransitionDomain_isOpen hA i j).mem_nhds hz] with w hw
  exact F05Transition_lift hA i j hw

end Yau.Proofs.F05Aux
