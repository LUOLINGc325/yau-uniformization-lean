import Yau.Proofs.F05AtlasModel

/-! The computed atlas maps give genuine open partial homeomorphisms. -/

open Set
open scoped Topology ContDiff Manifold
noncomputable section

namespace Yau.Proofs.F05Aux

open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n} {O : Set M.Carrier} {A : AtlasData M}

def F05AtlasFlatten (hA : GenuineAtlas O A) (i : Fin A.count) :
    OpenPartialHomeomorph (Space n) (Space n) where
  toFun := A.forward i
  invFun := A.inverse i
  source := A.source i
  target := Metric.ball 0 3
  map_source' := fun z hz => hz.2
  map_target' := fun z hz => (hA.1 i).2.2.2.2.1 ⟨z,hz,rfl⟩
  left_inv' := (hA.1 i).2.2.2.2.2.2.1
  right_inv' := (hA.1 i).2.2.2.2.2.1
  continuousOn_toFun := (hA.1 i).2.2.1.continuousOn
  continuousOn_invFun := (hA.1 i).2.2.2.1.continuousOn
  open_source := (hA.1 i).1
  open_target := Metric.isOpen_ball

def F05AtlasEquiv (hA : GenuineAtlas O A) (i : Fin A.count) :
    OpenPartialHomeomorph M.Carrier (Space n) :=
  (chartAt (Space n) (A.center i)).trans (F05AtlasFlatten hA i)

theorem F05AtlasEquiv_inverse (hA : GenuineAtlas O A) (i : Fin A.count) :
    (F05AtlasEquiv hA i).symm = lift A i := by
  funext z
  simp [F05AtlasEquiv,F05AtlasFlatten,lift,chartInv,ComplexModel]

theorem F05AtlasEquiv_target (hA : GenuineAtlas O A) (i : Fin A.count) :
    (F05AtlasEquiv hA i).target = Metric.ball 0 3 := by
  change Metric.ball 0 3 ∩ (A.inverse i) ⁻¹'
    (chartAt (Space n) (A.center i)).target = Metric.ball 0 3
  apply inter_eq_left.mpr
  intro z hz
  have h := (hA.1 i).2.1 ((hA.1 i).2.2.2.2.1 ⟨z,hz,rfl⟩)
  simpa [chartTarget,ComplexModel] using h

theorem F05_lift_ball_isOpen (hA : GenuineAtlas O A) (i : Fin A.count)
    {r : ℝ} (hr : r ≤ 3) : IsOpen (lift A i '' Metric.ball 0 r) := by
  rw [← F05AtlasEquiv_inverse hA i]
  apply (F05AtlasEquiv hA i).symm.isOpen_image_of_subset_source Metric.isOpen_ball
  rw [(F05AtlasEquiv hA i).symm_source,F05AtlasEquiv_target]
  exact Metric.ball_subset_ball hr

theorem F05_lift_closedBall_isCompact (hA : GenuineAtlas O A) (i : Fin A.count)
    {r : ℝ} (hr : r < 3) : IsCompact (lift A i '' Metric.closedBall 0 r) := by
  rw [← F05AtlasEquiv_inverse hA i]
  apply (isCompact_closedBall (0 : Space n) r).image_of_continuousOn
  apply (F05AtlasEquiv hA i).symm.continuousOn.mono
  rw [(F05AtlasEquiv hA i).symm_source,F05AtlasEquiv_target]
  exact Metric.closedBall_subset_ball hr

end Yau.Proofs.F05Aux
