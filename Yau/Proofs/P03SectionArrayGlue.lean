import Yau.Proofs.P03CompactBallExtensions
import Yau.Proofs.P03FieldChartCriteria
import Yau.Proofs.P03Frames

open scoped Manifold Topology
open Set Filter

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ} {M : ComplexManifold n} {ι : Type*}

variable (a : ι → M.Carrier) (r : ι → ℝ)
  (hcover : ∀ x : M.Carrier, ∃ i,
    x ∈ (extChartAt (ComplexModel n) (a i)).source ∧
    chartPt (a i) x ∈ Metric.ball (chartPt (a i) (a i)) (r i))

/-- Reconstruction uses an actual inverse-chart differential at each point.
The selected index depends only on the fixed geometric cover. -/
def sectionArrayField (b : closedSectionArrays a r) : VectorField M := fun x =>
  let i := Classical.choose (hcover x)
  chartVec (a i) x (b.1 i ⟨chartPt (a i) x,
    Metric.ball_subset_closedBall (Classical.choose_spec (hcover x)).2⟩)

theorem sectionArrayField_eq (b : closedSectionArrays a r) (i : ι) (x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) (a i)).source)
    (hi : chartPt (a i) x ∈ chartClosedBall (a i) (r i)) :
    sectionArrayField a r hcover b x =
      chartVec (a i) x (b.1 i ⟨chartPt (a i) x, hi⟩) := by
  have hb : ∀ (j k : ι) (x : M.Carrier)
      (_ : x ∈ (extChartAt (ComplexModel n) (a j)).source)
      (_ : x ∈ (extChartAt (ComplexModel n) (a k)).source)
      (hj : chartPt (a j) x ∈ chartClosedBall (a j) (r j))
      (hk : chartPt (a k) x ∈ chartClosedBall (a k) (r k)),
      sectionArrayOverlapCLM a r j k x hj hk b.1 = 0 := by
    have hm := b.2.1
    simp only [compatibleSectionArrays, Submodule.coe_iInf, Set.mem_iInter] at hm
    intro j k x hsi hsj hj hk
    exact LinearMap.mem_ker.mp (hm j k x hsi hsj hj hk)
  let j := Classical.choose (hcover x)
  have hj := Classical.choose_spec (hcover x)
  exact sub_eq_zero.mp (hb j i x hj.1 hx (Metric.ball_subset_closedBall hj.2) hi)

theorem fieldCoords_sectionArrayField_eq (b : closedSectionArrays a r)
    (hsub : ∀ i, chartClosedBall (a i) (r i) ⊆ chartTarget (a i))
    (i : ι) {z : ComplexVector n} (hz : z ∈ chartClosedBall (a i) (r i)) :
    fieldCoords (sectionArrayField a r hcover b) (a i) z =
      compactBallExtension (a i) (r i) (b.1 i) z := by
  have hzt := hsub i hz
  have hx := (extChartAt (ComplexModel n) (a i)).map_target hzt
  have hinv : chartPt (a i) (chartInv (a i) z) = z :=
    (extChartAt (ComplexModel n) (a i)).right_inv hzt
  have hi : chartPt (a i) (chartInv (a i) z) ∈ chartClosedBall (a i) (r i) := by
    simpa only [hinv] using hz
  change tangentCoords (a i) (chartInv (a i) z)
    (sectionArrayField a r hcover b (chartInv (a i) z)) = _
  calc
    tangentCoords (a i) (chartInv (a i) z)
        (sectionArrayField a r hcover b (chartInv (a i) z)) =
      tangentCoords (a i) (chartInv (a i) z)
        (chartVec (a i) (chartInv (a i) z)
          (b.1 i ⟨chartPt (a i) (chartInv (a i) z), hi⟩)) :=
      congrArg (tangentCoords (a i) (chartInv (a i) z))
        (sectionArrayField_eq a r hcover b i (chartInv (a i) z) hx hi)
    _ = b.1 i ⟨chartPt (a i) (chartInv (a i) z), hi⟩ :=
      tangentCoords_chartVec (a i) _ hx _
    _ = compactBallExtension (a i) (r i) (b.1 i) z := by
      simp only [hinv, compactBallExtension, dif_pos hz]

/-- Compatibility and the actual scalar weak CR equations suffice for the
reconstructed intrinsic section to be holomorphic. -/
theorem sectionArrayField_holomorphic (b : closedSectionArrays a r)
    (hsub : ∀ i, chartClosedBall (a i) (r i) ⊆ chartTarget (a i)) :
    IsHolomorphicField (sectionArrayField a r hcover b) := by
  intro x
  obtain ⟨i, hxs, hxi⟩ := hcover x
  apply (field_mdifferentiableAt_iff (sectionArrayField a r hcover b) (a i) x hxs).mpr
  have hg := (CRSectionArrays_holomorphic_extension a r b i).differentiableAt
    (Metric.isOpen_ball.mem_nhds hxi)
  have heq : fieldCoords (sectionArrayField a r hcover b) (a i) =ᶠ[𝓝 (chartPt (a i) x)]
      compactBallExtension (a i) (r i) (b.1 i) := by
    apply Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hxi)
    intro z hz
    exact fieldCoords_sectionArrayField_eq a r hcover b hsub i
      (Metric.ball_subset_closedBall hz)
  exact hg.congr_of_eventuallyEq heq

end Yau.NodeProofs.P03Aux
