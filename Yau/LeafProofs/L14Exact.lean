import Yau.LeafProofs.L14TwoPairAnnihilation
import Yau.LeafProofs.L14RieszToWeakSolution

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder ENNReal
open MeasureTheory Bundle Filter Module
namespace Yau.LeafProofs.L14Aux
open BundleDbar
variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)] [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- The weighted estimate for the original locally square-integrable closed source. -/
theorem weightedDbarEstimate : LeafCandidates.WeightedDbarEstimate (r := r) E := by
  intro g μ h φ hμ hE hh hφ hN f hclosed hfinite
  obtain ⟨u,w,hnorm,hrep⟩ := exists_compact_joint_riesz_pair E g μ hμ h hh φ hφ hE hN f hclosed.1 hfinite
  let U := weightedTopHilbertRepresentative E g μ hμ h hh φ hφ u
  refine ⟨U.1,U.2,?_,?_⟩
  · exact weakDbar_of_compact_joint_riesz_annihilation E g μ hμ h hh φ hφ hE f hclosed.1 u w hrep
      (compact_joint_pair_annihilation E g μ hμ h hh φ hφ hE f hclosed.1 hclosed u w hrep)
  · exact weightedTopHilbertRepresentative_normSq_le E g μ hμ h hh φ hφ u _ hfinite
      (by nlinarith [sq_nonneg ‖w‖])

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs

/-- The exact, closed original L14 bundle solvability obligation. -/
theorem L14 : Yau.LeafObligations.L14 := by
  intro n r M E _ _ _ _ _ _ _
  exact ⟨L14Aux.weightedDbarEstimate E,topDegreeMetricIndependence (r := r) E⟩

end Yau.LeafProofs
