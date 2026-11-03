import Yau.Proofs.F01OpenMetricSmooth
import Yau.LeafProofs.L22Locality

/-! Actual centered metric, Levi and gradient formulas commute with the
constructed open-manifold inclusion. All inverse-chart equalities are used
on a genuine open neighborhood. -/
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology Manifold
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} (M : ComplexManifold n) (S : Opens M.Carrier)
  (hS : IsConnected (S : Set M.Carrier))

theorem openRestrictedField_hMat (g : HermitianField M)
    (a : (openConnectedManifold M S hS).Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget a) :
    hMat (openRestrictedField M S hS g) a z = hMat g a.val z := by
  ext i j
  unfold hMat
  rw [openRestrictedField_value, openInclusion_chartVec M S hS a hz,
    openInclusion_chartVec M S hS a hz, openInclusion_chartInv M S hS a hz]

theorem openRestrictedField_gMat (g : HermitianField M)
    (a : (openConnectedManifold M S hS).Carrier) :
    gMat (openRestrictedField M S hS g) a = gMat g a.val := by
  calc
    gMat (openRestrictedField M S hS g) a =
      hMat (openRestrictedField M S hS g) a (chartPt a a) := rfl
    _ = hMat g a.val (chartPt a a) :=
      openRestrictedField_hMat M S hS g a (z := chartPt a a) (mem_extChartAt_target a)
    _ = gMat g a.val := rfl

theorem openRestriction_inChart_eventuallyEq (f : M.Carrier → ℝ)
    (a : (openConnectedManifold M S hS).Carrier) :
    inChart a (fun x : (openConnectedManifold M S hS).Carrier => f x.val) =ᶠ[𝓝 (chartPt a a)] inChart a.val f := by
  filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds
    (mem_extChartAt_target a)] with z hz
  exact congrArg f (openInclusion_chartInv M S hS a hz)

theorem openRestriction_levi (f : M.Carrier → ℝ)
    (a : (openConnectedManifold M S hS).Carrier) :
    levi (fun x : (openConnectedManifold M S hS).Carrier => f x.val) a = levi f a.val := by
  unfold levi
  rw [LeafProofs.L22Aux.leviC_congr_of_eventuallyEq
    (openRestriction_inChart_eventuallyEq M S hS f a), openInclusion_chartPt M S hS a a]

theorem openRestriction_gradNormSq (g : HermitianField M) (f : M.Carrier → ℝ)
    (a : (openConnectedManifold M S hS).Carrier) :
    gradNormSq (openRestrictedField M S hS g) (fun x : (openConnectedManifold M S hS).Carrier => f x.val) a =
      gradNormSq g f a.val := by
  have he : (fun z => Complex.ofReal (inChart a (fun x : (openConnectedManifold M S hS).Carrier => f x.val) z)) =ᶠ[𝓝 (chartPt a a)]
      (fun z => Complex.ofReal (inChart a.val f z)) := by
    filter_upwards [openRestriction_inChart_eventuallyEq M S hS f a] with z hz
    exact congrArg Complex.ofReal hz
  unfold gradNormSq
  simp only [wirt]
  rw [he.fderiv_eq, openRestrictedField_gMat M S hS]
  rfl

end Yau.NodeProofs.F01Aux
