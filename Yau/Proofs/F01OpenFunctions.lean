import Yau.Proofs.F01OpenCharts
import Yau.Proofs.F01ConformalSmooth

/-! Restriction of the original smooth functions to the actual open manifold,
and the explicit conformal scalar on a genuine sublevel. -/
open Set TopologicalSpace
open scoped Manifold ContDiff
noncomputable section
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} (M : ComplexManifold n) (S : Opens M.Carrier)
  (hS : IsConnected (S : Set M.Carrier))

theorem smoothFn_openRestriction {f : M.Carrier → ℝ} (hf : SmoothFn f) :
    SmoothFn (M := openConnectedManifold M S hS) (fun x => f x.val) := by
  intro a
  apply ((hf a.val).mono (openInclusion_chartTarget_subset M S hS a)).congr
  intro z hz
  unfold inChart
  exact congrArg f (openInclusion_chartInv M S hS a hz)

theorem conformalScalar_smoothFn_openRestriction {u : M.Carrier → ℝ}
    (hu : SmoothFn u) {L : ℝ} (hL : 0 < L)
    (hlevel : ∀ x ∈ S, u x < L) :
    SmoothFn (conformalScalar (M := openConnectedManifold M S hS) (fun x => u x.val) L) := by
  intro a
  apply conformalProfile_contDiffOn.comp
    (((smoothFn_openRestriction M S hS hu) a).div_const L)
  intro z _
  exact (div_lt_one hL).mpr (hlevel (chartInv a z).val (chartInv a z).property)

end Yau.NodeProofs.F01Aux
