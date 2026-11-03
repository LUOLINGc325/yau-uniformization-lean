import Yau.Proofs.F01OpenFunctions
import Yau.Proofs.F01OpenMetricSmooth
import Yau.Proofs.F01SmoothContinuity

/-! Concrete approximating backgrounds on the base-point component of each
large open sublevel. Completeness and bounded geometry are proved separately;
this construction supplies actual manifolds, metrics and chartwise smoothness. -/
open Set TopologicalSpace
open scoped Manifold ContDiff
noncomputable section
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} (M : ComplexManifold n)

def sublevelOpens (u : M.Carrier → ℝ) (hu : SmoothFn u) (o : M.Carrier) (L : ℝ) :
    Opens M.Carrier := by
  letI : LocallyConnectedSpace M.Carrier :=
    ChartedSpace.locallyConnectedSpace (ComplexVector n) M.Carrier
  exact ⟨sublevelComponent u o L,
    sublevelComponent_isOpen (continuous_of_smoothFn hu) o L⟩

def sublevelManifold (u : M.Carrier → ℝ) (hu : SmoothFn u) (o : M.Carrier)
    (L : ℝ) (ho : u o < L) : ComplexManifold n :=
  openConnectedManifold M (sublevelOpens M u hu o L) (sublevelComponent_isConnected ho)

def approximatingMetric (g : HermitianField M) (u : M.Carrier → ℝ) (hu : SmoothFn u)
    (o : M.Carrier) (L : ℝ) (ho : u o < L) :
    HermitianField (sublevelManifold M u hu o L ho) :=
  conformalField
    (openRestrictedField M (sublevelOpens M u hu o L) (sublevelComponent_isConnected ho) g)
    (conformalScalar (fun x => u x.val) L)

theorem approximatingMetric_metricSmooth {g : HermitianField M}
    (hg : MetricSmooth g) {u : M.Carrier → ℝ} (hu : SmoothFn u)
    (o : M.Carrier) {L : ℝ} (hL : 0 < L) (ho : u o < L) :
    MetricSmooth (approximatingMetric M g u hu o L ho) := by
  apply conformalField_metricSmooth
    (openRestrictedField_metricSmooth M (sublevelOpens M u hu o L)
      (sublevelComponent_isConnected ho) hg)
  apply conformalScalar_smoothFn_openRestriction M (sublevelOpens M u hu o L)
    (sublevelComponent_isConnected ho) hu hL
  intro x hx
  exact sublevelComponent_subset u o L hx

/-- Membership is in the same base-point component, stronger than merely
belonging to the open sublevel. It is retained in every constructed point. -/
theorem sublevelManifold_point_mem (u : M.Carrier → ℝ) (hu : SmoothFn u)
    (o : M.Carrier) (L : ℝ) (ho : u o < L)
    (x : (sublevelManifold M u hu o L ho).Carrier) :
    x.val ∈ sublevelComponent u o L := x.property

theorem sublevelManifold_point_level (u : M.Carrier → ℝ) (hu : SmoothFn u)
    (o : M.Carrier) (L : ℝ) (ho : u o < L)
    (x : (sublevelManifold M u hu o L ho).Carrier) : u x.val < L :=
  sublevelComponent_subset u o L x.property

end Yau.NodeProofs.F01Aux
