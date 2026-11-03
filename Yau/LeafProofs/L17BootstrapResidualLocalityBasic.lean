import Yau.LeafProofs.L17PotentialMetricNaturality
import Yau.LeafProofs.L17BootstrapPatchHomeomorph

/-! Locality of the actual metric and the actual compactly supported forward map. -/
noncomputable section
open Set Metric Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius ComplexOrder
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace Yau.LeafProofs.L17BootstrapResidualLocalityAux
open L17Aux L17HolderAux L17SchauderAux L17BootstrapPatchAux

local instance residualLocalityBasicMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

/-- The canonical Levi derivative is local on spatial germs, without a regularity premise. -/
theorem potentialMetricMatrix_eq_of_spatial_germ
    (P : UniformChartPartition g) (T gamma : ℝ) (hT : 0 < T)
    (u v : SchauderSpace P T gamma hT) (q : Cylinder M T)
    (hGerm : (fun y => schauderFun v (y,q.2)) =ᶠ[𝓝 q.1]
      (fun y => schauderFun u (y,q.2))) :
    potentialMetricMatrix v q = potentialMetricMatrix u q := by
  simp only [potentialMetricMatrix,L22Aux.levi_congr_of_eventuallyEq hGerm]

/-- Closed physical support gives the spatial germ of the original function outside the patch. -/
theorem patch_spatial_germ_of_transport_values
    (P : UniformChartPartition g) (T gamma : ℝ) (hT : 0 < T)
    (u v : SchauderSpace P T gamma hT) {x : M.Carrier}
    (D : BootstrapPatch P x) (theta : ComplexVector n)
    (hValue : ∀ (y : M.Carrier) (t : Time T),
      schauderFun v (y,t) = schauderFun u (D.forward theta y,t))
    (y : M.Carrier) (hy : y ∉ D.supportSet) (t : Time T) :
    (fun z => schauderFun v (z,t)) =ᶠ[𝓝 y] (fun z => schauderFun u (z,t)) := by
  filter_upwards [D.supportSet_isCompact.isClosed.isOpen_compl.mem_nhds hy] with z hz
  rw [hValue,D.forward_eq_self_of_not_mem_support theta hz]

end Yau.LeafProofs.L17BootstrapResidualLocalityAux
