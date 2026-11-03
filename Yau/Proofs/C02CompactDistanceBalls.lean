import Yau.LeafProofs.L12
import Yau.LeafProofs.L23FieldMetric

noncomputable section
open Set
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem isCompact_closure_distBall (g : SmoothMetric M) (p : M.Carrier)
    (r : ℝ) (hr : 0 < r) : IsCompact (closure (distBall g.form p r)) := by
  apply (isCompact_inducedDistance_sublevel g p r).of_isClosed_subset isClosed_closure
  apply closure_minimal
  · intro x hx
    exact (mem_distBall_iff g p x hr).mp hx |>.le
  · exact isClosed_le
      (L23Aux.continuous_distFrom g.form (metricSmooth_of_smoothMetric g) p) continuous_const

end Yau.Blueprint.C02Proof
