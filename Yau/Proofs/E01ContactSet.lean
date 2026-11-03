import Yau.Proofs.E01QuadraticFiber
import Yau.Proofs.E01LowerGap

/-! Compactness of the actual unit contact set for lower semicontinuous data. -/

noncomputable section
open scoped Matrix ComplexOrder

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {n : ℕ}

def unitContactSet (v : ComplexVector n → EReal) : Set (ComplexVector n) :=
  {η | η ∈ Metric.sphere 0 1 ∧ v η = 1}

theorem unitContactSet_norm {v : ComplexVector n → EReal}
    {η : ComplexVector n} (hη : η ∈ unitContactSet v) : ‖η‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using hη.1

theorem isCompact_unitContactSet
    (v : ComplexVector n → EReal)
    (hv : LowerSemicontinuousOn v (Metric.sphere 0 1))
    (hlower : ∀ η ∈ Metric.sphere (0 : ComplexVector n) 1, (1 : EReal) ≤ v η) :
    IsCompact (unitContactSet v) := by
  have hk := hv.isCompact_inter_preimage_Iic
    (isCompact_sphere (0 : ComplexVector n) 1) (1 : EReal)
  convert hk using 1
  ext η
  change (η ∈ Metric.sphere 0 1 ∧ v η = 1) ↔
    (η ∈ Metric.sphere 0 1 ∧ v η ≤ 1)
  constructor
  · exact fun h => ⟨h.1, h.2.le⟩
  · exact fun h => ⟨h.1, le_antisymm h.2 (hlower η h.1)⟩

theorem continuous_contactRankOne :
    Continuous (contactRankOne (n := n)) := by
  unfold contactRankOne Matrix.vecMulVec
  fun_prop

theorem isCompact_contact_generators
    (v : ComplexVector n → EReal)
    (hv : LowerSemicontinuousOn v (Metric.sphere 0 1))
    (hlower : ∀ η ∈ Metric.sphere (0 : ComplexVector n) 1, (1 : EReal) ≤ v η) :
    IsCompact (contactRankOne '' unitContactSet v) :=
  (isCompact_unitContactSet v hv hlower).image continuous_contactRankOne

end Yau.NodeProofs.E01Aux
