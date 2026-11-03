import Yau.Proofs.F05BootstrapRegions
import Yau.Proofs.F05BootstrapHalfSpaceEstimate

/-! Spatial unique differentiation on the actual unbounded physical set. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_flat_closure_uniqueDiffOn (ν : Option (RIdx n)) :
    UniqueDiffOn ℝ (closure (F05FlatOpen ν)) := by
  cases ν with
  | none => simpa only [F05FlatOpen,closure_univ] using (uniqueDiffOn_univ (𝕜 := ℝ) (E := Space n))
  | some j =>
    have hEq : closure (F05FlatOpen (some j)) = {x : Space n | 0 ≤ inner ℝ (-(realVec j)) x} := by
      rw [F05FlatOpen_closure]
      ext x
      simp only [mem_setOf_eq,inner_neg_left,real_inner_comm,real_inner_realVec,neg_nonneg]
    rw [hEq]
    exact F05_halfSpace_uniqueDiffOn (by simp only [norm_neg,realVec_norm])

theorem F05_region_eq_flat_inter_ball (ν : Option (RIdx n)) (r : ℝ) :
    region ν r = closure (F05FlatOpen ν) ∩ Metric.closedBall (0 : Space n) r := by
  ext x
  cases ν <;> simp [F05FlatOpen_closure,region,Metric.mem_closedBall,dist_zero_right,and_comm]

theorem F05_region_mem_flat {ν : Option (RIdx n)} {r : ℝ} {x : Space n}
    (hx : x ∈ region ν r) : x ∈ closure (F05FlatOpen ν) := by
  rw [F05_region_eq_flat_inter_ball] at hx
  exact hx.1

end Yau.Proofs.F05Aux
