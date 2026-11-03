import Yau.Proofs.F03DyadicPartition
import Yau.Blueprint.Analytic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-! The actual dyadic gluing is locally a finite sum, including at both time faces. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau Blueprint
variable {n : ℕ} {M : ComplexManifold n}

def dyadicGluing (u : M.Carrier → ℝ) (F : ℕ → M.Carrier → ℝ → ℝ)
    (x : M.Carrier) (t : ℝ) : ℝ :=
  ∑' j : ℕ,dyadicPartition j (u x)*F j x t

theorem dyadicGluing_eq_sum_of_tail (u : M.Carrier → ℝ)
    (F : ℕ → M.Carrier → ℝ → ℝ) (x : M.Carrier) (t : ℝ) (N : ℕ)
    (hTail : ∀ j,N ≤ j → dyadicPartition j (u x)=0) :
    dyadicGluing u F x t=∑ j ∈ Finset.range N,dyadicPartition j (u x)*F j x t := by
  apply tsum_eq_sum
  intro j hj
  rw [hTail j (by simpa only [Finset.mem_range,not_lt] using hj),zero_mul]

theorem dyadicGluing_smoothSpaceC1Time (u : M.Carrier → ℝ) (hu : SmoothFn u)
    (F : ℕ → M.Carrier → ℝ → ℝ) {I : Set ℝ}
    (hF : ∀ j,SmoothSpaceC1Time (F j) I) :
    SmoothSpaceC1Time (dyadicGluing u F) I := by
  constructor
  · intro t ht a z hz
    obtain ⟨N,V,hV,hVz,hTail⟩ := dyadicPartition_locally_eventually_zero (u (chartInv a z))
    have hCont : ContinuousWithinAt (fun w => u (chartInv a w)) (chartTarget a) z :=
      (hu a).continuousOn z hz
    have hEq : (fun w => dyadicGluing u F (chartInv a w) t) =ᶠ[𝓝[chartTarget a] z]
        (fun w => ∑ j ∈ Finset.range N,dyadicPartition j (u (chartInv a w))*F j (chartInv a w) t) := by
      filter_upwards [hCont.eventually (hV.mem_nhds hVz)] with w hw
      exact dyadicGluing_eq_sum_of_tail u F _ _ N (fun j hj => hTail j hj _ hw)
    have hSum : ContDiffOn ℝ ∞ (fun w =>
        ∑ j ∈ Finset.range N,dyadicPartition j (u (chartInv a w))*F j (chartInv a w) t)
        (chartTarget a) := by
      apply ContDiffOn.sum
      intro j _
      exact ((dyadicPartition_contDiff j).comp_contDiffOn (hu a)).mul ((hF j).1 t ht a)
    exact (hSum z hz).congr_of_eventuallyEq_of_mem hEq hz
  · intro a p hp
    obtain ⟨N,V,hV,hVp,hTail⟩ := dyadicPartition_locally_eventually_zero (u (chartInv a p.1))
    have huj : ContDiffOn ℝ 1 (fun q : ComplexVector n × ℝ => u (chartInv a q.1))
        (chartTarget a ×ˢ I) :=
      ((hu a).comp contDiffOn_fst (fun q hq => hq.1)).of_le (by simp)
    have hEq : (fun q : ComplexVector n × ℝ => dyadicGluing u F (chartInv a q.1) q.2)
        =ᶠ[𝓝[chartTarget a ×ˢ I] p]
        (fun q => ∑ j ∈ Finset.range N,dyadicPartition j (u (chartInv a q.1))*F j (chartInv a q.1) q.2) := by
      filter_upwards [(huj.continuousOn p hp).eventually (hV.mem_nhds hVp)] with q hq
      exact dyadicGluing_eq_sum_of_tail u F _ _ N (fun j hj => hTail j hj _ hq)
    have hSum : ContDiffOn ℝ 1 (fun q : ComplexVector n × ℝ =>
        ∑ j ∈ Finset.range N,dyadicPartition j (u (chartInv a q.1))*F j (chartInv a q.1) q.2)
        (chartTarget a ×ˢ I) := by
      apply ContDiffOn.sum
      intro j _
      exact (((dyadicPartition_contDiff j).of_le (by simp)).comp_contDiffOn huj).mul ((hF j).2 a)
    exact (hSum p hp).congr_of_eventuallyEq_of_mem hEq hp

end Yau.Proofs.F03Aux
