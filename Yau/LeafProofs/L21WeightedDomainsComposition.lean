import Yau.LeafProofs.L21WeightedDomainsStrongIdentities
import Yau.LeafProofs.L21HilbertSolvability

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem weightedCompactT_mem_kernelS (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA : MatrixSmoothOn A (Metric.ball 0 1))
    (hMC : CommutesOn A (Metric.ball 0 1)) (ψ : CompactTest (Metric.ball (0 : X n) 1)) :
    (weightedMaximalT K hK A hA) (weightedCompactTPoint K hK A hA ψ) ∈
      (weightedMaximalS K hK A hA).ker := by
  let u := weightedStrongRowsTest Yau.realVec (weightedTPrincipal A) (fun _ _ _ => 0)
    (weightedTPrincipal_smooth hA) (fun _ _ => contDiffOn_const) (fun _ : Unit => ψ)
  have hu (x : X n) (j : Fin n) : u j x = degenerateT A ψ x j :=
    (weightedStrongRowsTest_apply _ _ _ _ _ _ j x).trans (weightedTSystemApply_eq_degenerateT A ψ x j)
  have hT : (weightedMaximalT K hK A hA) (weightedCompactTPoint K hK A hA ψ) =
      weightedCompactField K hK u := by
    apply Lp.ext
    filter_upwards [weightedCompactTPoint_apply_rep K hK A hA ψ,weightedCompactField_coeFn K hK u] with x hx hy
    rw [hx,hy]
    ext j
    exact (hu x j).symm
  have hOut : weightedCompactSOutput K hK A hA u = 0 := by
    apply Lp.ext
    filter_upwards [weightedCompactSOutput_rep K hK A hA u,
      Lp.coeFn_zero (E := EuclideanSpace ℂ (Fin n × Fin n)) (p := 2) (μ := weightedBallMeasure n K)] with x hx hz
    rw [hx,hz]
    ext r
    change Yau.LeafProofs.L14Aux.complexFirstOrderSystemApply Yau.realVec
      (weightedSPrincipal A) (weightedSZeroOrder A) (fun y c => u c y) x r = 0
    by_cases hxb : x ∈ Metric.ball (0 : X n) 1
    · rw [weightedSSystemApply_eq_degenerateS]
      have he : (fun y c => u c y) = degenerateT A ψ := by funext y c; exact hu y c
      rw [he]
      exact degenerateS_degenerateT_eq_zero Metric.isOpen_ball hA hMC ψ.property.1.contDiffOn hxb r.1 r.2
    · rw [← weightedStrongRowsTest_apply Yau.realVec (weightedSPrincipal A) (weightedSZeroOrder A)
        (weightedSPrincipal_smooth hA) (weightedSZeroOrder_smooth hA) u r x]
      exact image_eq_zero_of_notMem_tsupport (fun hx => hxb
        ((weightedStrongRowsTest Yau.realVec (weightedSPrincipal A) (weightedSZeroOrder A)
          (weightedSPrincipal_smooth hA) (weightedSZeroOrder_smooth hA) u r).property.2.2 hx))
  have hGraph := weightedCompactS_graph K hK A hA u
  rw [hOut,← hT] at hGraph
  obtain ⟨s,hs,hzero⟩ := (LinearPMap.mem_graph_iff (weightedMaximalS K hK A hA)).mp hGraph
  exact LinearPMap.mem_ker_iff.mpr ⟨s,hs.symm,hzero⟩

/-- The actual maximal weak complex has ST=0, by the genuine scalar graph
core and the closed kernel of S. -/
theorem weightedMaximalT_range_subset_kernelS (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA2 : MatrixSmoothOn A (Metric.ball 0 2))
    (hMC : CommutesOn A (Metric.ball 0 1))
    (u : (weightedMaximalT K hK A (weightedDomains_matrixSmoothOn_ball_one hA2)).domain) :
    (weightedMaximalT K hK A (weightedDomains_matrixSmoothOn_ball_one hA2)) u ∈
      (weightedMaximalS K hK A (weightedDomains_matrixSmoothOn_ball_one hA2)).ker := by
  obtain ⟨ψ,hInput,hOutput⟩ := weightedMaximalT_compact_graph_core K hK A hA2 u
  apply (closed_operator_kernel_isClosed _
    (weightedMaximalS_isClosed K hK A (weightedDomains_matrixSmoothOn_ball_one hA2))).mem_of_tendsto hOutput
  exact Eventually.of_forall (fun m => weightedCompactT_mem_kernelS K hK A
    (weightedDomains_matrixSmoothOn_ball_one hA2) hMC (ψ m))

end Yau.LeafProofs.L21Aux
