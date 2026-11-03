import Yau.LeafProofs.L21WeightedDomainsColumns

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

/-- The prescribed compact energy inequality alone yields a genuine small
scalar weak solution of each column equation, with exact constant one. -/
theorem weightedDomains_small_column_solution_of_compact_coercivity (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA2 : MatrixSmoothOn A (Metric.ball 0 2))
    (hMC : CommutesOn A (Metric.ball 0 1))
    (hCompact : ∀ v : Fin n → CompactTest (Metric.ball (0 : X n) 1),
      (∑ j, weightedScalarEnergy (boundaryWeight K) (v j)) ≤
        weightedScalarEnergy (boundaryWeight K) (fun x =>
          ∑ j, weightedDStar A (boundaryWeight K) j (fun y => (rho y : ℂ)*v j y) x)+
        ∑ i, ∑ j, weightedScalarEnergy (boundaryWeight K)
          (fun x => degenerateS A (fun y k => v k y) x i j))
    (k : Fin n) :
    ∃ u : X n → ℂ, MemLp u 2 (weightedBallMeasure n K) ∧
      LocallyL2On u (Metric.ball 0 1) ∧ DbarWeakOn A u (fun x j => A x j k) (Metric.ball 0 1) ∧
      (∫ x, ‖u x‖^2 ∂weightedBallMeasure n K) ≤
        ∑ j, ∫ x, ‖(rho x : ℂ)*A x j k‖^2 ∂weightedBallMeasure n K := by
  let hA := weightedDomains_matrixSmoothOn_ball_one hA2
  let T := weightedMaximalT K hK A hA
  let S := weightedMaximalS K hK A hA
  let f := weightedColumn K hK A hA2 k
  obtain ⟨z,hz,hTf⟩ := (LinearPMap.mem_graph_iff T).mp (weightedColumn_graph K hK A hA2 k)
  change T z = f at hTf
  have hf : f ∈ S.ker := by
    rw [← hTf]
    exact weightedMaximalT_range_subset_kernelS K hK A hA2 hMC z
  obtain ⟨u,hu,hNorm⟩ := exists_solution_of_hilbert_complex T S
    (weightedMaximalT_domain_dense K hK A hA) (weightedMaximalT_isClosed K hK A hA)
    (weightedMaximalS_isClosed K hK A hA) (weightedMaximalT_range_subset_kernelS K hK A hA2 hMC)
    (weightedMaximal_joint_coercivity K hK A hA2 hCompact) f hf
  refine ⟨((u : WeightedScalar n K) : X n → ℂ),Lp.memLp _,
    weightedScalar_locallyL2On K (u : WeightedScalar n K),?_,?_⟩
  · apply weightedMaximalT_graph_weak_scaled_representative K hK A hA (u : WeightedScalar n K) f (fun x j => A x j k)
    · have hh := T.mem_graph u
      rwa [hu] at hh
    · exact weightedColumn_rep K hK A hA2 k
  · calc
      _ = ‖(u : WeightedScalar n K)‖^2 := (weightedScalar_norm_sq K (u : WeightedScalar n K)).symm
      _ ≤ ‖f‖^2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hNorm
      _ = _ := weightedColumn_norm_sq K hK A hA2 k

end Yau.LeafProofs.L21Aux
