import Yau.LeafProofs.L21WeightedDomainsAdjoint

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem weightedCompactFormalTstarOutput_norm_sq (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA : MatrixSmoothOn A (Metric.ball 0 1))
    (u : Fin n → CompactTest (Metric.ball (0 : X n) 1)) :
    ‖weightedCompactFormalTstarOutput K hK A hA u‖^2 =
      weightedScalarEnergy (boundaryWeight K) (fun x =>
        ∑ j, weightedDStar A (boundaryWeight K) j (fun y => (rho y : ℂ)*u j y) x) := by
  unfold weightedCompactFormalTstarOutput
  rw [compactToWeightedScalar_norm_sq]
  congr 1
  funext x
  rw [weightedStrongRowsTest_apply]
  exact weightedTstarSystemApply_eq_formalTstar K A (fun y c => u c y) x
    (fun j => (u j).property.1.differentiable (by simp) x)

theorem weightedCompactSOutput_norm_sq (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA : MatrixSmoothOn A (Metric.ball 0 1))
    (u : Fin n → CompactTest (Metric.ball (0 : X n) 1)) :
    ‖weightedCompactSOutput K hK A hA u‖^2 = ∑ i, ∑ j,
      weightedScalarEnergy (boundaryWeight K) (fun x => degenerateS A (fun y k => u k y) x i j) := by
  unfold weightedCompactSOutput
  rw [weightedCompactField_norm_sq,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  funext x
  rw [weightedStrongRowsTest_apply,weightedSSystemApply_eq_degenerateS]

/-- The sole compact energy inequality extends to the true Hilbert adjoint
and maximal curl domains through the already proved common graph core. -/
theorem weightedMaximal_joint_coercivity (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA2 : MatrixSmoothOn A (Metric.ball 0 2))
    (hCompact : ∀ u : Fin n → CompactTest (Metric.ball (0 : X n) 1),
      (∑ j, weightedScalarEnergy (boundaryWeight K) (u j)) ≤
        weightedScalarEnergy (boundaryWeight K) (fun x =>
          ∑ j, weightedDStar A (boundaryWeight K) j (fun y => (rho y : ℂ)*u j y) x)+
        ∑ i, ∑ j, weightedScalarEnergy (boundaryWeight K)
          (fun x => degenerateS A (fun y k => u k y) x i j))
    (v : (weightedMaximalT K hK A (weightedDomains_matrixSmoothOn_ball_one hA2)).adjoint.domain)
    (hs : (v : WeightedOneForm n K) ∈ (weightedMaximalS K hK A (weightedDomains_matrixSmoothOn_ball_one hA2)).domain) :
    ‖(v : WeightedOneForm n K)‖^2 ≤
      ‖(weightedMaximalT K hK A (weightedDomains_matrixSmoothOn_ball_one hA2)).adjoint v‖^2+
      ‖(weightedMaximalS K hK A (weightedDomains_matrixSmoothOn_ball_one hA2)) ⟨v,hs⟩‖^2 := by
  let hA := weightedDomains_matrixSmoothOn_ball_one hA2
  obtain ⟨U,hInput,hStar,hS⟩ := weightedMaximal_joint_compact_graph_core K hK A hA2 v _ _
    (weightedMaximalT_adjoint_graph_formal K hK A hA2 v)
    ((weightedMaximalS K hK A hA).mem_graph ⟨v,hs⟩)
  apply le_of_tendsto_of_tendsto (hInput.norm.pow 2) ((hStar.norm.pow 2).add (hS.norm.pow 2))
  exact Eventually.of_forall (fun m => by
    dsimp only
    rw [weightedCompactField_norm_sq,weightedCompactFormalTstarOutput_norm_sq,weightedCompactSOutput_norm_sq]
    exact hCompact (U m))

end Yau.LeafProofs.L21Aux
