import Yau.LeafProofs.L21WeightedDomainsJointRows

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

/-- One and the same compact family approximates the input, the maximal
formal adjoint, and every ordered curl component in their actual Hilbert norms. -/
theorem weightedMaximal_joint_compact_graph_core (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA2 : MatrixSmoothOn A (Metric.ball 0 2))
    (v : WeightedOneForm n K) (g : WeightedScalar n K) (w : WeightedTwoForm n K)
    (hStar : (v,g) ∈ (weightedMaximalFormalTstar K hK A (weightedDomains_matrixSmoothOn_ball_one hA2)).graph)
    (hS : (v,w) ∈ (weightedMaximalS K hK A (weightedDomains_matrixSmoothOn_ball_one hA2)).graph) :
    ∃ U : ℕ → Fin n → CompactTest (Metric.ball (0 : X n) 1),
      Tendsto (fun m => weightedCompactField K hK (U m)) atTop (𝓝 v) ∧
      Tendsto (fun m => weightedCompactFormalTstarOutput K hK A
        (weightedDomains_matrixSmoothOn_ball_one hA2) (U m)) atTop (𝓝 g) ∧
      Tendsto (fun m => weightedCompactSOutput K hK A
        (weightedDomains_matrixSmoothOn_ball_one hA2) (U m)) atTop (𝓝 w) := by
  classical
  let hA := weightedDomains_matrixSmoothOn_ball_one hA2
  let a := weightedJointPrincipal A
  let b := weightedJointZeroOrder K A
  let p := weightedJointPrincipalFactor A
  let rawV := fun x c => (weightedFieldProjection K c v : X n → ℂ) x
  let rawW := fun x r => Sum.elim (fun _ : Unit => (g : X n → ℂ) x)
    (fun r => (weightedFieldProjection K r w : X n → ℂ) x) r
  obtain ⟨C,hC,hBound⟩ := weightedDomains_finite_principal_bound p
    (fun r c i => (weightedJointPrincipalFactor_smooth hA2 r c i).continuousOn)
  have hInput (c : Fin n) : MemLp (fun x => rawV x c) 2 (weightedBallMeasure n K) := Lp.memLp _
  have hOutput (r : WeightedJointRow n) : MemLp (fun x => rawW x r) 2 (weightedBallMeasure n K) := by
    cases r with
    | inl r => exact Lp.memLp g
    | inr r => exact Lp.memLp _
  have hRow : ∀ r (ψ : X n → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball 0 1 →
      (∫ x, (ψ x : ℂ)*rawW x r ∂Yau.lebesgueC n) =
        ∫ x, ∑ c, rawV x c*Yau.LeafProofs.L14Aux.complexFormalAdjointTestRow
          Yau.realVec a b r c ψ x ∂Yau.lebesgueC n := by
    intro r ψ hψ hc hs
    cases r with
    | inl r =>
      exact weightedRowsGraph_real_weak K hK _ _ _ _ _ _ _ _ _
        (weightedMaximalFormalTstar_graph_rows K hK A hA hStar) r ψ hψ hc hs
    | inr r =>
      exact weightedRowsGraph_real_weak K hK _ _ _ _ _ _ _ _ _
        (weightedMaximalS_graph_rows K hK A hA hS) r ψ hψ hc hs
  obtain ⟨U,hIn,hOut⟩ := weightedDomains_graph_core K hK Yau.realVec a p b
    (weightedJointPrincipal_smooth hA) (weightedJointZeroOrder_smooth K hA)
    (weightedJointPrincipal_factor A) (fun r c i => (weightedJointPrincipalFactor_smooth hA r c i).continuousOn)
    hC hBound rawV rawW hInput hOutput hRow
  refine ⟨U,?_,?_,?_⟩
  · apply weightedField_tendsto_of_representative_errors K _ _
      (fun m x c => U m c x) rawV
    · intro m c
      filter_upwards [weightedCompactField_coeFn K hK (U m)] with x hx
      exact congrArg (fun z : X n => z c) hx
    · intro c
      exact (weightedFieldProjection_coeFn K c v).symm
    · exact fun c => (hIn c).2
  · apply weightedScalar_tendsto_of_representative_errors K _ _
      (fun m x => Yau.LeafProofs.L14Aux.complexFirstOrderSystemApply Yau.realVec
        a b (fun y c => U m c y) x (Sum.inl ())) (g : X n → ℂ)
    · exact fun m => weightedCompactFormalTstarOutput_rep K hK A hA (U m)
    · exact EventuallyEq.rfl
    · exact (hOut (Sum.inl ())).2
  · apply weightedField_tendsto_of_representative_errors K _ _
      (fun m x r => Yau.LeafProofs.L14Aux.complexFirstOrderSystemApply Yau.realVec
        a b (fun y c => U m c y) x (Sum.inr r)) (fun x r => (weightedFieldProjection K r w : X n → ℂ) x)
    · intro m r
      filter_upwards [weightedCompactSOutput_rep K hK A hA (U m)] with x hx
      exact congrArg (fun z : EuclideanSpace ℂ (Fin n × Fin n) => z r) hx
    · intro r
      exact (weightedFieldProjection_coeFn K r w).symm
    · exact fun r => (hOut (Sum.inr r)).2

end Yau.LeafProofs.L21Aux
