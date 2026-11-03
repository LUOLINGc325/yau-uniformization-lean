import Yau.LeafProofs.L21WeightedDomainsPrincipal

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem weightedDomains_apply_eq_of_graph
    {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (T : E →ₗ.[ℂ] F) {x : E} {y : F} (h : (x,y) ∈ T.graph) (hx : x ∈ T.domain) :
    T ⟨x,hx⟩ = y := by
  obtain ⟨u,hu,he⟩ := (LinearPMap.mem_graph_iff T).mp h
  change (u : E) = x at hu
  have hEq : u = ⟨x,hx⟩ := Subtype.ext hu
  simpa only [hEq] using he

def weightedCompactTPoint (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA : MatrixSmoothOn A (Metric.ball 0 1))
    (ψ : CompactTest (Metric.ball (0 : X n) 1)) : (weightedMaximalT K hK A hA).domain :=
  ⟨compactToWeightedScalar K hK ψ,weightedCompactT_mem_domain K hK A hA ψ⟩

theorem weightedCompactTPoint_apply_rep (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA : MatrixSmoothOn A (Metric.ball 0 1))
    (ψ : CompactTest (Metric.ball (0 : X n) 1)) :
    ((weightedMaximalT K hK A hA) (weightedCompactTPoint K hK A hA ψ) : X n → X n) =ᵐ[weightedBallMeasure n K]
      (fun x => WithLp.toLp 2 (degenerateT A ψ x)) := by
  obtain ⟨f,hGraph,hRep⟩ := weightedCompactT_graph K hK A hA ψ
  have he := weightedDomains_apply_eq_of_graph (weightedMaximalT K hK A hA) hGraph
    (weightedCompactT_mem_domain K hK A hA ψ)
  change (weightedMaximalT K hK A hA) (weightedCompactTPoint K hK A hA ψ) = f at he
  rw [he]
  exact hRep

/-- Scalar compact tests form a genuine graph core for the actual maximal T. -/
theorem weightedMaximalT_compact_graph_core (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA2 : MatrixSmoothOn A (Metric.ball 0 2))
    (u : (weightedMaximalT K hK A (weightedDomains_matrixSmoothOn_ball_one hA2)).domain) :
    ∃ ψ : ℕ → CompactTest (Metric.ball (0 : X n) 1),
      Tendsto (fun m => (weightedCompactTPoint K hK A (weightedDomains_matrixSmoothOn_ball_one hA2) (ψ m) :
        WeightedScalar n K)) atTop (𝓝 (u : WeightedScalar n K)) ∧
      Tendsto (fun m => (weightedMaximalT K hK A (weightedDomains_matrixSmoothOn_ball_one hA2))
        (weightedCompactTPoint K hK A (weightedDomains_matrixSmoothOn_ball_one hA2) (ψ m))) atTop
        (𝓝 ((weightedMaximalT K hK A (weightedDomains_matrixSmoothOn_ball_one hA2)) u)) := by
  classical
  let hA := weightedDomains_matrixSmoothOn_ball_one hA2
  let T := weightedMaximalT K hK A hA
  let f := T u
  let p := fun j (_ : Unit) a => dbarRealCoefficient A j a
  obtain ⟨C,hC,hBound⟩ := weightedDomains_finite_principal_bound p
    (fun j _ a => (dbarRealCoefficient_smoothOn hA2 j a).continuousOn)
  have hGraph := T.mem_graph u
  change ((u : WeightedScalar n K),f) ∈ (weightedMaximalRows K hK
    (fun _ : Unit => ContinuousLinearMap.id ℂ (WeightedScalar n K)) (weightedFieldProjection K)
    Yau.realVec (weightedTPrincipal A) (fun _ _ _ => 0)
    (weightedTPrincipal_smooth hA) (fun _ _ => contDiffOn_const)).graph at hGraph
  rw [weightedMaximalRows_graph _ _ _ _ _ _ _ _ _ (weightedField_eq_zero_of_projections K)] at hGraph
  obtain ⟨U,hIn,hOut⟩ := weightedDomains_graph_core K hK Yau.realVec
    (weightedTPrincipal A) p (fun _ _ _ => 0) (weightedTPrincipal_smooth hA) (fun _ _ => contDiffOn_const)
    (fun _ _ _ _ => rfl) (fun j _ a => (dbarRealCoefficient_smoothOn hA j a).continuousOn) hC hBound
    (fun x (_ : Unit) => (u : WeightedScalar n K) x)
    (fun x j => (weightedFieldProjection K j f : X n → ℂ) x)
    (fun _ => Lp.memLp _) (fun _ => Lp.memLp _)
    (weightedRowsGraph_real_weak K hK _ _ _ _ _ _ _ _ _ hGraph)
  refine ⟨fun m => U m (),?_,?_⟩
  · exact weightedScalar_tendsto_of_representative_errors K _ _
      (fun m x => U m () x) (u : X n → ℂ)
      (fun m => compactToWeightedScalar_coeFn K hK (U m ())) (EventuallyEq.rfl) (hIn ()).2
  · apply weightedField_tendsto_of_representative_errors K _ _
      (fun m x j => Yau.LeafProofs.L14Aux.complexFirstOrderSystemApply Yau.realVec
        (weightedTPrincipal A) (fun _ _ _ => 0) (fun y c => U m c y) x j)
      (fun x j => (weightedFieldProjection K j f : X n → ℂ) x)
    · intro m j
      filter_upwards [weightedCompactTPoint_apply_rep K hK A hA (U m ())] with x hx
      rw [hx]
      change degenerateT A (U m ()) x j = _
      rw [← weightedTSystemApply_eq_degenerateT]
    · intro j
      exact (weightedFieldProjection_coeFn K j f).symm
    · exact fun j => (hOut j).2

end Yau.LeafProofs.L21Aux
