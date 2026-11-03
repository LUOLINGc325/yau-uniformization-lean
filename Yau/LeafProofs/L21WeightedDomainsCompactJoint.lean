import Yau.LeafProofs.L21WeightedDomainsScalarCore

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

def weightedCompactSOutput (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA : MatrixSmoothOn A (Metric.ball 0 1))
    (u : Fin n → CompactTest (Metric.ball (0 : X n) 1)) : WeightedTwoForm n K :=
  weightedCompactField K hK (weightedStrongRowsTest Yau.realVec (weightedSPrincipal A)
    (weightedSZeroOrder A) (weightedSPrincipal_smooth hA) (weightedSZeroOrder_smooth hA) u)

theorem weightedCompactS_graph (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA : MatrixSmoothOn A (Metric.ball 0 1))
    (u : Fin n → CompactTest (Metric.ball (0 : X n) 1)) :
    (weightedCompactField K hK u,weightedCompactSOutput K hK A hA u) ∈
      (weightedMaximalS K hK A hA).graph := by
  unfold weightedMaximalS
  rw [weightedMaximalRows_graph _ _ _ _ _ _ _ _ _ (weightedField_eq_zero_of_projections K)]
  apply weightedRowsGraph_of_smooth_representatives K hK _ _ _ _ _ _ _
    (weightedCompactField K hK u) (weightedCompactSOutput K hK A hA u) (fun x c => u c x)
  · exact fun c => (u c).property.1.contDiffOn
  · exact fun c => weightedCompactFieldProjection_rep K hK u c
  · intro r
    have hh := weightedCompactFieldProjection_rep K hK
      (weightedStrongRowsTest Yau.realVec (weightedSPrincipal A) (weightedSZeroOrder A)
        (weightedSPrincipal_smooth hA) (weightedSZeroOrder_smooth hA) u) r
    filter_upwards [hh] with x hx
    exact (weightedStrongRowsTest_apply _ _ _ _ _ u r x).symm.trans hx

theorem weightedCompactSOutput_rep (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA : MatrixSmoothOn A (Metric.ball 0 1))
    (u : Fin n → CompactTest (Metric.ball (0 : X n) 1)) :
    (weightedCompactSOutput K hK A hA u : X n → EuclideanSpace ℂ (Fin n × Fin n)) =ᵐ[weightedBallMeasure n K]
      (fun x => WithLp.toLp 2 (fun r => Yau.LeafProofs.L14Aux.complexFirstOrderSystemApply
        Yau.realVec (weightedSPrincipal A) (weightedSZeroOrder A) (fun y c => u c y) x r)) := by
  apply (weightedCompactField_coeFn K hK _).trans
  filter_upwards [] with x
  ext r
  exact weightedStrongRowsTest_apply _ _ _ _ _ u r x

def weightedCompactFormalTstarOutput (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA : MatrixSmoothOn A (Metric.ball 0 1))
    (u : Fin n → CompactTest (Metric.ball (0 : X n) 1)) : WeightedScalar n K :=
  compactToWeightedScalar K hK (weightedStrongRowsTest Yau.realVec (weightedTstarPrincipal A)
    (weightedTstarZeroOrder K A) (weightedTstarPrincipal_smooth hA) (weightedTstarZeroOrder_smooth K hA) u ())

theorem weightedCompactFormalTstar_graph (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA : MatrixSmoothOn A (Metric.ball 0 1))
    (u : Fin n → CompactTest (Metric.ball (0 : X n) 1)) :
    (weightedCompactField K hK u,weightedCompactFormalTstarOutput K hK A hA u) ∈
      (weightedMaximalFormalTstar K hK A hA).graph := by
  unfold weightedMaximalFormalTstar
  rw [weightedMaximalRows_graph _ _ _ _ _ _ _ _ _ (fun y hy => hy ())]
  apply weightedRowsGraph_of_smooth_representatives K hK _ _ _ _ _ _ _
    (weightedCompactField K hK u) (weightedCompactFormalTstarOutput K hK A hA u) (fun x c => u c x)
  · exact fun c => (u c).property.1.contDiffOn
  · exact fun c => weightedCompactFieldProjection_rep K hK u c
  · intro r
    cases r
    have hh := (compactToWeightedScalar_coeFn K hK
      (weightedStrongRowsTest Yau.realVec (weightedTstarPrincipal A) (weightedTstarZeroOrder K A)
        (weightedTstarPrincipal_smooth hA) (weightedTstarZeroOrder_smooth K hA) u ())).symm
    filter_upwards [hh] with x hx
    exact (weightedStrongRowsTest_apply _ _ _ _ _ u () x).symm.trans hx

theorem weightedCompactFormalTstarOutput_rep (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA : MatrixSmoothOn A (Metric.ball 0 1))
    (u : Fin n → CompactTest (Metric.ball (0 : X n) 1)) :
    (weightedCompactFormalTstarOutput K hK A hA u : X n → ℂ) =ᵐ[weightedBallMeasure n K]
      (fun x => Yau.LeafProofs.L14Aux.complexFirstOrderSystemApply Yau.realVec (weightedTstarPrincipal A)
        (weightedTstarZeroOrder K A) (fun y c => u c y) x ()) := by
  apply (compactToWeightedScalar_coeFn K hK _).trans
  exact Eventually.of_forall (fun x => weightedStrongRowsTest_apply _ _ _ _ _ u () x)

end Yau.LeafProofs.L21Aux
