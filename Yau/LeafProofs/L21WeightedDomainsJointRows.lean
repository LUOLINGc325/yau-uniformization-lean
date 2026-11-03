import Yau.LeafProofs.L21WeightedDomainsCompactJoint

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

abbrev WeightedJointRow (n : ℕ) := Unit ⊕ (Fin n × Fin n)

def weightedJointPrincipal (A : X n → Matrix (Fin n) (Fin n) ℂ) :
    WeightedJointRow n → Fin n → Yau.RIdx n → X n → ℂ :=
  Sum.elim (weightedTstarPrincipal A) (weightedSPrincipal A)

def weightedJointZeroOrder (K : ℝ) (A : X n → Matrix (Fin n) (Fin n) ℂ) :
    WeightedJointRow n → Fin n → X n → ℂ :=
  Sum.elim (weightedTstarZeroOrder K A) (weightedSZeroOrder A)

def weightedJointPrincipalFactor (A : X n → Matrix (Fin n) (Fin n) ℂ) :
    WeightedJointRow n → Fin n → Yau.RIdx n → X n → ℂ :=
  Sum.elim (fun _ j a x => -star (dbarRealCoefficient A j a x))
    (fun r k a x => (if k = r.2 then dbarRealCoefficient A r.1 a x else 0)-
      (if k = r.1 then dbarRealCoefficient A r.2 a x else 0))

theorem weightedJointPrincipal_smooth
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A (Metric.ball 0 1))
    (r : WeightedJointRow n) (c : Fin n) (a : Yau.RIdx n) :
    ContDiffOn ℝ ∞ (weightedJointPrincipal A r c a) (Metric.ball 0 1) := by
  cases r with
  | inl r => exact weightedTstarPrincipal_smooth hA r c a
  | inr r => exact weightedSPrincipal_smooth hA r c a

theorem weightedJointZeroOrder_smooth (K : ℝ)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A (Metric.ball 0 1))
    (r : WeightedJointRow n) (c : Fin n) :
    ContDiffOn ℝ ∞ (weightedJointZeroOrder K A r c) (Metric.ball 0 1) := by
  cases r with
  | inl r => exact weightedTstarZeroOrder_smooth K hA r c
  | inr r => exact weightedSZeroOrder_smooth hA r c

theorem weightedJointPrincipalFactor_smooth {O : Set (X n)}
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    (r : WeightedJointRow n) (c : Fin n) (a : Yau.RIdx n) :
    ContDiffOn ℝ ∞ (weightedJointPrincipalFactor A r c a) O := by
  cases r with
  | inl r =>
    exact ((starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn (dbarRealCoefficient_smoothOn hA c a)).neg
  | inr r =>
    apply ContDiffOn.sub
    · split_ifs <;> first | exact dbarRealCoefficient_smoothOn hA _ _ | exact contDiffOn_const
    · split_ifs <;> first | exact dbarRealCoefficient_smoothOn hA _ _ | exact contDiffOn_const

theorem weightedJointPrincipal_factor
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (r : WeightedJointRow n) (c : Fin n)
    (a : Yau.RIdx n) (x : X n) :
    weightedJointPrincipal A r c a x = (rho x : ℂ)*weightedJointPrincipalFactor A r c a x := by
  cases r with
  | inl r => simp [weightedJointPrincipal,weightedJointPrincipalFactor,weightedTstarPrincipal]
  | inr r => rfl

theorem weightedMaximalFormalTstar_graph_rows (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA : MatrixSmoothOn A (Metric.ball 0 1))
    {u : WeightedOneForm n K} {g : WeightedScalar n K}
    (hGraph : (u,g) ∈ (weightedMaximalFormalTstar K hK A hA).graph) :
    (u,g) ∈ weightedRowsGraph K hK (weightedFieldProjection K)
      (fun _ : Unit => ContinuousLinearMap.id ℂ (WeightedScalar n K)) Yau.realVec
      (weightedTstarPrincipal A) (weightedTstarZeroOrder K A)
      (weightedTstarPrincipal_smooth hA) (weightedTstarZeroOrder_smooth K hA) := by
  change (u,g) ∈ (weightedMaximalRows K hK _ _ _ _ _ _ _).graph at hGraph
  rwa [weightedMaximalRows_graph _ _ _ _ _ _ _ _ _ (fun y hy => hy ())] at hGraph

theorem weightedMaximalS_graph_rows (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA : MatrixSmoothOn A (Metric.ball 0 1))
    {u : WeightedOneForm n K} {g : WeightedTwoForm n K}
    (hGraph : (u,g) ∈ (weightedMaximalS K hK A hA).graph) :
    (u,g) ∈ weightedRowsGraph K hK (weightedFieldProjection K) (weightedFieldProjection K) Yau.realVec
      (weightedSPrincipal A) (weightedSZeroOrder A) (weightedSPrincipal_smooth hA) (weightedSZeroOrder_smooth hA) := by
  change (u,g) ∈ (weightedMaximalRows K hK _ _ _ _ _ _ _).graph at hGraph
  rwa [weightedMaximalRows_graph _ _ _ _ _ _ _ _ _ (weightedField_eq_zero_of_projections K)] at hGraph

end Yau.LeafProofs.L21Aux
