import Yau.Proofs.P06Resolvent
import Yau.Proofs.P06GraphEnergy

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

/-- Positive resolvents of the actual complete Hodge core have genuine raw
L² form representatives, and satisfy the original second-order graph law. -/
theorem hodgeMinimal_positiveRange (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f : RealForm M 2) (hf : L2RealForm g.form μ f)
    (lam : ℝ) (hlam : 0 < lam) :
    ∃ A W : RealForm M 2, OperatorCandidates.HodgeMinimalGraph g.form μ A W ∧
      ∀ᵐ x ∂μ, W x + lam • A x = f x := by
  let T := hodgeCoreOperator g μ hμ 2
  have hd : Dense (T.domain : Set (L2FormHilbert g μ 2)) := hodgeCoreOperator_domain_dense g μ hμ 2
  have hc : T.IsClosable := hodgeCoreOperator_closable g μ hμ 2
  have hs : T.IsFormalAdjoint T := hodgeCoreOperator_symmetric g μ hμ 2
  have hp : ∀ u : T.domain, 0 ≤ inner ℝ (u : L2FormHilbert g μ 2) (T u) :=
    hodgeCoreOperator_nonnegative g μ hμ 2
  have he : T.closure = T.adjoint := hodgeCoreOperator_closure_eq_adjoint g μ hμ 2
  have hdc : Dense (T.closure.domain : Set (L2FormHilbert g μ 2)) := hd.mono T.le_closure.1
  have hself := realClosure_selfAdjoint T hd hc hs he
  have hpc := realClosure_nonnegative T hc hp
  obtain ⟨a, w, haw, hsum⟩ := positiveSelfAdjoint_range T.closure hdc hself hpc hlam
    (realizeActualForm g μ f hf)
  obtain ⟨A, hA, ha⟩ := l2FormHilbert_exists_section g μ a
  obtain ⟨W, hW, hw⟩ := l2FormHilbert_exists_section g μ w
  have hmin : OperatorCandidates.HodgeMinimalGraph g.form μ A W := by
    apply (hodgeMinimalGraph_iff_operator_closure g μ hμ A W hA hW).mpr
    rw [ha, hw]
    exact haw
  have hsumL : L2RealForm g.form μ (W + lam • A) :=
    l2RealForm_add g μ W (lam • A) hW (l2RealForm_smul g μ lam A hA)
  have hr : realizeActualForm g μ (W + lam • A) hsumL = realizeActualForm g μ f hf := by
    have hmap : realizeActualForm g μ (W + lam • A) hsumL =
        realizeActualForm g μ W hW + lam • realizeActualForm g μ A hA := by
      change ((L2FormSpace.ofSection W hW + lam • L2FormSpace.ofSection A hA :
        L2FormSpace g μ 2) : L2FormHilbert g μ 2) = _
      rw [UniformSpace.Completion.coe_add, UniformSpace.Completion.coe_smul]
      rfl
    rw [hmap]
    change realizeL2Form g μ (L2FormSpace.ofSection W hW) +
      lam • realizeL2Form g μ (L2FormSpace.ofSection A hA) = _
    rw [ha, hw]
    exact hsum
  refine ⟨A, W, hmin, ?_⟩
  exact (realizeL2Form_eq_iff_ae g μ (L2FormSpace.ofSection (W + lam • A) hsumL)
    (L2FormSpace.ofSection f hf)).mp hr

/-- The third original form-domain conclusion, with its exact prequotient
Friedrichs relation and positive shift equation. -/
theorem friedrichsHodge_positiveRange (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f : RealForm M 2) (lam : ℝ)
    (hf : L2RealForm g.form μ f) (hlam : 0 < lam) :
    ∃ A W, FriedrichsHodgeRelation g.form μ A W ∧
      ∀ᵐ x ∂μ, W x + lam • A x = f x := by
  obtain ⟨A, W, hmin, heq⟩ := hodgeMinimal_positiveRange g μ hμ f hf lam hlam
  exact ⟨A, W, hodgeMinimalGraph_friedrichs g μ hμ hmin, heq⟩

/-- The complete original form-domain target, including its resolvent range,
is now a theorem of the actual complete metric and Riemannian volume. -/
theorem hodgeFormDomain (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) : HodgeFormDomainTarget g.form μ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro A dA δA dB δB hA hB
    exact formGraph_unique g μ hμ A dA dB δA δB hA hB
  · intro A W Z hW hZ
    exact friedrichsHodge_unique g μ hμ A W Z hW hZ
  · intro f lam hf hlam
    exact friedrichsHodge_positiveRange g μ hμ f lam hf hlam
  · intro A W hA hW hcA hF
    exact friedrichsHodge_represents g μ hμ A W hA hW hcA hF
  · intro A hA hcA
    exact friedrichsHodge_core g μ hμ A hA hcA

end Yau.NodeProofs.P06Aux
