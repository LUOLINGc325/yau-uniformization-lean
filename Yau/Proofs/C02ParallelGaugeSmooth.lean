import Yau.Proofs.C02ParallelGaugeApply
import Yau.Proofs.C02TransportInitialPair

/-! Joint smoothness of the genuine radial frame as a map to the actual
tangent bundle. Every frame vector is the same chosen parallel transport. -/

noncomputable section
open scoped Manifold InnerProductSpace ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

def normalParallelTotalSpace (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (q : ComplexVector n × ComplexVector n) :
    TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  exact ⟨normalRealMap g p U q.1, normalParallelIsometry g p U hU q.1 q.2⟩

theorem normalParallelTotalSpace_eq_endpointVector (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (q : ComplexVector n × ComplexVector n) :
    normalParallelTotalSpace g p U hU q =
      realTransportVector (realParallelTransportFlow g
        (⟨p, (normalInitialLinearMap p U q.1, normalInitialLinearMap p U q.2)⟩ :
          realTransportBundle M) 1) := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  have hp := normalParallelIsometry_apply g p U hU q.1 q.2
  have ht := realParallelField_totalSpace g ⟨p, normalInitialLinearMap p U q.1⟩
    (normalInitialLinearMap p U q.2) 1
  exact (congrArg (fun w : TangentSpace 𝓘(ℝ, ComplexVector n) (normalRealMap g p U q.1) =>
    (⟨normalRealMap g p U q.1, w⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)) hp).trans ht

theorem normalParallelTotalSpace_smooth (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ContMDiff 𝓘(ℝ, ComplexVector n × ComplexVector n) (realPhaseModel n) ∞
      (normalParallelTotalSpace g p U hU) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := manifold_realTransport M
  letI := underlyingRealTangentNormedAddCommGroup g.form p
  letI := underlyingRealTangentInnerProductSpace g.form p
  let W := (normalInitialIsometryEquiv g.form p U hU).toContinuousLinearMap
  have hinit := transportInitialPair_smooth p
    (W.comp (ContinuousLinearMap.fst ℝ (ComplexVector n) (ComplexVector n)))
    (W.comp (ContinuousLinearMap.snd ℝ (ComplexVector n) (ComplexVector n)))
  have hend := (parallelTransportEndpointVector_smooth g).comp hinit
  have heq : (fun q : ComplexVector n × ComplexVector n =>
      realTransportVector (realParallelTransportFlow g
        (⟨p, (W q.1, W q.2)⟩ : realTransportBundle M) 1)) =
      normalParallelTotalSpace g p U hU :=
    funext (fun q => (normalParallelTotalSpace_eq_endpointVector g p U hU q).symm)
  rw [← heq]
  exact hend

end Yau.Blueprint.C02Proof
