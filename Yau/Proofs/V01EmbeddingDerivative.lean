import Yau.Proofs.V01EmbeddingDerivativeData
import Yau.Proofs.V01EmbeddingHolomorphic

/-! V01 scratch source: identify the explicit block operator with the
genuine complex derivative at an actual point of the fixed chart target. -/

noncomputable section
open scoped Manifold Topology ContDiff

namespace Yau.Blueprint.V01Proof

variable {n N m : ℕ} {M : ComplexManifold n}

theorem cotangentEmbeddingChart_hasFDerivAt
    (F : M.Carrier → ComplexVector N) (hF : IsHolomorphicVecMap F)
    (V : Fin m → VectorField M) (hV : ∀ j, IsHolomorphicField (V j))
    (x : M.Carrier) (p : CotangentCoord n) (hp : p ∈ cotangentTarget x) :
    HasFDerivAt (cotangentEmbeddingChart F V x) (embeddingChartDerivative F V x p) p := by
  have hFchart : DifferentiableAt ℂ (inChart x F) p.1 :=
    ((Yau.NodeProofs.P03Aux.mdifferentiable_iff_chartDifferentiable F).mp hF x).differentiableAt
      ((isOpen_extChartAt_target x).mem_nhds hp.1)
  have hFD : HasFDerivAt (fun q : CotangentCoord n => F (chartInv x q.1))
      ((fderiv ℂ (inChart x F) p.1).comp
        (ContinuousLinearMap.fst ℂ (ComplexVector n) (ComplexVector n))) p :=
    hFchart.hasFDerivAt.comp p hasFDerivAt_fst
  unfold cotangentEmbeddingChart embeddingChartDerivative
  apply (PiLp.hasFDerivAt_toLp (𝕜 := ℂ) 2 _).comp p
  apply hasFDerivAt_pi.mpr
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [Fin.addCases_left, Function.comp_def, EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj j).hasFDerivAt.comp p hFD
  · have hVchart : DifferentiableAt ℂ (fieldCoords (V j) x) p.1 :=
      ((Yau.NodeProofs.P03Aux.holomorphicField_iff_chartDifferentiable (V j)).mp (hV j) x).differentiableAt
        ((isOpen_extChartAt_target x).mem_nhds hp.1)
    have hVD : HasFDerivAt (fun q : CotangentCoord n => fieldCoords (V j) x q.1)
        ((fderiv ℂ (fieldCoords (V j) x) p.1).comp
          (ContinuousLinearMap.fst ℂ (ComplexVector n) (ComplexVector n))) p :=
      hVchart.hasFDerivAt.comp p hasFDerivAt_fst
    have hsum : HasFDerivAt
        (fun q : CotangentCoord n => ∑ b, (fieldCoords (V j) x q.1) b * q.2 b)
        (∑ b, (p.2 b • ((EuclideanSpace.proj b).comp
          ((fderiv ℂ (fieldCoords (V j) x) p.1).comp
            (ContinuousLinearMap.fst ℂ (ComplexVector n) (ComplexVector n)))) +
          (fieldCoords (V j) x p.1) b • ((EuclideanSpace.proj b).comp
            (ContinuousLinearMap.snd ℂ (ComplexVector n) (ComplexVector n))))) p := by
      apply HasFDerivAt.fun_sum
      intro b _
      have h₁ := (EuclideanSpace.proj b).hasFDerivAt.comp p hVD
      have h₂ := (EuclideanSpace.proj b).hasFDerivAt.comp p
        (hasFDerivAt_snd (𝕜 := ℂ) (p := p))
      convert h₁.mul h₂ using 1 <;>
        first | rfl | simp only [Function.comp_def, EuclideanSpace.coe_proj, add_comm]
    simpa only [Fin.addCases_right] using hsum

end Yau.Blueprint.V01Proof
