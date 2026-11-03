import Yau.Proofs.V01EmbeddingChart
import Yau.Proofs.P03FieldChartCriteria
import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-! V01 scratch source: holomorphicity of the actual finite cotangent map,
using the canonical published P03 chart criteria. -/

noncomputable section
open Set
open scoped Manifold Topology ContDiff

namespace Yau.Blueprint.V01Proof

variable {n N m : ℕ} {M : ComplexManifold n}

theorem cotangentEmbeddingChart_differentiableOn
    (F : M.Carrier → ComplexVector N) (hF : IsHolomorphicVecMap F)
    (V : Fin m → VectorField M) (hV : ∀ j, IsHolomorphicField (V j))
    (x : M.Carrier) :
    DifferentiableOn ℂ (cotangentEmbeddingChart F V x) (cotangentTarget x) := by
  have hFchart : DifferentiableOn ℂ (inChart x F) (chartTarget x) :=
    (Yau.NodeProofs.P03Aux.mdifferentiable_iff_chartDifferentiable F).mp hF x
  have hFfst : DifferentiableOn ℂ
      (fun p : CotangentCoord n => F (chartInv x p.1)) (cotangentTarget x) :=
    hFchart.comp (by fun_prop) (fun _ hp => hp.1)
  apply (differentiableOn_piLp 2).mpr
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa [cotangentEmbeddingChart, Function.comp_def] using
      (EuclideanSpace.proj j).differentiable.comp_differentiableOn hFfst
  · have hVchart : DifferentiableOn ℂ (fieldCoords (V j) x) (chartTarget x) :=
      (Yau.NodeProofs.P03Aux.holomorphicField_iff_chartDifferentiable (V j)).mp (hV j) x
    have hVfst : DifferentiableOn ℂ
        (fun p : CotangentCoord n => fieldCoords (V j) x p.1) (cotangentTarget x) :=
      hVchart.comp (by fun_prop) (fun _ hp => hp.1)
    have hsum : DifferentiableOn ℂ
        (fun p : CotangentCoord n => ∑ b, (fieldCoords (V j) x p.1) b * p.2 b)
          (cotangentTarget x) := by
      apply DifferentiableOn.fun_sum
      intro b _
      have hη : DifferentiableOn ℂ (fun p : CotangentCoord n => p.2 b)
          (cotangentTarget x) :=
        ((EuclideanSpace.proj b).comp
          (ContinuousLinearMap.snd ℂ (ComplexVector n) (ComplexVector n))).differentiable.differentiableOn
      exact ((EuclideanSpace.proj b).differentiable.comp_differentiableOn hVfst).mul hη
    simpa [cotangentEmbeddingChart, Function.comp_def] using hsum

theorem cotangentEmbedding_holomorphic
    (F : M.Carrier → ComplexVector N) (hF : IsHolomorphicVecMap F)
    (V : Fin m → VectorField M) (hV : ∀ j, IsHolomorphicField (V j)) :
    CotangentHolomorphic (cotangentEmbedding F V) := by
  intro x
  apply (cotangentEmbeddingChart_differentiableOn F hF V hV x).congr
  intro p hp
  exact cotangentEmbedding_in_chart F V x hp

end Yau.Blueprint.V01Proof
