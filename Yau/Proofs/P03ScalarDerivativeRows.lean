import Yau.Proofs.P03ScalarFrameDifferentials
import Yau.Proofs.P03SpanParameters
import Yau.LeafProofs.L17HolomorphicRegularity

open scoped Manifold Topology
open Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ} {M : ComplexManifold n}

def functionDerivativeCoordinates (f : holomorphicFunctions M) (a : M.Carrier)
    (z : ComplexVector n) : ComplexVector n :=
  WithLp.toLp 2 (fun k => fderiv ℂ (inChart a (f.1 : M.Carrier → ℂ)) z (stdVec k))

theorem derivativeCoordinates_pairing (f : holomorphicFunctions M) (a : M.Carrier)
    (z : ComplexVector n) (q : Fin n → ℂ) :
    coordinatePairing q (functionDerivativeCoordinates f a z) =
      fderiv ℂ (inChart a (f.1 : M.Carrier → ℂ)) z (WithLp.toLp 2 q) := by
  rw [coordinatePairing_apply]
  calc
    (∑ k, q k * functionDerivativeCoordinates f a z k) =
        ∑ k, fderiv ℂ (inChart a (f.1 : M.Carrier → ℂ)) z (stdVec k) * q k := by
      apply Finset.sum_congr rfl
      intro k _
      exact mul_comm _ _
    _ = _ := (linearFunctional_coordinates
      (fderiv ℂ (inChart a (f.1 : M.Carrier → ℂ)) z).toLinearMap (WithLp.toLp 2 q)).symm

theorem derivativeRows_span_top_iff_tupleDerivative_injective {N : ℕ}
    (f : Fin N → holomorphicFunctions M) (a : M.Carrier) (z : ComplexVector n) :
    Submodule.span ℂ (range fun j => functionDerivativeCoordinates (f j) a z) = ⊤ ↔
      Function.Injective (tupleDerivativeCLM a f z) := by
  rw [span_top_iff_annihilatorEvaluation_injective]
  constructor
  · intro ha v w h
    have hq : WithLp.ofLp v = WithLp.ofLp w := ha (by
      ext j
      rw [annihilatorEvaluationCLM_apply, annihilatorEvaluationCLM_apply,
        derivativeCoordinates_pairing, derivativeCoordinates_pairing]
      exact congrFun h j)
    exact (WithLp.equiv 2 (Fin n → ℂ)).injective hq
  · intro ht q q' h
    have hv : WithLp.toLp 2 q = WithLp.toLp 2 q' := ht (by
      ext j
      have hj := congrFun h j
      rw [annihilatorEvaluationCLM_apply, annihilatorEvaluationCLM_apply,
        derivativeCoordinates_pairing, derivativeCoordinates_pairing] at hj
      exact hj)
    exact congrArg WithLp.ofLp hv

theorem functionDerivativeCoordinates_differentiableOn (f : holomorphicFunctions M)
    (a : M.Carrier) : DifferentiableOn ℂ (functionDerivativeCoordinates f a) (chartTarget a) := by
  apply (differentiableOn_piLp 2).mpr
  intro k
  exact Yau.LeafProofs.L17Holomorphic.differentiableOn_directional_of_complex
    (isOpen_extChartAt_target a)
    ((mdifferentiable_iff_chartDifferentiable (f.1 : M.Carrier → ℂ)).mp f.2 a) (stdVec k)

theorem functionDerivativeCoordinates_joint_continuousOn (a : M.Carrier) :
    ContinuousOn (fun p : holomorphicFunctions M × ComplexVector n =>
      functionDerivativeCoordinates p.1 a p.2) (univ ×ˢ chartTarget a) := by
  have hc : ContinuousOn (fun p : holomorphicFunctions M × ComplexVector n =>
      fun k : Fin n => fderiv ℂ (inChart a (p.1.1 : M.Carrier → ℂ)) p.2 (stdVec k))
      (univ ×ˢ chartTarget a) := by
    apply continuousOn_pi.mpr
    intro k
    exact (continuousOn_chart_derivativeEvaluation a).clm_apply continuousOn_const
  exact (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).comp_continuousOn hc

end Yau.NodeProofs.P03Aux
